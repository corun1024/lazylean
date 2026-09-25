#include "kernel.h"
#include "kam.h"
#include "fuse.h"
#include "fix.h"
#include "nbe.h"
#ifdef LL_CALLGRIND
#include <valgrind/callgrind.h>
#endif
#include <iostream>
#include <chrono>
#include <thread>
#include <cstring>
#include <algorithm>
#include <unordered_set>
#include <fstream>
#include <sys/resource.h>
#include <cstdlib>
#include <malloc.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>
#include <atomic>

namespace ll { extern bool g_strict_metadata; }
void dump_census();
using namespace ll;

// LL_MEMREPORT: resident and peak memory at points of the run (from /proc/self/status)
static void mem_report(const char* where) {
  static const bool on = getenv("LL_MEMREPORT") != nullptr;
  if (!on) return;
  FILE* f = fopen("/proc/self/status", "r"); if (!f) return;
  char line[256]; long rss = 0, hwm = 0;
  while (fgets(line, sizeof line, f)) { sscanf(line, "VmRSS: %ld", &rss); sscanf(line, "VmHWM: %ld", &hwm); }
  fclose(f);
  struct mallinfo2 mi = mallinfo2();
  std::cerr << "mem " << where << ": rss " << rss / 1024 << " MB, peak " << hwm / 1024 << " MB; malloc in use " << (mi.uordblks >> 20)
            << " MB (heap " << (mi.arena >> 20) << " MB, mmapped " << (mi.hblkhd >> 20) << " MB, free in heap " << (mi.fordblks >> 20) << " MB)\n";
}
static double now() {
  using namespace std::chrono;
  return duration<double>(steady_clock::now().time_since_epoch()).count();
}

struct Options {
  std::string file;
  bool verbose = false;
  bool trust_inductives = false;
  bool keep_going = false;
  double slow = 1.0;
  unsigned max_depth = 0;
  size_t max_rss_mb = 0;
  std::string progress;  // file rewritten at the start of each checked declaration
  std::string trust_file; // declarations named in this file (one per line) are added unchecked
  std::vector<std::string> print;   // --print NAME: print the constant's type and value after loading
  std::string only;      // check only this declaration (others added unchecked)
  std::string stop_at;   // stop after this declaration
  long from_line = 0;    // declarations before this line are added without checking
  long count = 0;        // stop after checking this many declarations (0: no limit)
  unsigned shard = 0, nshards = 1;   // check only declarations with index % nshards == shard
  unsigned jobs = 1;     // worker processes, forked after the export is parsed
};


// ---------------------------------------------------------------- parallel checking
//
// Declarations are checked by `--jobs N` worker processes forked after the export has been
// parsed, so the parse and the interning of the permanent tier happen once and the workers
// share them read-only through copy-on-write.  Each worker walks the whole declaration list in
// order, exactly as a single process does, claiming declarations as it reaches them: a claimed
// declaration is checked, an unclaimed one is added to the worker's own environment unchecked.
// Claiming is an atomic exchange on a shared flag, so every declaration is checked by exactly
// one worker, and a worker held up by an expensive declaration simply claims fewer.
struct Shared {
  std::atomic<unsigned char> stop;       // set when a worker rejects and the run is to end
  std::atomic<unsigned char> claim[1];   // one flag per declaration, allocated past the struct
};
struct WorkerAbort { std::atomic<unsigned char> stop; };
struct WorkerResult {
  size_t ok, failed, unchecked, steps, peak_exprs;
  double check_time;
  long max_rss_kb;
  int status;        // 0 fine, 1 a declaration was rejected, 2 declined, 3 the worker died
};

// Checking a declaration against an environment that already holds *later* declarations would
// accept a circular export (A's proof cites B, B's cites A, neither ever established).  A
// single process is protected by construction, because a later constant is simply not there
// yet.  Workers are not, so the order is verified once, up front: every constant a declaration
// mentions must be introduced by an earlier declaration, or by that same declaration.
// Add a declaration's constants without checking them (the loader's data, plus the two fields
// the checker derives on the way in).
static void add_unchecked(Environment& env, const Decl& d) {
  for (auto c : d.consts) {
    if (c.kind == CKind::Rec) {
      Expr t = c.type; u32 idx = 0;
      while (is_pi(t)) { if (idx == c.rec_major_idx()) { Expr I = get_app_fn(binding_dom(t)); if (is_const(I)) c.major_induct = const_name(I); } t = binding_body(t); idx++; }
    }
    if (c.kind == CKind::Quot && c.quot_kind == QuotKind::Ind) env.quot_init = true;
    env.add(c);
  }
}

static Shared* g_shared = nullptr;         // claim flags, shared with the workers
static WorkerResult* g_results = nullptr;  // one slot per worker
static int g_worker = -1;                  // this process's worker index, -1 = not a worker

// Finish a worker.  A forked worker runs on the copy of the checking thread and has no main
// thread to return to, so it reports through shared memory and leaves by _Exit.
[[noreturn]] static void worker_exit(size_t ok, size_t failed, size_t unchecked, size_t steps,
                                     size_t peak_exprs, double check_time) {
  WorkerResult& r = g_results[g_worker];
  r.ok = ok; r.failed = failed; r.unchecked = unchecked; r.steps = steps;
  r.peak_exprs = peak_exprs; r.check_time = check_time;
  struct rusage ru; getrusage(RUSAGE_SELF, &ru); r.max_rss_kb = ru.ru_maxrss;
  r.status = failed ? 1 : 0;
  std::cerr.flush();
  std::_Exit(failed ? 1 : 0);
}

static bool check_topological_order(const ExportFile& ef) {
  std::vector<u32> intro;   // Name -> 1 + index of the declaration that introduces it
  for (size_t i = 0; i < ef.decls.size(); i++)
    for (const ConstInfo& c : ef.decls[i].consts) {
      Name n = c.name;
      if (n >= intro.size()) intro.resize(std::max<size_t>(n + 1, intro.size() * 2 + 1024), 0);
      if (!intro[n]) intro[n] = (u32)i + 1;
    }
  // latest[e] = 1 + the latest declaration that introduces a constant occurring in e (0: none).
  // The export writes a term's parts before the term, so one pass in handle order computes it
  // for every node; a declaration is then one comparison, instead of a walk over its terms that
  // revisits every shared subterm.  What is verified is that nothing cites a later declaration:
  // a declaration that cites its own constants is rejected by the checker itself, which hides
  // them while it runs, except where the kernel allows it (an inductive block, an unsafe or
  // partial definition).
  const u32 n = (u32)g_exprs->size();
  std::vector<u32> latest(n, 0);
  for (u32 e = 0; e < n; e++) {
    const ExprNode& nd = raw(e);
    u32 v = 0;
    auto child = [&](u32 c) -> bool { if (c >= e) return false; v = std::max(v, latest[c]); return true; };
    bool ok = true;
    switch (nd.kind) {
      case EKind::Const: v = nd.name < intro.size() ? intro[nd.name] : 0; break;
      case EKind::App: case EKind::Lam: case EKind::Pi: ok = child(nd.a) && child(nd.b); break;
      case EKind::Let: ok = child(nd.a) && child(nd.b) && child(nd.c); break;
      case EKind::Proj: ok = child(nd.b); break;
      default: break;
    }
    if (!ok) fail("declaration order: a term refers to a later term");   // not possible for a loaded export
    latest[e] = v;
  }
  for (size_t i = 0; i < ef.decls.size(); i++) {
    const Decl& d = ef.decls[i];
    u32 worst = 0; Expr at = NIL;
    auto see = [&](Expr e) { if (e != NIL && e < n && latest[e] > worst) { worst = latest[e]; at = e; } };
    for (const ConstInfo& c : d.consts) { see(c.type); see(c.value); for (const RecRule& r : c.rules) see(r.rhs); }
    if (worst > i + 1) {
      // find the constant, for the message
      Name bad = 0;
      std::vector<Expr> todo{at};
      while (!todo.empty() && !bad) {
        Expr e = todo.back(); todo.pop_back();
        const ExprNode& nd = raw(e);
        if (latest[e] != worst) continue;
        switch (nd.kind) {
          case EKind::Const: bad = nd.name; break;
          case EKind::App: case EKind::Lam: case EKind::Pi: todo.push_back(nd.a); todo.push_back(nd.b); break;
          case EKind::Let: todo.push_back(nd.a); todo.push_back(nd.b); todo.push_back(nd.c); break;
          case EKind::Proj: todo.push_back(nd.b); break;
          default: break;
        }
      }
      std::cerr << "FAIL " << name_str(d.consts[0].name) << " (line " << d.line
                << "): declaration order: it cites '" << (bad ? name_str(bad) : std::string("?"))
                << "', which is only introduced later (declaration " << (worst - 1) << ")\n";
      return false;
    }
  }
  return true;
}

static int run(const Options& opt) {
  init_names();
  g_levels = new LevelTable();
  g_exprs = new ExprTable();
  double t0 = now();
  ExportFile ef = load_export(opt.file, opt.verbose);
  double t1 = now();
  mem_report("after load");
  { struct stat st; if (stat(opt.file.c_str(), &st) == 0) nbe_size_sessions((size_t)st.st_size); }
  std::cerr << "loaded " << ef.decls.size() << " declarations, " << ef.nexprs << " exprs (" << g_exprs->size()
            << " unique), " << ef.nnames << " names in " << (t1 - t0) << "s\n";
  kam_init();
  g_exprs->freeze();
  if (!opt.print.empty()) {
    for (const Decl& d : ef.decls) for (const ConstInfo& c : d.consts) for (auto& want : opt.print) if (name_str(c.name) == want) {
      std::cerr << "== " << want << " : " << expr_str(c.type) << "\n";
      if (c.value != NIL) std::cerr << "   := " << expr_str(c.value) << "\n";
      std::cerr << "   hint " << (c.kind == CKind::Def ? std::to_string((int)c.hint) + "/" + std::to_string(c.height) : std::string("-")) << "\n";
    }
    return 0;
  }
  g_max_rss_kb = opt.max_rss_mb * 1024;

  Environment env;
  std::vector<pid_t> kids;
  bool prebuilt = false;
  // Any mode that checks a declaration against an environment holding declarations it has not
  // itself checked needs the export's order verified first; a single unsharded process gets the
  // same guarantee for free, because a later constant is simply not there yet.
  { double to = now();
    if ((opt.jobs > 1 || opt.nshards > 1) && !check_topological_order(ef)) return 1;
    if (opt.jobs > 1 || opt.nshards > 1) std::cerr << "declaration order verified in " << (now() - to) << "s\n"; }
  if (opt.jobs > 1) {
    size_t nd = ef.decls.size();
    size_t claim_bytes = sizeof(std::atomic<unsigned char>) * (nd + 1);
    void* cm = mmap(nullptr, claim_bytes, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    void* rm = mmap(nullptr, sizeof(WorkerResult) * opt.jobs, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    if (cm == MAP_FAILED || rm == MAP_FAILED) { std::cerr << "error: cannot map shared memory for --jobs\n"; return 1; }
    memset(cm, 0, claim_bytes); memset(rm, 0, sizeof(WorkerResult) * opt.jobs);
    g_shared = (Shared*)cm; g_results = (WorkerResult*)rm;
    // Build the environment once, here, so the workers inherit it instead of each walking the
    // whole declaration list to rebuild it -- that walk does not shrink as workers are added.
    // Checking a declaration against an environment that also holds the later ones is sound
    // because the order was just verified: nothing cites a constant introduced after it.
    double tb = now();
    size_t nconsts = 0; for (const Decl& d : ef.decls) nconsts += d.consts.size();
    env.consts.reserve(nconsts * 2 + 1024);   // no reallocation in a worker: it would copy the lot
    for (const Decl& d : ef.decls) add_unchecked(env, d);
    prebuilt = true;
    std::cerr << "environment built in " << (now() - tb) << "s; checking with " << opt.jobs
              << " worker processes\n";
    std::cerr.flush();
    for (unsigned k = 0; k < opt.jobs; k++) {
      pid_t pid = fork();
      if (pid == 0) { g_worker = (int)k; kids.clear(); break; }
      if (pid < 0) { std::cerr << "error: fork failed\n"; return 1; }
      kids.push_back(pid);
    }
    if (g_worker < 0) {
      // the parent only waits: every declaration is checked by one of the workers
      WorkerResult tot{}; bool died = false;
      for (size_t k = 0; k < kids.size(); k++) {
        int wst = 0; waitpid(kids[k], &wst, 0);
        if (WIFEXITED(wst) && WEXITSTATUS(wst) == 1) died = died;   // a rejection, reported below
        if (!WIFEXITED(wst) || WEXITSTATUS(wst) > 1) {
          std::cerr << "FAIL worker " << k << " died ("
                    << (WIFSIGNALED(wst) ? "signal " + std::to_string(WTERMSIG(wst))
                                         : "exit " + std::to_string(WEXITSTATUS(wst))) << ")\n";
          died = true;
        }
        const WorkerResult& r = g_results[k];
        tot.ok += r.ok; tot.failed += r.failed; tot.unchecked += r.unchecked; tot.steps += r.steps;
        tot.peak_exprs = std::max(tot.peak_exprs, r.peak_exprs);
        tot.max_rss_kb = std::max(tot.max_rss_kb, r.max_rss_kb);
        tot.check_time = std::max(tot.check_time, r.check_time);
      }
      double wall = now() - t1;
      double cpu = 0; for (size_t k = 0; k < kids.size(); k++) cpu += g_results[k].check_time;
      std::cerr << "checked " << tot.ok << " declarations, " << tot.failed << " failed, in "
                << wall << "s wall (" << (cpu / 3600) << " core-hours over " << opt.jobs
                << " workers); " << tot.steps << " reduction steps; peak " << (tot.max_rss_kb / 1024)
                << " MB in one worker\n";
      return (died || tot.failed) ? 1 : 0;
    }
  }

  size_t ok = 0, failed = 0, unchecked = 0;
  struct { u64 steps = 0; } st;
  std::vector<std::pair<double, std::string>> slow;
  size_t peak_exprs = 0;
  size_t di = 0;
  std::unordered_set<std::string> trusted;
  if (!opt.trust_file.empty()) {
    std::ifstream tf(opt.trust_file); std::string line;
    while (std::getline(tf, line)) if (!line.empty()) trusted.insert(line);
    std::cerr << "trusting " << trusted.size() << " named declarations (added unchecked)\n";
  }
  for (Decl& d : ef.decls) {
    // the declaration's name as a string, built only when something needs it
    const Name dname = d.consts[0].name;
    std::string nm_s; bool nm_ok = false;
    auto nm = [&]() -> const std::string& { if (!nm_ok) { nm_s = name_str(dname); nm_ok = true; } return nm_s; };
    bool check = true;
    size_t my_index = di++;
    if (opt.nshards > 1 && (my_index % opt.nshards) != opt.shard) check = false;
    // one worker per declaration: whoever reaches it first takes it
    if (check && g_shared && g_shared->claim[my_index].exchange(1) != 0) check = false;
    if (g_shared && g_shared->stop.load(std::memory_order_relaxed)) break;   // another worker rejected
    if (!opt.only.empty() && nm() != opt.only) check = false;
    if (!trusted.empty() && trusted.count(nm())) check = false;
    if (opt.from_line && (long)d.line < opt.from_line) check = false;
    double s = now();
    if (check && !opt.progress.empty()) {
      FILE* pf = fopen(g_worker >= 0 ? (opt.progress + "." + std::to_string(g_worker)).c_str() : opt.progress.c_str(), "w");
      if (pf) { fprintf(pf, "%zu/%zu line %zu ok %zu failed %zu elapsed %.0fs\n%s\n", my_index, ef.decls.size(), d.line, ok, failed, now() - t1, nm().c_str()); fclose(pf); }
    }
#ifdef LL_CALLGRIND
    { static bool on = false; if (check && !on) { on = true; CALLGRIND_START_INSTRUMENTATION; } }
#endif
    try {
      if (check) {
        if (prebuilt) for (const ConstInfo& c : d.consts) env.hide(c.name);   // let check_and_add add them
        check_decl(env, d);
        ok++;
      } else if (!prebuilt) {
        add_unchecked(env, d);
        unchecked++;
      }
    } catch (KernelError& e) {
      failed++;
      std::cerr << "FAIL " << nm() << " (line " << d.line << "): " << e.what() << "\n";
      if (!opt.keep_going) {
        if (g_shared) g_shared->stop.store(1, std::memory_order_relaxed);
        if (g_worker >= 0) worker_exit(ok, failed, unchecked, st.steps, peak_exprs, now() - t1);
        return 1;
      }
      // A failed declaration may have left a lot of capacity behind: give it back, so that the
      // resident-set limit does not keep tripping on the declarations that follow.
      g_lctx.decls.clear(); g_exprs->trim(); kam_pools_trim(); malloc_trim(0);
      // add unchecked so later declarations can proceed
      for (auto c : d.consts) if (!env.contains(c.name)) env.add(c);
    }
    double dt = now() - s;
    if (g_exprs->size() > peak_exprs) peak_exprs = g_exprs->size();
    if (check && getenv("LL_HIST") && !opt.only.empty()) dump_census();
    fix_before_reclaim();
    g_exprs->reclaim();
    fix_after_reclaim();
    g_lctx.decls.clear();
    nbe_between_decls();
    // The environment has its own copy of what it needs: the export's is no longer used.
    std::vector<ConstInfo>().swap(d.consts);
    { static const bool mr = getenv("LL_MEMREPORT") != nullptr; static long last = 0;
      static const unsigned every = mr && atoi(getenv("LL_MEMREPORT")) == 2 ? 0 : 255;   // LL_MEMREPORT=2: after every declaration
      if (mr && (ok & every) == 0) {
        FILE* f = fopen("/proc/self/status", "r"); char line[256]; long hwm = 0;
        if (f) { while (fgets(line, sizeof line, f)) sscanf(line, "VmHWM: %ld", &hwm); fclose(f); }
        if (hwm > last + 51200) { std::cerr << "mem peak " << hwm / 1024 << " MB at declaration " << ok << " " << nm() << "\n"; last = hwm; }
      } }
    if (dt > opt.slow) slow.emplace_back(dt, nm());
    if (opt.verbose) std::cerr << (check ? "ok   " : "skip ") << nm() << " " << dt << "s\n";
    if (!opt.stop_at.empty() && nm() == opt.stop_at) break;
    if (opt.count && (long)(ok + failed) >= opt.count) break;
  }
  double t2 = now();
  if (g_worker >= 0) worker_exit(ok, failed, unchecked, st.steps, peak_exprs, t2 - t1);
  std::cerr << "checked " << ok << " declarations, " << failed << " failed, " << unchecked << " added unchecked, in "
            << (t2 - t1) << "s; " << g_exprs->size() << " exprs live\n";
  mem_report("end");
  if (getenv("LL_MEMREPORT")) {
    size_t ci = 0; for (const ConstInfo& c : env.consts) ci += sizeof(ConstInfo) + (c.lparams.capacity() + c.all.capacity() + c.ctors.capacity()) * 4 + c.rules.capacity() * sizeof(RecRule);
    size_t di = 0; for (const Decl& d : ef.decls) { di += sizeof(Decl); for (const ConstInfo& c : d.consts) di += sizeof(ConstInfo) + (c.lparams.capacity() + c.all.capacity() + c.ctors.capacity()) * 4 + c.rules.capacity() * sizeof(RecRule); }
    std::cerr << "env consts " << env.consts.size() << " (" << (ci >> 20) << " MB), export decls " << ef.decls.size() << " (" << (di >> 20) << " MB), names " << g_names->nodes.size() << " x " << sizeof(NameNode) << " B\n";
  }
  nbe_report();
  std::cerr << "machine: app " << g_k_app << ", bvar " << g_k_bvar << ", beta " << g_k_beta << ", let " << g_k_let << ", delta " << g_k_delta << ", iota " << g_k_iota << ", proj " << g_k_proj << ", enter value/delayed/re-eval " << g_k_enter_val << "/" << g_k_enter_delayed << "/" << g_k_reeval << ", memo hit/insert " << g_k_memo_hit << "/" << g_k_memo_ins << "\n";
  { std::cerr << "intern: permanent probes " << g_int_perm_probe << " (hits " << g_int_perm_hit << "), temporary hits " << g_int_temp_hit << ", new " << g_int_new << "; by kind";
    const char* kn[] = {"bvar","fvar","sort","const","app","lam","pi","let","lit","proj","clos"};
    for (int i = 0; i < 11; i++) std::cerr << " " << kn[i] << " " << g_int_kind[i];
    std::cerr << "\n"; }
  if (g_fix) std::cerr << "fixpoint rules: derived " << g_fix_derived << ", rejected " << g_fix_rejected << ", applied " << g_fix_applied << "\n";
  if (g_fuse) std::cerr << "fusion: bodies " << g_fuse_bodies << ", unfolds " << g_fuse_unfolds << ", betas " << g_fuse_betas << ", iotas " << g_fuse_iotas << ", projs " << g_fuse_projs << ", overflows " << g_fuse_overflows << "\n";
  if (getenv("LL_HIST")) {
    auto dump = [](const char* title, std::unordered_map<u32, u64>& h) {
      std::vector<std::pair<u64, u32>> v; for (auto& kv : h) v.push_back({kv.second, kv.first});
      std::sort(v.rbegin(), v.rend()); std::cerr << title << "\n";
      for (size_t i = 0; i < v.size() && i < 25; i++) std::cerr << "  " << v[i].first << "  " << name_str(v[i].second) << "\n";
    };
    dump("delta unfoldings per constant:", g_delta_hist); dump("iota per recursor:", g_iota_hist);
  }
  std::cerr << "nat ops: " << g_nat_ops << ", first-operand limbs " << g_nat_limbs << ", GMP " << g_nat_cycles / 1e9 << " Gcycles, literal interning " << g_natlit_cycles / 1e9 << " Gcycles\n";
  KamStats ks = kam_stats();
  std::cerr << "peak exprs in a declaration: " << peak_exprs << "; thunk pool " << ks.thunk_chunks * 4096 * sizeof(Thunk) / (1 << 20)
            << " MB; env pool " << ks.env_chunks * 4096 * sizeof(Env) / (1 << 20) << " MB; thunks live/total " << ks.thunks_live << "/" << ks.thunks_total
            << "; envs live/total " << ks.envs_live << "/" << ks.envs_total << "; peak live thunks " << ks.thunks_max << ", envs " << ks.envs_max << ", frames " << ks.max_frames << "\n";
  std::sort(slow.begin(), slow.end());
  for (size_t i = slow.size(); i-- > 0 && i + 10 >= slow.size();) std::cerr << "  slow: " << slow[i].second << " " << slow[i].first << "s\n";
  return failed ? 1 : 0;
}

// The LL_HIST live-thunk census, printed before the declaration's temporary expressions are
// reclaimed (the census keys are expression handles of that tier).
void dump_census() {
  { std::cerr << "live thunks at peak (" << g_site_peak_total << "):"; for (int i = 0; i < 8; i++) if (g_site_peak[i]) std::cerr << " " << g_site_names[i] << " " << g_site_peak[i] << ","; std::cerr << " | by state: delayed " << g_state_peak[0] << ", evaluating " << g_state_peak[1] << ", value " << g_state_peak[2] + g_state_peak[3] << "\n";
    std::vector<std::pair<long, Expr>> v; for (auto& kv : g_peak_by_term) if (kv.second > 0) v.push_back({kv.second, kv.first});
    std::sort(v.rbegin(), v.rend()); for (size_t i = 0; i < v.size() && i < 12; i++) { std::string t = expr_str(v[i].second); if (t.size() > 160) t = t.substr(0, 160) + "..."; std::cerr << "  " << v[i].first << "  " << t << "\n"; }
    std::cerr << "live values at peak by head:\n"; v.clear(); for (auto& kv : g_peak_by_head) if (kv.second > 0) v.push_back({kv.second, kv.first});
    std::sort(v.rbegin(), v.rend()); for (size_t i = 0; i < v.size() && i < 14; i++) { std::string t = expr_str(v[i].second); if (t.size() > 120) t = t.substr(0, 120) + "..."; std::cerr << "  " << v[i].first << "  " << t << "\n"; } }
}

int main(int argc, char** argv) {
  Options opt;
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    if (a == "-v" || a == "--verbose") opt.verbose = true;
    else if (a == "-k" || a == "--keep-going") opt.keep_going = true;
    else if (a == "--only" && i + 1 < argc) opt.only = argv[++i];
    else if (a == "--stop-at" && i + 1 < argc) opt.stop_at = argv[++i];
    else if (a == "--from-line" && i + 1 < argc) opt.from_line = atol(argv[++i]);
    else if (a == "--count" && i + 1 < argc) opt.count = atol(argv[++i]);
    else if (a == "--slow" && i + 1 < argc) opt.slow = atof(argv[++i]);
    else if (a == "--max-rss" && i + 1 < argc) opt.max_rss_mb = atol(argv[++i]);   // MB
    else if (a == "--progress" && i + 1 < argc) opt.progress = argv[++i];
    else if (a == "--trust-file" && i + 1 < argc) opt.trust_file = argv[++i];
    else if (a == "--print" && i + 1 < argc) opt.print.push_back(argv[++i]);
    else if (a == "--memo") g_memo = 1;
    else if (a == "--strict-metadata") g_strict_metadata = true;
    else if (a == "--no-memo") g_memo = 0;
    else if ((a == "-j" || a == "--jobs") && i + 1 < argc) opt.jobs = (unsigned)atoi(argv[++i]);
    else if (a == "--shard" && i + 1 < argc) { std::string s = argv[++i]; size_t p = s.find('/'); opt.shard = atoi(s.substr(0, p).c_str()); opt.nshards = atoi(s.substr(p + 1).c_str()); }
    else if (a[0] == '-') { std::cerr << "unknown option " << a << "\n"; return 2; }
    else opt.file = a;
  }
  if (opt.file.empty()) { std::cerr << "usage: lazylean [options] export.ndjson\n"; return 2; }
  // Run on a thread with a large stack: the checker is recursive.
  int rc = 0;
  pthread_attr_t attr; pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, (size_t)4 << 30);
  pthread_t th;
  struct Arg { const Options* o; int* rc; } arg{&opt, &rc};
  pthread_create(&th, &attr, [](void* p) -> void* {
    Arg* a = (Arg*)p;
    try { *a->rc = run(*a->o); }
    catch (std::exception& e) { std::cerr << "error: " << e.what() << "\n"; *a->rc = 1; }
    return nullptr;
  }, &arg);
  pthread_join(th, nullptr);
  std::cerr.flush(); std::cout.flush();
  if (getenv("LL_EXIT_NORMAL")) exit(rc);   // profilers (gprof) need the atexit handlers
  std::_Exit(rc);   // skip global destructors: freeing millions of pooled thunks and exprs at exit is wasted time
}
