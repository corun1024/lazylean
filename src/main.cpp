#include "tc.h"
#include "kam.h"
#include "fuse.h"
#include "fix.h"
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

namespace ll { extern bool g_strict_metadata; }
void dump_census();
using namespace ll;

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
  unsigned shard = 0, nshards = 1;   // check only declarations with index % nshards == shard
};

static int run(const Options& opt) {
  init_names();
  g_levels = new LevelTable();
  g_exprs = new ExprTable();
  double t0 = now();
  ExportFile ef = load_export(opt.file, opt.verbose);
  double t1 = now();
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
  if (opt.max_depth) g_max_depth = opt.max_depth;
  if (g_engine == 2 && !getenv("LL_FIX")) g_fix = 0;   // the differential mode compares whnf results syntactically; fixpoint rules change their shape
  g_max_rss_kb = opt.max_rss_mb * 1024;
  Environment env;
  size_t ok = 0, failed = 0, unchecked = 0;
  CheckStats st;
  std::vector<std::pair<double, std::string>> slow;
  size_t peak_exprs = 0;
  size_t di = 0;
  std::unordered_set<std::string> trusted;
  if (!opt.trust_file.empty()) {
    std::ifstream tf(opt.trust_file); std::string line;
    while (std::getline(tf, line)) if (!line.empty()) trusted.insert(line);
    std::cerr << "trusting " << trusted.size() << " named declarations (added unchecked)\n";
  }
  for (const Decl& d : ef.decls) {
    std::string nm = name_str(d.consts[0].name);
    bool check = true;
    size_t my_index = di++;
    if (opt.nshards > 1 && (my_index % opt.nshards) != opt.shard) check = false;
    if (!opt.only.empty() && nm != opt.only) check = false;
    if (!trusted.empty() && trusted.count(nm)) check = false;
    if (opt.from_line && (long)d.line < opt.from_line) check = false;
    double s = now();
    if (check && !opt.progress.empty()) {
      FILE* pf = fopen(opt.progress.c_str(), "w");
      if (pf) { fprintf(pf, "%zu/%zu line %zu ok %zu failed %zu elapsed %.0fs\n%s\n", my_index, ef.decls.size(), d.line, ok, failed, now() - t1, nm.c_str()); fclose(pf); }
    }
    try {
      if (check) {
        check_and_add(env, d, opt.trust_inductives, st);
        ok++;
      } else {
        for (auto c : d.consts) {
          if (c.kind == CKind::Rec) {
            Expr t = c.type; u32 idx = 0;
            while (is_pi(t)) { if (idx == c.rec_major_idx()) { Expr I = get_app_fn(binding_dom(t)); if (is_const(I)) c.major_induct = const_name(I); } t = binding_body(t); idx++; }
          }
          if (c.kind == CKind::Quot && c.quot_kind == QuotKind::Ind) env.quot_init = true;
          env.add(c);
        }
        unchecked++;
      }
    } catch (KernelError& e) {
      failed++;
      std::cerr << "FAIL " << nm << " (line " << d.line << "): " << e.what() << "\n";
      if (!opt.keep_going) return 1;
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
    if (dt > opt.slow) slow.emplace_back(dt, nm);
    if (opt.verbose) std::cerr << (check ? "ok   " : "skip ") << nm << " " << dt << "s\n";
    if (!opt.stop_at.empty() && nm == opt.stop_at) break;
  }
  double t2 = now();
  std::cerr << "checked " << ok << " declarations, " << failed << " failed, " << unchecked << " added unchecked, in "
            << (t2 - t1) << "s; " << st.steps << " reduction steps; " << g_exprs->size() << " exprs live"
            << (g_engine == 2 ? "; engine mismatches: " + std::to_string(g_engine_mismatches) : std::string("")) << "\n";
  std::cerr << "counters: defeq " << g_cnt_defeq << " (quick " << g_cnt_defeq_quick << ", proof-irrel " << g_cnt_pi << ", lazy " << g_cnt_lazy << ", binding " << g_cnt_binding
            << "); infer " << g_cnt_infer << " (hit " << g_cnt_infer_hit << "); whnf " << g_cnt_whnf << " (hit " << g_cnt_whnf_hit << "); whnf_core " << g_cnt_whnfcore << " (hit " << g_cnt_whnfcore_hit << ")\n";
  if (getenv("LL_COUNT_REPEATS")) std::cerr << "defeq pairs compared again: " << g_cnt_defeq_repeat << " (of which previously failed: " << g_cnt_defeq_refail << ")\n";
  std::cerr << "subst engine: unfold " << g_cnt_unfold << ", iota/proj/quot " << g_cnt_iota << "; spine-prefix cache hits " << g_cnt_prefix_hits << "\n";
  std::cerr << "machine: app " << g_k_app << ", bvar " << g_k_bvar << ", beta " << g_k_beta << ", let " << g_k_let << ", delta " << g_k_delta << ", iota " << g_k_iota << ", proj " << g_k_proj << ", enter value/delayed/re-eval " << g_k_enter_val << "/" << g_k_enter_delayed << "/" << g_k_reeval << ", memo hit/insert " << g_k_memo_hit << "/" << g_k_memo_ins << "\n";
  if (g_fix) std::cerr << "fixpoint rules: derived " << g_fix_derived << ", rejected " << g_fix_rejected << ", applied " << g_fix_applied << "\n";
  if (g_fuse) std::cerr << "fusion: bodies " << g_fuse_bodies << ", unfolds " << g_fuse_unfolds << ", betas " << g_fuse_betas << ", iotas " << g_fuse_iotas << ", projs " << g_fuse_projs << ", overflows " << g_fuse_overflows << "\n";
  std::cerr << "closures: " << g_cnt_clos << " created, " << g_cnt_expose << " exposed, " << g_cnt_env << " envs, " << g_cnt_clos_compose << " composed, " << g_cnt_clos_expand << " expanded\n";
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
    else if (a == "--trust-inductives") opt.trust_inductives = true;
    else if (a == "-k" || a == "--keep-going") opt.keep_going = true;
    else if (a == "--only" && i + 1 < argc) opt.only = argv[++i];
    else if (a == "--stop-at" && i + 1 < argc) opt.stop_at = argv[++i];
    else if (a == "--from-line" && i + 1 < argc) opt.from_line = atol(argv[++i]);
    else if (a == "--slow" && i + 1 < argc) opt.slow = atof(argv[++i]);
    else if (a == "--max-depth" && i + 1 < argc) opt.max_depth = atoi(argv[++i]);
    else if (a == "--max-rss" && i + 1 < argc) opt.max_rss_mb = atol(argv[++i]);   // MB
    else if (a == "--progress" && i + 1 < argc) opt.progress = argv[++i];
    else if (a == "--trust-file" && i + 1 < argc) opt.trust_file = argv[++i];
    else if (a == "--print" && i + 1 < argc) opt.print.push_back(argv[++i]);
    else if (a == "--memo") g_memo = 1;
    else if (a == "--strict-metadata") g_strict_metadata = true;
    else if (a == "--no-memo") g_memo = 0;
    else if (a == "--shard" && i + 1 < argc) { std::string s = argv[++i]; size_t p = s.find('/'); opt.shard = atoi(s.substr(0, p).c_str()); opt.nshards = atoi(s.substr(p + 1).c_str()); }
    else if (a == "--engine" && i + 1 < argc) { std::string e = argv[++i]; g_engine = e == "subst" ? 0 : e == "kam" ? 1 : e == "both" ? 2 : atoi(e.c_str()); }
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
