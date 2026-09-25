// The lazy machine.  See kam.h for the data structures.
//
// The loop below is a Krivine machine with an explicit frame stack, after Coq's `knh`/`knr`:
//   Arg  frames carry pending arguments (thunks);
//   Upd  frames mark a thunk whose value is being computed: when the head above the mark reaches
//        weak-head normal form, the thunk is overwritten with it (call by need, Coq's `Zupdate`);
//   RecK / ProjK / NatK / QuotK frames are continuations waiting for an argument (a recursor's
//        major premise, a projection's structure, a primitive's operand, a quotient's `Quot.mk`)
//        to be evaluated, as Coq's `Zfix`, `Zproj`, `Zprimitive` frames do.
// Nothing recurses in C++ while reducing: a reduction chain of any length runs in constant stack,
// and a thunk under evaluation holds no reference to its original closure (Coq's `FLOCKED`), so
// memory is proportional to the live data, not to the work done.
#include "kam.h"
#include "fuse.h"
#include "fix.h"
#include <unordered_map>
#include <iostream>
#include <memory>

namespace ll {
static long g_call_no = 0;
u64 g_k_memo_hit = 0, g_k_memo_ins = 0;
std::unordered_map<u32, u64> g_delta_hist, g_iota_hist;   // LL_HIST: unfoldings per constant, iota per recursor
static bool g_hist = getenv("LL_HIST") != nullptr;
u64 g_k_app = 0, g_k_bvar = 0, g_k_beta = 0, g_k_let = 0, g_k_delta = 0, g_k_iota = 0, g_k_proj = 0, g_k_projk = 0, g_k_reck = 0, g_k_natk = 0, g_k_enter_val = 0, g_k_enter_delayed = 0, g_k_reeval = 0;
u64 g_nat_ops = 0, g_nat_cycles = 0, g_nat_limbs = 0, g_natlit_cycles = 0;
static inline u64 rdtsc_() { unsigned lo, hi; __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi)); return ((u64)hi << 32) | lo; }

extern bool g_trace_steps;
u64 g_kam_steps = 0;

// ---------------------------------------------------------------- allocation

namespace {
template <class T> struct Pool {
  std::vector<T*> free_list;
  std::vector<T*> chunks;
  size_t next = 0, chunk_size = 4096;
  long live = 0, total = 0, max_live = 0;
  T* alloc() {
    live++; total++; if (live > max_live) max_live = live;
    if (!free_list.empty()) { T* t = free_list.back(); free_list.pop_back(); return t; }
    if (chunks.empty() || next == chunk_size) { chunks.push_back(static_cast<T*>(::operator new(sizeof(T) * chunk_size))); next = 0; }
    return chunks.back() + next++;
  }
  void dealloc(T* t) { live--; free_list.push_back(t); }
  // Give every chunk back when nothing is live (after a declaration that blew up).
  void trim() { if (live != 0) return; for (T* c : chunks) ::operator delete(c); chunks.clear(); free_list.clear(); next = chunk_size; }
};
Pool<Thunk> g_thunks;
Pool<Env> g_envs;
} // namespace

size_t g_max_frames = 0;
void kam_pools_trim() { g_thunks.trim(); g_envs.trim(); }
KamStats kam_stats() { return KamStats{g_thunks.chunks.size(), g_envs.chunks.size(), g_thunks.live, g_thunks.total, g_envs.live, g_envs.total, g_thunks.max_live, g_envs.max_live, g_max_frames}; }

void Env::destroy(Env* e) {
  Ref<Env> tl = std::move(e->tl);
  e->hd.release();
  e->~Env(); g_envs.dealloc(e);
  // release long tails iteratively
  while (tl && tl->rc == 1) {
    Env* n = tl.get();
    Ref<Env> nt = std::move(n->tl);
    n->hd.release();
    tl.p = nullptr;
    n->~Env(); g_envs.dealloc(n);
    tl = std::move(nt);
  }
}

long g_site_live[8], g_site_peak[8]; long g_site_peak_total = 0;
long g_state_live[4], g_state_peak[4];
extern std::unordered_map<Expr, long> g_live_by_term, g_live_by_head;
void Thunk::destroy(Thunk* t) {
  if (g_hist) { g_site_live[t->site]--; g_state_live[t->state]--; if (t->site >= 1 && t->site <= 4) g_live_by_term[t->term]--; if (t->state >= 2) g_live_by_head[t->vterm]--; }
  // release argument thunks iteratively (a long list of constructor cells would otherwise recurse)
  std::vector<Ref<Thunk>> pending;
  pending.swap(t->args);
  t->~Thunk(); g_thunks.dealloc(t);
  while (!pending.empty()) {
    Ref<Thunk> r = std::move(pending.back()); pending.pop_back();
    Thunk* p = r.get();
    if (p && p->rc == 1) { for (auto& a : p->args) pending.push_back(std::move(a)); p->args.clear(); }
  }
}

void free_closed_thunks(void* m) { delete static_cast<ClosedThunkMap*>(m); }

// Live-thunk census by allocation site (LL_HIST): counts are kept incrementally and copied
// when the number of live thunks reaches a new maximum.
const char* g_site_names[8] = {"?", "delayed app", "delayed lam", "delayed proj/let", "delayed other", "closed shared", "value (iota/literal)", "value (assign)"};
std::unordered_map<Expr, long> g_live_by_term, g_peak_by_term;   // LL_HIST: live delayed thunks per term
std::unordered_map<Expr, long> g_live_by_head, g_peak_by_head;   // LL_HIST: live values per head term
static inline void site_alloc(Thunk* t, u8 site) {
  t->site = site; if (!g_hist) return;
  g_site_live[site]++; g_state_live[t->state]++;
  if (site >= 1 && site <= 4) g_live_by_term[t->term]++;
  if (g_thunks.live > g_site_peak_total) {
    g_site_peak_total = g_thunks.live; for (int i = 0; i < 8; i++) g_site_peak[i] = g_site_live[i];
    for (int i = 0; i < 4; i++) g_state_peak[i] = g_state_live[i];
    if ((g_site_peak_total & 0xffff) == 0) { g_peak_by_term = g_live_by_term; g_peak_by_head = g_live_by_head; }
  }
}

ClosedThunkMap& Machine::closed_map() {
  if (!tc.closed_thunks) tc.closed_thunks = new ClosedThunkMap();
  return *static_cast<ClosedThunkMap*>(tc.closed_thunks);
}
Ref<Thunk> Machine::mk_thunk(Expr term, const Ref<Env>& env) {
  // A bound variable is resolved to its environment entry right away (Coq's `mk_clos` on `Rel`):
  // a wrapper closure would capture the whole environment for as long as it stays unforced.
  if (is_bvar(term)) return Ref<Thunk>(lookup(env.get(), bvar_idx(term)));
  if (!has_loose_bvars(term)) {
    // closed subterm: one shared thunk per declaration (values persist across machine runs)
    EKind k = kind(term);
    if (k == EKind::App || k == EKind::Proj || k == EKind::Let || k == EKind::Const) {
      ClosedThunkMap& m = closed_map();
      auto it = m.find(term);
      if (it != m.end()) return it->second;
      Thunk* t = new (g_thunks.alloc()) Thunk();
      t->term = term; site_alloc(t, 5);
      Ref<Thunk> r(t);
      m.emplace(term, r);
      return r;
    }
  }
  Thunk* t = new (g_thunks.alloc()) Thunk();
  t->term = term;
  if (has_loose_bvars(term)) t->env = env;
  { EKind k = kind(term); site_alloc(t, k == EKind::App ? 1 : k == EKind::Lam ? 2 : (k == EKind::Proj || k == EKind::Let) ? 3 : 4); }
  return Ref<Thunk>(t);
}
Ref<Thunk> Machine::mk_value(Expr head, const Ref<Env>& env, std::vector<Ref<Thunk>> args, u8 state) {
  Thunk* t = new (g_thunks.alloc()) Thunk();
  t->vterm = head; if (has_loose_bvars(head)) t->venv = env; t->args = std::move(args); t->state = state; site_alloc(t, 6); if (g_hist) g_live_by_head[head]++;
  return Ref<Thunk>(t);
}
Ref<Env> Machine::cons(const Ref<Thunk>& t, const Ref<Env>& e) {
  Env* n = new (g_envs.alloc()) Env();
  n->hd = t; n->tl = e; n->len = e ? e->len + 1 : 1;
  return Ref<Env>(n);
}
Thunk* Machine::lookup(Env* e, u32 idx) {
  while (e && idx--) e = e->tl.get();
  if (!e) fail("lazy machine: unbound variable (loose bound variable in a term)");
  return e->hd.get();
}

// ---------------------------------------------------------------- readback

std::string g_last_select;
Expr g_unused_const = NIL;
void kam_init() { g_unused_const = mk_const(g_names->of_string("lazylean.unused_hypothesis")); }
Expr Machine::readback_closure(Expr term, Env* env) {
  u32 r = loose_bvar_range(term);
  if (r == 0) return term;
  std::vector<Expr> subst; subst.reserve(r);
  Env* e = env;
  for (u32 i = 0; i < r; i++) { if (!e) fail("lazy machine: environment shorter than the term's variables (range " + std::to_string(r) + ", env " + std::to_string(env ? env->len : 0) + ", last select_branch: " + g_last_select + "): " + expr_str(term).substr(0, 300)); subst.push_back(readback(e->hd.get())); e = e->tl.get(); }
  return instantiate(term, r, subst.data());   // lazy: closures are hash-consed modulo materialisation, so identity is kept
}

Expr Machine::readback(Thunk* th) {
  if (th->rb != NIL) return th->rb;
  Expr r;
  if (th->term != NIL && loose_bvar_range(th->term) > (th->env ? th->env->len : 0)) fail("lazy machine: open closure without environment: site " + std::to_string((int)th->site) + " state " + std::to_string((int)th->state) + " rc " + std::to_string(th->rc) + " range " + std::to_string(loose_bvar_range(th->term)) + " env " + std::to_string(th->env ? th->env->len : 0) + " clos " + std::to_string(is_clos(th->term)) + " raw kind " + std::to_string((int)raw(th->term).kind) + " " + expr_str(th->term).substr(0, 200));
  if (th->term != NIL) r = readback_closure(th->term, th->env.get());   // as written (also while under evaluation, when the closure was kept)
  else if (th->state >= 2) r = readback_value(th);
  else fail("lazy machine: readback of a thunk under evaluation");
  th->rb = r;
  return r;
}

Expr Machine::readback_value(Thunk* th) {
  if (th->state < 2) fail("lazy machine: readback_value of an unforced thunk");
  Expr r = readback_closure(th->vterm, th->venv.get());
  for (auto& a : th->args) r = mk_app(r, readback(a.get()));
  return r;
}

Expr Machine::readback(const State& s) {
  Expr r = readback_closure(s.term, s.env.get());
  for (size_t i = s.stack.size(); i-- > 0;) r = mk_app(r, readback(s.stack[i].get()));
  return r;
}

Expr Machine::unfold_body(Expr head) { return tc.unfold_value(head, tc.env.get(const_name(head))); }

// The arm body of a fixpoint rule at the levels of `head` (cached per head and arm).
Expr Machine::fix_body(Expr head, const FixRule* r, const FixArm* arm) {
  if (g_levels->list_size(const_levels(head)) == 0) return arm->body;
  std::vector<Expr>& arms = tc.fix_inst[head];
  size_t idx = arm - r->arms.data();
  if (arms.empty()) {
    const ConstInfo& c = tc.env.get(const_name(head));
    const std::vector<Level> ls = g_levels->list(const_levels(head));
    for (auto& a : r->arms) arms.push_back(instantiate_lparams(a.body, c.lparams, ls));
  }
  return arms[idx];
}

// ---------------------------------------------------------------- the machine

namespace {
// Continuation data lives out of line so that the common Arg/Upd frames stay small.
struct Cont {
  Expr head = NIL;                // saved head term
  Ref<Env> env;                   // saved environment of the head
  std::vector<Ref<Thunk>> args;   // saved arguments (application order)
};
struct Frame {
  enum K : u8 { Arg, Upd, RecK, ProjK, NatK, QuotK } k = Arg;
  bool saved_delta = false;
  Ref<Thunk> th;                  // Arg/Upd: the thunk; continuations: the thunk being forced
  std::unique_ptr<Cont> c;        // continuations only
};

struct MachineRun {
  Machine& M;
  MachineCtx& tc;
  Expr h = NIL; Ref<Env> env; bool delta; bool cheap_proj;
  std::vector<Frame> st;
  MachineRun(Machine& m, bool d, bool cp) : M(m), tc(m.tc), delta(d), cheap_proj(cp) {}

  void push_arg(const Ref<Thunk>& t) { st.emplace_back(); Frame& f = st.back(); f.k = Frame::Arg; f.th = t; }
  void push_args(const std::vector<Ref<Thunk>>& args) { for (size_t i = args.size(); i-- > 0;) push_arg(args[i]); }

  // Enter thunk `t`: use its value if it has one for the current mode, otherwise evaluate it under
  // an update mark.  The thunk keeps its original closure, so that reading it back gives the term
  // as it was written (a thunk entered to look at its value may stay in the result unreduced).
  void enter(Thunk* t) {
    Ref<Thunk> keep(t);
    // A value computed with delta must not be used as the head of a no-delta (whnf_core) run:
    // it may be reduced further than whnf_core would go (shared thunks persist across runs).
    // Re-evaluate from the original closure instead, without updating the thunk.
    if (t->state == 3 && !delta && t->term != NIL) { g_k_reeval++; h = t->term; env = t->env; return; }
    if (t->state == 3 || (t->state == 2 && !delta)) { g_k_enter_val++; if (g_trace_steps) std::cerr << "  [enter value state " << (int)t->state << "]\n"; h = t->vterm; env = t->venv; push_args(t->args); return; }
    if (t->state == 1) fail("lazy machine: cyclic thunk");
    g_k_enter_delayed++;
    // Memoisation: a delayed application under an environment is keyed by its read-back (the term
    // the kernel would see); equal closures share one value, as with a kernel's whnf cache.  Only
    // in delta runs, whose values do not depend on the run's flags.
    if (delta && t->state == 0 && t->term != NIL && is_app(t->term) && has_loose_bvars(t->term)) {
      ClosedThunkMap& m = M.closed_map();
      Expr key = M.readback(t);
      auto it = m.find(key);
      if (it != m.end()) {
        Thunk* u = it->second.get();
        if (u != t && u->state == 3) {
          g_k_memo_hit++;
          if (g_hist) { g_state_live[t->state]--; g_state_live[3]++; g_live_by_head[u->vterm]++; }
          t->vterm = u->vterm; t->venv = u->venv; t->args = u->args; t->state = 3;
          h = t->vterm; env = t->venv; push_args(t->args); return;
        }
      } else { m.emplace(key, keep); g_k_memo_ins++; }
    }
    Frame f; f.k = Frame::Upd; f.th = keep; st.push_back(std::move(f));
    if (t->state == 2) { h = t->vterm; env = std::move(t->venv); std::vector<Ref<Thunk>> a; a.swap(t->args); push_args(a); }
    else { h = t->term; env = t->env; }
    if (g_hist) { g_state_live[t->state]--; g_state_live[1]++; }
    t->state = 1; t->rb = NIL;
  }

  void assign(Thunk* t, const std::vector<Ref<Thunk>>& args) {
    static const char* dbg = getenv("LL_TRACE_ASSIGN");
    if (dbg && t->term != NIL) { std::string ts = expr_str(t->term); if (ts.rfind(dbg, 0) == 0) { std::string hs = expr_str(h); if (hs.size() > 80) hs = hs.substr(0, 80); std::cerr << "  [assign call " << g_call_no << " delta " << delta << " cheap_proj " << cheap_proj << " frames " << st.size() << "] " << ts.substr(0, 60) << " := " << hs << " +" << args.size() << " args\n"; } }
    if (g_hist) { g_state_live[t->state]--; g_state_live[delta ? 3 : 2]++; if (t->state >= 2) g_live_by_head[t->vterm]--; g_live_by_head[h]++; }
    // A value keeps its environment only if its head has variables (a lambda, a stuck term under
    // binders); a constructor or constant head under the whole creating environment would pin
    // everything that environment reaches for as long as the value lives.
    t->vterm = h; t->venv = has_loose_bvars(h) ? env : Ref<Env>(); t->args = args; t->state = delta ? 3 : 2; t->rb = NIL;
  }

  // Collect the first `k` pending arguments, reading through update marks (a stuck partial
  // application is a weak-head normal form, so a mark passed on the way is updated with it).
  // Returns false if fewer than k arguments are available; on success the k arguments and the
  // marks among them are removed from the stack.
  bool take_args(size_t k, std::vector<Ref<Thunk>>& out) {
    size_t avail = 0;
    for (size_t i = st.size(); i-- > 0 && avail < k;) {
      if (st[i].k == Frame::Arg) avail++;
      else if (st[i].k == Frame::Upd) continue;
      else break;
    }
    if (avail < k) return false;
    out.clear();
    while (out.size() < k) {
      Frame f = std::move(st.back()); st.pop_back();
      if (f.k == Frame::Arg) out.push_back(std::move(f.th));
      else assign(f.th.get(), out);
    }
    return true;
  }

  // Suspend on continuation `k` and evaluate thunk `t` (with delta) first.
  void force_via(Frame&& k, Thunk* t) {
    k.saved_delta = delta;
    st.push_back(std::move(k));
    if (st.size() > g_max_frames) g_max_frames = st.size();
    delta = true;
    enter(t);
  }

  static bool is_ctor_head(const Environment& env, Expr head, const ConstInfo** out) {
    if (!is_const(head)) return false;
    const ConstInfo* c = env.find(const_name(head));
    if (!c || c->kind != CKind::Ctor) return false;
    if (out) *out = c;
    return true;
  }

  // Iota on a recursor application with arguments `args` (application order) whose major premise
  // is forced.  Returns false if stuck.
  bool iota(const ConstInfo& rec, Expr rec_head, std::vector<Ref<Thunk>>& args) {
    u32 major_idx = rec.rec_major_idx();
    Ref<Thunk> major = args[major_idx];
    Expr head = major->vterm;
    if (is_nat_lit(head) && major->args.empty()) {
      const mpz_class& v = nat_lit_val(head);
      if (v == 0) major = M.mk_value(mk_const(N.Nat_zero), Ref<Env>(), {}, 3);
      else major = M.mk_value(mk_const(N.Nat_succ), Ref<Env>(), {M.closed(mk_nat_lit(v - 1))}, 3);
    } else if (is_str_lit(head) && major->args.empty()) {
      major = M.closed(str_lit_to_ctor(head));
      M.force(major.get(), true);
    } else if (!is_ctor_head(tc.env, head, nullptr) && tc.env.is_structure_like(rec.major_induct)) {
      Expr m = M.readback_value(major.get());
      Expr m2 = tc.k.to_ctor_when_struct(rec.major_induct, m);
      if (m2 != m) { major = M.closed(m2); M.force(major.get(), true); }
    }
    head = major->vterm;
    static int trace_stuck = getenv("LL_TRACE_STUCK") ? atoi(getenv("LL_TRACE_STUCK")) : 0;
    const RecRule* rule = nullptr;
    if (is_const(head)) for (auto& r : rec.rules) if (r.ctor == const_name(head)) { rule = &r; break; }
    if (!is_const(head) || !rule || rule->nfields > major->args.size()) {
      if (trace_stuck > 0) { Expr mv = M.readback_value(major.get()); if (!has_fvar(mv)) { trace_stuck--; std::string m = expr_str(mv); std::cerr << "[stuck iota] " << name_str(rec.name) << " delta " << delta << " major state " << (int)major->state << ": " << m.substr(0, 600) << "\n"; } }
      return false;
    }
    if (g_levels->list_size(const_levels(rec_head)) != rec.lparams.size()) return false;
    Expr rhs = rule->rhs;
    if (g_levels->list_size(const_levels(rec_head)) != 0) {
      const std::vector<Level> ls = g_levels->list(const_levels(rec_head));
      Expr key = mk_app(rec_head, mk_const(rule->ctor));
      auto it = tc.unfold_cache.find(key);
      if (it != tc.unfold_cache.end()) rhs = it->second;
      else { rhs = instantiate_lparams(rule->rhs, rec.lparams, ls); tc.unfold_cache.emplace(key, rhs); }
    }
    g_k_iota++; M.steps++; if (g_hist) g_iota_hist[rec.name]++;
    u32 nbefore = rec.rec_first_index_idx();
    if (select_branch(rec, rhs, nbefore, rule->nfields, args, *major)) return true;
    // new application  rhs a_1 .. a_nbefore fields extra...   (a_1 ends on top)
    for (size_t i = args.size(); i-- > major_idx + 1;) push_arg(args[i]);
    for (size_t k = major->args.size(); k-- > major->args.size() - rule->nfields;) push_arg(major->args[k]);
    for (size_t i = nbefore; i-- > 0;) push_arg(args[i]);
    h = rhs; env = Ref<Env>();
    return true;
  }

  // Direct branch selection (Coq's Zcase): a rule's right-hand side is
  //   fun params motive minors fields => minor_k fields ih_1 .. ih_r
  // and when the selected minor premise is a lambda closure with binders for the fields and the
  // induction hypotheses, its body can be entered directly under its own environment extended
  // with the fields (the constructor's arguments) and the hypotheses, instead of replaying the
  // rule's lambdas, pushing the application and entering the minor.  A hypothesis the body never
  // mentions is not built at all (a `casesOn` ignores them): its cell holds a placeholder that
  // no lookup can reach, since the body has no occurrence of that variable.
  bool select_branch(const ConstInfo& rec, Expr rhs, u32 nbefore, u32 nfields, std::vector<Ref<Thunk>>& args, Thunk& major) {
    MachineCtx::RuleShape& sh = tc.rule_shapes[rhs];
    if (sh.ok < 0) {
      sh.ok = 0;
      Expr b = rhs; u32 nl = 0;
      while (is_lam(b) && nl < nbefore + nfields) { b = binding_body(b); nl++; }
      if (nl == nbefore + nfields) {
        std::vector<Expr> bargs; Expr h = get_app_args_fn(b, bargs);
        if (is_bvar(h) && bvar_idx(h) >= nfields && bvar_idx(h) < nfields + rec.nminors && bargs.size() >= nfields) {
          bool fields_ok = true;
          for (u32 i = 0; i < nfields; i++) if (!is_bvar(bargs[i]) || bvar_idx(bargs[i]) != nfields - 1 - i) { fields_ok = false; break; }
          if (fields_ok) { sh.ok = 1; sh.minor_bvar = bvar_idx(h); sh.ihs.assign(bargs.begin() + nfields, bargs.end()); }
        }
      }
    }
    if (!sh.ok) return false;
    // the minor premise: bvar i (i >= nfields) of the rule env is args[nbefore - 1 - (i - nfields)]
    Thunk* minor = args[nbefore - 1 - (sh.minor_bvar - nfields)].get();
    Expr mt; Ref<Env> menv;
    if (minor->state == 0 && minor->term != NIL) { mt = minor->term; menv = minor->env; }
    else if (minor->state >= 2 && minor->args.empty()) { mt = minor->vterm; menv = minor->venv; }
    else return false;
    if (!is_lam(mt)) return false;
    u32 nb = nfields + (u32)sh.ihs.size();
    auto& lm = tc.lam_masks[mt];
    if (lm.first == 0) {
      // number of leading binders (up to nb) and the set of those occurring in the body
      Expr b = mt; u32 nl = 0;
      while (is_lam(b) && nl < nb) { b = binding_body(b); nl++; }
      u64 mask = 0;
      if (nl == nb) {
        std::vector<std::pair<Expr, u32>> todo{{b, 0}}; size_t visits = 0; bool capped = false;
        while (!todo.empty()) {
          auto [x, d] = todo.back(); todo.pop_back();
          if (loose_bvar_range(x) <= d) continue;
          if (++visits > 20000) { capped = true; break; }
          const ExprNode nd = ex(x);
          switch (nd.kind) {
            case EKind::BVar: if (nd.a >= d && nd.a - d < nb) mask |= 1ull << (nb - 1 - (nd.a - d)); break;
            case EKind::App: todo.push_back({nd.a, d}); todo.push_back({nd.b, d}); break;
            case EKind::Lam: case EKind::Pi: todo.push_back({nd.a, d}); todo.push_back({nd.b, d + 1}); break;
            case EKind::Let: todo.push_back({nd.a, d}); todo.push_back({nd.b, d}); todo.push_back({nd.c, d + 1}); break;
            case EKind::Proj: todo.push_back({nd.b, d}); break;
            default: break;
          }
        }
        if (capped) mask = ~0ull;
      }
      lm = {nl + 1, mask};   // nl+1: 0 means "not computed"
    }
    if (lm.first - 1 != nb || nb > 64) return false;
    u64 mask = lm.second;
    M.steps++;
    // fields (application order), then hypotheses
    Ref<Env> e = menv;
    size_t f0 = major.args.size() - nfields;
    for (u32 i = 0; i < nfields; i++) e = M.cons(major.args[f0 + i], e);
    if (!sh.ihs.empty()) {
      Ref<Env> renv;   // the rule's environment, built only if some hypothesis is used
      bool any = false;
      for (size_t j = 0; j < sh.ihs.size(); j++) if (mask & (1ull << (nfields + j))) { any = true; break; }
      if (any) {
        for (u32 i = 0; i < nbefore; i++) renv = M.cons(args[i], renv);
        for (u32 i = 0; i < nfields; i++) renv = M.cons(major.args[f0 + i], renv);
      }
      for (size_t j = 0; j < sh.ihs.size(); j++) {
        if (mask & (1ull << (nfields + j))) e = M.cons(M.mk_thunk(sh.ihs[j], renv), e);
        else e = M.cons(unused_cell(), e);
      }
    }
    Expr b = mt; for (u32 i = 0; i < nb; i++) b = binding_body(b);
    if (loose_bvar_range(b) > (e ? e->len : 0)) {
      std::cerr << "[select_branch] rec " << name_str(rec.name) << " minor state " << (int)minor->state << " nb " << nb << " lbr(mt) " << loose_bvar_range(mt) << " lbr(b) " << loose_bvar_range(b) << " menv " << (menv ? menv->len : 0) << " e " << (e ? e->len : 0) << " clos " << is_clos(mt) << "\n  mt: " << expr_str(mt).substr(0, 300) << "\n";
      fail("select_branch inconsistency");
    }
    if (g_trace_steps) g_last_select = "rec " + name_str(rec.name) + " minor state " + std::to_string((int)minor->state) + " nb " + std::to_string(nb) + " mask " + std::to_string(mask) + " menv " + std::to_string(menv ? menv->len : 0) + " e " + std::to_string(e ? e->len : 0) + " lbr(b) " + std::to_string(loose_bvar_range(b)) + " b: " + expr_str(b).substr(0, 200);
    h = b; env = std::move(e);
    return true;
  }
  static const Ref<Thunk>& unused_cell() {
    // A placeholder for an environment cell no variable of the body refers to; evaluating it
    // (which cannot happen) fails on an unknown constant.  Its term is created before the
    // expression table is frozen (kam_init, from main), so that the handle stays valid.
    static Ref<Thunk> cell = [] { Thunk* t = new (g_thunks.alloc()) Thunk(); t->term = g_unused_const != NIL ? g_unused_const : mk_const(g_names->of_string("lazylean.unused_hypothesis")); t->rc = 1 << 30; return Ref<Thunk>(t); }();
    return cell;
  }

  // The literal value of a forced operand: a literal, `Nat.zero`, or `Nat.succ` of such (the
  // kernel's reduce_nat folds `Nat.succ n` to a literal when n reduces to one, and its operand
  // whnf goes through that; without it `Nat.add (Nat.succ 2486023) y` unfolds unary).
  const mpz_class* lit_value(Thunk* t) {
    static const mpz_class zero(0);
    if (t->args.empty()) {
      if (is_nat_lit(t->vterm)) return &nat_lit_val(t->vterm);
      if (is_const_of(t->vterm, N.Nat_zero)) return &zero;
      return nullptr;
    }
    if (t->args.size() == 1 && is_const_of(t->vterm, N.Nat_succ)) {
      Thunk* a = t->args[0].get();
      if (a->state != 3) M.force(a, true);
      const mpz_class* v = lit_value(a);
      if (!v) return nullptr;
      succ_tmp = *v + 1; return &succ_tmp;
    }
    return nullptr;
  }
  mpz_class succ_tmp, succ_tmp2;

  // Arity of a Nat primitive by name handle (0 = not a primitive); a table lookup, as this runs
  // on every constant the machine dispatches.
  static bool is_nat_op(Name f, unsigned& arity) {
    static std::vector<u8> tab = [] {
      std::vector<u8> t(4096, 0);
      auto set = [&](Name n, u8 a) { if (n >= t.size()) t.resize(n + 1, 0); t[n] = a; };
      set(N.Nat_succ, 1);
      for (Name n : {N.Nat_add, N.Nat_sub, N.Nat_mul, N.Nat_pow, N.Nat_gcd, N.Nat_mod, N.Nat_div, N.Nat_beq, N.Nat_ble, N.Nat_land, N.Nat_lor, N.Nat_xor, N.Nat_shiftLeft, N.Nat_shiftRight}) set(n, 2);
      return t;
    }();
    if (f >= tab.size()) return false;
    arity = tab[f];
    return arity != 0;
  }

  bool nat_compute(Name f, std::vector<Ref<Thunk>>& args) {
    mpz_class r;
    const mpz_class* pa = lit_value(args[0].get()); if (!pa) return false;
    const mpz_class a = *pa;   // copy: the second operand's lookup may reuse the scratch value
    u64 t0 = rdtsc_(); g_nat_ops++; g_nat_limbs += mpz_size(a.get_mpz_t());
    if (f == N.Nat_succ) { h = mk_nat_lit(a + 1); env = Ref<Env>(); M.steps++; return true; }
    const mpz_class* pb = lit_value(args[1].get()); if (!pb) return false;
    const mpz_class& b = *pb;
    if (f == N.Nat_add) r = a + b;
    else if (f == N.Nat_sub) r = a >= b ? mpz_class(a - b) : mpz_class(0);
    else if (f == N.Nat_mul) r = a * b;
    else if (f == N.Nat_pow) { if (b > (1u << 24)) return false; mpz_pow_ui(r.get_mpz_t(), a.get_mpz_t(), b.get_ui()); }
    else if (f == N.Nat_gcd) mpz_gcd(r.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
    else if (f == N.Nat_mod) r = b == 0 ? a : mpz_class(a % b);
    else if (f == N.Nat_div) r = b == 0 ? mpz_class(0) : mpz_class(a / b);
    else if (f == N.Nat_beq || f == N.Nat_ble) {
      bool res = f == N.Nat_beq ? a == b : a <= b;
      h = mk_const(res ? N.Bool_true : N.Bool_false); env = Ref<Env>(); M.steps++; return true;
    }
    else if (f == N.Nat_land) r = a & b;
    else if (f == N.Nat_lor) r = a | b;
    else if (f == N.Nat_xor) r = a ^ b;
    else if (f == N.Nat_shiftLeft) { if (!b.fits_ulong_p()) fail("Nat.shiftLeft: shift too large"); mpz_mul_2exp(r.get_mpz_t(), a.get_mpz_t(), b.get_ui()); }
    else if (f == N.Nat_shiftRight) { if (!b.fits_ulong_p()) r = 0; else mpz_fdiv_q_2exp(r.get_mpz_t(), a.get_mpz_t(), b.get_ui()); }
    u64 t1 = rdtsc_(); g_nat_cycles += t1 - t0;
    h = mk_nat_lit(std::move(r)); env = Ref<Env>(); M.steps++;
    g_natlit_cycles += rdtsc_() - t1;
    return true;
  }

  // Reduce the head one step.  Returns true if h is now a value (unwind), false to keep reducing.
  bool step(std::vector<Ref<Thunk>>& args) {
    if (g_trace_steps) { std::string s = expr_str(h); if (s.size() > 300) s = s.substr(0, 300) + "..."; std::string fk; for (auto& f : st) fk += "AURPNQ"[f.k]; std::cerr << "  [step " << M.steps << " frames " << fk << " delta " << delta << "] " << s << "\n"; }
    switch (kind(h)) {
      case EKind::BVar: { g_k_bvar++; Thunk* t = Machine::lookup(env.get(), bvar_idx(h)); enter(t); return false; }
      case EKind::App: {
        // the whole spine at once: one argument thunk per application node
        do { g_k_app++; push_arg(M.mk_thunk(app_arg(h), env)); h = app_fn(h); } while (kind(h) == EKind::App);
        return false;
      }
      case EKind::Lam:
        if (!st.empty() && st.back().k == Frame::Arg) {
          do { g_k_beta++; M.steps++; env = M.cons(st.back().th, env); st.pop_back(); h = binding_body(h); } while (is_lam(h) && !st.empty() && st.back().k == Frame::Arg);
          return false;
        }
        return true;
      case EKind::Let: { g_k_let++; M.steps++; env = M.cons(M.mk_thunk(let_val(h), env), env); h = let_body(h); return false; }
      case EKind::Pi: case EKind::Sort: case EKind::Lit: return true;
      case EKind::FVar:
        if (g_lctx.is_let(h)) { M.steps++; h = g_lctx.get(h).value; env = Ref<Env>(); return false; }
        return true;
      case EKind::Const: {
        Name n = const_name(h);
        if (n == N.reduceBool || n == N.reduceNat) fail("lazylean does not support native reduction (Lean.reduceBool/reduceNat)");
        const ConstInfo* c = tc.env.find(n);
        if (!c) fail("unknown constant '" + name_str(n) + "'");
        if (c->kind == CKind::Rec) {
          u32 major_idx = c->rec_major_idx();
          if (!take_args(major_idx + 1, args)) return true;
          Thunk* major = args[major_idx].get();
          if (c->k && major->state != 3) {
            Expr m = M.readback(major);
            Expr m2 = tc.k.to_ctor_when_K(*c, m);
            if (m2 != m) { args[major_idx] = M.closed(m2); major = args[major_idx].get(); }
          }
          if (major->state != 3) {
            Frame k; k.k = Frame::RecK; k.c.reset(new Cont{h, env, std::move(args)}); k.th = k.c->args[major_idx];
            force_via(std::move(k), major); return false;
          }
          if (iota(*c, h, args)) return false;
          push_args(args); return true;
        }
        if (c->kind == CKind::Quot) {
          unsigned mk_pos, arg_pos;
          if (n == N.Quot_lift) { mk_pos = 5; arg_pos = 3; } else if (n == N.Quot_ind) { mk_pos = 4; arg_pos = 3; } else return true;
          if (!take_args(mk_pos + 1, args)) return true;
          Thunk* mk = args[mk_pos].get();
          if (mk->state != 3) {
            Frame k; k.k = Frame::QuotK; k.c.reset(new Cont{h, env, std::move(args)}); k.th = k.c->args[mk_pos];
            force_via(std::move(k), mk); return false;
          }
          if (is_const_of(mk->vterm, N.Quot_mk) && mk->args.size() == 3) {
            M.steps++;
            Ref<Thunk> f = args[arg_pos], a = mk->args[2];
            for (size_t i = args.size(); i-- > mk_pos + 1;) push_arg(args[i]);
            push_arg(a);
            enter(f.get());
            return false;
          }
          push_args(args); return true;
        }
        unsigned arity;
        if (delta && is_nat_op(n, arity) && take_args(arity, args)) {
          size_t i = 0; for (; i < arity; i++) if (args[i]->state != 3) break;
          if (i < arity) {
            Thunk* t = args[i].get();
            Frame k; k.k = Frame::NatK; k.c.reset(new Cont{h, env, std::move(args)}); k.th = k.c->args[i];
            force_via(std::move(k), t); return false;
          }
          if (nat_compute(n, args)) return false;
          push_args(args);
        }
        if (delta && c->kind == CKind::Def && g_levels->list_size(const_levels(h)) == c->lparams.size()) {
          // Fixpoint rule (fix.h): reduce straight to the arm when the recursive argument is a
          // constructor; otherwise unfold as usual.
          const FixRule* r = fix_rule(tc.env, *c);
          if (r && take_args(r->major + 1, args)) {
            Thunk* major = args[r->major].get();
            if (major->state != 3) {
              Frame k; k.k = Frame::RecK; k.c.reset(new Cont{h, env, std::move(args)}); k.th = k.c->args[r->major];
              force_via(std::move(k), major); return false;
            }
            Ref<Thunk> mj = args[r->major];
            if (r->induct == N.Nat && is_nat_lit(mj->vterm) && mj->args.empty()) {
              const mpz_class& v = nat_lit_val(mj->vterm);
              if (v == 0) mj = M.mk_value(mk_const(N.Nat_zero), Ref<Env>(), {}, 3);
              else mj = M.mk_value(mk_const(N.Nat_succ), Ref<Env>(), {M.closed(mk_nat_lit(v - 1))}, 3);
            }
            const FixArm* arm = nullptr;
            if (is_const(mj->vterm)) for (auto& a : r->arms) if (a.ctor == const_name(mj->vterm) && mj->args.size() == r->nparams + a.nfields) { arm = &a; break; }
            if (arm) {
              g_fix_applied++; M.steps++; if (g_hist) g_delta_hist[n]++;
              Expr body = M.fix_body(h, r, arm);
              Ref<Env> e;
              for (u32 i = 0; i < r->major; i++) e = M.cons(args[i], e);
              for (size_t i = mj->args.size() - arm->nfields; i < mj->args.size(); i++) e = M.cons(mj->args[i], e);
              h = body; env = std::move(e); return false;
            }
            push_args(args);
          }
        }
        if (delta && c->is_delta() && g_levels->list_size(const_levels(h)) == c->lparams.size()) {
          g_k_delta++; M.steps++; if (g_hist) g_delta_hist[n]++;
          h = M.unfold_body(h); env = Ref<Env>(); return false;
        }
        return true;
      }
      case EKind::Proj: {
        g_k_proj++;
        Ref<Thunk> s = M.mk_thunk(proj_expr(h), env);
        Frame k; k.k = Frame::ProjK; k.c.reset(new Cont{h, env, {}}); k.th = s; k.saved_delta = delta;
        st.push_back(std::move(k));
        if (!cheap_proj) delta = true;   // the structure is fully normalised (kernel: whnf)
        enter(s.get());
        return false;
      }
    }
    return true;
  }

  // Run to weak-head normal form.  On return h/env is the head and `result` its arguments.
  void loop(std::vector<Ref<Thunk>>& result) {
    std::vector<Ref<Thunk>> args, gathered;
    while (true) {
      static u64 hist_tick = 0;
      if (g_hist && (++hist_tick & 0xffffff) == 0) {
        std::vector<std::pair<u64, u32>> v; for (auto& kv : g_delta_hist) v.push_back({kv.second, kv.first});
        std::sort(v.rbegin(), v.rend()); std::cerr << "[hist @" << M.steps << "]";
        for (size_t i = 0; i < v.size() && i < 8; i++) std::cerr << " " << name_str(v[i].second) << " " << v[i].first;
        std::cerr << " | thunks " << g_thunks.live << " frames " << st.size() << "\n";
      }
      if ((++M.steps & 0x3ffff) == 0) check_rss(("machine loop, call " + std::to_string(g_call_no) + ", " + std::to_string(g_thunks.live) + " thunks, " + std::to_string(g_envs.live) + " envs, " + std::to_string(st.size()) + " frames").c_str());
      if (!step(args)) continue;
      // h is a value: unwind
      gathered.clear();
      bool resume = false;
      while (!resume) {
        if (st.empty()) { result = std::move(gathered); return; }
        Frame& f = st.back();
        if (f.k == Frame::Arg) {
          if (is_lam(h)) { g_k_beta++; M.steps++; env = M.cons(f.th, env); st.pop_back(); h = binding_body(h); resume = true; break; }
          gathered.push_back(std::move(f.th)); st.pop_back(); continue;
        }
        if (f.k == Frame::Upd) { assign(f.th.get(), gathered); st.pop_back(); continue; }
        Frame k = std::move(st.back()); st.pop_back();
        delta = k.saved_delta;
        std::vector<Ref<Thunk>> sargs; sargs.swap(gathered);   // the forced value's arguments
        switch (k.k) {
          case Frame::RecK: case Frame::NatK: case Frame::QuotK:
            // re-dispatch the head; the forced argument is now a value
            h = k.c->head; env = std::move(k.c->env); push_args(k.c->args); resume = true; break;
          case Frame::ProjK: {
            // The structure's value is the current head h with arguments sargs (not necessarily
            // recorded in the thunk: a no-delta run re-evaluates a delta value without updating it).
            Expr head = h;
            const std::vector<Ref<Thunk>>* fargs = &sargs;
            Ref<Thunk> t2;
            const ConstInfo* mi = nullptr;
            if (is_str_lit(head) && sargs.empty()) {
              t2 = M.closed(str_lit_to_ctor(head)); M.force(t2.get(), true); head = t2->vterm; fargs = &t2->args;
            }
            if (is_ctor_head(tc.env, head, &mi) && mi->induct == proj_sname(k.c->head) && mi->nparams + proj_idx(k.c->head) < fargs->size()) {
              M.steps++;
              Ref<Thunk> field = (*fargs)[mi->nparams + proj_idx(k.c->head)];
              enter(field.get());
              resume = true;
            } else {
              // stuck projection: it is itself the value; keep unwinding
              h = k.c->head; env = std::move(k.c->env);
            }
            break;
          }
          default: fail("lazy machine: bad frame");
        }
      }
    }
  }
};
} // namespace

void Machine::force(Thunk* th, bool delta) {
  if (th->state == 3 || (th->state == 2 && !delta)) return;
  MachineRun R(*this, delta, false);
  R.enter(th);
  std::vector<Ref<Thunk>> rest;
  R.loop(rest);
  // `enter` pushed an update mark for th, which the unwinder assigned; the head's arguments
  // gathered above the mark are th's arguments, and nothing can remain below the mark.
  if (!rest.empty() && th->state < 2) fail("lazy machine: arguments left after forcing");
}

void Machine::run(State& s, bool delta, bool cheap_proj) {
  MachineRun R(*this, delta, cheap_proj);
  R.h = s.term; R.env = s.env;
  for (auto& a : s.stack) R.push_arg(a);   // s.stack: back = first arg, so pushing in order keeps it on top
  std::vector<Ref<Thunk>> rest;
  R.loop(rest);
  s.term = R.h; s.env = R.env;
  s.stack.assign(rest.rbegin(), rest.rend());
}

long g_trace_call = getenv("LL_TRACE_CALL") ? atol(getenv("LL_TRACE_CALL")) : -1;   // -2: every call
bool g_trace_steps = false;
long kam_last_call() { return g_call_no; }
Expr Machine::whnf(Expr e, bool delta, bool cheap_proj) {
  State s; s.term = e;
  long live0 = g_thunks.live;
  long call = ++g_call_no;
  g_trace_steps = (call == g_trace_call || g_trace_call == -2);
  run(s, delta, cheap_proj);
  g_trace_steps = false;
  g_kam_steps += steps;
  Expr r = readback(s);
  s = State();
  static long thr = getenv("LL_TRACE_MEM") ? atol(getenv("LL_TRACE_MEM")) : -1;
  if (thr >= 0 && (long)steps > thr) {
    std::string in = expr_str(e); if (in.size() > 250) in = in.substr(0, 250) + "...";
    std::cerr << "[kam] call " << call << " " << (delta ? "whnf" : "whnf_core") << " steps " << steps << " thunks live before/after " << live0 << "/" << g_thunks.live << " in: " << in << "\n";
  }
  return r;
}

} // namespace ll
