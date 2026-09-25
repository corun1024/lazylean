// A lazy abstract machine for weak-head normalisation, in the style of Coq's kernel
// (kernel/cClosure.ml): terms are never rewritten; a *closure* pairs a term with an environment
// giving the values of its bound variables, arguments live on a stack of *thunks*, and a thunk is
// overwritten with its weak-head normal form the first time it is forced, so every other pointer
// to it sees the result (call by need).  Memory is reference counted; the structures are acyclic
// by construction (a thunk can only refer to thunks created before it).
#pragma once
#include "kernel.h"
#include <unordered_map>

namespace ll {

struct Thunk;
struct Env;

template <class T> struct Ref {
  T* p = nullptr;
  Ref() = default;
  Ref(T* x) : p(x) { if (p) p->rc++; }
  Ref(const Ref& o) : p(o.p) { if (p) p->rc++; }
  Ref(Ref&& o) noexcept : p(o.p) { o.p = nullptr; }
  ~Ref() { release(); }
  Ref& operator=(const Ref& o) { if (o.p) o.p->rc++; release(); p = o.p; return *this; }
  Ref& operator=(Ref&& o) noexcept { if (this != &o) { release(); p = o.p; o.p = nullptr; } return *this; }
  T* operator->() const { return p; }
  T& operator*() const { return *p; }
  explicit operator bool() const { return p != nullptr; }
  T* get() const { return p; }
  void release() { if (p && --p->rc == 0) T::destroy(p); p = nullptr; }
};

// Persistent environment: a cons list of thunks; de Bruijn index i is the i-th cell.
struct Env {
  u32 rc = 0;
  u32 len;
  Ref<Thunk> hd;
  Ref<Env> tl;
  static void destroy(Env* e);
};

// A thunk is either a delayed closure (term, env) or a weak-head normal form: a head term with
// the environment its binders need plus the argument spine.
struct Thunk {
  u32 rc = 0;
  u8 state = 0;        // 0 delayed, 1 being forced, 2 whnf (no delta), 3 whnf (full)
  u8 site = 0;         // allocation site (LL_HIST census): see kam.cpp g_site_names
  // The original closure.  It is kept after forcing: reading a thunk back yields the term as it
  // was written, exactly as the kernel's whnf never reduces inside arguments, so the machine's
  // results agree structurally with the reference and the lazy-delta heuristics see the same
  // terms.  `term == NIL` marks a synthesised value with no original (read back from the value).
  Expr term = NIL;
  Ref<Env> env;
  // The weak-head normal form, once forced: head `vterm` under `venv` applied to `args`.
  Expr vterm = NIL;
  Ref<Env> venv;
  std::vector<Ref<Thunk>> args;   // application order (args[0] applied first)
  Expr rb = NIL;                  // cached readback of the original closure
  static void destroy(Thunk* t);
};

// A machine state: head term under `env`, applied to the arguments on `stack` (top = back,
// i.e. stack.back() is the *first* argument).
struct State {
  Expr term;
  Ref<Env> env;
  std::vector<Ref<Thunk>> stack;
};

// Open-addressing map Expr -> thunk (no deletions; cleared with the declaration).  Looked up on
// every closed argument the machine pushes, so it is kept flat and probe-cheap.
struct ClosedThunkMap {
  struct Slot { u32 first = NIL; Ref<Thunk> second; };
  std::vector<Slot> slots; size_t count = 0;
  ClosedThunkMap() : slots(1 << 12) {}
  Slot* end() { return nullptr; }
  Slot* find(u32 k) {
    size_t mask = slots.size() - 1, i = (mix(k, 0x9E37) & mask);
    while (true) { Slot& s = slots[i]; if (s.first == k) return &s; if (s.first == NIL) return nullptr; i = (i + 1) & mask; }
  }
  void emplace(u32 k, const Ref<Thunk>& v) {
    if ((count + 1) * 2 > slots.size()) grow();
    size_t mask = slots.size() - 1, i = (mix(k, 0x9E37) & mask);
    while (slots[i].first != NIL) { if (slots[i].first == k) return; i = (i + 1) & mask; }
    slots[i].first = k; slots[i].second = v; count++;
  }
  void grow() {
    std::vector<Slot> old; old.swap(slots); slots.resize(old.size() * 2); count = 0;
    for (auto& s : old) if (s.first != NIL) emplace(s.first, s.second);
  }
};
struct Machine {
  MachineCtx& tc;
  u64 steps = 0;
  Machine(MachineCtx& t) : tc(t) {}

  // Weak-head normalise `e` (a term with no loose bvars); `delta` allows unfolding definitions.
  Expr whnf(Expr e, bool delta, bool cheap_proj = false);

  void run(State& s, bool delta, bool cheap_proj = false);
  void force(Thunk* th, bool delta);
  Expr readback(const State& s);
  Expr readback(Thunk* th);            // original form
  Expr readback_value(Thunk* th);      // forced form (th must be forced)
  Expr readback_closure(Expr term, Env* env);

  ClosedThunkMap& closed_map();
  Ref<Thunk> mk_thunk(Expr term, const Ref<Env>& env);
  Ref<Thunk> mk_value(Expr head, const Ref<Env>& env, std::vector<Ref<Thunk>> args, u8 state);
  Ref<Env> cons(const Ref<Thunk>& t, const Ref<Env>& e);
  static Thunk* lookup(Env* e, u32 idx);

  Ref<Thunk> closed(Expr e) { return mk_thunk(e, Ref<Env>()); }
  Expr unfold_body(Expr head);   // instantiated value of a definition head (cached)
  Expr fix_body(Expr head, const struct FixRule* r, const struct FixArm* arm);
};

extern int g_engine;   // 0 = substitution reference, 1 = lazy machine, 2 = both (differential check)
extern u64 g_kam_steps;
void free_closed_thunks(void* m);
long kam_last_call();
extern long g_trace_call;   // LL_TRACE_CALL; -2 traces every machine call
extern int g_memo;   // memoise delayed applications by their read-back (LL_MEMO=1 / --memo)
extern u64 g_k_memo_hit, g_k_memo_ins;
extern std::unordered_map<u32, u64> g_delta_hist, g_iota_hist;
extern std::unordered_map<Expr, long> g_peak_by_term, g_peak_by_head;
extern long g_site_peak[8], g_site_peak_total, g_state_peak[4]; extern const char* g_site_names[8];   // LL_HIST thunk census
extern u64 g_k_app, g_k_bvar, g_k_beta, g_k_let, g_k_delta, g_k_iota, g_k_proj, g_k_projk, g_k_reck, g_k_natk, g_k_enter_val, g_k_enter_delayed, g_k_reeval;
extern u64 g_nat_ops, g_nat_cycles, g_nat_limbs, g_natlit_cycles;   // Nat primitive profile (rdtsc cycles)   // number of the most recent Machine::whnf call (for LL_TRACE_CALL)
struct KamStats { size_t thunk_chunks = 0, env_chunks = 0; long thunks_live = 0, thunks_total = 0, envs_live = 0, envs_total = 0, thunks_max = 0, envs_max = 0; size_t max_frames = 0; };
KamStats kam_stats();
void kam_pools_trim();   // release pool memory when nothing is live
void kam_init();         // before the expression table is frozen: permanent handles the machine needs

} // namespace ll
