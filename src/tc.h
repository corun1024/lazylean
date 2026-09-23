#pragma once
#include "env.h"
#include <unordered_map>
#include <unordered_set>
#include <functional>

namespace ll {

struct LocalDecl { Name name; Expr type; Expr value; BInfo bi; };

// The local context is global to a run: fvar ids are unique and never reused, so cached
// results mentioning fvars of a closed scope can never be confused with new ones.
struct LocalCtx {
  std::vector<LocalDecl> decls;
  Expr push(Name n, Expr type, BInfo bi, Expr value = NIL) {
    decls.push_back(LocalDecl{n, type, value, bi});
    return mk_fvar((u32)decls.size() - 1);
  }
  const LocalDecl& get(Expr fv) const { return decls[fvar_id(fv)]; }
  bool is_let(Expr fv) const { return decls[fvar_id(fv)].value != NIL; }
  // Abstract fvars and rebuild binders.
  Expr mk_pi(const std::vector<Expr>& fvars, Expr body) const;
  Expr mk_lambda(const std::vector<Expr>& fvars, Expr body) const;
};
extern LocalCtx g_lctx;

struct PairHash { size_t operator()(u64 k) const { return (size_t)mix(0x1234, k); } };

// The kernel's equivalence manager: a union-find over terms in which every pair proved
// definitionally equal is merged, together with a structural comparison that looks through the
// classes.  Two large terms whose differing subterms were proved equal earlier are then
// recognised without any reduction (Lean's `equiv_manager`).
struct EquivManager {
  FlatMap<Expr> parent;
  Expr find(Expr e) {
    auto it = parent.find(e); if (it == parent.end()) return e;
    Expr r = it->second; while (true) { auto j = parent.find(r); if (j == parent.end()) break; r = j->second; }
    while (e != r) { auto j = parent.find(e); Expr n = j->second; j->second = r; e = n; }
    return r;
  }
  void merge(Expr a, Expr b) { a = find(a); b = find(b); if (a != b) parent[a] = b; }
  bool is_equiv(Expr a, Expr b, bool use_hash);
};
inline u64 pair_key(Expr a, Expr b) { return a < b ? ((u64)a << 32) | b : ((u64)b << 32) | a; }

extern unsigned g_max_depth;
extern size_t g_max_rss_kb;   // 0 = unlimited; a declaration whose check exceeds it fails
void check_rss(const char* where = "");
extern Expr g_rss_context;   // cheap (reads /proc/self/statm); call periodically
extern bool g_trace_depth;
extern unsigned g_trace_shallow;   // LL_TRACE_SHALLOW: also trace frames at depth <= this
extern u64 g_engine_mismatches;
extern u64 g_cnt_unfold, g_cnt_iota, g_cnt_prefix_hits, g_cnt_defeq_repeat, g_cnt_defeq_refail;
extern u64 g_cnt_defeq, g_cnt_defeq_quick, g_cnt_infer, g_cnt_infer_hit, g_cnt_whnf, g_cnt_whnf_hit, g_cnt_whnfcore, g_cnt_whnfcore_hit, g_cnt_pi, g_cnt_lazy, g_cnt_binding;

struct TypeChecker {
  const Environment& env;
  std::vector<Name> lparams;
  Safety safety = Safety::Safe;
  bool eager = false;
  // caches (live for one declaration)
  FlatMap<Expr> infer_i, infer_c, whnf_core_cache, whnf_cache, unfold_cache, fuse_cache;
  // kam.cpp direct branch selection: the shape of a recursor rule's right-hand side
  // (`fun params motive minors fields => minor fields ih_1 .. ih_r`), and which of a lambda's
  // leading binders occur in its body.
  struct RuleShape { int ok = -1; u32 minor_bvar = 0; std::vector<Expr> ihs; };
  std::unordered_map<Expr, RuleShape> rule_shapes;
  std::unordered_map<Expr, std::pair<u32, u64>> lam_masks;
  std::unordered_map<Expr, std::vector<Expr>> fix_inst;   // fixpoint-rule arms at a head's levels
  // Closed subterms share one machine thunk per declaration, so that a value computed in one
  // machine run (e.g. while probing a major premise) is reused by every later run: the kernel's
  // whnf cache, at thunk granularity.  Opaque pointer to avoid including kam.h here.
  void* closed_thunks = nullptr;
  ~TypeChecker();
  FlatSet64 defeq_fail;   // lazy delta: same-head pairs whose arguments differ
  FlatSet64 defeq_neg;    // pairs already found not definitionally equal
  EquivManager eqv;
  unsigned depth = 0;
  unsigned max_depth = g_max_depth;
  u64 steps = 0;   // reduction step counter (statistics)

  TypeChecker(const Environment& e, std::vector<Name> lps = {}, Safety s = Safety::Safe) : env(e), lparams(std::move(lps)), safety(s) {}

  Expr infer_type(Expr e, bool infer_only = true);
  Expr check_type(Expr e) { return infer_type(e, false); }
  Expr whnf_core(Expr e, bool cheap_proj = false);
  Expr apply_prefix_cache(Expr e);   // spine prefixes through the whnf_core cache (see tc.cpp)
  Expr whnf_core_subst(Expr e, bool cheap_proj);
  Expr whnf(Expr e);
  Expr whnf_subst(Expr e);
  bool is_def_eq(Expr t, Expr s);
  bool is_def_eq_core(Expr t, Expr s);
  bool is_def_eq_core_go(Expr t, Expr s);
  Expr ensure_sort(Expr e, Expr s);
  Expr ensure_pi(Expr e, Expr s);
  Expr ensure_type(Expr e) { return ensure_sort(infer_type(e), e); }
  bool is_prop(Expr e);
  Level get_sort_level(Expr e);

  // reduction helpers
  Expr unfold_definition(Expr e, bool& ok);
  Expr unfold_value(Expr f, const ConstInfo& c);
  Expr reduce_recursor(Expr e, bool& ok);
  Expr reduce_nat(Expr e, bool& ok);
  Expr reduce_proj(Name sname, u32 idx, Expr s, bool cheap_proj, bool& ok);
  Expr reduce_proj_core(u32 idx, Expr s, bool& ok);
  Expr reduce_proj_core(Name sname, u32 idx, Expr s, bool& ok);
  Expr inductive_reduce_rec(Expr e, bool& ok);
  Expr quot_reduce_rec(Expr e, bool& ok);
  Expr to_ctor_when_K(const ConstInfo& rec, Expr e);
  Expr to_ctor_when_struct(Name induct, Expr e);

  // definitional equality helpers
  int quick_is_def_eq(Expr t, Expr s, bool use_hash = false);  // 1 true, 0 false, -1 undef
  bool is_def_eq_lambda(Expr t, Expr s);
  bool is_def_eq_pi(Expr t, Expr s);
  bool is_def_eq_binding(Expr t, Expr s, std::vector<Expr>& subst);
  bool is_def_eq_args(Expr t, Expr s);
  bool is_def_eq_app(Expr t, Expr s);
  int is_def_eq_proof_irrel(Expr t, Expr s);
  int is_def_eq_offset(Expr t, Expr s);
  bool try_eta_expansion(Expr t, Expr s);
  bool try_eta_expansion_core(Expr t, Expr s);
  bool try_eta_struct(Expr t, Expr s);
  bool try_eta_struct_core(Expr t, Expr s);
  int try_string_lit_expansion(Expr t, Expr s);
  int try_string_lit_expansion_core(Expr t, Expr s);
  bool is_def_eq_unit_like(Expr t, Expr s);
  enum class RStatus { Continue, Unknown, True, False };
  RStatus lazy_delta_reduction_step(Expr& tn, Expr& sn);
  RStatus lazy_delta_reduction(Expr& tn, Expr& sn);
  bool lazy_delta_proj_reduction(Name sname, Expr t, Expr s, u32 idx);

  // inference helpers
  Expr infer_const(Expr e, bool infer_only);
  Expr infer_lambda(Expr e, bool infer_only);
  Expr infer_pi(Expr e, bool infer_only);
  Expr infer_app(Expr e);
  Expr infer_let(Expr e, bool infer_only);
  Expr infer_proj(Name sname, u32 idx, Expr s, Expr stype);
  void check_level(Level l);

  struct DepthGuard {
    TypeChecker& tc;
    DepthGuard(TypeChecker& t, const char* where, Expr e) : tc(t) {
      if (++tc.depth > tc.max_depth) fail("(kernel) deep recursion detected");
      if (g_trace_depth && (tc.depth + 40 > tc.max_depth || tc.depth <= g_trace_shallow)) trace(where, e);
    }
    ~DepthGuard() { tc.depth--; }
    void trace(const char* where, Expr e);
  };
};

void check_dup_lparams(const std::vector<Name>& ps);

// Literal expansions.
Expr nat_lit_to_ctor(Expr lit);
Expr str_lit_to_ctor(Expr lit);
Expr nat_lit_or_zero(Expr e, bool& ok, mpz_class& out);  // literal or Nat.zero

// Declaration checking. Adds to env on success; throws KernelError on failure.
struct CheckStats { u64 steps = 0; };
void check_and_add(Environment& env, const Decl& d, bool trust_inductives, CheckStats& st);

// A declaration is first checked without fusion or fixpoint rules, which cost more than they
// save on the ordinary declarations of a library.  What they pay off on is the evaluation of
// compiled recursion (brecOn, matchers, casesOn), so an attempt counts how many of those
// wrappers it unfolds, and one that unfolds more than the budget is abandoned by throwing this
// and checked again from scratch with both on.  Each attempt is consistent in itself: fusion
// is on or off for the whole of it.  (Not a KernelError: nothing may mistake it for a verdict.)
struct NeedsFusion {};
extern u64 g_step_budget;   // wrapper unfoldings allowed in a fusion-free attempt; 0 = no limit
extern u64 g_decl_work;
extern u64 g_decl_wrap;     // wrapper unfoldings in the current attempt (fuse.cpp)
inline void count_wrapper() {
  ++g_decl_wrap;
  if (g_step_budget && g_decl_wrap > g_step_budget) throw NeedsFusion{};
}

void add_inductive_decl(Environment& env, const Decl& d, bool trust);
void add_quot_decl(Environment& env, const Decl& d);

} // namespace ll
