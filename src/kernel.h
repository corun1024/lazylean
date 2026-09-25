// The kernel's interface.
//
// There is one type checker, the evaluation engine in nbe.cpp: every verdict on every
// declaration comes from it.  Everything else is either a client of it -- the checks on
// inductive types and quotients (inductive.cpp) and the verification of fixpoint rules
// (fix.cpp) ask it for weak-head normal forms, types and definitional equality through the
// term-level `Kernel` below -- or a component it uses: the lazy machine (kam.cpp), which the
// engine hands closed terms to when a declaration computes, and which asks the engine in turn
// about types (a K-like recursor's major premise, structure eta) through `MachineCtx`.
#pragma once
#include "env.h"
#include <unordered_map>

namespace ll {

// ---------------------------------------------------------------- local context

struct LocalDecl { Name name; Expr type; Expr value; BInfo bi; };

// Free variables of the terms the term-level interface is asked about: fvar i is decls[i].
// Ids are reused once a scope is popped; nothing caches a term that mentions a free variable.
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

// ---------------------------------------------------------------- utilities

extern size_t g_max_rss_kb;   // 0 = unlimited; a declaration whose check exceeds it fails
void check_rss(const char* where = "");   // cheap (reads /proc/self/statm); call periodically
void check_dup_lparams(const std::vector<Name>& ps);
Expr nat_lit_to_ctor(Expr lit);
Expr str_lit_to_ctor(Expr lit);

// ---------------------------------------------------------------- the term-level interface

// Questions about terms (with free variables from g_lctx) under a declaration's universe
// parameters, answered by the kernel.  Each method is a pure query; errors are KernelErrors.
struct Kernel {
  const Environment& env;
  std::vector<Name> lparams;
  Safety safety;
  FlatMap<Expr> fuse_cache;   // fix.cpp fuses the bodies it derives rules from
  Kernel(const Environment& e, std::vector<Name> lps = {}, Safety s = Safety::Safe) : env(e), lparams(std::move(lps)), safety(s) {}

  Expr whnf(Expr e);
  Expr whnf_core(Expr e);                 // beta/iota/projection, no unfolding of definitions
  Expr infer_type(Expr e);                // assumes e is well typed
  Expr check_type(Expr e);                // checks e, returns its type
  bool is_def_eq(Expr a, Expr b);
  Expr ensure_sort(Expr type, Expr of);   // type, reduced to a Sort, or a "type expected" error
  Expr ensure_pi(Expr type, Expr of);
  Expr ensure_type(Expr e) { return ensure_sort(infer_type(e), e); }
  bool is_prop(Expr type);                // `type : Prop`
  // Kernel reductions of a recursor's major premise (Lean's to_cnstr_when_K / to_cnstr_when_structure)
  Expr to_ctor_when_K(const ConstInfo& rec, Expr major);
  Expr to_ctor_when_struct(Name induct, Expr major);
};

// ---------------------------------------------------------------- the machine's context

// What the lazy machine keeps for one declaration, and asks the kernel.
struct MachineCtx {
  const Environment& env;
  Kernel k;
  FlatMap<Expr> unfold_cache, fuse_cache;
  void* closed_thunks = nullptr;
  struct RuleShape { int ok = -1; u32 minor_bvar = 0; std::vector<Expr> ihs; };
  std::unordered_map<Expr, RuleShape> rule_shapes;
  std::unordered_map<Expr, std::pair<u32, u64>> lam_masks;
  std::unordered_map<Expr, std::vector<Expr>> fix_inst;
  explicit MachineCtx(const Environment& e, std::vector<Name> lps = {}) : env(e), k(e, std::move(lps)) {}
  ~MachineCtx();
  Expr unfold_value(Expr f, const ConstInfo& c);   // the (fused) value of definition head f
};

// ---------------------------------------------------------------- declarations

// Check a declaration and add its constants to env; throws KernelError on rejection.
void check_decl(Environment& env, Decl& d);   // moves the checked constants into env
void add_inductive_decl(Environment& env, const Decl& d, bool trust);
void add_quot_decl(Environment& env, const Decl& d);
void kernel_env_rolled_back();   // after Environment::rollback while a declaration is being checked

} // namespace ll
