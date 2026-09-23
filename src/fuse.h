#pragma once
#include "env.h"
#include <unordered_map>

namespace ll {

// Wrapper fusion.  Lean compiles pattern matching and structural recursion into layers of
// definitions (`f` -> `f.match_1` -> `T.casesOn` -> `T.rec`; `T.brecOn` -> `T.brecOn.go` ->
// `T.rec` with `PProd` tables; `ite` -> `Decidable.casesOn`; instance projections through
// `instHAdd`/`Add.add`), and a Krivine machine that unfolds them one at a time pays several
// unfoldings, a dozen beta steps and as many argument thunks for every step of a Coq
// `match`/`fix`.  `fuse_body` pre-reduces a definition's instantiated value once: it beta-reduces
// the redexes that unfolding exposes, unfolds wrapper-like heads (matchers, casesOn, brecOn,
// abbreviations and small definitions) under every binder, and performs iota/projection steps
// whose major premise is already a constructor.  Every step is a beta, delta, iota or projection
// reduction of a well-typed closed term, so the result is definitionally equal to the value and
// the machine may use it wherever it would have used the value.  It is a performance device
// only: the checker's typing rules never look at fused terms.  The comparison `is_def_eq_core`
// fuses both of its operands as well, so that a term written out in a proof and the same term
// reached by unfolding a definition keep coinciding syntactically (the reference's shortcuts
// depend on that; without it a hand-written `Nat.rec` body and its fused twin could only be
// proved equal by unfolding a million steps of fuel).
// `cache` persists for a declaration: a term's fused form is a function of the term and the
// environment, so equal terms fuse to equal terms wherever they occur (results cut short by a
// size or depth limit are not cached, as they depend on the context).
Expr fuse_term(const Environment& env, FlatMap<Expr>& cache, Expr e);

bool is_nat_prim(Name f);   // a Nat primitive the machine computes with GMP: never unfolded, never given a fixpoint rule
// Fusion and fixpoint rules cost a tree walk and a verification per definition, and only repay
// on a definition that is evaluated repeatedly.  Across a library most definitions are unfolded
// once or twice, so both are held back until a constant has been unfolded often enough to be
// worth it.  The count is global and monotone, and the decision for one declaration is frozen by
// the per-declaration unfold cache, so a term keeps one shape while it is being checked.
bool is_recursion_wrapper(const ConstInfo& c);   // brecOn / casesOn / matcher / _f: compiled recursion
extern u64 g_decl_wrap;   // unfoldings of such wrappers in the current attempt
unsigned bump_unfolds(Name n);       // count this unfold, return the new count
unsigned unfold_count(Name n);
extern unsigned g_fuse_min, g_fix_min;
extern int g_fuse;   // LL_FUSE=0 disables
extern u64 g_fuse_bodies, g_fuse_unfolds, g_fuse_betas, g_fuse_iotas, g_fuse_projs, g_fuse_overflows;

} // namespace ll
