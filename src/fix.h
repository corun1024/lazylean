#pragma once
#include "env.h"
#include <vector>

namespace ll {

// Fixpoint rules.  Lean compiles structural recursion into `T.brecOn`, whose course-of-values
// table keeps every recursive result alive and costs a recursor step, tuple constructions and
// projections per call; Coq's kernel has a primitive `fix` that unfolds only when the recursive
// argument is a constructor and reduces straight to the matching arm.  A fixpoint rule gives a
// Lean definition the same treatment:
//
//   f x_1 .. x_{k-1} (c fields) x_{k+1} ..  ~~>  arm_c[x_1 .. x_{k-1}, fields] x_{k+1} ..
//
// where `arm_c` is the definition's own unfolding on that constructor with the table accesses
// that stand for recursive calls turned back into applications of `f`.  The rule is a guess made
// from the shape of the (fused) body, and it is *verified* before use: the kernel checks
// `f x⃗ (c fields) ≡ arm_c` with fresh variables by its ordinary definitional equality, so an
// installed rule is a definitional equation whatever the derivation did.  Without a verified
// rule the machine unfolds the definition as usual.
struct FixArm { Name ctor; u32 nfields; Expr body; };   // body under (major + nfields) binders: x_1..x_{k-1}, fields; further arguments are lambdas inside
struct FixRule { Name induct; u32 major; u32 nparams; std::vector<FixArm> arms; };   // major: 0-based index of the recursive argument

// The rule of definition `c`, deriving it on first request (in the temporary tier; promoted to
// the permanent tier at the end of the declaration by `fix_end_declaration`).  nullptr = none.
const FixRule* fix_rule(const Environment& env, const ConstInfo& c);
// Called by the main loop around the reclaim of the temporary tier.
void fix_before_reclaim();
void fix_after_reclaim();

extern int g_fix;   // LL_FIX=0 disables
extern u64 g_fix_derived, g_fix_rejected, g_fix_applied;

} // namespace ll
