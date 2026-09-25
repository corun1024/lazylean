// A second checking engine for definitions, theorems and axioms: normalisation by evaluation.
//
// Terms are evaluated into semantic values (closures over environments, neutral applications
// with a spine of eliminations), and the type checker works on values: beta is a cons onto an
// environment, a bound variable entering scope is a fresh de Bruijn level, and constants stay
// folded until conversion or a recursor needs them unfolded.  Nothing is substituted and no
// term is built, so the per-declaration cost is a walk over the declaration plus whatever the
// conversion checks actually unfold.  Values live in a bump arena that is kept across many
// declarations ("a session"), and so do the caches keyed by them, so a constant's type, an
// instance's unfolding or a conversion already decided is paid for once per session rather
// than once per declaration.
//
// The engine is a fast path, not a replacement.  It may decline a declaration (NbeFail) for any
// reason -- a construct it does not handle, a budget exceeded, or a check that fails -- and the
// caller then checks the declaration again with the reference type checker (tc.cpp), whose
// verdict is final.  So a rejection here costs time, never correctness; what must hold is that
// the engine accepts only well-typed declarations.
#pragma once
#include "env.h"

namespace ll {

struct NbeFail { const char* why; };

// Check a definition, theorem, axiom or opaque declaration.  Returns true if accepted (the
// caller adds the constant); false if the engine declined or the check failed (the caller falls
// back to the reference checker).  Inductive and quotient declarations are not handled here.
bool nbe_check(const Environment& env, const Decl& d);
// Between declarations: end the session if its arena has grown past the budget.
void nbe_between_decls();
void nbe_report();          // statistics to stderr
extern bool g_nbe;          // engine enabled (default on; LL_NBE=0 or --no-nbe turns it off)

} // namespace ll
