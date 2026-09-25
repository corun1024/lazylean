// The type checker: normalisation by evaluation.
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
// A declaration that computes (it runs past the main session's step or allocation budget) is
// checked again in a scratch session, where the lazy machine (kam.cpp) reduces closed terms.
// check_decl (kernel.h) is the entry point; NbeFail is internal to the engine.
#pragma once
#include "env.h"

namespace ll {

struct NbeFail { const char* why; };

// Between declarations: end the main session if its arena has grown past the budget.
void nbe_between_decls();
void nbe_size_sessions(size_t export_bytes);   // default session size from the export's size
void nbe_report();          // statistics to stderr

} // namespace ll
