// Utilities shared by the kernel's clients: the local context, literal expansions, the
// resident-memory limit, and the lazy machine's per-declaration context.
#include "kernel.h"
#include "kam.h"
#include "fuse.h"
#include <unistd.h>
#include <cstdio>
#include <iostream>

namespace ll {

LocalCtx g_lctx;
Expr g_rss_context = NIL;   // the term being reduced when the limit trips (for the message)
size_t g_max_rss_kb = 0;
void check_rss(const char* where) {
  if (!g_max_rss_kb) return;
  static long page_kb = sysconf(_SC_PAGESIZE) / 1024;
  FILE* f = fopen("/proc/self/statm", "r"); if (!f) return;
  long size = 0, resident = 0; int n = fscanf(f, "%ld %ld", &size, &resident); fclose(f);
  if (n == 2 && (size_t)resident * page_kb > g_max_rss_kb)
  {
    std::string ctx;
    if (g_rss_context != NIL) { ctx = expr_str(g_rss_context); if (ctx.size() > 600) ctx = ctx.substr(0, 600) + "..."; }
    fail("memory limit exceeded (RSS " + std::to_string(resident * page_kb / 1024) + " MB > " + std::to_string(g_max_rss_kb / 1024) + " MB; at " + where + ", " + std::to_string(g_exprs->size()) + " exprs)" + (ctx.empty() ? "" : "\n  while reducing: " + ctx));
  }
}

Expr LocalCtx::mk_pi(const std::vector<Expr>& fvars, Expr body) const {
  Expr r = abstract_fvars(body, fvars.size(), fvars.data());
  for (size_t i = fvars.size(); i-- > 0;) {
    const LocalDecl& d = get(fvars[i]);
    Expr ty = abstract_fvars(d.type, i, fvars.data());
    if (d.value != NIL) r = mk_let(d.name, ty, abstract_fvars(d.value, i, fvars.data()), r);
    else r = ll::mk_pi(d.name, ty, r, d.bi);
  }
  return r;
}
Expr LocalCtx::mk_lambda(const std::vector<Expr>& fvars, Expr body) const {
  Expr r = abstract_fvars(body, fvars.size(), fvars.data());
  for (size_t i = fvars.size(); i-- > 0;) {
    const LocalDecl& d = get(fvars[i]);
    Expr ty = abstract_fvars(d.type, i, fvars.data());
    if (d.value != NIL) r = mk_let(d.name, ty, abstract_fvars(d.value, i, fvars.data()), r);
    else r = ll::mk_lam(d.name, ty, r, d.bi);
  }
  return r;
}


// ---------------------------------------------------------------- literals

Expr nat_lit_to_ctor(Expr lit) {
  const mpz_class& v = nat_lit_val(lit);
  if (v == 0) return mk_const(N.Nat_zero);
  return mk_app(mk_const(N.Nat_succ), mk_nat_lit(v - 1));
}

Expr str_lit_to_ctor(Expr lit) {
  const std::string& s = str_lit_val(lit);
  // decode UTF-8 to code points
  std::vector<u32> cps;
  for (size_t i = 0; i < s.size();) {
    unsigned char c = s[i];
    u32 cp; int n;
    if (c < 0x80) { cp = c; n = 1; }
    else if ((c >> 5) == 6) { cp = c & 0x1F; n = 2; }
    else if ((c >> 4) == 14) { cp = c & 0x0F; n = 3; }
    else { cp = c & 0x07; n = 4; }
    for (int k = 1; k < n && i + k < s.size(); k++) cp = (cp << 6) | (s[i + k] & 0x3F);
    cps.push_back(cp); i += n;
  }
  LevelList l0 = g_levels->mk_list({LZERO});
  Expr charT = mk_const(N.Char);
  Expr r = mk_app(mk_const(N.List_nil, l0), charT);
  Expr cons = mk_app(mk_const(N.List_cons, l0), charT);
  Expr ofNat = mk_const(N.Char_ofNat);
  for (size_t i = cps.size(); i-- > 0;)
    r = mk_app(mk_app(cons, mk_app(ofNat, mk_nat_lit(mpz_class(cps[i])))), r);
  return mk_app(mk_const(N.String_ofList), r);
}

void check_dup_lparams(const std::vector<Name>& ps) {
  for (size_t i = 0; i < ps.size(); i++) for (size_t j = i + 1; j < ps.size(); j++)
    if (ps[i] == ps[j]) fail("duplicate universe level parameter '" + name_str(ps[i]) + "'");
}

// ---------------------------------------------------------------- the machine's context

MachineCtx::~MachineCtx() { if (closed_thunks) free_closed_thunks(closed_thunks); }

// The value of the definition head `f` (levels instantiated), fused when fusion is on (fuse.h).
Expr MachineCtx::unfold_value(Expr f, const ConstInfo& c) {
  auto it = unfold_cache.find(f);
  if (it != unfold_cache.end()) return it->second;
  bool fuse = g_fuse && c.kind == CKind::Def && bump_unfolds(c.name) >= g_fuse_min;
  if (c.lparams.empty() && !fuse) return c.value;
  Expr v = c.lparams.empty() ? c.value : instantiate_lparams(c.value, c.lparams, g_levels->list(const_levels(f)));
  if (fuse) v = fuse_term(env, fuse_cache, v);
  unfold_cache.emplace(f, v);
  return v;
}

} // namespace ll
