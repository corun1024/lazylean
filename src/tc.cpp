#include "tc.h"
#include <unistd.h>
#include <cstdio>
#include "kam.h"
#include "fuse.h"
#include <algorithm>
#include <iostream>

namespace ll {

LocalCtx g_lctx;
TypeChecker::~TypeChecker() { if (closed_thunks) free_closed_thunks(closed_thunks); }
unsigned g_max_depth = 1000000;
size_t g_max_rss_kb = 0;
Expr g_rss_context = NIL;   // the term being reduced when the limit trips (for the message)
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
bool g_trace_depth = getenv("LL_TRACE_DEPTH") != nullptr;
unsigned g_trace_shallow = getenv("LL_TRACE_SHALLOW") ? atoi(getenv("LL_TRACE_SHALLOW")) : 0;
u64 g_engine_mismatches = 0;
u64 g_cnt_unfold = 0, g_cnt_iota = 0, g_cnt_prefix_hits = 0;
static std::unordered_set<u64, PairHash> g_defeq_pairs_seen, g_defeq_failed_pairs; u64 g_cnt_defeq_repeat = 0, g_cnt_defeq_refail = 0;   // diagnostics: how often the same pair is compared again

static bool g_trace_subst = false;
u64 g_cnt_defeq = 0, g_cnt_defeq_quick = 0, g_cnt_infer = 0, g_cnt_infer_hit = 0, g_cnt_whnf = 0, g_cnt_whnf_hit = 0, g_cnt_whnfcore = 0, g_cnt_whnfcore_hit = 0, g_cnt_pi = 0, g_cnt_lazy = 0, g_cnt_binding = 0;
static bool g_trace_nat = getenv("LL_TRACE_NAT") != nullptr;
void TypeChecker::DepthGuard::trace(const char* where, Expr e) {
  std::string s = expr_str(e); if (s.size() > 300) s = s.substr(0, 300) + "...";
  std::cerr << "[depth " << tc.depth << "] " << where << ": " << s << "\n";
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

Expr nat_lit_or_zero(Expr e, bool& ok, mpz_class& out) {
  if (is_nat_lit(e)) { ok = true; out = nat_lit_val(e); return e; }
  if (is_const_of(e, N.Nat_zero)) { ok = true; out = 0; return e; }
  ok = false; return e;
}

// ---------------------------------------------------------------- basics

void TypeChecker::check_level(Level l) {
  Name bad = get_undef_param(l, lparams);
  if (bad != NIL) fail("invalid reference to undefined universe level parameter '" + name_str(bad) + "'");
}

Expr TypeChecker::ensure_sort(Expr e, Expr s) {
  if (is_sort(e)) return e;
  Expr e2 = whnf(e);
  if (is_sort(e2)) return e2;
  fail("type expected: " + expr_str(s));
}
Expr TypeChecker::ensure_pi(Expr e, Expr s) {
  if (is_pi(e)) return e;
  Expr e2 = whnf(e);
  if (is_pi(e2)) return e2;
  fail("function expected: " + expr_str(s));
}
Level TypeChecker::get_sort_level(Expr e) { return sort_level(ensure_sort(infer_type(e), e)); }
bool TypeChecker::is_prop(Expr e) { return is_always_zero(get_sort_level(e)); }

// ---------------------------------------------------------------- type inference

Expr TypeChecker::infer_const(Expr e, bool infer_only) {
  const ConstInfo& c = env.get(const_name(e));
  const std::vector<Level> ls = g_levels->list(const_levels(e));
  if (c.lparams.size() != ls.size())
    fail("incorrect number of universe levels for '" + name_str(c.name) + "'");
  if (!infer_only) {
    if (c.is_unsafe && safety != Safety::Unsafe)
      fail("invalid declaration, it uses unsafe declaration '" + name_str(c.name) + "'");
    if (c.kind == CKind::Def && c.safety == Safety::Partial && safety == Safety::Safe)
      fail("invalid declaration, safe declaration must not contain partial declaration '" + name_str(c.name) + "'");
    for (Level l : ls) check_level(l);
  }
  return instantiate_lparams(c.type, c.lparams, ls);
}

Expr TypeChecker::infer_lambda(Expr e, bool infer_only) {
  std::vector<Expr> fvars;
  Expr it = e;
  while (is_lam(it)) {
    Expr d = instantiate_rev(binding_dom(it), fvars.size(), fvars.data());
    if (!infer_only) ensure_sort(infer_type(d, infer_only), d);
    fvars.push_back(g_lctx.push(binding_name(it), d, binding_info(it)));
    it = binding_body(it);
  }
  Expr r = infer_type(instantiate_rev(it, fvars.size(), fvars.data()), infer_only);
  r = cheap_beta_reduce(r);
  return g_lctx.mk_pi(fvars, r);
}

Expr TypeChecker::infer_pi(Expr e, bool infer_only) {
  std::vector<Expr> fvars; std::vector<Level> us;
  Expr it = e;
  while (is_pi(it)) {
    Expr d = instantiate_rev(binding_dom(it), fvars.size(), fvars.data());
    Expr t1 = ensure_sort(infer_type(d, infer_only), d);
    us.push_back(sort_level(t1));
    fvars.push_back(g_lctx.push(binding_name(it), d, binding_info(it)));
    it = binding_body(it);
  }
  Expr r = infer_type(instantiate_rev(it, fvars.size(), fvars.data()), infer_only);
  Level s = sort_level(ensure_sort(r, it));
  for (size_t i = us.size(); i-- > 0;) s = mk_imax_s(us[i], s);
  return mk_sort(s);
}

Expr TypeChecker::infer_app(Expr e) {
  std::vector<Expr> args;
  Expr f = get_app_args_fn(e, args);
  Expr ftype = infer_type(f, true);
  size_t j = 0;
  for (size_t i = 0; i < args.size(); i++) {
    if (is_pi(ftype)) { ftype = binding_body(ftype); }
    else {
      ftype = instantiate_rev(ftype, i - j, args.data() + j);
      ftype = binding_body(ensure_pi(ftype, e));
      j = i;
    }
  }
  return instantiate_rev(ftype, args.size() - j, args.data() + j);
}

Expr TypeChecker::infer_let(Expr e, bool infer_only) {
  std::vector<Expr> fvars;
  Expr it = e;
  while (is_let(it)) {
    Expr ty = instantiate_rev(let_type(it), fvars.size(), fvars.data());
    Expr val = instantiate_rev(let_val(it), fvars.size(), fvars.data());
    if (!infer_only) {
      ensure_sort(infer_type(ty, infer_only), ty);
      Expr vt = infer_type(val, infer_only);
      if (!is_def_eq(vt, ty)) fail("let value type mismatch for '" + name_str(binding_name(it)) + "'");
    }
    fvars.push_back(g_lctx.push(binding_name(it), ty, BInfo::Default, val));
    it = let_body(it);
  }
  Expr r = infer_type(instantiate_rev(it, fvars.size(), fvars.data()), infer_only);
  r = cheap_beta_reduce(r);
  return g_lctx.mk_pi(fvars, r);
}

Expr TypeChecker::infer_proj(Name sname, u32 idx, Expr s, Expr stype) {
  auto bad = [&]() -> Expr { fail("invalid projection " + name_str(sname) + "." + std::to_string(idx)); };
  Expr type = whnf(stype);
  std::vector<Expr> args;
  Expr I = get_app_args_fn(type, args);
  if (!is_const(I) || const_name(I) != sname) bad();
  const ConstInfo& Ival = env.get(const_name(I));
  if (Ival.kind != CKind::Induct || Ival.ctors.size() != 1) bad();
  if (args.size() != Ival.nparams + Ival.nindices) bad();
  const ConstInfo& cinfo = env.get(Ival.ctors[0]);
  Expr r = instantiate_lparams(cinfo.type, cinfo.lparams, g_levels->list(const_levels(I)));
  for (u32 i = 0; i < Ival.nparams; i++) {
    Expr w = whnf(r);
    if (!is_pi(w)) bad();
    r = instantiate1(binding_body(w), args[i]);
  }
  bool maybe_prop = is_prop(type);
  for (u32 i = 0; i < idx; i++) {
    Expr w = whnf(r);
    if (!is_pi(w)) bad();
    if (has_loose_bvars(binding_body(w))) {
      if (maybe_prop && !is_prop(binding_dom(w))) bad();
      r = instantiate1(binding_body(w), mk_proj(sname, i, s));
    } else r = binding_body(w);
  }
  Expr w = whnf(r);
  if (!is_pi(w)) bad();
  if (maybe_prop && !is_prop(binding_dom(w))) bad();
  return binding_dom(w);
}

Expr TypeChecker::infer_type(Expr e, bool infer_only) {
  DepthGuard g(*this, "infer", e);
  if (has_loose_bvars(e)) fail("type checker does not support loose bound variables");
  auto& cache = infer_only ? infer_i : infer_c;
  g_cnt_infer++;
  auto it = cache.find(e);
  if (it != cache.end()) { g_cnt_infer_hit++; return it->second; }
  Expr r;
  switch (kind(e)) {
    case EKind::Lit:
      if (!infer_only) {
        if (is_nat_lit(e)) env.get(N.Nat); else { env.get(N.Char_ofNat); env.get(N.String_ofList); }
      }
      r = mk_const(is_nat_lit(e) ? N.Nat : N.String); break;
    case EKind::Proj: r = infer_proj(proj_sname(e), proj_idx(e), proj_expr(e), infer_type(proj_expr(e), infer_only)); break;
    case EKind::FVar: r = g_lctx.get(e).type; break;
    case EKind::BVar: fail("unreachable bvar");
    case EKind::Sort: if (!infer_only) check_level(sort_level(e)); r = mk_sort(mk_succ(sort_level(e))); break;
    case EKind::Const: r = infer_const(e, infer_only); break;
    case EKind::Lam: r = infer_lambda(e, infer_only); break;
    case EKind::Pi: r = infer_pi(e, infer_only); break;
    case EKind::App:
      if (infer_only) r = infer_app(e);
      else {
        Expr f = app_fn(e), a = app_arg(e);
        Expr ftype = ensure_pi(infer_type(f, false), e);
        Expr atype = infer_type(a, false);
        Expr dtype = binding_dom(ftype);
        bool ok;
        if (is_app_of_arity(a, N.eagerReduce, 2)) {
          bool old = eager; eager = true; ok = is_def_eq(dtype, atype); eager = old;
        } else ok = is_def_eq(dtype, atype);
        if (!ok) fail("application type mismatch in " + expr_str(e) + "\n  argument type: " + expr_str(atype) + "\n  expected: " + expr_str(dtype));
        r = instantiate1(binding_body(ftype), a);
      }
      break;
    case EKind::Let: r = infer_let(e, infer_only); break;
  }
  cache.emplace(e, r);
  return r;
}

// ---------------------------------------------------------------- reduction

Expr TypeChecker::reduce_proj_core(u32 idx, Expr s, bool& ok) { return reduce_proj_core(0, idx, s, ok); }
Expr TypeChecker::reduce_proj_core(Name sname, u32 idx, Expr s, bool& ok) {
  Expr c = s;
  if (is_str_lit(c)) c = whnf(str_lit_to_ctor(c));
  std::vector<Expr> args;
  Expr mk = get_app_args_fn(c, args);
  ok = false;
  if (!is_const(mk)) return s;
  const ConstInfo* mi = env.find(const_name(mk));
  if (!mi || mi->kind != CKind::Ctor) return s;
  if (sname != 0 && mi->induct != sname) return s;
  if (mi->nparams + idx >= args.size()) return s;
  ok = true;
  return args[mi->nparams + idx];
}

Expr TypeChecker::reduce_proj(Name sname, u32 idx, Expr s, bool cheap_proj, bool& ok) {
  Expr c = cheap_proj ? whnf_core(s, true) : whnf(s);
  return reduce_proj_core(sname, idx, c, ok);
}

Expr TypeChecker::quot_reduce_rec(Expr e, bool& ok) {
  ok = false;
  Expr fn = get_app_fn(e);
  if (!is_const(fn)) return e;
  unsigned mk_pos, arg_pos;
  if (const_name(fn) == N.Quot_lift) { mk_pos = 5; arg_pos = 3; }
  else if (const_name(fn) == N.Quot_ind) { mk_pos = 4; arg_pos = 3; }
  else return e;
  std::vector<Expr> args; get_app_args(e, args);
  if (mk_pos >= args.size()) return e;
  Expr mk = whnf(args[mk_pos]);
  if (!is_app_of_arity(mk, N.Quot_mk, 3)) return e;
  Expr r = mk_app(args[arg_pos], app_arg(mk));
  unsigned elim_arity = mk_pos + 1;
  if (elim_arity < args.size()) r = mk_apps_range(r, args, elim_arity, args.size());
  ok = true;
  return r;
}

Expr TypeChecker::to_ctor_when_K(const ConstInfo& rec, Expr e) {
  Expr app_type = whnf(infer_type(e));
  Expr I = get_app_fn(app_type);
  if (!is_const(I) || const_name(I) != rec.major_induct) return e;
  std::vector<Expr> args; get_app_args(app_type, args);
  const ConstInfo& ind = env.get(const_name(I));
  if (ind.ctors.empty()) return e;
  Expr ctor = mk_apps_range(mk_const(ind.ctors[0], const_levels(I)), args, 0, rec.nparams);
  if (!is_def_eq(app_type, infer_type(ctor))) return e;
  return ctor;
}

Expr TypeChecker::to_ctor_when_struct(Name induct, Expr e) {
  if (!env.is_structure_like(induct)) return e;
  Expr f = get_app_fn(e);
  if (is_const(f)) { const ConstInfo* c = env.find(const_name(f)); if (c && c->kind == CKind::Ctor) return e; }
  Expr etype = whnf(infer_type(e));
  Expr I = get_app_fn(etype);
  if (!is_const(I) || const_name(I) != induct) return e;
  if (is_prop(etype)) return e;
  std::vector<Expr> args; get_app_args(etype, args);
  const ConstInfo& ind = env.get(induct);
  const ConstInfo& ctor = env.get(ind.ctors[0]);
  Expr r = mk_apps_range(mk_const(ctor.name, const_levels(I)), args, 0, ctor.nparams);
  for (u32 i = 0; i < ctor.nfields; i++) r = mk_app(r, mk_proj(induct, i, e));
  return r;
}

Expr TypeChecker::inductive_reduce_rec(Expr e, bool& ok) {
  ok = false;
  Expr fn = get_app_fn(e);
  if (!is_const(fn)) return e;
  const ConstInfo* info = env.find(const_name(fn));
  if (!info || info->kind != CKind::Rec) return e;
  std::vector<Expr> rec_args; get_app_args(e, rec_args);
  u32 major_idx = info->rec_major_idx();
  if (major_idx >= rec_args.size()) return e;
  Expr major = rec_args[major_idx];
  if (info->k) major = to_ctor_when_K(*info, major);
  major = whnf(major);
  if (is_nat_lit(major)) major = nat_lit_to_ctor(major);
  else if (is_str_lit(major)) major = whnf(str_lit_to_ctor(major));
  else major = to_ctor_when_struct(info->major_induct, major);
  Expr mfn = get_app_fn(major);
  if (!is_const(mfn)) return e;
  const RecRule* rule = nullptr;
  for (auto& r : info->rules) if (r.ctor == const_name(mfn)) { rule = &r; break; }
  if (!rule) return e;
  std::vector<Expr> major_args; get_app_args(major, major_args);
  if (rule->nfields > major_args.size()) return e;
  const std::vector<Level> ls = g_levels->list(const_levels(fn));
  if (ls.size() != info->lparams.size()) return e;
  Expr rhs = instantiate_lparams(rule->rhs, info->lparams, ls);
  rhs = mk_apps_range(rhs, rec_args, 0, info->rec_first_index_idx());
  rhs = mk_apps_range(rhs, major_args, major_args.size() - rule->nfields, major_args.size());
  if (major_idx + 1 < rec_args.size()) rhs = mk_apps_range(rhs, rec_args, major_idx + 1, rec_args.size());
  ok = true;
  steps++;
  return rhs;
}

Expr TypeChecker::reduce_recursor(Expr e, bool& ok) {
  if (env.quot_init) { Expr r = quot_reduce_rec(e, ok); if (ok) return r; }
  return inductive_reduce_rec(e, ok);
}


// Lean's whnf_core recurses through an application's function, so every proper prefix of the
// spine is looked up in the whnf_core cache on the way; a "cheap" call thus returns earlier
// full results for the parts it has seen.  The machine takes the spine in one go, so the same
// lookups are made here before it starts (prefixes are the App nodes themselves: no allocation).
Expr TypeChecker::apply_prefix_cache(Expr e) {
  for (int rounds = 0; rounds < 8; rounds++) {
    if (!is_app(e)) return e;
    std::vector<Expr> rest;
    Expr x = app_fn(e); rest.push_back(app_arg(e));
    Expr hit = NIL;
    while (true) {   // every proper prefix, the bare head included (a projection, say)
      auto it = whnf_core_cache.find(x);
      if (it != whnf_core_cache.end()) { if (it->second != x) hit = it->second; break; }
      if (!is_app(x)) break;
      rest.push_back(app_arg(x)); x = app_fn(x);
    }
    if (hit == NIL) return e;
    Expr r = hit;
    for (size_t i = rest.size(); i-- > 0;) r = mk_app(r, rest[i]);
    g_cnt_prefix_hits++;
    e = r;
  }
  return e;
}

// Which reductions the machine performs: bit1 whnf (delta: the evaluation work), bit0 whnf_core.
// Default: whnf only.  whnf_core does no unfolding and the reference algorithm caches every
// sub-result of its recursion, which "cheap" calls later rely on; the machine, taking a spine in
// one go, cannot reproduce that, and on some Mathlib declarations lazy delta then unfolds without end.
static int g_kam_mode = getenv("LL_KAM_MODE") ? atoi(getenv("LL_KAM_MODE")) : 2;
Expr TypeChecker::whnf_core(Expr e, bool cheap_proj) {
  switch (kind(e)) {
    case EKind::BVar: case EKind::Sort: case EKind::Pi: case EKind::Const: case EKind::Lam: case EKind::Lit:
      return e;
    case EKind::FVar: if (!g_lctx.is_let(e)) return e; break;
    default: break;
  }
  if (g_engine >= 1 && (g_kam_mode & 1)) {
    // as in the kernel: the cache is consulted for every call but only non-cheap results are stored
    g_cnt_whnfcore++;
    { auto it = whnf_core_cache.find(e); if (it != whnf_core_cache.end()) { g_cnt_whnfcore_hit++; return it->second; } }
    DepthGuard g(*this, "whnf_core", e);
    Machine m(*this);
    Expr e1 = apply_prefix_cache(e);
    g_rss_context = e1;
    Expr r = m.whnf(e1, false, cheap_proj);
    long call_no = kam_last_call();
    steps += m.steps;
    if (g_engine == 2) {
      Expr r2 = whnf_core_subst(e, cheap_proj);
      if (expand_closures(r) != expand_closures(r2)) {
        std::string a = expr_str(r), b = expr_str(r2);
        if (a.size() > 400) a = a.substr(0, 400) + "..."; if (b.size() > 400) b = b.substr(0, 400) + "...";
        std::string in = expr_str(e); if (in.size() > 400) in = in.substr(0, 400) + "...";
        std::cerr << "[engine mismatch] whnf_core (cheap_proj=" << cheap_proj << ", call " << call_no << ")\n   in:    " << in << "\n   kam:   " << a << "\n   subst: " << b << "\n";
        g_engine_mismatches++;
        if (getenv("LL_TRACE_FIRST_MISMATCH")) {   // replay the reference computation with a trace, then stop
          g_trace_subst = true; long saved = g_trace_call; g_trace_call = -2; whnf_core_subst(e, cheap_proj); g_trace_call = saved; g_trace_subst = false;
          fail("stopped after the first engine mismatch (LL_TRACE_FIRST_MISMATCH)");
        }
      }
    }
    if (!cheap_proj) whnf_core_cache.emplace(e, r);
    return r;
  }
  return whnf_core_subst(e, cheap_proj);
}

// The substitution-based reference (Lean's whnf_core).
static void tsub(const char* what, Expr e) {
  if (!g_trace_subst) return;
  std::string s = expr_str(e); if (s.size() > 160) s = s.substr(0, 160) + "...";
  std::cerr << "    [subst " << what << "] " << s << "\n";
}
Expr TypeChecker::whnf_core_subst(Expr e, bool cheap_proj) {
  DepthGuard g(*this, "whnf_core", e);
  tsub(cheap_proj ? "enter(cheap)" : "enter", e);
  switch (kind(e)) {
    case EKind::BVar: case EKind::Sort: case EKind::Pi: case EKind::Const: case EKind::Lam: case EKind::Lit:
      return e;
    case EKind::FVar: if (!g_lctx.is_let(e)) return e; break;
    default: break;
  }
  auto it = whnf_core_cache.find(e);
  if (it != whnf_core_cache.end()) { tsub("cache hit ->", it->second); return it->second; }
  auto save = [&](Expr r) { if (!cheap_proj) whnf_core_cache.emplace(e, r); return r; };
  switch (kind(e)) {
    case EKind::FVar: return whnf_core(g_lctx.get(e).value, cheap_proj);
    case EKind::App: {
      std::vector<Expr> args;
      Expr f0 = get_app_args_fn(e, args);
      Expr f = whnf_core(f0, cheap_proj);
      if (is_lam(f)) {
        size_t m = 0;
        while (is_lam(f) && m < args.size()) { f = binding_body(f); m++; }
        steps++;
        Expr r = instantiate_rev(f, m, args.data());
        r = mk_apps_range(r, args, m, args.size());
        return save(whnf_core(r, cheap_proj));
      } else if (f == f0) {
        bool ok; Expr r = reduce_recursor(e, ok);
        if (ok) return whnf_core(r, cheap_proj);
        return e;
      } else {
        Expr r = mk_apps(f, args);
        return save(whnf_core(r, cheap_proj));
      }
    }
    case EKind::Let: steps++; return save(whnf_core(instantiate1(let_body(e), let_val(e)), cheap_proj));
    case EKind::Proj: {
      bool ok; Expr m = reduce_proj(proj_sname(e), proj_idx(e), proj_expr(e), cheap_proj, ok);
      tsub(ok ? "proj reduced ->" : "proj stuck", ok ? m : e);
      if (ok) { steps++; g_cnt_iota++; return save(whnf_core(m, cheap_proj)); }
      return save(e);
    }
    default: return e;
  }
}

// The value of the definition head `f` (levels instantiated), fused when fusion is on (fuse.h).
// Both engines unfold through this one cache so that every delta step, in lazy delta as in the
// machine, exposes the same term: the reference's syntactic shortcuts in is_def_eq depend on the
// two sides of a comparison having been unfolded alike.
Expr TypeChecker::unfold_value(Expr f, const ConstInfo& c) {
  bool fuse = g_fuse && c.kind == CKind::Def;
  if (c.lparams.empty() && !fuse) return c.value;
  auto it = unfold_cache.find(f);
  if (it != unfold_cache.end()) return it->second;
  Expr v = c.lparams.empty() ? c.value : instantiate_lparams(c.value, c.lparams, g_levels->list(const_levels(f)));
  if (fuse) v = fuse_term(env, fuse_cache, v);
  unfold_cache.emplace(f, v);
  return v;
}

Expr TypeChecker::unfold_definition(Expr e, bool& ok) {
  ok = false;
  Expr f = get_app_fn(e);
  if (!is_const(f)) return e;
  const ConstInfo* c = env.find(const_name(f));
  if (!c || !c->is_delta()) return e;
  if (g_levels->list_size(const_levels(f)) != c->lparams.size()) return e;
  g_cnt_unfold++;
  Expr v = unfold_value(f, *c);
  ok = true; steps++;
  if (g_trace_nat && (c->name == N.Nat_add || c->name == N.Nat_sub || c->name == N.Nat_mul || c->name == N.Nat_mod || c->name == N.Nat_div || c->name == N.Nat_pow || c->name == N.Nat_beq || c->name == N.Nat_ble)) {
    std::string s = expr_str(e); if (s.size() > 400) s = s.substr(0, 400) + "...";
    std::cerr << "[unfold " << name_str(c->name) << "] " << s << "\n";
    std::vector<Expr> args; get_app_args(e, args);
    for (Expr a : args) { std::string w = expr_str(whnf(a)); if (w.size() > 300) w = w.substr(0, 300) + "..."; std::cerr << "   arg whnf: " << w << "\n"; }
  }
  if (f == e) return v;
  std::vector<Expr> args; get_app_args(e, args);
  return mk_apps(v, args);
}

Expr TypeChecker::reduce_nat(Expr e, bool& ok) {
  ok = false;
  unsigned n = get_app_num_args(e);
  if (n == 1) {
    Expr f = app_fn(e);
    if (is_const_of(f, N.Nat_succ)) {
      bool k; mpz_class v; nat_lit_or_zero(whnf(app_arg(e)), k, v);
      if (!k) return e;
      ok = true; return mk_nat_lit(v + 1);
    }
    return e;
  }
  if (n != 2) return e;
  Expr f = app_fn(app_fn(e));
  if (!is_const(f)) return e;
  Name fn = const_name(f);
  bool bin = fn == N.Nat_add || fn == N.Nat_sub || fn == N.Nat_mul || fn == N.Nat_pow || fn == N.Nat_gcd || fn == N.Nat_mod ||
             fn == N.Nat_div || fn == N.Nat_beq || fn == N.Nat_ble || fn == N.Nat_land || fn == N.Nat_lor || fn == N.Nat_xor ||
             fn == N.Nat_shiftLeft || fn == N.Nat_shiftRight;
  if (!bin) return e;
  bool k1, k2; mpz_class a, b;
  Expr w1 = whnf(app_arg(app_fn(e))); nat_lit_or_zero(w1, k1, a);
  if (g_trace_nat && (fn == N.Nat_add || fn == N.Nat_mul)) { std::string s1 = expr_str(w1); if (s1.size() > 100) s1 = s1.substr(0, 100); std::cerr << "[reduce_nat " << name_str(fn) << "] arg1 whnf=" << s1 << " lit=" << k1 << " has_fvar(e)=" << has_fvar(e) << "\n"; }
  if (!k1) return e;
  nat_lit_or_zero(whnf(app_arg(e)), k2, b); if (!k2) return e;
  ok = true; steps++;
  mpz_class r;
  if (fn == N.Nat_add) r = a + b;
  else if (fn == N.Nat_sub) r = a >= b ? mpz_class(a - b) : mpz_class(0);
  else if (fn == N.Nat_mul) r = a * b;
  else if (fn == N.Nat_pow) {
    if (b > (1u << 24)) { ok = false; return e; }
    mpz_pow_ui(r.get_mpz_t(), a.get_mpz_t(), b.get_ui());
  }
  else if (fn == N.Nat_gcd) mpz_gcd(r.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
  else if (fn == N.Nat_mod) r = b == 0 ? a : mpz_class(a % b);
  else if (fn == N.Nat_div) r = b == 0 ? mpz_class(0) : mpz_class(a / b);
  else if (fn == N.Nat_beq) return mk_const(a == b ? N.Bool_true : N.Bool_false);
  else if (fn == N.Nat_ble) return mk_const(a <= b ? N.Bool_true : N.Bool_false);
  else if (fn == N.Nat_land) r = a & b;
  else if (fn == N.Nat_lor) r = a | b;
  else if (fn == N.Nat_xor) r = a ^ b;
  else if (fn == N.Nat_shiftLeft) {
    if (!b.fits_ulong_p()) fail("Nat.shiftLeft: shift too large");
    mpz_mul_2exp(r.get_mpz_t(), a.get_mpz_t(), b.get_ui());
  }
  else if (fn == N.Nat_shiftRight) {
    if (!b.fits_ulong_p()) r = 0; else mpz_fdiv_q_2exp(r.get_mpz_t(), a.get_mpz_t(), b.get_ui());
  }
  return mk_nat_lit(r);
}

Expr TypeChecker::whnf(Expr e) {
  switch (kind(e)) {
    case EKind::BVar: case EKind::Sort: case EKind::Pi: case EKind::Lit: return e;
    case EKind::FVar: if (!g_lctx.is_let(e)) return e; break;
    default: break;
  }
  g_cnt_whnf++;
  if ((g_cnt_whnf & 0xffff) == 0) check_rss("whnf");
  auto it = whnf_cache.find(e);
  if (it != whnf_cache.end()) { g_cnt_whnf_hit++; return it->second; }
  DepthGuard g(*this, "whnf", e);
  if (g_engine >= 1 && (g_kam_mode & 2)) {
    if (is_app(e) || is_const(e)) {   // heads that no rule applies to
      Expr f = get_app_fn(e);
      if (is_const(f)) {
        const ConstInfo* c = env.find(const_name(f));
        // (`Nat.succ n` is excluded: whnf turns it into a literal when n reduces to one, and
        //  reduce_nat / lazy_delta rely on that.)
        if (c && (c->kind == CKind::Ctor || c->kind == CKind::Induct || c->kind == CKind::Axiom || c->kind == CKind::Opaque) &&
            !(const_name(f) == N.Nat_succ && is_app(e))) { whnf_cache.emplace(e, e); return e; }
      }
    }
    Machine m(*this);
    Expr e1 = apply_prefix_cache(e);
    g_rss_context = e1;
    Expr r = m.whnf(e1, true);
    steps += m.steps;
    if (g_engine == 2) {
      Expr r2 = whnf_subst(e);
      if (expand_closures(r) != expand_closures(r2)) {
        std::string a = expr_str(r), b = expr_str(r2);
        if (a.size() > 400) a = a.substr(0, 400) + "..."; if (b.size() > 400) b = b.substr(0, 400) + "...";
        std::cerr << "[engine mismatch] whnf\n   kam:   " << a << "\n   subst: " << b << "\n";
        g_engine_mismatches++;
      }
    }
    whnf_cache.emplace(e, r);
    return r;
  }
  Expr t = whnf_subst(e);
  whnf_cache.emplace(e, t);
  return t;
}

// The substitution-based reference weak-head normaliser (Lean's algorithm).
Expr TypeChecker::whnf_subst(Expr e) {
  Expr t = e;
  for (unsigned fuel = 0;; fuel++) {
    if (fuel > 100000000) fail("(kernel) deterministic timeout in whnf");
    t = whnf_core(t);
    Expr f = get_app_fn(t);
    if (is_const(f) && (const_name(f) == N.reduceBool || const_name(f) == N.reduceNat))
      fail("lazylean does not support native reduction (Lean.reduceBool/reduceNat)");
    bool ok;
    Expr r = reduce_nat(t, ok);
    if (ok) { t = r; break; }
    r = unfold_definition(t, ok);
    if (!ok) break;
    t = r;
  }
  return t;
}

// ---------------------------------------------------------------- definitional equality

bool TypeChecker::is_def_eq_binding(Expr t, Expr s, std::vector<Expr>& subst) {
  g_cnt_binding++;
  // t, s are both lambdas or both pis of the same kind
  EKind k = kind(t);
  while (kind(t) == k && kind(s) == k) {
    Expr sdom = NIL;
    if (binding_dom(t) != binding_dom(s)) {
      sdom = instantiate_rev(binding_dom(s), subst.size(), subst.data());
      Expr tdom = instantiate_rev(binding_dom(t), subst.size(), subst.data());
      if (!is_def_eq(tdom, sdom)) return false;
    }
    if (has_loose_bvars(binding_body(t)) || has_loose_bvars(binding_body(s))) {
      if (sdom == NIL) sdom = instantiate_rev(binding_dom(s), subst.size(), subst.data());
      subst.push_back(g_lctx.push(binding_name(s), sdom, binding_info(s)));
    } else {
      subst.push_back(mk_sort(LZERO));  // dummy, never referenced
    }
    t = binding_body(t); s = binding_body(s);
  }
  return is_def_eq(instantiate_rev(t, subst.size(), subst.data()), instantiate_rev(s, subst.size(), subst.data()));
}
bool TypeChecker::is_def_eq_lambda(Expr t, Expr s) { std::vector<Expr> subst; return is_def_eq_binding(t, s, subst); }
bool TypeChecker::is_def_eq_pi(Expr t, Expr s) { std::vector<Expr> subst; return is_def_eq_binding(t, s, subst); }

bool EquivManager::is_equiv(Expr a, Expr b, bool use_hash) {
  if (a == b) return true;
  if (use_hash && raw(a).hash != raw(b).hash) return false;
  if (is_bvar(a) && is_bvar(b)) return bvar_idx(a) == bvar_idx(b);
  Expr ra = find(a), rb = find(b);
  if (ra == rb) return true;
  EKind ka = kind(a), kb = kind(b);
  if (ka != kb) return false;
  bool r = false;
  switch (ka) {
    case EKind::FVar: r = fvar_id(a) == fvar_id(b); break;
    case EKind::Sort: r = is_equivalent(sort_level(a), sort_level(b)); break;
    case EKind::Const: r = const_name(a) == const_name(b) && is_equiv_list(const_levels(a), const_levels(b)); break;
    case EKind::App: r = is_equiv(app_fn(a), app_fn(b), use_hash) && is_equiv(app_arg(a), app_arg(b), use_hash); break;
    case EKind::Lam: case EKind::Pi: r = is_equiv(binding_dom(a), binding_dom(b), use_hash) && is_equiv(binding_body(a), binding_body(b), use_hash); break;
    case EKind::Let: r = is_equiv(let_type(a), let_type(b), use_hash) && is_equiv(let_val(a), let_val(b), use_hash) && is_equiv(let_body(a), let_body(b), use_hash); break;
    case EKind::Proj: r = proj_sname(a) == proj_sname(b) && proj_idx(a) == proj_idx(b) && is_equiv(proj_expr(a), proj_expr(b), use_hash); break;
    case EKind::Lit: r = false; break;   // distinct interned literals
    default: r = false; break;
  }
  if (r) merge(ra, rb);
  return r;
}

int TypeChecker::quick_is_def_eq(Expr t, Expr s, bool use_hash) {
  if (eqv.is_equiv(t, s, use_hash)) return 1;
  if (is_lam(t) && is_lam(s)) return is_def_eq_lambda(t, s) ? 1 : 0;
  if (is_pi(t) && is_pi(s)) return is_def_eq_pi(t, s) ? 1 : 0;
  if (is_sort(t) && is_sort(s)) return is_equivalent(sort_level(t), sort_level(s)) ? 1 : 0;
  if (is_lit(t) && is_lit(s)) return 0;  // distinct interned literals
  return -1;
}

bool TypeChecker::is_def_eq_args(Expr t, Expr s) {
  while (is_app(t) && is_app(s)) {
    if (!is_def_eq(app_arg(t), app_arg(s))) return false;
    t = app_fn(t); s = app_fn(s);
  }
  return !is_app(t) && !is_app(s);
}

bool TypeChecker::is_def_eq_app(Expr t, Expr s) {
  if (!is_app(t) || !is_app(s)) return false;
  if (get_app_num_args(t) != get_app_num_args(s)) return false;
  if (!is_def_eq(get_app_fn(t), get_app_fn(s))) return false;
  return is_def_eq_args(t, s);
}

int TypeChecker::is_def_eq_proof_irrel(Expr t, Expr s) {
  Expr tt = infer_type(t);
  if (!is_prop(tt)) return -1;
  return is_def_eq(tt, infer_type(s)) ? 1 : 0;
}

static bool is_nat_zero_e(Expr e) { return is_const_of(e, N.Nat_zero) || (is_nat_lit(e) && nat_lit_val(e) == 0); }
static Expr nat_succ_of(Expr e) {
  if (is_nat_lit(e) && nat_lit_val(e) > 0) return mk_nat_lit(nat_lit_val(e) - 1);
  if (is_app(e) && is_const_of(app_fn(e), N.Nat_succ)) return app_arg(e);
  return NIL;
}

int TypeChecker::is_def_eq_offset(Expr t, Expr s) {
  if (is_nat_zero_e(t) && is_nat_zero_e(s)) return 1;
  Expr t2 = nat_succ_of(t), s2 = nat_succ_of(s);
  if (t2 != NIL && s2 != NIL) return is_def_eq_core(t2, s2) ? 1 : 0;
  return -1;
}

bool TypeChecker::try_eta_expansion_core(Expr t, Expr s) {
  if (is_lam(t) && !is_lam(s)) {
    Expr st = whnf(infer_type(s));
    if (!is_pi(st)) return false;
    return is_def_eq(t, mk_lam(binding_name(st), binding_dom(st), mk_app(s, mk_bvar(0)), binding_info(st)));
  }
  return false;
}
bool TypeChecker::try_eta_expansion(Expr t, Expr s) { return try_eta_expansion_core(t, s) || try_eta_expansion_core(s, t); }

bool TypeChecker::try_eta_struct_core(Expr t, Expr s) {
  Expr f = get_app_fn(s);
  if (!is_const(f)) return false;
  const ConstInfo* fi = env.find(const_name(f));
  if (!fi || fi->kind != CKind::Ctor) return false;
  if (get_app_num_args(s) != fi->nparams + fi->nfields) return false;
  if (!env.is_structure_like(fi->induct)) return false;
  if (!is_def_eq(infer_type(t), infer_type(s))) return false;
  std::vector<Expr> args; get_app_args(s, args);
  for (size_t i = fi->nparams; i < args.size(); i++)
    if (!is_def_eq(mk_proj(fi->induct, (u32)(i - fi->nparams), t), args[i])) return false;
  return true;
}
bool TypeChecker::try_eta_struct(Expr t, Expr s) { return try_eta_struct_core(t, s) || try_eta_struct_core(s, t); }

int TypeChecker::try_string_lit_expansion_core(Expr t, Expr s) {
  if (!is_str_lit(t)) return -1;
  if (!is_app(s) || !is_const_of(app_fn(s), N.String_ofList)) return -1;
  return is_def_eq_core(str_lit_to_ctor(t), s) ? 1 : 0;
}
int TypeChecker::try_string_lit_expansion(Expr t, Expr s) {
  int r = try_string_lit_expansion_core(t, s);
  if (r != -1) return r;
  return try_string_lit_expansion_core(s, t);
}

bool TypeChecker::is_def_eq_unit_like(Expr t, Expr s) {
  Expr tt = whnf(infer_type(t));
  Expr I = get_app_fn(tt);
  if (!is_const(I)) return false;
  const ConstInfo* ii = env.find(const_name(I));
  if (!ii || ii->kind != CKind::Induct || ii->is_rec || ii->ctors.size() != 1 || ii->nindices != 0) return false;
  const ConstInfo& c = env.get(ii->ctors[0]);
  if (c.nfields != 0) return false;
  return is_def_eq_core(tt, infer_type(s));
}

// Kernel `compare(reducibility_hints)` (declaration.cpp): negative means "unfold the left side
// first": a regular definition of greater height, an abbreviation against a non-abbreviation, or
// anything against an opaque hint.
static int hint_compare(const ConstInfo& a, const ConstInfo& b) {
  if (a.hint == b.hint) {
    if (a.hint == HintKind::Regular) return a.height == b.height ? 0 : (a.height > b.height ? -1 : 1);
    return 0;
  }
  if (a.hint == HintKind::Opaque) return 1;
  if (b.hint == HintKind::Opaque) return -1;
  if (a.hint == HintKind::Abbrev) return -1;
  return 1;  // b is an abbreviation
}

TypeChecker::RStatus TypeChecker::lazy_delta_reduction_step(Expr& tn, Expr& sn) {
  Expr tf = get_app_fn(tn), sf = get_app_fn(sn);
  const ConstInfo* dt = nullptr; const ConstInfo* ds = nullptr;
  if (is_const(tf)) { const ConstInfo* c = env.find(const_name(tf)); if (c && c->is_delta() && g_levels->list(const_levels(tf)).size() == c->lparams.size()) dt = c; }
  if (is_const(sf)) { const ConstInfo* c = env.find(const_name(sf)); if (c && c->is_delta() && g_levels->list(const_levels(sf)).size() == c->lparams.size()) ds = c; }
  auto delta = [&](Expr e) { bool ok; Expr u = unfold_definition(e, ok); return whnf_core(u, true); };
  static long lazy_trace = getenv("LL_TRACE_LAZY") ? atol(getenv("LL_TRACE_LAZY")) : 0;   // print every n-th step's heads
  if (lazy_trace) {
    static long n = 0;
    if (++n % lazy_trace == 0) {
      std::cerr << "[lazy " << n << "] " << (dt ? name_str(dt->name) + "/" + std::to_string(dt->height) : is_const(tf) ? name_str(const_name(tf)) : std::string("?")) << " (" << get_app_num_args(tn) << " args)  vs  "
                << (ds ? name_str(ds->name) + "/" + std::to_string(ds->height) : is_const(sf) ? name_str(const_name(sf)) : std::string("?")) << " (" << get_app_num_args(sn) << " args)  depth " << depth << "\n";
    }
  }
  if (g_trace_nat && ((dt && (dt->name == N.Nat_sub || dt->name == N.Nat_add)) || (ds && (ds->name == N.Nat_sub || ds->name == N.Nat_add)))) {
    std::string a = expr_str(tn), b = expr_str(sn); if (a.size() > 700) a = a.substr(0, 700) + "..."; if (b.size() > 700) b = b.substr(0, 700) + "...";
    std::cerr << "[lazy-delta] t=" << a << "\n             s=" << b << "\n             hints: " << (dt ? (int)dt->hint : -1) << "/" << (dt ? dt->height : 0) << " vs " << (ds ? (int)ds->hint : -1) << "/" << (ds ? ds->height : 0) << "\n";
  }
  auto try_unfold_proj_app = [&](Expr e, Expr& out) {
    if (!is_proj(get_app_fn(e))) return false;
    Expr e2 = whnf_core(e);
    if (e2 == e) return false;
    out = e2; return true;
  };
  auto cont = [&](Expr t2, Expr s2) {
    tn = t2; sn = s2;
    int q = quick_is_def_eq(tn, sn);
    if (q == 1) return RStatus::True;
    if (q == 0) return RStatus::False;
    return RStatus::Continue;
  };
  if (!dt && !ds) return RStatus::Unknown;
  if (dt && !ds) {
    Expr s2;
    if (try_unfold_proj_app(sn, s2)) return cont(tn, s2);
    return cont(delta(tn), sn);
  }
  if (!dt && ds) {
    Expr t2;
    if (try_unfold_proj_app(tn, t2)) return cont(t2, sn);
    return cont(tn, delta(sn));
  }
  int cmp = hint_compare(*dt, *ds);
  if (cmp < 0) return cont(delta(tn), sn);
  if (cmp > 0) return cont(tn, delta(sn));
  if (is_app(tn) && is_app(sn) && dt == ds && dt->hint == HintKind::Regular && !defeq_fail.count(pair_key(tn, sn))) {
    if (is_equiv_list(const_levels(tf), const_levels(sf)) && is_def_eq_args(tn, sn)) return RStatus::True;
    defeq_fail.insert(pair_key(tn, sn));
  }
  return cont(delta(tn), delta(sn));
}

TypeChecker::RStatus TypeChecker::lazy_delta_reduction(Expr& tn, Expr& sn) {
  for (unsigned fuel = 0;; fuel++) {
    if (fuel > 100000000) fail("(kernel) deterministic timeout in lazy delta");
    int r = is_def_eq_offset(tn, sn);
    if (r != -1) return r == 1 ? RStatus::True : RStatus::False;
    // A closed Nat primitive application is computed on its own side (the other side may well
    // mention free variables: `ring` proofs compare literal arithmetic against open terms, and
    // unfolding `Nat.add` on a literal instead recurses unary through millions of successors).
    if (!has_fvar(tn) || eager) {
      bool ok; Expr t2 = reduce_nat(tn, ok);
      if (ok) { tn = t2; return is_def_eq_core(tn, sn) ? RStatus::True : RStatus::False; }
    }
    if (!has_fvar(sn) || eager) {
      bool ok; Expr s2 = reduce_nat(sn, ok);
      if (ok) { sn = s2; return is_def_eq_core(tn, sn) ? RStatus::True : RStatus::False; }
    }
    RStatus st = lazy_delta_reduction_step(tn, sn);
    if (st != RStatus::Continue) return st;
  }
}

bool TypeChecker::lazy_delta_proj_reduction(Name sname, Expr t, Expr s, u32 idx) {
  Expr tn = t, sn = s;
  for (unsigned fuel = 0;; fuel++) {
    if (fuel > 100000000) fail("(kernel) deterministic timeout");
    RStatus st = lazy_delta_reduction_step(tn, sn);
    if (st == RStatus::Continue) continue;
    if (st == RStatus::True) return true;
    bool ok1, ok2;
    Expr tf = reduce_proj_core(sname, idx, tn, ok1);
    if (ok1) { Expr sf = reduce_proj_core(sname, idx, sn, ok2); if (ok2) return is_def_eq_core(tf, sf); }
    return is_def_eq_core(tn, sn);
  }
}

bool TypeChecker::is_def_eq(Expr t, Expr s) {
  bool r = is_def_eq_core(t, s);
  if (r) eqv.merge(t, s);
  else if (getenv("LL_COUNT_REPEATS")) g_defeq_failed_pairs.insert(pair_key(t, s));
  return r;
}

bool TypeChecker::is_def_eq_core(Expr t, Expr s) {
  DepthGuard g(*this, "defeq", t); DepthGuard g2(*this, "defeq-rhs", s);
  g_cnt_defeq++;
  if (g_fuse && t != s) { t = fuse_term(env, fuse_cache, t); s = fuse_term(env, fuse_cache, s); }
  // A pair found not convertible stays so within a declaration (fixed environment, fixed free
  // variables), so a failed comparison is not repeated; on some Mathlib declarations the same
  // failing pairs were otherwise compared millions of times.
  if (t != s && defeq_neg.count(pair_key(t, s))) return false;
  u64 before = g_cnt_defeq + g_cnt_whnf + g_cnt_whnfcore;
  bool res = is_def_eq_core_go(t, s);
  // only comparisons that did some work are worth remembering (cheap structural failures are
  // cheaper to redo than to look up)
  if (!res && g_cnt_defeq + g_cnt_whnf + g_cnt_whnfcore - before > 8) defeq_neg.insert(pair_key(t, s));
  return res;
}
bool TypeChecker::is_def_eq_core_go(Expr t, Expr s) {
  static bool count_repeats = getenv("LL_COUNT_REPEATS");
  if (count_repeats) { if (!g_defeq_pairs_seen.insert(pair_key(t, s)).second) g_cnt_defeq_repeat++; if (g_defeq_failed_pairs.count(pair_key(t, s))) g_cnt_defeq_refail++; }
  int q = quick_is_def_eq(t, s, true);
  if (q != -1) { g_cnt_defeq_quick++; return q == 1; }
  if ((!has_fvar(t) || eager) && is_const_of(s, N.Bool_true)) {
    if (is_const_of(whnf(t), N.Bool_true)) return true;
  }
  Expr tn = whnf_core(t, true), sn = whnf_core(s, true);
  if (!(tn == t && sn == s)) {
    q = quick_is_def_eq(tn, sn);
    if (q != -1) return q == 1;
  }
  q = is_def_eq_proof_irrel(tn, sn);
  if (q != -1) { g_cnt_pi++; return q == 1; }
  g_cnt_lazy++;
  RStatus st = lazy_delta_reduction(tn, sn);
  if (st == RStatus::True) return true;
  if (st == RStatus::False) return false;
  if (is_const(tn) && is_const(sn) && const_name(tn) == const_name(sn) && is_equiv_list(const_levels(tn), const_levels(sn))) return true;
  if (is_fvar(tn) && is_fvar(sn) && tn == sn) return true;
  if (is_proj(tn) && is_proj(sn) && proj_idx(tn) == proj_idx(sn) && proj_sname(tn) == proj_sname(sn)) {
    if (lazy_delta_proj_reduction(proj_sname(tn), proj_expr(tn), proj_expr(sn), proj_idx(tn))) return true;
  }
  Expr tnn = whnf_core(tn), snn = whnf_core(sn);
  if (!(tnn == tn && snn == sn)) return is_def_eq_core(tnn, snn);
  if (is_def_eq_app(tn, sn)) return true;
  if (try_eta_expansion(tn, sn)) return true;
  if (try_eta_struct(tn, sn)) return true;
  q = try_string_lit_expansion(tn, sn);
  if (q != -1) return q == 1;
  if (is_def_eq_unit_like(tn, sn)) return true;
  return false;
}

// ---------------------------------------------------------------- declarations

void check_dup_lparams(const std::vector<Name>& ps) {
  for (size_t i = 0; i < ps.size(); i++) for (size_t j = i + 1; j < ps.size(); j++)
    if (ps[i] == ps[j]) fail("duplicate universe level parameter '" + name_str(ps[i]) + "'");
}

static void check_const_val(TypeChecker& tc, const ConstInfo& c) {
  check_dup_lparams(c.lparams);
  if (has_fvar(c.type)) fail("declaration type has free variables");
  Expr s = tc.check_type(c.type);
  tc.ensure_sort(s, c.type);
}

void check_and_add(Environment& env, const Decl& d, bool trust_inductives, CheckStats& st) {
  // Terms handed to the checker are closed (locally nameless): a loose bound variable is a
  // malformed declaration, as in the kernel ("type checker does not support loose bound variables").
  for (const ConstInfo& c : d.consts) {
    if (d.kind == Decl::Quot) break;   // quotient constants are defined by the kernel, the export's terms are not used
    if (has_loose_bvars(c.type) || (c.value != NIL && has_loose_bvars(c.value))) fail("declaration '" + name_str(c.name) + "' has loose bound variables");
    for (const RecRule& r : c.rules) if (has_loose_bvars(r.rhs)) fail("recursor rule of '" + name_str(c.name) + "' has loose bound variables");
  }
  switch (d.kind) {
    case Decl::Quot: add_quot_decl(env, d); return;
    case Decl::Inductive: add_inductive_decl(env, d, trust_inductives); return;
    default: break;
  }
  const ConstInfo& c = d.consts[0];
  if (env.contains(c.name)) fail("constant already declared: " + name_str(c.name));
  Safety sf = c.is_unsafe ? Safety::Unsafe : (c.kind == CKind::Def ? c.safety : Safety::Safe);
  if (d.kind == Decl::Axiom) {
    TypeChecker tc(env, c.lparams, sf);
    check_const_val(tc, c);
    st.steps += tc.steps;
    env.add(c); return;
  }
  if (d.kind == Decl::Def && c.safety != Safety::Safe) {
    // unsafe/partial: header first, add, then body (may be recursive)
    { TypeChecker tc(env, c.lparams, c.safety); check_const_val(tc, c); st.steps += tc.steps; }
    ConstInfo ax = c; ax.kind = CKind::Axiom; ax.is_unsafe = true; ax.value = NIL;
    size_t m = env.mark();
    env.add(ax);
    try {
      TypeChecker tc(env, c.lparams, c.safety);
      Expr vt = tc.check_type(c.value);
      if (!tc.is_def_eq(vt, c.type)) fail("declaration type mismatch for '" + name_str(c.name) + "'");
      st.steps += tc.steps;
    } catch (...) { env.rollback(m); throw; }
    env.rollback(m);
    env.add(c); return;
  }
  TypeChecker tc(env, c.lparams, sf);
  check_const_val(tc, c);
  if (d.kind == Decl::Thm && !tc.is_prop(c.type)) fail("theorem type is not a proposition: " + name_str(c.name));
  if (has_fvar(c.value)) fail("declaration value has free variables");
  Expr vt = tc.check_type(c.value);
  if (!tc.is_def_eq(vt, c.type))
    fail("declaration type mismatch for '" + name_str(c.name) + "'\n  inferred: " + expr_str(vt) + "\n  declared: " + expr_str(c.type));
  st.steps += tc.steps;
  env.add(c);
}

} // namespace ll
