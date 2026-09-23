#include "fix.h"
#include "fuse.h"
#include "tc.h"
#include "level.h"
#include <iostream>
#include <unordered_map>
#include <deque>
#include <cstdlib>

namespace ll {

int g_fix = getenv("LL_FIX") ? atoi(getenv("LL_FIX")) : 1;
u64 g_fix_derived = 0, g_fix_rejected = 0, g_fix_applied = 0;
static const char* g_fix_trace = getenv("LL_FIX_TRACE");

namespace {

// Rules by definition name.  state: 0 unknown, 1 being derived / none, 2 rule in the temporary
// tier (this declaration), 3 permanent rule, 4 no rule (final).
struct Slot { u8 state = 0; Name name = 0; FixRule rule; };
std::deque<Slot> g_slots;
std::unordered_map<Name, u32> g_slot_of;   // (a ConstInfo caches its slot index in fix_idx; the map serves re-added constants)
Slot& slot_for(const ConstInfo& c) {
  if (c.fix_idx >= 0) return g_slots[c.fix_idx];
  auto it = g_slot_of.find(c.name);
  if (it == g_slot_of.end()) { g_slots.emplace_back(); g_slots.back().name = c.name; it = g_slot_of.emplace(c.name, (u32)g_slots.size() - 1).first; }
  c.fix_idx = (int)it->second;
  return g_slots[it->second];
}
std::vector<Name> g_pending;   // slots in state 2
unsigned g_deriving = 0;

// ---- promotion of expressions to the permanent tier across a reclaim -------------------------
struct Saved {
  struct N { EKind k; Name name = 0; u32 a = 0, b = 0, c = 0; LevelList lvls = 0; BInfo bi = BInfo::Default; };
  std::vector<N> nodes; std::vector<mpz_class> nats; std::vector<std::string> strs;
  std::unordered_map<Expr, u32> memo;
  u32 save(Expr e) {
    auto it = memo.find(e); if (it != memo.end()) return it->second;
    N n; n.k = kind(e);
    switch (n.k) {
      case EKind::BVar: n.a = bvar_idx(e); break;
      case EKind::FVar: fail("fix rule: free variable in a promoted term");
      case EKind::Sort: n.a = sort_level(e); break;
      case EKind::Const: n.name = const_name(e); n.lvls = const_levels(e); break;
      case EKind::App: n.a = save(app_fn(e)); n.b = save(app_arg(e)); break;
      case EKind::Lam: case EKind::Pi: n.name = binding_name(e); n.bi = binding_info(e); n.a = save(binding_dom(e)); n.b = save(binding_body(e)); break;
      case EKind::Let: n.name = ex(e).name; n.a = save(let_type(e)); n.b = save(let_val(e)); n.c = save(let_body(e)); break;
      case EKind::Proj: n.name = proj_sname(e); n.a = proj_idx(e); n.b = save(proj_expr(e)); break;
      case EKind::Lit:
        if (is_nat_lit(e)) { n.a = (u32)nats.size(); nats.push_back(nat_lit_val(e)); n.b = 0; }
        else { n.a = (u32)strs.size(); strs.push_back(str_lit_val(e)); n.b = 1; }
        break;
      default: fail("fix rule: unexpected node kind");
    }
    nodes.push_back(n); u32 i = (u32)nodes.size() - 1; memo.emplace(e, i); return i;
  }
  std::vector<Expr> restore() {
    std::vector<Expr> out(nodes.size());
    for (size_t i = 0; i < nodes.size(); i++) {
      const N& n = nodes[i]; Expr r;
      switch (n.k) {
        case EKind::BVar: r = mk_bvar(n.a); break;
        case EKind::Sort: r = mk_sort(n.a); break;
        case EKind::Const: r = mk_const(n.name, n.lvls); break;
        case EKind::App: r = mk_app(out[n.a], out[n.b]); break;
        case EKind::Lam: r = mk_lam(n.name, out[n.a], out[n.b], n.bi); break;
        case EKind::Pi: r = mk_pi(n.name, out[n.a], out[n.b], n.bi); break;
        case EKind::Let: r = mk_let(n.name, out[n.a], out[n.b], out[n.c]); break;
        case EKind::Proj: r = mk_proj(n.name, n.a, out[n.b]); break;
        case EKind::Lit: r = n.b == 0 ? mk_nat_lit(nats[n.a]) : mk_str_lit(strs[n.a]); break;
        default: fail("fix rule: unexpected node kind");
      }
      out[i] = r;
    }
    return out;
  }
};
Saved* g_saved = nullptr;
std::vector<std::pair<Name, std::vector<u32>>> g_saved_roots;

// ---- derivation ---------------------------------------------------------------------------------

// Is `e` an application `T.rec params motives minors [indices] major`, possibly missing the major?
// Returns the recursor's ConstInfo and the arguments.
const ConstInfo* rec_app(const Environment& env, Expr e, std::vector<Expr>& args, bool& has_major) {
  Expr h = get_app_args_fn(e, args);
  if (!is_const(h)) return nullptr;
  const ConstInfo* r = env.find(const_name(h));
  if (!r || r->kind != CKind::Rec) return nullptr;
  u32 mi = r->rec_major_idx();
  if (args.size() == mi + 1) has_major = true;
  else if (args.size() == mi) has_major = false;
  else return nullptr;
  return r;
}

bool reject(const ConstInfo& c, int where) { if (g_fix_trace) std::cerr << "[fix] " << name_str(c.name) << ": rejected (" << where << ")\n"; return false; }

bool derive(const Environment& env, const ConstInfo& c, FixRule& out) {
  if (c.kind != CKind::Def || c.safety != Safety::Safe || c.value == NIL || c.hint == HintKind::Opaque || is_nat_prim(c.name)) return reject(c, 1);
  FlatMap<Expr> fcache;
  Expr B0 = fuse_term(env, fcache, c.value);
  // lambda prefix x_1 .. x_n
  std::vector<Expr> doms; std::vector<Name> names; std::vector<BInfo> bis;
  Expr B = B0;
  while (is_lam(B)) { doms.push_back(binding_dom(B)); names.push_back(binding_name(B)); bis.push_back(binding_info(B)); B = binding_body(B); }
  size_t n = doms.size();
  // shape:  (T.rec ... x_k).i t_1 .. t_m   |   T.rec ... x_k t_1 .. t_m   |   T.rec ... (major missing)
  // where the t_j are distinct lambda variables other than x_k.
  std::vector<Expr> all; Expr h0 = get_app_args_fn(B, all);
  Expr recterm, head; std::vector<Expr> trailing; std::vector<Expr> rargs; bool has_major = false; const ConstInfo* rec = nullptr;
  if (is_proj(h0)) {
    head = h0; recterm = proj_expr(h0); trailing = all;
    rec = rec_app(env, recterm, rargs, has_major);
    if (!rec || !has_major) return reject(c, 2);
  } else if (is_const(h0)) {
    const ConstInfo* r = env.find(const_name(h0));
    if (!r || r->kind != CKind::Rec) return reject(c, 2);
    size_t mi = r->rec_major_idx();
    if (all.size() >= mi + 1) { has_major = true; rargs.assign(all.begin(), all.begin() + mi + 1); trailing.assign(all.begin() + mi + 1, all.end()); }
    else if (all.size() == mi) { has_major = false; rargs = all; }
    else return reject(c, 2);
    recterm = mk_apps(h0, rargs); head = recterm; rec = r;
  } else return reject(c, 2);
  if (rec->nmotives != 1 || rec->nindices != 0) return reject(c, 3);   // mutual/nested recursion and indexed families: not handled
  size_t k;   // 1-based position of the recursive argument
  std::vector<size_t> tpos;   // positions (1-based) of the trailing variables
  if (has_major) {
    Expr m = rargs.back();
    if (!is_bvar(m)) return reject(c, 4);
    k = n - bvar_idx(m);
    if (k < 1 || k > n) return reject(c, 5);
    // Trailing arguments: lambda variables (distinct, other than the major: the arguments that vary
    // along the recursion) or other terms (typically proofs threaded by a sparse match; the
    // verification decides whether the rule holds for them).
    for (Expr t : trailing) {
      if (!is_bvar(t)) { tpos.push_back(0); continue; }
      size_t pos = n - bvar_idx(t);
      if (pos < 1 || pos > n || pos == k) return reject(c, 6);
      for (size_t q : tpos) if (q == pos) return reject(c, 7);
      tpos.push_back(pos);
    }
  } else {
    if (!trailing.empty()) return reject(c, 8);
    k = n + 1;
  }
  Expr headpart = has_major ? head : recterm;   // the part that stands for `f x⃗_{<k} x_k`
  const ConstInfo* ind = env.find(rec->major_induct);
  if (!ind || ind->kind != CKind::Induct || ind->nparams != rec->nparams) return reject(c, 9);
  // Fresh variables.  Levels are the definition's own parameters.
  std::vector<Level> lvls; for (Name p : c.lparams) lvls.push_back(mk_param(p));
  Expr fconst = mk_const(c.name, g_levels->mk_list(lvls));
  size_t lctx0 = g_lctx.decls.size();
  struct Pop { size_t m; ~Pop() { g_lctx.decls.resize(m); } } pop{lctx0};
  TypeChecker tc(env, c.lparams, Safety::Safe);
  std::vector<Expr> xs;   // x_1 .. x_n (and the eta major for the partial shape)
  Expr ty = c.type;
  size_t total = has_major ? n : n + 1;
  for (size_t i = 0; i < total; i++) {
    ty = tc.whnf(ty);
    if (!is_pi(ty)) return reject(c, 10);
    Expr x = g_lctx.push(binding_name(ty), binding_dom(ty), binding_info(ty));
    xs.push_back(x); ty = instantiate1(binding_body(ty), x);
  }
  // The head part with x_1..x_{k-1} substituted and the major left open: P(l) = headpart[l].
  // Substitute x_i for bvars: under n lambdas, bvar j is x_{n-j}.
  auto subst_all = [&](Expr e, Expr major_val) {
    std::vector<Expr> vals(n);
    for (size_t i = 0; i < n; i++) vals[i] = (i + 1 == k) ? major_val : xs[i];
    return instantiate_rev(e, n, vals.data());   // instantiate_rev: bvar 0 = vals[n-1]
  };
  if (has_major) {
    // the trailing arguments must not occur in the head part (else f x⃗_{<k} l is not its eta form)
    std::vector<Expr> probe(n), probe2(n);
    auto is_trailing = [&](size_t i) { for (size_t q : tpos) if (q && q == i + 1) return true; return false; };
    for (size_t i = 0; i < n; i++) { probe[i] = is_trailing(i) ? mk_const(N.Nat) : xs[i]; probe2[i] = is_trailing(i) ? mk_const(N.Bool) : xs[i]; }
    if (instantiate_rev(headpart, n, probe.data()) != instantiate_rev(headpart, n, probe2.data())) return reject(c, 11);
  }
  out.induct = ind->name; out.major = (u32)(k - 1); out.nparams = ind->nparams; out.arms.clear();
  Expr f_prefix = mk_apps(fconst, std::vector<Expr>(xs.begin(), xs.begin() + (k - 1)));
  for (Name ctor_name : ind->ctors) {
    const ConstInfo& ctor = env.get(ctor_name);
    size_t lctx1 = g_lctx.decls.size();
    // fields: the constructor type at the inductive levels and parameters of the major argument
    Expr majty = tc.whnf(g_lctx.get(xs[k - 1]).type);
    Expr I = get_app_fn(majty);
    if (!is_const_of(I, ind->name)) return reject(c, 12);
    Expr cty = instantiate_lparams(ctor.type, ctor.lparams, g_levels->list(const_levels(I)));
    std::vector<Expr> iargs; get_app_args(majty, iargs);
    if (iargs.size() != ind->nparams) return reject(c, 13);
    for (u32 i = 0; i < ctor.nparams; i++) { cty = tc.whnf(cty); if (!is_pi(cty)) return reject(c, 14); cty = instantiate1(binding_body(cty), iargs[i]); }
    std::vector<Expr> fields;
    for (u32 i = 0; i < ctor.nfields; i++) {
      cty = tc.whnf(cty); if (!is_pi(cty)) return reject(c, 15);
      Expr fv = g_lctx.push(binding_name(cty), binding_dom(cty), binding_info(cty));
      fields.push_back(fv); cty = instantiate1(binding_body(cty), fv);
    }
    Expr ctor_app = mk_apps(mk_apps(mk_const(ctor_name, const_levels(I)), iargs), fields);
    // the unfolding on this constructor, reduced at the head and canonicalised
    Expr B_inst;
    if (has_major) B_inst = subst_all(B, ctor_app);
    else { std::vector<Expr> vals(n); for (size_t i = 0; i < n; i++) vals[i] = xs[i]; B_inst = mk_app(instantiate_rev(B, n, vals.data()), ctor_app); }
    Expr R = tc.whnf_core(B_inst);
    R = fuse_term(env, tc.fuse_cache, R);
    // recursive calls: the pattern P(l) for every field l of the inductive type
    std::vector<std::pair<Expr, Expr>> pats;
    for (Expr fv : fields) {
      Expr fty = tc.whnf(g_lctx.get(fv).type);
      if (!is_const_of(get_app_fn(fty), ind->name)) continue;
      Expr P;
      if (has_major) P = subst_all(headpart, fv);
      else { std::vector<Expr> vals(n); for (size_t i = 0; i < n; i++) vals[i] = xs[i]; P = mk_app(instantiate_rev(recterm, n, vals.data()), fv); }
      // the recursive call: f x⃗ with x_k := l, abstracted over the trailing variables (the head
      // part is their eta form)
      std::vector<Expr> callargs(xs.begin(), xs.begin() + n);
      if (has_major) callargs[k - 1] = fv; else callargs.push_back(fv);
      std::vector<Expr> ys;
      if (!tpos.empty()) {
        Expr Pty = tc.whnf(tc.infer_type(P));
        for (size_t j = 0; j < tpos.size(); j++) {
          if (!is_pi(Pty)) return reject(c, 17);
          Expr y = g_lctx.push(binding_name(Pty), binding_dom(Pty), binding_info(Pty));
          ys.push_back(y); Pty = tc.whnf(instantiate1(binding_body(Pty), y));
          if (tpos[j]) callargs[tpos[j] - 1] = y;
        }
      }
      Expr call = mk_apps(fconst, callargs);
      pats.push_back({P, ys.empty() ? call : g_lctx.mk_lambda(ys, call)});
    }
    // Replace the patterns by the recursive calls.  A result used more than once is bound by a
    // `let`, so that the machine shares it as the course-of-values table did.
    Expr Rp = R;
    if (!pats.empty()) {
      std::vector<unsigned> occ(pats.size(), 0);
      replace_expr(R, [&](Expr e, u32) -> Expr {
        if (has_fvar(e)) for (size_t i = 0; i < pats.size(); i++) if (e == pats[i].first) { occ[i]++; return e; }
        return NIL;
      });
      std::vector<Expr> lets; std::vector<Expr> letvals;
      std::vector<Expr> repl(pats.size());
      // Every recursive result that occurs is let-bound: the term is a DAG evaluated as a tree,
      // and an occurrence inside a lambda is evaluated once per call of that lambda, so only a
      // binding shares the result the way the table did (a `let` is one thunk, forced at most
      // once and only if used).
      for (size_t i = 0; i < pats.size(); i++) {
        if (occ[i] >= 1) { Expr fv = g_lctx.push(N.anonymous, tc.infer_type(pats[i].second), BInfo::Default, pats[i].second); lets.push_back(fv); repl[i] = fv; }
        else repl[i] = pats[i].second;
      }
      Rp = replace_expr(R, [&](Expr e, u32) -> Expr {
        if (has_fvar(e)) for (size_t i = 0; i < pats.size(); i++) if (e == pats[i].first) return repl[i];
        return NIL;
      });
      if (!lets.empty()) Rp = g_lctx.mk_lambda(lets, Rp);   // let-bound fvars become `let` binders
    }
    // verify
    Expr lhs = mk_apps(mk_app(f_prefix, ctor_app), std::vector<Expr>(xs.begin() + std::min(xs.size(), k), xs.end()));
    bool ok = false;
    // (R already has the trailing arguments applied: B is the head part applied to them)
    try { ok = tc.is_def_eq(lhs, Rp); } catch (KernelError&) { ok = false; }
    if (!ok) { g_lctx.decls.resize(lctx1); if (g_fix_trace) std::cerr << "[fix] " << name_str(c.name) << ": arm " << name_str(ctor_name) << " not verified\n"; return reject(c, 16); }
    // abstract over x_1..x_{k-1}, fields, x_{k+1}..x_n
    std::vector<Expr> binders(xs.begin(), xs.begin() + (k - 1));
    binders.insert(binders.end(), fields.begin(), fields.end());
    Expr body = Rp;
    if (has_major) {
      std::vector<Expr> tail(xs.begin() + k, xs.end());
      body = g_lctx.mk_lambda(tail, body);
    }
    // the major's variable may still occur in binder types (e.g. a bound `hfuel : x < fuel`)
    Expr major_fv = xs[k - 1];
    body = replace_expr(body, [&](Expr e, u32) -> Expr { if (e == major_fv) return ctor_app; return has_fvar(e) ? NIL : e; });
    body = abstract_fvars(body, binders.size(), binders.data());
    body = expand_closures(body);
    if (has_fvar(body)) { if (g_fix_trace) std::cerr << "[fix] " << name_str(c.name) << ": free variable left in arm " << name_str(ctor_name) << ": " << expr_str(body).substr(0, 600) << "\n"; g_lctx.decls.resize(lctx1); return reject(c, 18); }
    out.arms.push_back(FixArm{ctor_name, ctor.nfields, body});
    if (g_fix_trace && atoi(g_fix_trace) >= 2) { std::string t = expr_str(out.arms.back().body); std::cerr << "[fix]   arm " << name_str(ctor_name) << " (" << t.size() << " chars): " << t.substr(0, 1500) << "\n"; }
    g_lctx.decls.resize(lctx1);
  }
  return true;
}

} // namespace

static bool skipped(Name n) {
  static const char* sk = getenv("LL_FIX_SKIP");
  if (!sk) return false;
  std::string s = std::string(",") + sk + ",", nm = "," + name_str(n) + ",";
  return s.find(nm) != std::string::npos;
}
const FixRule* fix_rule(const Environment& env, const ConstInfo& c) {
  if (!g_fix) return nullptr;
  if (c.fix_idx < 0 && skipped(c.name)) { slot_for(c).state = 4; return nullptr; }
  // not yet worth a derivation and its verification: unfold the definition as usual
  if (unfold_count(c.name) < g_fix_min && slot_for(c).state == 0) return nullptr;
  Slot& s = slot_for(c);
  if (s.state == 2 || s.state == 3) return &s.rule;
  if (s.state != 0) return nullptr;
  if (g_deriving >= 8) return nullptr;   // leave unknown; try again from a shallower context
  s.state = 1;
  if (g_fix_trace) std::cerr << "[fix] deriving " << name_str(c.name) << "\n";
  g_deriving++;
  bool ok = false;
  try { ok = derive(env, c, s.rule); } catch (KernelError& e) { if (g_fix_trace) std::cerr << "[fix] " << name_str(c.name) << ": " << e.what() << "\n"; ok = false; }
  g_deriving--;
  Slot& s2 = s;   // (deque: stable)
  if (ok) { s2.state = 2; g_pending.push_back(c.name); g_fix_derived++; if (g_fix_trace) std::cerr << "[fix] " << name_str(c.name) << ": rule with " << s2.rule.arms.size() << " arms, major " << s2.rule.major << "\n"; return &s2.rule; }
  s2.state = 4; g_fix_rejected++; s2.rule = FixRule();
  return nullptr;
}

void fix_before_reclaim() {
  if (g_pending.empty()) return;
  g_saved = new Saved();
  g_saved_roots.clear();
  for (Name nm : g_pending) {
    Slot& s = g_slots[g_slot_of[nm]];
    std::vector<u32> roots;
    for (auto& a : s.rule.arms) roots.push_back(g_saved->save(a.body));
    g_saved_roots.push_back({nm, roots});
  }
}

void fix_after_reclaim() {
  if (!g_saved) { g_pending.clear(); return; }
  bool was = g_exprs->frozen;
  g_exprs->frozen = false;
  std::vector<Expr> out = g_saved->restore();
  if (was) g_exprs->freeze();
  for (auto& [nm, roots] : g_saved_roots) {
    Slot& s = g_slots[g_slot_of[nm]];
    for (size_t i = 0; i < roots.size(); i++) s.rule.arms[i].body = out[roots[i]];
    s.state = 3;
  }
  delete g_saved; g_saved = nullptr; g_saved_roots.clear(); g_pending.clear();
}

} // namespace ll
