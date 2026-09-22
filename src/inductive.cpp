// Inductive types and quotients.
//
// An exported inductive block is re-checked the way the Lean kernel's `add_inductive` does it:
// the types are checked, nested occurrences are eliminated by introducing auxiliary types, the
// constructors are checked (parameters, universes, positivity, result type), and the recursors are
// *derived* (elimination universe, K-target, motives, minors, rules).  The derived recursors,
// restored to the nested form, must be definitionally equal to the exported ones; any recursor the
// export contains that we did not derive is rejected.
#include "tc.h"
#include <iostream>
#include <map>

namespace ll {

bool g_strict_metadata = false;
static void meta_mismatch(const std::string& msg) {
  if (g_strict_metadata) fail(msg);
  static int shown = 0; if (shown++ < 20) std::cerr << "warning: " << msg << "\n";
}

void check_dup_lparams(const std::vector<Name>& ps);

namespace {

struct Ctor { Name name; Expr type; };
struct IndType { Name name; Expr type; std::vector<Ctor> ctors; };

bool occurs_any(const std::vector<Name>& names, Expr e) {
  for (Name n : names) if (occurs_const(e, n)) return true;
  return false;
}

Name replace_prefix(Name n, Name from, Name to) {
  if (n == from) return to;
  if (n == 0) return 0;
  const NameNode nd = (*g_names)[n];
  Name p = replace_prefix(nd.parent, from, to);
  return nd.is_str ? g_names->mk_str(p, nd.str) : g_names->mk_num(p, nd.num);
}

Name append_index_after(Name n, unsigned i) {
  const NameNode nd = (*g_names)[n];
  if (nd.is_str) return g_names->mk_str(nd.parent, nd.str + "_" + std::to_string(i));
  return g_names->mk_num(n, i);
}

// Strip `n` pi binders, instantiating them with `args` (in order).
Expr instantiate_pis(Expr e, size_t n, const std::vector<Expr>& args) {
  for (size_t i = 0; i < n; i++) {
    if (!is_pi(e)) fail("invalid inductive datatype declaration, ill-formed declaration");
    e = binding_body(e);
  }
  return instantiate_rev(e, n, args.data());
}

// ---------------------------------------------------------------- nested elimination

struct NestedElim {
  const Environment& env;
  std::vector<Name> lparams; std::vector<Level> lvls; LevelList lvl_list;
  u32 nparams;
  std::vector<Expr> params;                       // fvars
  std::vector<IndType> types;                     // grows with auxiliaries
  std::vector<std::pair<Expr, Name>> nested_aux;  // (I Ds over params, aux name)
  std::map<Name, std::pair<Expr, Name>> aux2nested; // aux name -> (I Ds over params, aux name)
  std::map<Name, Name> aux_ctor_of;              // aux ctor name -> aux type name
  unsigned next_idx = 1;

  bool is_new_type(Name n) const { for (auto& t : types) if (t.name == n) return true; return false; }
  bool mentions_new_type(Expr e) const { for (auto& t : types) if (occurs_const(e, t.name)) return true; return false; }

  Name unique_name(Name base) {
    while (true) { Name r = append_index_after(base, next_idx++); if (!env.contains(r)) return r; }
  }

  // e over As  ->  e over params
  Expr over_params(Expr e, const std::vector<Expr>& As) {
    return instantiate_rev(abstract_fvars(e, As.size(), As.data()), params.size(), params.data());
  }

  // If `e` is `I Ds is` with `I` an existing inductive whose parameters mention the new types,
  // return `Iaux As is`; otherwise NIL.
  Expr replace_if_nested(Expr e, const std::vector<Expr>& As) {
    if (!is_app(e)) return NIL;
    std::vector<Expr> args;
    Expr fn = get_app_args_fn(e, args);
    if (!is_const(fn)) return NIL;
    const ConstInfo* ci = env.find(const_name(fn));
    if (!ci || ci->kind != CKind::Induct) return NIL;
    if (ci->nparams > args.size()) return NIL;
    bool nested = false, loose = false;
    for (u32 i = 0; i < ci->nparams; i++) {
      if (has_loose_bvars(args[i])) loose = true;
      if (mentions_new_type(args[i])) nested = true;
    }
    if (!nested) return NIL;
    if (loose) fail("invalid nested inductive datatype '" + name_str(ci->name) + "', nested inductive datatypes parameters cannot contain local variables.");
    LevelList I_lvls = const_levels(fn);
    Expr IAs = mk_apps_range(fn, args, 0, ci->nparams);
    Expr key = over_params(IAs, As);
    for (auto& p : nested_aux) if (p.first == key)
      return mk_apps_range(mk_apps(mk_const(p.second, lvl_list), As), args, ci->nparams, args.size());
    Expr result = NIL;
    for (Name J_name : ci->all) {
      const ConstInfo& J = env.get(J_name);
      Expr Jc = mk_const(J_name, I_lvls);
      Expr JAs = mk_apps_range(Jc, args, 0, ci->nparams);
      Name auxJ = unique_name(g_names->mk_str(mk_name("_nested"), name_str(J_name)));
      // auxJ's name is `_nested.J_k` with J's dotted string as one component, as Lean does
      // (`_nested ++ J_name` keeps components; we keep components too):
      auxJ = unique_name_components(J_name);
      Expr auxJ_type = g_lctx.mk_pi(As, instantiate_pis(instantiate_lparams(J.type, J.lparams, g_levels->list(I_lvls)), ci->nparams, args));
      Expr JAs_key = over_params(JAs, As);
      nested_aux.emplace_back(JAs_key, auxJ);
      aux2nested[auxJ] = {JAs_key, auxJ};
      if (J_name == ci->name) result = mk_apps_range(mk_apps(mk_const(auxJ, lvl_list), As), args, ci->nparams, args.size());
      IndType nt; nt.name = auxJ; nt.type = auxJ_type;
      for (Name cn : J.ctors) {
        const ConstInfo& cinfo = env.get(cn);
        Name aux_cn = replace_prefix(cn, J_name, auxJ);
        Expr ct = instantiate_pis(instantiate_lparams(cinfo.type, cinfo.lparams, g_levels->list(I_lvls)), ci->nparams, args);
        nt.ctors.push_back(Ctor{aux_cn, g_lctx.mk_pi(As, ct)});
        aux_ctor_of[aux_cn] = auxJ;
      }
      types.push_back(nt);
    }
    if (result == NIL) fail("nested inductive elimination failed");
    return result;
  }

  // `_nested` ++ J_name (component-wise), made unique with an index suffix
  Name unique_name_components(Name J_name) {
    Name base = mk_name("_nested");
    std::vector<Name> comps; for (Name x = J_name; x != 0; x = (*g_names)[x].parent) comps.push_back(x);
    for (size_t i = comps.size(); i-- > 0;) {
      const NameNode nd = (*g_names)[comps[i]];
      base = nd.is_str ? g_names->mk_str(base, nd.str) : g_names->mk_num(base, nd.num);
    }
    return unique_name(base);
  }

  Expr replace_all_nested(Expr e, const std::vector<Expr>& As) {
    return replace_expr(e, [&](Expr x, u32) -> Expr { return replace_if_nested(x, As); });
  }

  void run() {
    for (size_t i = 0; i < types.size(); i++) {
      for (size_t k = 0; k < types[i].ctors.size(); k++) {
        Expr t = types[i].ctors[k].type;
        std::vector<Expr> As;
        for (u32 p = 0; p < nparams; p++) {
          if (!is_pi(t)) fail("invalid inductive datatype declaration, incorrect number of parameters");
          Expr fv = g_lctx.push(binding_name(t), instantiate_rev(binding_dom(t), As.size(), As.data()), binding_info(t));
          As.push_back(fv); t = binding_body(t);
        }
        t = instantiate_rev(t, As.size(), As.data());
        types[i].ctors[k].type = g_lctx.mk_pi(As, replace_all_nested(t, As));
      }
    }
  }

  // Restore: aux types -> nested applications, aux ctors -> real ctors, aux recs -> renamed recs.
  Expr restore(Expr e, const std::map<Name, Name>& aux_rec) {
    if (nested_aux.empty() && aux_rec.empty()) return e;
    bool pi = is_pi(e);
    std::vector<Expr> As;
    Expr t = e;
    for (u32 p = 0; p < nparams; p++) {
      if (!is_pi(t) && !is_lam(t)) fail("restore_nested: ill-formed");
      Expr fv = g_lctx.push(binding_name(t), instantiate_rev(binding_dom(t), As.size(), As.data()), binding_info(t));
      As.push_back(fv); t = binding_body(t);
    }
    t = instantiate_rev(t, As.size(), As.data());
    t = replace_expr(t, [&](Expr x, u32) -> Expr {
      if (is_const(x)) {
        auto it = aux_rec.find(const_name(x));
        if (it != aux_rec.end()) return mk_const(it->second, const_levels(x));
      }
      Expr fn = get_app_fn(x);
      if (!is_const(fn)) return NIL;
      Name c = const_name(fn);
      auto it = aux2nested.find(c);
      if (it != aux2nested.end()) {
        std::vector<Expr> args; get_app_args(x, args);
        if (args.size() < nparams) fail("restore_nested: under-applied auxiliary type");
        for (auto& a : args) a = restore_inner(a, aux_rec);
        Expr nested = instantiate_rev(abstract_fvars(it->second.first, params.size(), params.data()), As.size(), As.data());
        return mk_apps_range(nested, args, nparams, args.size());
      }
      auto ic = aux_ctor_of.find(c);
      if (ic != aux_ctor_of.end()) {
        std::vector<Expr> args; get_app_args(x, args);
        if (args.size() < nparams) fail("restore_nested: under-applied auxiliary constructor");
        for (auto& a : args) a = restore_inner(a, aux_rec);
        Expr nested = instantiate_rev(abstract_fvars(aux2nested[ic->second].first, params.size(), params.data()), As.size(), As.data());
        std::vector<Expr> I_args; Expr I = get_app_args_fn(nested, I_args);
        Expr cc = mk_const(replace_prefix(c, ic->second, const_name(I)), const_levels(I));
        return mk_apps_range(mk_apps(cc, I_args), args, nparams, args.size());
      }
      return NIL;
    });
    return pi ? g_lctx.mk_pi(As, t) : g_lctx.mk_lambda(As, t);
  }
  // recursion into arguments during restore (same As in scope: the callback above closes over As)
  Expr restore_inner(Expr a, const std::map<Name, Name>& aux_rec) {
    // arguments are restored by the outer replace_expr traversal order: we call the same logic
    // by re-running replace on the argument with the current As captured through `cur_As`.
    return restore_sub(a, aux_rec);
  }
  std::vector<Expr>* cur_As = nullptr;
  Expr restore_sub(Expr t, const std::map<Name, Name>& aux_rec);
};

Expr NestedElim::restore_sub(Expr t, const std::map<Name, Name>& aux_rec) {
  // Handled by the outer traversal: replace_expr is memoized top-down, so nested aux occurrences
  // inside arguments are reached because we return the rebuilt application and replace_expr
  // does not descend into a replaced node.  Therefore we must descend ourselves.
  return replace_expr(t, [&](Expr x, u32) -> Expr {
    if (is_const(x)) {
      auto it = aux_rec.find(const_name(x));
      if (it != aux_rec.end()) return mk_const(it->second, const_levels(x));
    }
    Expr fn = get_app_fn(x);
    if (!is_const(fn)) return NIL;
    Name c = const_name(fn);
    auto it = aux2nested.find(c);
    auto ic = aux_ctor_of.find(c);
    if (it == aux2nested.end() && ic == aux_ctor_of.end()) return NIL;
    std::vector<Expr> args; get_app_args(x, args);
    if (args.size() < nparams) fail("restore_nested: under-applied auxiliary");
    std::vector<Expr> As(args.begin(), args.begin() + nparams);
    for (auto& a : args) a = restore_sub(a, aux_rec);
    if (it != aux2nested.end()) {
      Expr nested = instantiate_rev(abstract_fvars(it->second.first, params.size(), params.data()), As.size(), As.data());
      return mk_apps_range(nested, args, nparams, args.size());
    }
    Expr nested = instantiate_rev(abstract_fvars(aux2nested[ic->second].first, params.size(), params.data()), As.size(), As.data());
    std::vector<Expr> I_args; Expr I = get_app_args_fn(nested, I_args);
    Expr cc = mk_const(replace_prefix(c, ic->second, const_name(I)), const_levels(I));
    return mk_apps_range(mk_apps(cc, I_args), args, nparams, args.size());
  });
}

// ---------------------------------------------------------------- the block checker

struct RecInfo { Expr motive; std::vector<Expr> minors; std::vector<Expr> indices; Expr major; };

struct AddInductive {
  Environment& env;      // working environment (types added; rolled back by caller)
  const std::vector<Name>& lparams;
  std::vector<Level> lvls; LevelList lvl_list;
  u32 nparams;
  std::vector<Expr> params;
  std::vector<IndType>& types;
  Safety sf;
  bool is_unsafe;
  Level result_level = LZERO; bool is_not_zero = false;
  std::vector<u32> nindices;
  std::vector<Expr> ind_consts;
  std::vector<Name> ind_names;

  TypeChecker tc;
  AddInductive(Environment& e, const std::vector<Name>& lps, u32 np, std::vector<Expr> ps, std::vector<IndType>& ts, Safety s)
    : env(e), lparams(lps), nparams(np), params(std::move(ps)), types(ts), sf(s), is_unsafe(s == Safety::Unsafe), tc(e, lps, s) {
    for (Name p : lparams) lvls.push_back(mk_param(p));
    lvl_list = g_levels->mk_list(lvls);
    for (auto& t : types) { ind_names.push_back(t.name); ind_consts.push_back(mk_const(t.name, lvl_list)); }
  }

  bool has_ind_occ(Expr e) const { return occurs_any(ind_names, e); }

  int valid_ind_app(Expr t) const {
    std::vector<Expr> args;
    Expr I = get_app_args_fn(t, args);
    if (!is_const(I)) return -1;
    for (size_t i = 0; i < types.size(); i++) {
      if (I != ind_consts[i]) continue;
      if (args.size() != nparams + nindices[i]) return -1;
      for (size_t k = 0; k < nparams; k++) if (args[k] != params[k]) return -1;
      for (size_t k = nparams; k < args.size(); k++) if (has_ind_occ(args[k])) return -1;
      return (int)i;
    }
    return -1;
  }

  // Computes result level, indices; the types must already be in env.
  void check_types() {
    for (size_t i = 0; i < types.size(); i++) {
      Expr t = tc.whnf(types[i].type);
      u32 nidx = 0;
      for (u32 p = 0; p < nparams; p++) {
        if (!is_pi(t)) fail("number of parameters mismatch in inductive datatype declaration");
        if (i == 0) { /* params already opened by caller with these binders */ }
        else if (!tc.is_def_eq(binding_dom(t), g_lctx.get(params[p]).type)) fail("parameters of all inductive datatypes must match");
        t = tc.whnf(instantiate1(binding_body(t), params[p]));
      }
      while (is_pi(t)) { Expr fv = g_lctx.push(binding_name(t), binding_dom(t), binding_info(t)); t = tc.whnf(instantiate1(binding_body(t), fv)); nidx++; }
      Level rl = sort_level(tc.ensure_sort(t, t));
      if (i == 0) { result_level = rl; is_not_zero = is_never_zero(rl); }
      else if (!is_equivalent(rl, result_level)) fail("mutually inductive types must live in the same universe");
      nindices.push_back(nidx);
    }
  }

  void check_positivity(Expr t, Name ctor, unsigned idx) {
    for (unsigned fuel = 0; fuel < 100000; fuel++) {
      t = tc.whnf(t);
      if (!has_ind_occ(t)) return;
      if (is_pi(t)) {
        if (has_ind_occ(binding_dom(t)))
          fail("arg #" + std::to_string(idx + 1) + " of '" + name_str(ctor) + "' has a non positive occurrence of the datatypes being declared");
        Expr fv = g_lctx.push(binding_name(t), binding_dom(t), binding_info(t));
        t = instantiate1(binding_body(t), fv);
      } else {
        if (valid_ind_app(t) < 0)
          fail("arg #" + std::to_string(idx + 1) + " of '" + name_str(ctor) + "' has a non valid occurrence of the datatypes being declared");
        return;
      }
    }
    fail("deep recursion in positivity check");
  }

  void check_ctors() {
    for (size_t i = 0; i < types.size(); i++) {
      std::vector<Name> seen;
      for (auto& c : types[i].ctors) {
        for (Name s : seen) if (s == c.name) fail("duplicate constructor name '" + name_str(c.name) + "'");
        seen.push_back(c.name);
        if (has_fvar(c.type)) fail("constructor type has free variables");
        tc.ensure_sort(tc.check_type(c.type), c.type);
        Expr t = c.type; unsigned k = 0;
        while (is_pi(t)) {
          if (k < nparams) {
            if (!tc.is_def_eq(binding_dom(t), g_lctx.get(params[k]).type))
              fail("arg #" + std::to_string(k + 1) + " of '" + name_str(c.name) + "' does not match inductive datatype parameters");
            t = instantiate1(binding_body(t), params[k]);
          } else {
            Expr s = tc.ensure_type(binding_dom(t));
            if (!(is_geq(result_level, sort_level(s)) || is_always_zero(result_level)))
              fail("universe level of type_of(arg #" + std::to_string(k + 1) + ") of '" + name_str(c.name) + "' is too big for the corresponding inductive datatype");
            if (!is_unsafe) check_positivity(binding_dom(t), c.name, k);
            Expr fv = g_lctx.push(binding_name(t), binding_dom(t), binding_info(t));
            t = instantiate1(binding_body(t), fv);
          }
          k++;
        }
        if (k < nparams) fail("constructor '" + name_str(c.name) + "' has too few parameters");
        if (valid_ind_app(t) != (int)i) fail("invalid return type for '" + name_str(c.name) + "'");
      }
    }
  }

  bool is_rec_flag() const {
    for (auto& t : types) for (auto& c : t.ctors) { Expr x = c.type; while (is_pi(x)) { if (has_ind_occ(binding_dom(x))) return true; x = binding_body(x); } }
    return false;
  }
  bool is_reflexive_flag() const {
    for (auto& t : types) for (auto& c : t.ctors) { Expr x = c.type; while (is_pi(x)) { if (is_pi(binding_dom(x)) && has_ind_occ(binding_dom(x))) return true; x = binding_body(x); } }
    return false;
  }

  bool large_eliminator() {
    if (is_not_zero) return true;
    if (types.size() != 1) return false;
    if (types[0].ctors.empty()) return true;
    if (types[0].ctors.size() > 1) return false;
    Expr t = types[0].ctors[0].type;
    std::vector<Expr> to_check; unsigned i = 0;
    while (is_pi(t)) {
      Expr fv = g_lctx.push(binding_name(t), binding_dom(t), binding_info(t));
      if (i >= nparams && !is_always_zero(sort_level(tc.ensure_type(binding_dom(t))))) to_check.push_back(fv);
      t = instantiate1(binding_body(t), fv); i++;
    }
    std::vector<Expr> args; get_app_args(t, args);
    for (Expr x : to_check) { bool found = false; for (Expr a : args) if (a == x) found = true; if (!found) return false; }
    return true;
  }

  bool k_target() {
    if (types.size() != 1 || !is_always_zero(result_level) || types[0].ctors.size() != 1) return false;
    Expr t = types[0].ctors[0].type; unsigned i = 0;
    while (is_pi(t)) { if (i >= nparams) return false; t = binding_body(t); i++; }
    return true;
  }

  // is the field type (after whnf through pis) a valid app of one of the block's types?
  int rec_arg_type(Expr t, std::vector<Expr>* xs = nullptr, Expr* head = nullptr) {
    for (unsigned fuel = 0; fuel < 100000; fuel++) {
      t = tc.whnf(t);
      if (!is_pi(t)) { if (head) *head = t; return valid_ind_app(t); }
      Expr fv = g_lctx.push(binding_name(t), binding_dom(t), binding_info(t));
      if (xs) xs->push_back(fv);
      t = instantiate1(binding_body(t), fv);
    }
    fail("deep recursion");
  }

  std::vector<RecInfo> recs;
  std::vector<Expr> motives, minors;
  Level elim_level;

  void mk_rec_infos(Name elim_param_name) {
    elim_level = large_eliminator() ? (elim_param_name == NIL ? LZERO : mk_param(elim_param_name)) : LZERO;
    for (size_t d = 0; d < types.size(); d++) {
      RecInfo ri;
      Expr t = tc.whnf(types[d].type);
      unsigned i = 0;
      while (is_pi(t)) {
        if (i < nparams) { t = tc.whnf(instantiate1(binding_body(t), params[i])); i++; }
        else { Expr fv = g_lctx.push(binding_name(t), binding_dom(t), binding_info(t)); ri.indices.push_back(fv); t = tc.whnf(instantiate1(binding_body(t), fv)); }
      }
      Expr tTy = mk_apps(mk_apps(ind_consts[d], params), ri.indices);
      ri.major = g_lctx.push(N.t, tTy, BInfo::Default);
      Expr motiveTy = g_lctx.mk_pi(ri.indices, g_lctx.mk_pi({ri.major}, mk_sort(elim_level)));
      Name mname = types.size() > 1 ? append_index_after(N.motive, (unsigned)d + 1) : N.motive;
      ri.motive = g_lctx.push(mname, motiveTy, BInfo::Default);
      recs.push_back(ri);
    }
    for (size_t d = 0; d < types.size(); d++) motives.push_back(recs[d].motive);
    for (size_t d = 0; d < types.size(); d++) {
      for (auto& c : types[d].ctors) {
        Expr t = c.type; unsigned i = 0;
        std::vector<Expr> bu, u;
        while (is_pi(t)) {
          if (i < nparams) { t = instantiate1(binding_body(t), params[i]); }
          else {
            Expr fv = g_lctx.push(binding_name(t), binding_dom(t), binding_info(t));
            bu.push_back(fv);
            if (rec_arg_type(binding_dom(t)) >= 0) u.push_back(fv);
            t = instantiate1(binding_body(t), fv);
          }
          i++;
        }
        std::vector<Expr> targs; get_app_args(t, targs);
        int it_idx = valid_ind_app(t);
        if (it_idx < 0) fail("invalid return type for '" + name_str(c.name) + "'");
        Expr intro = mk_apps(mk_apps(mk_const(c.name, lvl_list), params), bu);
        Expr motive_app = mk_app(mk_apps_range(recs[it_idx].motive, targs, nparams, targs.size()), intro);
        std::vector<Expr> v;
        for (Expr ui : u) {
          std::vector<Expr> xs; Expr uiTy;
          int j = rec_arg_type(g_lctx.get(ui).type, &xs, &uiTy);
          std::vector<Expr> uargs; get_app_args(uiTy, uargs);
          Expr viTy = g_lctx.mk_pi(xs, mk_app(mk_apps_range(recs[j].motive, uargs, nparams, uargs.size()), mk_apps(ui, xs)));
          const NameNode un = (*g_names)[g_lctx.get(ui).name];
          Name vname = g_names->mk_str(un.parent, un.str + "_ih");
          v.push_back(g_lctx.push(vname, viTy, BInfo::Default));
        }
        Expr minorTy = g_lctx.mk_pi(bu, g_lctx.mk_pi(v, motive_app));
        Name mn = replace_prefix(c.name, types[d].name, 0);
        recs[d].minors.push_back(g_lctx.push(mn, minorTy, BInfo::Default));
      }
    }
    for (size_t d = 0; d < types.size(); d++) for (Expr m : recs[d].minors) minors.push_back(m);
  }

  std::vector<Level> rec_lvls() const {
    std::vector<Level> r; if (is_param(elim_level)) r.push_back(elim_level); for (Level l : lvls) r.push_back(l); return r;
  }
  Expr rec_const(size_t d) const { return mk_const(g_names->mk_str(types[d].name, "rec"), g_levels->mk_list(rec_lvls())); }

  Expr rec_type(size_t d) {
    const RecInfo& ri = recs[d];
    Expr body = mk_app(mk_apps(ri.motive, ri.indices), ri.major);
    Expr r = g_lctx.mk_pi({ri.major}, body);
    r = g_lctx.mk_pi(ri.indices, r);
    r = g_lctx.mk_pi(minors, r);
    r = g_lctx.mk_pi(motives, r);
    return g_lctx.mk_pi(params, r);
  }

  std::vector<RecRule> rec_rules(size_t d, size_t& minor_idx) {
    std::vector<RecRule> rules;
    for (auto& c : types[d].ctors) {
      Expr t = c.type; unsigned i = 0;
      std::vector<Expr> bu, u;
      while (is_pi(t)) {
        if (i < nparams) { t = instantiate1(binding_body(t), params[i]); }
        else {
          Expr fv = g_lctx.push(binding_name(t), binding_dom(t), binding_info(t));
          bu.push_back(fv);
          if (rec_arg_type(binding_dom(t)) >= 0) u.push_back(fv);
          t = instantiate1(binding_body(t), fv);
        }
        i++;
      }
      std::vector<Expr> v;
      for (Expr ui : u) {
        std::vector<Expr> xs; Expr uiTy;
        int j = rec_arg_type(g_lctx.get(ui).type, &xs, &uiTy);
        std::vector<Expr> uargs; get_app_args(uiTy, uargs);
        Expr val = mk_apps(mk_apps(mk_apps(rec_const(j), params), motives), minors);
        val = mk_apps_range(val, uargs, nparams, uargs.size());
        v.push_back(g_lctx.mk_lambda(xs, mk_app(val, mk_apps(ui, xs))));
      }
      Expr rhs = mk_apps(mk_apps(minors[minor_idx], bu), v);
      rhs = g_lctx.mk_lambda(params, g_lctx.mk_lambda(motives, g_lctx.mk_lambda(minors, g_lctx.mk_lambda(bu, rhs))));
      rules.push_back(RecRule{c.name, (u32)bu.size(), rhs});
      minor_idx++;
    }
    return rules;
  }
};

} // namespace

void add_inductive_decl(Environment& env, const Decl& d, bool /*trust*/) {
  for (auto& c : d.consts) if (env.contains(c.name)) fail("constant already declared: " + name_str(c.name));
  bool is_unsafe = d.consts[0].is_unsafe;
  // unsafe-ness is a property of the whole block: types, constructors and recursors must agree
  for (const ConstInfo& c : d.consts) if (c.is_unsafe != is_unsafe) fail("inductive block of '" + name_str(d.consts[0].name) + "': inconsistent isUnsafe flags (" + name_str(c.name) + ")");
  Safety sf = is_unsafe ? Safety::Unsafe : Safety::Safe;
  const std::vector<Name>& lparams = d.consts[0].lparams;
  check_dup_lparams(lparams);
  u32 nparams = d.nparams;
  size_t mark = env.mark();
  try {
    // Reserved prefix check and type checks of the inductive types.
    Name nested_prefix = mk_name("_nested");
    auto has_nested_prefix = [&](Name n) { for (Name x = n; x != 0; x = (*g_names)[x].parent) if (x == nested_prefix) return true; return false; };
    std::vector<IndType> orig;
    {
      TypeChecker tc(env, lparams, sf);
      for (size_t i = 0; i < d.ntypes; i++) {
        const ConstInfo& c = d.consts[i];
        if (c.lparams != lparams) fail("mutually inductive types must have the same universe parameters");
        if (c.nparams != nparams) fail("inconsistent parameter counts in inductive block");
        if (has_fvar(c.type)) fail("inductive type has free variables");
        if (has_nested_prefix(c.name)) fail("invalid declaration '" + name_str(c.name) + "', it uses the reserved prefix '_nested'");
        tc.ensure_sort(tc.check_type(c.type), c.type);
        IndType it; it.name = c.name; it.type = c.type;
        for (Name cn : c.ctors) {
          const ConstInfo* ci = nullptr;
          for (size_t k = d.ntypes; k < d.ntypes + d.nctors; k++) if (d.consts[k].name == cn) ci = &d.consts[k];
          if (!ci) fail("constructor '" + name_str(cn) + "' missing from the export");
          if (ci->induct != c.name || ci->lparams != lparams) fail("constructor '" + name_str(cn) + "' does not belong to '" + name_str(c.name) + "'");
          bool bad = false;
          replace_expr(ci->type, [&](Expr x, u32) -> Expr {
            if (is_const(x) && has_nested_prefix(const_name(x))) bad = true;
            if (is_proj(x) && has_nested_prefix(proj_sname(x))) bad = true;
            return NIL; });
          if (bad) fail("invalid declaration '" + name_str(cn) + "', it uses the reserved prefix '_nested'");
          it.ctors.push_back(Ctor{cn, ci->type});
        }
        orig.push_back(it);
      }
      if (d.nctors != [&]{ size_t n = 0; for (auto& t : orig) n += t.ctors.size(); return n; }()) fail("constructor count mismatch in inductive block");
    }
    // Parameters: fvars opened from the first type.
    std::vector<Expr> params;
    {
      Expr t = orig[0].type;
      for (u32 p = 0; p < nparams; p++) {
        if (!is_pi(t)) fail("invalid inductive datatype declaration, incorrect number of parameters");
        Expr fv = g_lctx.push(binding_name(t), instantiate_rev(binding_dom(t), params.size(), params.data()), binding_info(t));
        params.push_back(fv); t = binding_body(t);
      }
    }
    // Nested elimination.
    NestedElim ne{env, lparams, {}, 0, nparams, params, orig};
    for (Name p : lparams) ne.lvls.push_back(mk_param(p));
    ne.lvl_list = g_levels->mk_list(ne.lvls);
    ne.run();
    size_t nnested = ne.nested_aux.size();
    // Derived metadata (numNested, isRec, isReflexive, numIndices) is recomputed here and only
    // cross-checked against the export: Lean's kernel ignores the exported values too, so a
    // mismatch is reported as a warning rather than a rejection (--strict-metadata makes it one).
    if (d.consts[0].nnested != nnested) meta_mismatch("numNested mismatch for '" + name_str(orig[0].name) + "': export says " + std::to_string(d.consts[0].nnested) + ", derived " + std::to_string(nnested));
    // Declare all (including auxiliary) types, then check constructors.
    std::vector<Name> all_names; for (auto& t : ne.types) all_names.push_back(t.name);
    for (auto& t : ne.types) {
      ConstInfo c; c.kind = CKind::Induct; c.name = t.name; c.lparams = lparams; c.type = t.type; c.nparams = nparams;
      c.is_unsafe = is_unsafe; c.all = all_names; for (auto& ct : t.ctors) c.ctors.push_back(ct.name);
      // nindices: count pis after params (syntactic; refined below)
      Expr x = t.type; unsigned k = 0; while (is_pi(x)) { if (k >= nparams) c.nindices++; x = binding_body(x); k++; }
      env.add(c);
    }
    AddInductive ai(env, lparams, nparams, params, ne.types, sf);
    ai.check_types();
    // fix nindices from whnf-based count
    for (size_t i = 0; i < ne.types.size(); i++) const_cast<ConstInfo&>(env.get(ne.types[i].name)).nindices = ai.nindices[i];
    ai.check_ctors();
    bool is_rec = ai.is_rec_flag(), is_reflexive = ai.is_reflexive_flag();
    for (size_t i = 0; i < d.ntypes; i++) {
      if (d.consts[i].is_rec != is_rec) meta_mismatch("isRec flag mismatch for '" + name_str(d.consts[i].name) + "'");
      if (d.consts[i].is_reflexive != is_reflexive) meta_mismatch("isReflexive flag mismatch for '" + name_str(d.consts[i].name) + "'");
      if (d.consts[i].nindices != ai.nindices[i]) meta_mismatch("numIndices mismatch for '" + name_str(d.consts[i].name) + "'");
      // `all` is structural: it names the block, as the kernel requires (a mutual block is never empty)
      std::vector<Name> block; for (size_t j = 0; j < d.ntypes; j++) block.push_back(d.consts[j].name);
      if (d.consts[i].all != block) fail("inductive '" + name_str(d.consts[i].name) + "': 'all' does not list the types of its mutual block");
    }
    // Declare constructors of all block types (auxiliary ones included) so recursor terms typecheck.
    for (size_t i = 0; i < ne.types.size(); i++) {
      u32 cidx = 0;
      for (auto& ct : ne.types[i].ctors) {
        ConstInfo c; c.kind = CKind::Ctor; c.name = ct.name; c.lparams = lparams; c.type = ct.type; c.induct = ne.types[i].name;
        c.cidx = cidx++; c.nparams = nparams; c.is_unsafe = is_unsafe;
        Expr x = ct.type; unsigned k = 0; while (is_pi(x)) { k++; x = binding_body(x); }
        c.nfields = k - nparams;
        if (i < d.ntypes) {
          const ConstInfo* ex = nullptr;
          for (size_t q = d.ntypes; q < d.ntypes + d.nctors; q++) if (d.consts[q].name == ct.name) ex = &d.consts[q];
          if (ex->nfields != c.nfields || ex->nparams != nparams || ex->cidx != c.cidx) fail("constructor field/parameter/index counts do not match: " + name_str(ct.name));
        }
        env.add(c);
      }
    }
    // Recursors: derive and compare.
    // Elimination level parameter name: taken from the exported main recursor.
    Name main_rec = g_names->mk_str(orig[0].name, "rec");
    const ConstInfo* exp_main = nullptr;
    for (size_t k = d.ntypes + d.nctors; k < d.consts.size(); k++) if (d.consts[k].name == main_rec) exp_main = &d.consts[k];
    if (!exp_main) fail("recursor '" + name_str(main_rec) + "' missing from the export");
    Name elim_name = NIL;
    if (exp_main->lparams.size() == lparams.size() + 1) elim_name = exp_main->lparams[0];
    else if (exp_main->lparams.size() != lparams.size()) fail("recursor '" + name_str(main_rec) + "' has an unexpected number of universe parameters");
    ai.mk_rec_infos(elim_name);
    if (is_param(ai.elim_level)) {
      // the kernel picks `u`, or `u_1`, `u_2`, ... not among lparams
      Name want = N.u; unsigned i = 1;
      while (std::find(lparams.begin(), lparams.end(), want) != lparams.end()) want = append_index_after(N.u, i++);
      if (want != elim_name) fail("recursor '" + name_str(main_rec) + "' elimination universe is named '" + name_str(elim_name) + "', expected '" + name_str(want) + "'");
    } else if (elim_name != NIL) fail("recursor '" + name_str(main_rec) + "' should only eliminate into Prop");
    bool K = ai.k_target();
    std::vector<Name> rec_lps; if (elim_name != NIL) rec_lps.push_back(elim_name); for (Name p : lparams) rec_lps.push_back(p);
    // aux recursor renaming: `_nested.J_k.rec` -> `Main.rec_k`
    std::map<Name, Name> aux_rec;
    for (size_t i = d.ntypes, k = 1; i < ne.types.size(); i++, k++)
      aux_rec[g_names->mk_str(ne.types[i].name, "rec")] = append_index_after(main_rec, (unsigned)k);
    std::vector<Name> orig_names; for (auto& t : orig) orig_names.push_back(t.name);
    size_t minor_idx = 0;
    std::vector<ConstInfo> derived;
    for (size_t i = 0; i < ne.types.size(); i++) {
      ConstInfo c; c.kind = CKind::Rec;
      Name rn = g_names->mk_str(ne.types[i].name, "rec");
      c.name = i < d.ntypes ? rn : aux_rec[rn];
      c.lparams = rec_lps; c.all = orig_names; c.nparams = nparams; c.nindices = ai.nindices[i];
      c.nmotives = (u32)ai.motives.size(); c.nminors = (u32)ai.minors.size(); c.k = K; c.is_unsafe = is_unsafe;
      c.type = ne.restore(ai.rec_type(i), aux_rec);
      for (RecRule r : ai.rec_rules(i, minor_idx)) {
        r.rhs = ne.restore(r.rhs, aux_rec);
        if (i >= d.ntypes) {
          // constructor of an auxiliary type -> real constructor name
          Name auxI = ne.aux_ctor_of[r.ctor];
          Expr nested = ne.aux2nested[auxI].first;
          Expr I = get_app_fn(nested);
          r.ctor = replace_prefix(r.ctor, auxI, const_name(I));
        }
        c.rules.push_back(r);
      }
      derived.push_back(c);
    }
    // Compare with the export.
    if (d.nrecs != derived.size()) fail("recursor count mismatch for '" + name_str(orig[0].name) + "': export has " + std::to_string(d.nrecs) + ", derived " + std::to_string(derived.size()));
    // For comparison we need an environment where the *original* constants are the real ones:
    // roll back to the mark and add the exported types and constructors.
    env.rollback(mark);
    for (size_t k = 0; k < d.ntypes + d.nctors; k++) env.add(d.consts[k]);
    for (const ConstInfo& dc : derived) {
      const ConstInfo* ec = nullptr;
      for (size_t k = d.ntypes + d.nctors; k < d.consts.size(); k++) if (d.consts[k].name == dc.name) ec = &d.consts[k];
      if (!ec) fail("derived recursor '" + name_str(dc.name) + "' is not in the export");
      if (ec->lparams != dc.lparams) fail("recursor '" + name_str(dc.name) + "': universe parameters differ");
      if (ec->nparams != dc.nparams || ec->nindices != dc.nindices || ec->nmotives != dc.nmotives || ec->nminors != dc.nminors || ec->k != dc.k)
        fail("recursor '" + name_str(dc.name) + "': parameter/index/motive/minor/K data differs from the derived recursor");
      if (ec->all != dc.all) fail("recursor '" + name_str(dc.name) + "': 'all' differs");
      if (ec->rules.size() != dc.rules.size()) fail("recursor '" + name_str(dc.name) + "': rule count differs");
      TypeChecker tc(env, dc.lparams, sf);
      tc.ensure_sort(tc.check_type(dc.type), dc.type);
      if (!tc.is_def_eq(ec->type, dc.type)) fail("recursor '" + name_str(dc.name) + "': exported type differs from the derived type\n  exported: " + expr_str(ec->type) + "\n  derived:  " + expr_str(dc.type));
      for (size_t r = 0; r < dc.rules.size(); r++) {
        if (ec->rules[r].ctor != dc.rules[r].ctor || ec->rules[r].nfields != dc.rules[r].nfields)
          fail("recursor '" + name_str(dc.name) + "': rule " + std::to_string(r) + " constructor/field data differs");
        if (!tc.is_def_eq(ec->rules[r].rhs, dc.rules[r].rhs))
          fail("recursor '" + name_str(dc.name) + "': rule for '" + name_str(dc.rules[r].ctor) + "' differs from the derived rule");
      }
    }
    for (size_t k = d.ntypes + d.nctors; k < d.consts.size(); k++) {
      ConstInfo c = d.consts[k];
      // the major premise's inductive
      Expr t = c.type; u32 idx = 0;
      while (is_pi(t)) { if (idx == c.rec_major_idx()) { Expr I = get_app_fn(binding_dom(t)); if (is_const(I)) c.major_induct = const_name(I); } t = binding_body(t); idx++; }
      env.add(c);
    }
  } catch (...) { env.rollback(mark); throw; }
}

// Quotient declarations: verify the four constants have exactly the expected types.
void add_quot_decl(Environment& env, const Decl& d) {
  const ConstInfo& c = d.consts[0];
  if (env.contains(c.name)) fail("constant already declared: " + name_str(c.name));
  Level u = mk_param(N.u), v = mk_param(N.v);
  auto Sort = [](Level l) { return mk_sort(l); };
  Expr expected = NIL; std::vector<Name> lps;
  // α → α → Prop, under a context where α is bvar 0
  Expr relTy = mk_pi(N.anonymous, mk_bvar(0), mk_pi(N.anonymous, mk_bvar(1), Sort(LZERO), BInfo::Default), BInfo::Default);
  switch (c.quot_kind) {
    case QuotKind::Type:
      lps = {N.u};
      expected = mk_pi(mk_name("α"), Sort(u), mk_pi(mk_name("r"), relTy, Sort(u), BInfo::Default), BInfo::Implicit);
      break;
    case QuotKind::Ctor: {
      lps = {N.u};
      Expr quot = mk_app(mk_app(mk_const(N.Quot, g_levels->mk_list({u})), mk_bvar(2)), mk_bvar(1));
      expected = mk_pi(mk_name("α"), Sort(u), mk_pi(mk_name("r"), relTy, mk_pi(mk_name("a"), mk_bvar(1), quot, BInfo::Default), BInfo::Default), BInfo::Implicit);
      break;
    }
    case QuotKind::Lift: {
      lps = {N.u, N.v};
      // binders [α, r, β, f, a, b]: α=#5 r=#4 β=#3 f=#2 a=#1 b=#0
      Expr r_ab = mk_app(mk_app(mk_bvar(4), mk_bvar(1)), mk_bvar(0));
      Expr fa = mk_app(mk_bvar(2), mk_bvar(1)), fb = mk_app(mk_bvar(2), mk_bvar(0));
      Expr eq = mk_app(mk_app(mk_app(mk_const(N.Eq, g_levels->mk_list({v})), mk_bvar(3)), fa), fb);
      // under [α, r, β, f]: a : α=#3 ; under [.., a]: b : α=#4
      Expr sanity = mk_pi(mk_name("a"), mk_bvar(3), mk_pi(mk_name("b"), mk_bvar(4), mk_pi(N.anonymous, r_ab, lift_loose_bvars(eq, 0, 1), BInfo::Default), BInfo::Default), BInfo::Default);
      // under [α, r, β, f, sanity]: Quot α r → β  with α=#4 r=#3 β=#2 (inside the arrow, β=#3)
      Expr quot = mk_app(mk_app(mk_const(N.Quot, g_levels->mk_list({u})), mk_bvar(4)), mk_bvar(3));
      Expr body = mk_pi(N.anonymous, quot, mk_bvar(3), BInfo::Default);
      // under [α r β]: f : α → β with α=#2, β=#0 (inside arrow β=#1)
      Expr fty = mk_pi(N.anonymous, mk_bvar(2), mk_bvar(1), BInfo::Default);
      expected = mk_pi(mk_name("α"), Sort(u), mk_pi(mk_name("r"), relTy, mk_pi(mk_name("β"), Sort(v),
                   mk_pi(mk_name("f"), fty, mk_pi(N.anonymous, sanity, body, BInfo::Default), BInfo::Default), BInfo::Implicit), BInfo::Implicit), BInfo::Implicit);
      break;
    }
    case QuotKind::Ind: {
      lps = {N.u};
      // under [α r]: β : Quot α r → Prop
      Expr quot2 = mk_app(mk_app(mk_const(N.Quot, g_levels->mk_list({u})), mk_bvar(1)), mk_bvar(0));
      Expr betaTy = mk_pi(N.anonymous, quot2, Sort(LZERO), BInfo::Default);
      // under [α r β a]: α=#3 r=#2 β=#1 a=#0
      Expr mk_a = mk_app(mk_app(mk_app(mk_const(N.Quot_mk, g_levels->mk_list({u})), mk_bvar(3)), mk_bvar(2)), mk_bvar(0));
      Expr mkTy = mk_pi(mk_name("a"), mk_bvar(2), mk_app(mk_bvar(1), mk_a), BInfo::Default);
      // under [α r β mk]: q : Quot α r with α=#3 r=#2; body β q with β=#2 (inside), q=#0
      Expr quot3 = mk_app(mk_app(mk_const(N.Quot, g_levels->mk_list({u})), mk_bvar(3)), mk_bvar(2));
      Expr body = mk_pi(mk_name("q"), quot3, mk_app(mk_bvar(2), mk_bvar(0)), BInfo::Default);
      expected = mk_pi(mk_name("α"), Sort(u), mk_pi(mk_name("r"), relTy, mk_pi(mk_name("β"), betaTy,
                   mk_pi(mk_name("mk"), mkTy, body, BInfo::Default), BInfo::Implicit), BInfo::Implicit), BInfo::Implicit);
      break;
    }
  }
  if (c.quot_kind == QuotKind::Type) {
    const ConstInfo& eq = env.get(N.Eq);
    if (eq.kind != CKind::Induct || eq.lparams.size() != 1 || eq.ctors.size() != 1) fail("Quot: 'Eq' has an unexpected shape");
    // Eq.{u} : {α : Sort u} → α → α → Prop, and Eq.refl : ∀ {α} (a : α), Eq a a
    Level eu = mk_param(eq.lparams[0]);
    Expr eqTy = mk_pi(mk_name("α"), Sort(eu), mk_pi(N.anonymous, mk_bvar(0), mk_pi(N.anonymous, mk_bvar(1), Sort(LZERO), BInfo::Default), BInfo::Default), BInfo::Implicit);
    TypeChecker tc0(env, eq.lparams);
    if (!tc0.is_def_eq(eqTy, eq.type)) fail("Quot: 'Eq' has an unexpected type");
    const ConstInfo& rf = env.get(eq.ctors[0]);
    Expr reflTy = mk_pi(mk_name("α"), Sort(eu), mk_pi(mk_name("a"), mk_bvar(0),
                    mk_app(mk_app(mk_app(mk_const(N.Eq, g_levels->mk_list({eu})), mk_bvar(1)), mk_bvar(0)), mk_bvar(0)), BInfo::Default), BInfo::Implicit);
    TypeChecker tc1(env, rf.lparams);
    if (rf.lparams.size() != 1 || !tc1.is_def_eq(reflTy, rf.type)) fail("Quot: 'Eq.refl' has an unexpected type");
  }
  // The kernel defines the quotient constants itself and ignores what an export says about
  // them (Lean's replay does the same), so the exported type is only cross-checked: a mismatch
  // is a warning (--strict-metadata: a rejection) and the built-in type is what gets added.
  ConstInfo added = c;
  bool ok = c.lparams.size() == lps.size();
  if (ok) {
    std::vector<Level> theirs; for (Name p : c.lparams) theirs.push_back(mk_param(p));
    Expr exp2 = instantiate_lparams(expected, lps, theirs);
    if (!has_loose_bvars(c.type)) { TypeChecker tc(env, c.lparams); ok = tc.is_def_eq(exp2, c.type); } else ok = false;
    if (ok) added.type = exp2;
  }
  if (!ok) { meta_mismatch("Quot constant '" + name_str(c.name) + "' is exported with an unexpected type; using the built-in one"); added.type = expected; added.lparams = lps; }
  env.add(added);
  if (c.quot_kind == QuotKind::Ind) env.quot_init = true;
}

} // namespace ll
