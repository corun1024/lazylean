#pragma once
#include "common.h"
#include "name.h"
#include "level.h"
#include <gmpxx.h>
#include <functional>

namespace ll {

enum class EKind : u8 { BVar = 0, FVar, Sort, Const, App, Lam, Pi, Let, Lit, Proj, Clos };
enum class BInfo : u8 { Default = 0, Implicit, StrictImplicit, InstImplicit };
enum class LitKind : u8 { Nat = 0, Str = 1 };

struct ExprNode {
  EKind kind;
  BInfo binfo;
  u8 flags;            // bit0: has_fvar
  u32 loose_bvar_range;
  u32 a, b, c;         // children / payload (see mk_* below)
  u32 name;            // binder name, const name, proj struct name
  u32 lvls;            // const: LevelList
  u64 hash;
};
// Payload conventions:
//  BVar : a = de Bruijn index
//  FVar : a = fvar id (unique, assigned by the type checker)
//  Sort : a = level
//  Const: name, lvls
//  App  : a = fn, b = arg
//  Lam/Pi: name, a = domain, b = body, binfo
//  Let  : name, a = type, b = value, c = body
//  Lit  : a = literal index, b = LitKind
//  Proj : name = struct name, a = field index, b = struct expr
//  Clos : a = term t, b = environment id, c = p.  A suspended substitution (explicit
//         substitution with closed entries): bvar i of t stands for  bvar i  if i < p,
//         E[i-p] if p <= i < p+|E|, and bvar (i-|E|) otherwise.  `name` caches the exposed
//         node (NIL until computed).  Never created for terms the substitution leaves alone.

struct ExprTable {
  std::vector<ExprNode> nodes;
  std::vector<mpz_class> nat_lits;
  std::vector<std::string> str_lits;
  // Closure environments (temporary tier only: closures are created while checking).
  std::vector<std::vector<Expr>> envs; std::vector<u64> env_hash; std::vector<u8> env_flags;
  ExprTable();
  u32 mk_env(const Expr* es, size_t n, bool rev);        // E[i] = es[i] (or es[n-1-i] if rev)
  u32 mk_env_concat(const std::vector<Expr>& parts);     // helper for composition
  Expr expose(Expr e);                                   // e must be a Clos node; returns the exposed handle
  // Closures are hash-consed modulo materialisation: a Clos node's hash is the hash of its
  // expansion, and sem_eq decides equality of expansions without building them.
  u64 sem_hash(Expr t, u32 env, u32 p, u32* lbr_out = nullptr, u8* flags_out = nullptr);   // also the exact loose-bvar range and flags
  bool sem_eq(Expr x, Expr y);
  const ExprNode& raw(Expr e) const { return nodes[e]; }
  const ExprNode& exposed(Expr e) { if (nodes[e].kind == EKind::Clos) expose(e); return nodes[e]; }
  Expr intern(ExprNode nd);
  u32 intern_nat(const mpz_class& v);
  u32 intern_nat(mpz_class&& v);
  u32 intern_str(const std::string& s);
  size_t size() const { return nodes.size(); }
  // Two-tier interning: nodes created before `freeze()` are permanent (the loaded export);
  // nodes created afterwards live in a temporary table that `reclaim()` drops, truncating the
  // node table back to the watermark.  Callers must not keep temporary handles across reclaim().
  void freeze();
  void reclaim();
  void trim();   // after reclaim: return the temporary tier's capacity to the allocator (after a blow-up)
  bool frozen = false;
  size_t wm_nodes = 0, wm_nat = 0, wm_str = 0;
private:
  struct H { ExprTable* t; u64 operator()(u32 h) const { return t->nodes[h].hash; } };
  // Structural identity is up to binder names and binder infos, as Lean's `Expr` equality and
  // hash are: alpha-equivalent terms intern to the same handle.  The name field still counts for
  // constants and projections, where it is the constant / structure name.
  struct E { ExprTable* t; bool operator()(u32 x, u32 y) const {
    auto& a = t->nodes[x]; auto& b = t->nodes[y];
    if (a.kind == EKind::Clos || b.kind == EKind::Clos) return t->sem_eq(x, y);   // modulo materialisation
    if (a.kind != b.kind || a.a != b.a || a.b != b.b || a.c != b.c || a.lvls != b.lvls) return false;
    return (a.kind != EKind::Const && a.kind != EKind::Proj) || a.name == b.name; } };
  struct NH { ExprTable* t; u64 operator()(u32 h) const {
    const mpz_class& v = t->nat_lits[h]; size_t n = mpz_size(v.get_mpz_t()); const mp_limb_t* l = mpz_limbs_read(v.get_mpz_t());
    u64 r = 0x51ED270B + n; for (size_t i = 0; i < n; i++) r = mix(r, (u64)l[i]); return r; } };
  struct NE { ExprTable* t; bool operator()(u32 x, u32 y) const { return t->nat_lits[x] == t->nat_lits[y]; } };
  struct SH { ExprTable* t; u64 operator()(u32 h) const { return hash_str(t->str_lits[h]); } };
  struct SE { ExprTable* t; bool operator()(u32 x, u32 y) const { return t->str_lits[x] == t->str_lits[y]; } };
  struct EH { ExprTable* t; u64 operator()(u32 h) const { return t->env_hash[h]; } };
  struct EE { ExprTable* t; bool operator()(u32 x, u32 y) const { return t->envs[x] == t->envs[y]; } };
  InternTable<EH, EE>* etable;
  InternTable<H, E>* table;  InternTable<H, E>* ttable;    // permanent / temporary
  InternTable<NH, NE>* ntable; InternTable<NH, NE>* tntable;
  InternTable<SH, SE>* stable; InternTable<SH, SE>* tstable;
};
extern ExprTable* g_exprs;
extern u64 g_cnt_clos, g_cnt_clos_compose, g_cnt_clos_expand, g_cnt_expose, g_cnt_env;
// `ex` looks through closure nodes: a Clos handle presents the node of its exposed form, so
// kind() and the field accessors below see ordinary structure.  Flags and the loose-bvar
// range are read from the node itself (they are the same either way, without exposing).
inline const ExprNode& ex(Expr e) { return g_exprs->exposed(e); }
inline const ExprNode& raw(Expr e) { return g_exprs->raw(e); }
inline EKind kind(Expr e) { return ex(e).kind; }
inline bool is_clos(Expr e) { return raw(e).kind == EKind::Clos; }
inline bool has_fvar(Expr e) { return raw(e).flags & 1; }
inline bool has_loose_bvars(Expr e) { return raw(e).loose_bvar_range > 0; }
inline u32 loose_bvar_range(Expr e) { return raw(e).loose_bvar_range; }

Expr mk_bvar(u32 idx);
Expr mk_fvar(u32 id);
Expr mk_sort(Level l);
Expr mk_const(Name n, LevelList ls);
inline Expr mk_const(Name n) { return mk_const(n, 0); }
Expr mk_app(Expr f, Expr a);
Expr mk_lam(Name n, Expr dom, Expr body, BInfo bi);
Expr mk_pi(Name n, Expr dom, Expr body, BInfo bi);
Expr mk_let(Name n, Expr type, Expr val, Expr body);
Expr mk_nat_lit(const mpz_class& v);
Expr mk_nat_lit(mpz_class&& v);
Expr mk_str_lit(const std::string& s);
Expr mk_proj(Name s, u32 idx, Expr e);
inline Expr mk_arrow(Expr a, Expr b) { return mk_pi(N.anonymous, a, b, BInfo::Default); }
Expr mk_apps(Expr f, const std::vector<Expr>& args);
Expr mk_apps(Expr f, const Expr* args, size_t n);
Expr mk_apps_range(Expr f, const std::vector<Expr>& args, size_t lo, size_t hi);

inline bool is_bvar(Expr e) { return kind(e) == EKind::BVar; }
inline bool is_fvar(Expr e) { return kind(e) == EKind::FVar; }
inline bool is_sort(Expr e) { return kind(e) == EKind::Sort; }
inline bool is_const(Expr e) { return kind(e) == EKind::Const; }
inline bool is_app(Expr e) { return kind(e) == EKind::App; }
inline bool is_lam(Expr e) { return kind(e) == EKind::Lam; }
inline bool is_pi(Expr e) { return kind(e) == EKind::Pi; }
inline bool is_let(Expr e) { return kind(e) == EKind::Let; }
inline bool is_lit(Expr e) { return kind(e) == EKind::Lit; }
inline bool is_proj(Expr e) { return kind(e) == EKind::Proj; }
inline bool is_nat_lit(Expr e) { return is_lit(e) && ex(e).b == (u32)LitKind::Nat; }
inline bool is_str_lit(Expr e) { return is_lit(e) && ex(e).b == (u32)LitKind::Str; }
inline const mpz_class& nat_lit_val(Expr e) { return g_exprs->nat_lits[ex(e).a]; }
inline const std::string& str_lit_val(Expr e) { return g_exprs->str_lits[ex(e).a]; }
inline Expr app_fn(Expr e) { return ex(e).a; }
inline Expr app_arg(Expr e) { return ex(e).b; }
inline Expr binding_dom(Expr e) { return ex(e).a; }
inline Expr binding_body(Expr e) { return ex(e).b; }
inline Name binding_name(Expr e) { return ex(e).name; }
inline BInfo binding_info(Expr e) { return ex(e).binfo; }
inline Expr let_type(Expr e) { return ex(e).a; }
inline Expr let_val(Expr e) { return ex(e).b; }
inline Expr let_body(Expr e) { return ex(e).c; }
inline Level sort_level(Expr e) { return ex(e).a; }
inline Name const_name(Expr e) { return ex(e).name; }
inline LevelList const_levels(Expr e) { return ex(e).lvls; }
inline u32 bvar_idx(Expr e) { return ex(e).a; }
inline u32 fvar_id(Expr e) { return ex(e).a; }
inline Name proj_sname(Expr e) { return ex(e).name; }
inline u32 proj_idx(Expr e) { return ex(e).a; }
inline Expr proj_expr(Expr e) { return ex(e).b; }
inline bool is_const_of(Expr e, Name n) { return is_const(e) && const_name(e) == n; }

// Application spine helpers.
Expr get_app_fn(Expr e);
unsigned get_app_num_args(Expr e);
void get_app_args(Expr e, std::vector<Expr>& args);   // args in order
Expr get_app_args_fn(Expr e, std::vector<Expr>& args); // returns fn, fills args
inline bool is_app_of(Expr e, Name n) { return is_const_of(get_app_fn(e), n); }
inline bool is_app_of_arity(Expr e, Name n, unsigned k) { return is_app_of(e, n) && get_app_num_args(e) == k; }

// Substitution. `instantiate(e, n, subst)` replaces loose bvars 0..n-1 by subst[n-1-i]?? No:
// we follow Lean: instantiate(e, subst[0..n)) replaces bvar i (i < n) by subst[i], where
// subst[i] itself is lifted by the binder depth. instantiate_rev uses subst[n-1-i].
Expr instantiate(Expr e, size_t n, const Expr* subst);        // lazy (a Clos node) when the entries are closed
Expr instantiate_rev(Expr e, size_t n, const Expr* subst);
Expr instantiate_eager(Expr e, size_t n, const Expr* subst);  // always materialises
Expr instantiate_rev_eager(Expr e, size_t n, const Expr* subst);
Expr mk_clos(Expr t, u32 env, u32 p);                         // suspended substitution (see ExprNode)
Expr expand_closures(Expr e);                                 // materialise every Clos node in e
Expr canon(Expr e);                                           // e itself, or its materialisation if e is a Clos (cached)
inline Expr instantiate1(Expr e, Expr v) { return instantiate(e, 1, &v); }
// Replace loose bvars with offset: bvar (s+i) -> subst... (Lean's instantiate with start s).
Expr instantiate_range_rev(Expr e, const std::vector<Expr>& subst, size_t lo, size_t hi);
Expr lift_loose_bvars(Expr e, u32 s, u32 d);   // bvars >= s are shifted by d
Expr lower_loose_bvars(Expr e, u32 s, u32 d);  // bvars >= s are shifted down by d (s >= d)
// Abstract fvars: occurrences of fvars[i] (i in 0..n) become bvar (n-1-i) at depth 0.
Expr abstract_fvars(Expr e, size_t n, const Expr* fvars);
Expr instantiate_lparams(Expr e, const std::vector<Name>& ps, const std::vector<Level>& ls);
// Generic memoized replacement: f(e, binder_depth) returns NIL to recurse into e, or a replacement.
Expr replace_expr(Expr e, const std::function<Expr(Expr, u32)>& f);
// Cheap beta at the head: (fun x => b) a ... -> b[a] ... without full whnf (Lean's cheapBetaReduce).
Expr cheap_beta_reduce(Expr e);
Expr head_beta(Expr e);
bool occurs_const(Expr e, Name c);

std::string expr_str(Expr e);   // debugging printer

} // namespace ll
