#include "expr.h"
#include <thread>
#include <cstdlib>
#include <unordered_map>
#include <algorithm>

namespace ll {

ExprTable* g_exprs = nullptr;
void clear_sem_memos();   // below: handles and env ids are recycled by reclaim(), so the memos must not outlive it
u64 g_cnt_clos = 0, g_cnt_clos_compose = 0, g_cnt_clos_expand = 0, g_cnt_expose = 0, g_cnt_env = 0;
void check_rss(const char* where);   // kernel.cpp

ExprTable::ExprTable() {
  nodes.reserve(1 << 20);
  table = new InternTable<H, E, true>(H{this}, E{this}, 1 << 20);
  ttable = new InternTable<H, E>(H{this}, E{this}, 1 << 16);
  ntable = new InternTable<NH, NE>(NH{this}, NE{this});
  tntable = new InternTable<NH, NE>(NH{this}, NE{this});
  stable = new InternTable<SH, SE>(SH{this}, SE{this});
  tstable = new InternTable<SH, SE>(SH{this}, SE{this});
  etable = new InternTable<EH, EE>(EH{this}, EE{this});
  ttable->track = tntable->track = tstable->track = etable->track = true;
}

void ExprTable::reserve_permanent(size_t n, bool size_table) {
  // Room above the permanent tier for the terms a declaration builds: were the array to grow
  // later, a forked worker would copy the whole shared tier into its own memory.
  size_t cap = n + std::max<size_t>(n / 4, (size_t)1 << 24);
  if (nodes.empty()) {
    std::vector<ExprNode>().swap(nodes);
    nodes.reserve(cap);
    advise_huge(nodes.data(), cap * sizeof(ExprNode));
  } else nodes.reserve(cap);
  g_node_base = nodes.data();
  if (size_table) table->reserve(n);
}

// Look up `cand` (already appended) in the permanent table without inserting.
template <class T> static u32 find_only(T* t, u32 cand) { return t->find(cand); }

const ExprNode* g_node_base = nullptr;
u64 g_int_perm_probe = 0, g_int_perm_hit = 0, g_int_temp_hit = 0, g_int_new = 0;
u64 g_int_kind[16];
#ifdef LL_INTERN_STATS
#define ISTAT(x) (x)
#else
#define ISTAT(x) ((void)0)
#endif
Expr ExprTable::intern(ExprNode nd) {
  ISTAT(g_int_kind[(int)nd.kind]++);
  const bool temp_hint = nd.flags & 0x80;
  nd.flags &= 0x7f;
  nodes.push_back(nd);
  g_node_base = nodes.data();
  if ((nodes.size() & 0xfffff) == 0) check_rss("intern");
  if (bulk) return (u32)nodes.size() - 1;   // indexed later by build_index()
  u32 cand = (u32)nodes.size() - 1;
  u32 r;
  if (!frozen) r = table->intern(cand);
  else {
    // The permanent tier is hash-consed and frozen, and a temporary handle is never equal to a
    // permanent node (had one existed, interning would have returned it).  So a node with a
    // temporary child cannot equal any permanent node, and the probe into the permanent table
    // -- a cache miss into a table of tens of millions of entries -- can be skipped.  A closure
    // is compared semantically, not by its children, and is always looked up.
    bool maybe_perm = true;
    switch (nd.kind) {
      case EKind::App: case EKind::Lam: case EKind::Pi:
        maybe_perm = nd.a < wm_nodes && nd.b < wm_nodes; break;
      case EKind::Let: maybe_perm = nd.a < wm_nodes && nd.b < wm_nodes && nd.c < wm_nodes; break;
      case EKind::Proj: maybe_perm = nd.b < wm_nodes; break;
      case EKind::FVar: maybe_perm = false; break;   // the loader never makes free variables
      case EKind::Clos: maybe_perm = !temp_hint; break;   // its materialisation contains a temporary term
      default: break;
    }
    if (maybe_perm) ISTAT(g_int_perm_probe++);
    r = maybe_perm ? find_only(table, cand) : NIL;
    if (r != NIL) ISTAT(g_int_perm_hit++);
    else {
#ifdef LL_INTERN_STATS
      size_t c0 = ttable->count; r = ttable->intern(cand); if (ttable->count != c0) g_int_new++; else g_int_temp_hit++;
#else
      r = ttable->intern(cand);
#endif
    }
  }
  // An equality test may have interned further nodes (closures); only pop when still last.
  if (r != cand && cand + 1 == nodes.size()) nodes.pop_back();
  return r;
}
u32 ExprTable::intern_nat(const mpz_class& v) {
  nat_lits.push_back(v);
  u32 cand = (u32)nat_lits.size() - 1;
  u32 r;
  if (!frozen) r = ntable->intern(cand);
  else { r = find_only(ntable, cand); if (r == NIL) r = tntable->intern(cand); }
  if (r != cand) nat_lits.pop_back();
  return r;
}
u32 ExprTable::intern_nat(mpz_class&& v) {
  nat_lits.push_back(std::move(v));
  u32 cand = (u32)nat_lits.size() - 1;
  u32 r;
  if (!frozen) r = ntable->intern(cand);
  else { r = find_only(ntable, cand); if (r == NIL) r = tntable->intern(cand); }
  if (r != cand) nat_lits.pop_back();
  return r;
}
u32 ExprTable::intern_str(const std::string& s) {
  str_lits.push_back(s);
  u32 cand = (u32)str_lits.size() - 1;
  u32 r;
  if (!frozen) r = stable->intern(cand);
  else { r = find_only(stable, cand); if (r == NIL) r = tstable->intern(cand); }
  if (r != cand) str_lits.pop_back();
  return r;
}
bool ExprTable::build_index(unsigned threads) {
  u32 n = (u32)nodes.size();
  table->reserve(n);
  bool dup = false;
  if (threads < 2 || n < (1u << 20)) table->bulk_insert(0, n, &dup);
  else {
    std::vector<std::thread> ts;
    for (unsigned k = 0; k < threads; k++) {
      u32 lo = (u32)((u64)n * k / threads), hi = (u32)((u64)n * (k + 1) / threads);
      ts.emplace_back([this, lo, hi, &dup] { table->bulk_insert(lo, hi, &dup); });
    }
    for (auto& t : ts) t.join();
  }
  table->count = n;
  bulk = false;
  return !dup;
}
void ExprTable::reset_permanent() {
  nodes.clear(); nat_lits.clear(); str_lits.clear();
  table->slots.assign(table->slots.size(), table->EMPTY); table->count = 0;
  ntable->slots.assign(ntable->slots.size(), ntable->EMPTY); ntable->count = 0;
  stable->slots.assign(stable->slots.size(), stable->EMPTY); stable->count = 0;
  bulk = false;
}

void ExprTable::freeze() { frozen = true; wm_nodes = nodes.size(); wm_nat = nat_lits.size(); wm_str = str_lits.size(); }
void ExprTable::reclaim() {
  if (!frozen) return;
  nodes.resize(wm_nodes); g_node_base = nodes.data(); nat_lits.resize(wm_nat); str_lits.resize(wm_str);
  // Clearing a table costs its capacity, so an untouched table is left alone and an oversized
  // one is shrunk rather than wiped in place (a declaration that interned little pays little).
  auto reset = [](auto* t, size_t small) {
    if (t->count == 0) return;
    size_t cap = t->slots.size();
    // A table grown by one large declaration is shrunk back: a sparse table spread over many
    // megabytes costs a cache miss per probe for every small declaration that follows.
    if (cap > 4 * small) { t->slots.assign(small, t->EMPTY); t->dirty.clear(); t->count = 0; }
    else t->clear_used();
  };
  reset(ttable, 1u << 16); reset(tntable, 1u << 12); reset(tstable, 1u << 12); reset(etable, 1u << 12);
  envs.clear(); env_hash.clear(); env_flags.clear();
  clear_sem_memos();   // bumps the memo generation; nothing is wiped
}

void ExprTable::trim() {
  reclaim();
  nodes.shrink_to_fit(); g_node_base = nodes.data(); nat_lits.shrink_to_fit(); str_lits.shrink_to_fit();
  envs.shrink_to_fit(); env_hash.shrink_to_fit(); env_flags.shrink_to_fit();
  for (auto* t : {ttable}) { t->slots.assign(1u << 16, t->EMPTY); t->slots.shrink_to_fit(); t->count = 0; t->dirty.clear(); t->dirty.shrink_to_fit(); }
  tntable->slots.assign(1u << 12, tntable->EMPTY); tntable->slots.shrink_to_fit(); tntable->count = 0; tntable->dirty.clear();
  tstable->slots.assign(1u << 12, tstable->EMPTY); tstable->slots.shrink_to_fit(); tstable->count = 0; tstable->dirty.clear();
  etable->slots.assign(1u << 12, etable->EMPTY); etable->slots.shrink_to_fit(); etable->count = 0; etable->dirty.clear();
}

u32 ExprTable::mk_env(const Expr* es, size_t n, bool rev) {
  std::vector<Expr> v(n);
  for (size_t i = 0; i < n; i++) v[i] = es[rev ? n - 1 - i : i];
  u64 h = 0x243F6A8885A308D3ull + n; u8 fl = 0;
  for (Expr x : v) { h = mix(h, nodes[x].hash); fl |= nodes[x].flags; }
  g_cnt_env++;
  envs.push_back(std::move(v)); env_hash.push_back(h); env_flags.push_back(fl);
  u32 cand = (u32)envs.size() - 1;
  u32 r = etable->intern(cand);
  if (r != cand) { envs.pop_back(); env_hash.pop_back(); env_flags.pop_back(); }
  return r;
}
u32 ExprTable::mk_env_concat(const std::vector<Expr>& parts) { return mk_env(parts.data(), parts.size(), false); }


static inline u32 hk(EKind k, u64 x) { u64 h = mix((u64)k + 101, x); return (u32)(h ^ (h >> 32)); }

Expr mk_bvar(u32 idx) {
  return g_exprs->intern(ExprNode{EKind::BVar, BInfo::Default, 0, idx + 1, idx, 0, 0, 0, 0, hk(EKind::BVar, idx)});
}
Expr mk_fvar(u32 id) {
  return g_exprs->intern(ExprNode{EKind::FVar, BInfo::Default, 1, 0, id, 0, 0, 0, 0, hk(EKind::FVar, id)});
}
Expr mk_sort(Level l) {
  return g_exprs->intern(ExprNode{EKind::Sort, BInfo::Default, (u8)(lv(l).has_param ? 2 : 0), 0, l, 0, 0, 0, 0, hk(EKind::Sort, lv(l).hash)});
}
Expr mk_const(Name n, LevelList ls) {
  u32 h = hk(EKind::Const, mix((*g_names)[n].hash, ls));
  return g_exprs->intern(ExprNode{EKind::Const, BInfo::Default, (u8)(g_levels->list_has_param(ls) ? 2 : 0), 0, 0, 0, 0, n, ls, h});
}
static ExprNode node_app(Expr f, Expr a) {
  const ExprNode nf = raw(f); const ExprNode na = raw(a);
  u32 h = hk(EKind::App, mix(nf.hash, na.hash));
  return ExprNode{EKind::App, BInfo::Default, (u8)(nf.flags | na.flags), std::max(nf.loose_bvar_range, na.loose_bvar_range), f, a, 0, 0, 0, h};
}
static ExprNode node_binding(EKind k, Name n, Expr dom, Expr body, BInfo bi) {
  const ExprNode nd = raw(dom); const ExprNode nb = raw(body);
  u32 lbr = std::max(nd.loose_bvar_range, nb.loose_bvar_range > 0 ? nb.loose_bvar_range - 1 : 0);
  u32 h = hk(k, mix(nd.hash, nb.hash));
  return ExprNode{k, bi, (u8)(nd.flags | nb.flags), lbr, dom, body, 0, n, 0, h};
}
static ExprNode node_let(Name n, Expr type, Expr val, Expr body) {
  const ExprNode nt = raw(type); const ExprNode nv = raw(val); const ExprNode nb = raw(body);
  u32 lbr = std::max({nt.loose_bvar_range, nv.loose_bvar_range, nb.loose_bvar_range > 0 ? nb.loose_bvar_range - 1 : 0});
  u32 h = hk(EKind::Let, mix(mix(nt.hash, nv.hash), nb.hash));
  return ExprNode{EKind::Let, BInfo::Default, (u8)(nt.flags | nv.flags | nb.flags), lbr, type, val, body, n, 0, h};
}
static ExprNode node_proj(Name s, u32 idx, Expr e) {
  const ExprNode ne = raw(e);
  u32 h = hk(EKind::Proj, mix(mix((*g_names)[s].hash, idx), ne.hash));
  return ExprNode{EKind::Proj, BInfo::Default, ne.flags, ne.loose_bvar_range, idx, e, 0, s, 0, h};
}
Expr mk_app(Expr f, Expr a) { return g_exprs->intern(node_app(f, a)); }

// The loader's bulk path: while the permanent tier is being appended (see ExprTable::bulk) a
// node is pushed without any lookup, reading only the fields of its children it needs.
Expr bulk_app(Expr f, Expr a) {
  ExprTable& T = *g_exprs;
  if (!T.bulk) return mk_app(f, a);
  const ExprNode* nd = T.nodes.data();
  const u8 fl = nd[f].flags | nd[a].flags;
  const u32 lbr = std::max(nd[f].loose_bvar_range, nd[a].loose_bvar_range);
  const u32 h = hk(EKind::App, mix(nd[f].hash, nd[a].hash));
  T.nodes.push_back(ExprNode{EKind::App, BInfo::Default, fl, lbr, f, a, 0, 0, 0, h});
  g_node_base = T.nodes.data();
  return (u32)T.nodes.size() - 1;
}
Expr bulk_binding(bool pi, Name n, Expr dom, Expr body, BInfo bi) {
  ExprTable& T = *g_exprs;
  if (!T.bulk) return pi ? mk_pi(n, dom, body, bi) : mk_lam(n, dom, body, bi);
  T.nodes.push_back(node_binding(pi ? EKind::Pi : EKind::Lam, n, dom, body, bi));
  g_node_base = T.nodes.data();
  return (u32)T.nodes.size() - 1;
}
static Expr mk_binding(EKind k, Name n, Expr dom, Expr body, BInfo bi) { return g_exprs->intern(node_binding(k, n, dom, body, bi)); }
Expr mk_lam(Name n, Expr dom, Expr body, BInfo bi) { return mk_binding(EKind::Lam, n, dom, body, bi); }
Expr mk_pi(Name n, Expr dom, Expr body, BInfo bi) { return mk_binding(EKind::Pi, n, dom, body, bi); }
Expr mk_let(Name n, Expr type, Expr val, Expr body) { return g_exprs->intern(node_let(n, type, val, body)); }
Expr mk_nat_lit(const mpz_class& v) {
  u32 i = g_exprs->intern_nat(v);
  return g_exprs->intern(ExprNode{EKind::Lit, BInfo::Default, 0, 0, i, (u32)LitKind::Nat, 0, 0, 0, hk(EKind::Lit, mix(1, i))});
}
Expr mk_nat_lit(mpz_class&& v) {
  u32 i = g_exprs->intern_nat(std::move(v));
  return g_exprs->intern(ExprNode{EKind::Lit, BInfo::Default, 0, 0, i, (u32)LitKind::Nat, 0, 0, 0, hk(EKind::Lit, mix(1, i))});
}
Expr mk_str_lit(const std::string& s) {
  u32 i = g_exprs->intern_str(s);
  return g_exprs->intern(ExprNode{EKind::Lit, BInfo::Default, 0, 0, i, (u32)LitKind::Str, 0, 0, 0, hk(EKind::Lit, mix(2, i))});
}
Expr mk_proj(Name s, u32 idx, Expr e) { return g_exprs->intern(node_proj(s, idx, e)); }

// ---- Suspended substitutions ------------------------------------------------------------

namespace {
// Small direct-mapped memo tables (no allocation) that make the walks below linear on DAGs in
// practice: identical shared subterms are met close together.
constexpr size_t MEMO_BITS = 18;
struct HashMemo { u64 key[1 << MEMO_BITS]; u64 val[1 << MEMO_BITS]; u32 lbr[1 << MEMO_BITS]; u8 fl[1 << MEMO_BITS]; HashMemo() { for (auto& k : key) k = ~0ull; } };
struct EqMemo { u64 key[1 << MEMO_BITS]; EqMemo() { for (auto& k : key) k = ~0ull; } };
HashMemo g_hmemo; EqMemo g_eqmemo;
}
u64 g_memo_gen = 1;   // folded into every memo key: entries of earlier declarations can never match
void clear_sem_memos() { g_memo_gen++; }

// Hash and exact loose-bvar range of the expansion of t under (E, p): what the materialised
// term would carry.
u64 ExprTable::sem_hash(Expr t, u32 env, u32 p, u32* lbr_out, u8* flags_out) {
  const ExprNode n = nodes[t];   // copy: recursive calls may intern nodes and grow the table
  // Bit 7 of the reported flags (never stored in a node) says that the materialisation contains
  // a temporary term, and so cannot be equal to anything in the permanent tier.
  const u8 tmp_t = (frozen && t >= wm_nodes) ? 0x80 : 0;
  if (n.loose_bvar_range <= p) { if (lbr_out) *lbr_out = n.loose_bvar_range; if (flags_out) *flags_out = n.flags | tmp_t; return n.hash; }
  u32 m = (u32)envs[env].size();
  switch (n.kind) {
    case EKind::BVar: {
      u32 i = n.a;
      if (i - p < m) {
        Expr ent = envs[env][i - p];
        const ExprNode& en = nodes[ent];
        if (lbr_out) *lbr_out = 0;
        if (flags_out) *flags_out = en.flags | ((frozen && ent >= wm_nodes) ? 0x80 : 0);
        return en.hash;
      }
      if (lbr_out) *lbr_out = i - m + 1; if (flags_out) *flags_out = 0; return hk(EKind::BVar, i - m);
    }
    case EKind::Clos: {
      Expr c = mk_clos(t, env, p);
      if (lbr_out) *lbr_out = nodes[c].loose_bvar_range;
      if (flags_out) *flags_out = nodes[c].flags | ((frozen && c >= wm_nodes) ? 0x80 : 0);
      return nodes[c].hash;
    }
    default: break;
  }
  u64 k = mix(mix(t, p), env ^ (g_memo_gen << 32));
  size_t slot = k & ((1 << MEMO_BITS) - 1);
  if (g_hmemo.key[slot] == k) { if (lbr_out) *lbr_out = g_hmemo.lbr[slot]; if (flags_out) *flags_out = g_hmemo.fl[slot]; return g_hmemo.val[slot]; }
  u64 h; u32 l = 0, l1, l2, l3; u8 f = 0, f1 = 0, f2 = 0, f3 = 0;
  switch (n.kind) {
    case EKind::App: h = hk(EKind::App, mix(sem_hash(n.a, env, p, &l1, &f1), sem_hash(n.b, env, p, &l2, &f2))); l = std::max(l1, l2); f = f1 | f2; break;
    case EKind::Lam: case EKind::Pi:
      h = hk(n.kind, mix(sem_hash(n.a, env, p, &l1, &f1), sem_hash(n.b, env, p + 1, &l2, &f2))); l = std::max(l1, l2 > 0 ? l2 - 1 : 0); f = f1 | f2; break;
    case EKind::Let:
      h = hk(EKind::Let, mix(mix(sem_hash(n.a, env, p, &l1, &f1), sem_hash(n.b, env, p, &l2, &f2)), sem_hash(n.c, env, p + 1, &l3, &f3)));
      l = std::max({l1, l2, l3 > 0 ? l3 - 1 : 0}); f = f1 | f2 | f3; break;
    case EKind::Proj: h = hk(EKind::Proj, mix(mix((*g_names)[n.name].hash, n.a), sem_hash(n.b, env, p, &l1, &f1))); l = l1; f = f1; break;
    default: h = n.hash; l = n.loose_bvar_range; f = n.flags | tmp_t; break;
  }
  g_hmemo.key[slot] = k; g_hmemo.val[slot] = h; g_hmemo.lbr[slot] = l; g_hmemo.fl[slot] = f;
  if (lbr_out) *lbr_out = l; if (flags_out) *flags_out = f;
  return h;
}

namespace {
struct View { Expr t; u32 env; u32 p; bool clos; };   // clos=false: a plain handle
// Resolve a view to a node that the substitution does not rewrite at its root.
View resolve(ExprTable& T, View v) {
  while (true) {
    const ExprNode& n = T.nodes[v.t];
    if (!v.clos) {
      if (n.kind != EKind::Clos) return v;
      v = View{n.a, n.b, n.c, true}; continue;
    }
    if (n.loose_bvar_range <= v.p) return View{v.t, 0, 0, false};
    if (n.kind == EKind::BVar) {
      const std::vector<Expr>& E = T.envs[v.env]; u32 i = n.a, m = (u32)E.size();
      if (i - v.p < m) { v = View{E[i - v.p], 0, 0, false}; continue; }
      return View{mk_bvar(i - m), 0, 0, false};
    }
    if (n.kind == EKind::Clos) { Expr c = mk_clos(v.t, v.env, v.p); v = View{c, 0, 0, false}; continue; }
    return v;
  }
}
bool view_eq(ExprTable& T, View x, View y) {
  x = resolve(T, x); y = resolve(T, y);
  if (!x.clos && !y.clos) return x.t == y.t;          // interned nodes are canonical
  if (x.clos && y.clos && x.t == y.t && x.env == y.env && x.p == y.p) return true;
  const ExprNode a = T.nodes[x.t], b = T.nodes[y.t];  // copies: the table may grow below
  if (a.kind != b.kind) return false;
  u64 k = mix(mix(mix(((u64)x.t << 32) | y.t, ((u64)x.p << 32) | y.p), ((u64)x.env << 32) | y.env), g_memo_gen);
  size_t slot = k & ((1 << MEMO_BITS) - 1);
  if (g_eqmemo.key[slot] == k) return true;            // only positive results are remembered
  bool r;
  auto sub = [&](Expr xt, Expr yt, u32 dp) { return view_eq(T, View{xt, x.env, x.p + dp, x.clos}, View{yt, y.env, y.p + dp, y.clos}); };
  switch (a.kind) {
    case EKind::App: r = sub(a.a, b.a, 0) && sub(a.b, b.b, 0); break;
    case EKind::Lam: case EKind::Pi: r = sub(a.a, b.a, 0) && sub(a.b, b.b, 1); break;
    case EKind::Let: r = sub(a.a, b.a, 0) && sub(a.b, b.b, 0) && sub(a.c, b.c, 1); break;
    case EKind::Proj: r = a.name == b.name && a.a == b.a && sub(a.b, b.b, 0); break;
    case EKind::BVar: r = a.a == b.a; break;             // both untouched (i < p on each side)
    case EKind::Const: r = a.name == b.name && a.lvls == b.lvls; break;
    default: r = a.a == b.a && a.b == b.b && a.c == b.c; break;
  }
  if (r) g_eqmemo.key[slot] = k;
  return r;
}
}

bool ExprTable::sem_eq(Expr x, Expr y) {
  if (x == y) return true;
  const ExprNode& a = nodes[x]; const ExprNode& b = nodes[y];
  if (a.kind == EKind::Clos && b.kind == EKind::Clos && a.a == b.a && a.b == b.b && a.c == b.c) return true;   // same closure
  return view_eq(*this, View{x, 0, 0, false}, View{y, 0, 0, false});
}


Expr mk_clos(Expr t, u32 env, u32 p) {
  const ExprNode nt = g_exprs->raw(t);   // copy: the tables may grow below
  u32 lt = nt.loose_bvar_range;
  if (lt <= p) return t;                                   // nothing to substitute
  u32 m = (u32)g_exprs->envs[env].size();
  if (nt.kind == EKind::BVar) {
    u32 i = nt.a;                                          // i >= p
    return i - p < m ? g_exprs->envs[env][i - p] : mk_bvar(i - m);
  }
  if (nt.kind == EKind::Clos) {
    // compose: inner Clos(t', E', p') under (E, p).  Representable when p <= p' <= p+|E|:
    // the inner prefix positions [p, p') become the entries E[0..p'-p), then E', then the
    // rest of E.  Otherwise materialise the inner closure first.
    u32 p2 = nt.c; u32 env2 = nt.b;
    if (p <= p2 && p2 <= p + m) {
      const std::vector<Expr> E = g_exprs->envs[env], E2 = g_exprs->envs[env2];   // copies
      std::vector<Expr> parts; parts.reserve(m + E2.size());
      for (u32 i = 0; i < p2 - p; i++) parts.push_back(E[i]);
      for (Expr x : E2) parts.push_back(x);
      for (u32 i = p2 - p; i < m; i++) parts.push_back(E[i]);
      u32 env3 = g_exprs->mk_env_concat(parts);
      g_cnt_clos_compose++;
      return mk_clos(nt.a, env3, p);
    }
    g_cnt_clos_expand++;
    return mk_clos(expand_closures(t), env, p);
  }
  g_cnt_clos++;
  u32 lbr = 0; u8 fl = 0;
  u64 h = g_exprs->sem_hash(t, env, p, &lbr, &fl);   // exact range and flags of the expansion (has_fvar must not over-approximate)
  return g_exprs->intern(ExprNode{EKind::Clos, BInfo::Default, fl, lbr, t, env, p, NIL, NIL, (u32)h});
}

Expr ExprTable::expose(Expr e) {
  // The closure node is rewritten in place into the root of its expansion (children are
  // closures again, or plain terms).  Its hash is unchanged, being the hash of the expansion,
  // so the intern table stays consistent and the handle keeps denoting the same term.
  g_cnt_expose++;
  const ExprNode n = nodes[e];                              // copy: the table may reallocate below
  if (n.kind != EKind::Clos) return e;
  const ExprNode t = nodes[n.a];
  ExprNode r;
  switch (t.kind) {
    case EKind::App: r = node_app(mk_clos(t.a, n.b, n.c), mk_clos(t.b, n.b, n.c)); break;
    case EKind::Lam: case EKind::Pi: r = node_binding(t.kind, t.name, mk_clos(t.a, n.b, n.c), mk_clos(t.b, n.b, n.c + 1), t.binfo); break;
    case EKind::Let: r = node_let(t.name, mk_clos(t.a, n.b, n.c), mk_clos(t.b, n.b, n.c), mk_clos(t.c, n.b, n.c + 1)); break;
    case EKind::Proj: r = node_proj(t.name, t.a, mk_clos(t.b, n.b, n.c)); break;
    default: fail("expose: malformed closure node");
  }
  if (r.hash != n.hash || r.loose_bvar_range != n.loose_bvar_range) {
    u32 l2 = 0; u64 h2 = sem_hash(n.a, n.b, n.c, &l2);
    fail("expose: expansion disagrees with the closure node: kind " + std::to_string((int)t.kind) + " p=" + std::to_string(n.c) +
         " |E|=" + std::to_string(envs[n.b].size()) + " lbr(t)=" + std::to_string(t.loose_bvar_range) +
         " node hash/lbr " + std::to_string(n.hash) + "/" + std::to_string(n.loose_bvar_range) +
         " expansion " + std::to_string(r.hash) + "/" + std::to_string(r.loose_bvar_range) +
         " recomputed " + std::to_string(h2) + "/" + std::to_string(l2) + " children lbr " + std::to_string(nodes[r.a].loose_bvar_range) + "," + std::to_string(nodes[r.b].loose_bvar_range) +
         " child kinds " + std::to_string((int)nodes[r.a].kind) + "," + std::to_string((int)nodes[r.b].kind));
  }
  nodes[e] = r;
  return e;
}

Expr mk_apps(Expr f, const std::vector<Expr>& args) { for (Expr a : args) f = mk_app(f, a); return f; }
Expr mk_apps(Expr f, const Expr* args, size_t n) { for (size_t i = 0; i < n; i++) f = mk_app(f, args[i]); return f; }
Expr mk_apps_range(Expr f, const std::vector<Expr>& args, size_t lo, size_t hi) {
  for (size_t i = lo; i < hi; i++) f = mk_app(f, args[i]); return f;
}

Expr get_app_fn(Expr e) { while (is_app(e)) e = app_fn(e); return e; }
unsigned get_app_num_args(Expr e) { unsigned n = 0; while (is_app(e)) { e = app_fn(e); n++; } return n; }
void get_app_args(Expr e, std::vector<Expr>& args) { get_app_args_fn(e, args); }
Expr get_app_args_fn(Expr e, std::vector<Expr>& args) {
  args.clear();
  while (is_app(e)) { args.push_back(app_arg(e)); e = app_fn(e); }
  std::reverse(args.begin(), args.end());
  return e;
}

// ---- Generic traversal with memoization on (expr, offset) -------------------------------

namespace {
struct ReplaceCache {
  std::unordered_map<u64, Expr> m;
  bool get(Expr e, u32 off, Expr& r) const {
    auto it = m.find(((u64)e << 32) | off); if (it == m.end()) return false; r = it->second; return true;
  }
  void put(Expr e, u32 off, Expr r) { m.emplace(((u64)e << 32) | off, r); }
};

// f(e, offset) returns NIL to recurse, or the replacement.
template <class F>
Expr replace_rec(Expr e, u32 off, F& f, ReplaceCache& cache) {
  Expr r;
  if (cache.get(e, off, r)) return r;
  r = f(e, off);
  if (r == NIL) {
    // A closure handle is rebuilt from its exposed node, so the result never contains it.
    Expr self = is_clos(e) ? g_exprs->expose(e) : e;
    const ExprNode n = ex(e);   // copy: the node table may reallocate during recursion
    switch (n.kind) {
      case EKind::App: {
        Expr a = replace_rec(n.a, off, f, cache), b = replace_rec(n.b, off, f, cache);
        r = (a == n.a && b == n.b) ? self : mk_app(a, b); break;
      }
      case EKind::Lam: case EKind::Pi: {
        Expr a = replace_rec(n.a, off, f, cache), b = replace_rec(n.b, off + 1, f, cache);
        r = (a == n.a && b == n.b) ? self : (n.kind == EKind::Lam ? mk_lam(n.name, a, b, n.binfo) : mk_pi(n.name, a, b, n.binfo)); break;
      }
      case EKind::Let: {
        Expr a = replace_rec(n.a, off, f, cache), b = replace_rec(n.b, off, f, cache), c = replace_rec(n.c, off + 1, f, cache);
        r = (a == n.a && b == n.b && c == n.c) ? self : mk_let(n.name, a, b, c); break;
      }
      case EKind::Proj: {
        Expr b = replace_rec(n.b, off, f, cache);
        r = (b == n.b) ? self : mk_proj(n.name, n.a, b); break;
      }
      default: r = self;
    }
  }
  cache.put(e, off, r);
  return r;
}
template <class F> Expr replace(Expr e, F f) { ReplaceCache c; return replace_rec(e, 0, f, c); }
} // namespace

Expr replace_expr(Expr e, const std::function<Expr(Expr, u32)>& f) { return replace(e, f); }

Expr lift_loose_bvars(Expr e, u32 s, u32 d) {
  if (d == 0 || loose_bvar_range(e) <= s) return e;
  return replace(e, [&](Expr x, u32 off) -> Expr {
    u32 s1 = s + off;
    if (loose_bvar_range(x) <= s1) return x;
    if (is_bvar(x)) return mk_bvar(bvar_idx(x) + d);
    return NIL;
  });
}

Expr lower_loose_bvars(Expr e, u32 s, u32 d) {
  if (d == 0 || loose_bvar_range(e) <= s) return e;
  return replace(e, [&](Expr x, u32 off) -> Expr {
    u32 s1 = s + off;
    if (loose_bvar_range(x) <= s1) return x;
    if (is_bvar(x)) return mk_bvar(bvar_idx(x) - d);
    return NIL;
  });
}

// bvar i (i < n) at depth off -> lift(subst[i], off)
Expr instantiate_eager(Expr e, size_t n, const Expr* subst) {
  if (n == 0 || !has_loose_bvars(e)) return e;
  return replace(e, [&](Expr x, u32 off) -> Expr {
    if (loose_bvar_range(x) <= off) return x;
    if (is_bvar(x)) {
      u32 i = bvar_idx(x);
      if (i < off) return x;
      if (i - off < n) return lift_loose_bvars(subst[i - off], 0, off);
      return mk_bvar(i - (u32)n);
    }
    return NIL;
  });
}

Expr instantiate_rev_eager(Expr e, size_t n, const Expr* subst) {
  if (n == 0 || !has_loose_bvars(e)) return e;
  return replace(e, [&](Expr x, u32 off) -> Expr {
    if (loose_bvar_range(x) <= off) return x;
    if (is_bvar(x)) {
      u32 i = bvar_idx(x);
      if (i < off) return x;
      if (i - off < n) return lift_loose_bvars(subst[n - 1 - (i - off)], 0, off);
      return mk_bvar(i - (u32)n);
    }
    return NIL;
  });
}

static bool all_closed(size_t n, const Expr* subst) {
  for (size_t i = 0; i < n; i++) if (has_loose_bvars(subst[i])) return false;
  return true;
}
// With closed entries the substitution is suspended in a Clos node: O(1) now, and later
// paid only for the parts of the term that are actually looked at.
static const bool g_lazy_subst = !getenv("LL_LAZY") || atoi(getenv("LL_LAZY")) != 0;   // LL_LAZY=0: always substitute eagerly
Expr instantiate(Expr e, size_t n, const Expr* subst) {
  if (n == 0 || !has_loose_bvars(e)) return e;
  if (!g_lazy_subst || !g_exprs->frozen || !all_closed(n, subst)) return instantiate_eager(e, n, subst);
  return mk_clos(e, g_exprs->mk_env(subst, n, false), 0);
}
Expr instantiate_rev(Expr e, size_t n, const Expr* subst) {
  if (n == 0 || !has_loose_bvars(e)) return e;
  if (!g_lazy_subst || !g_exprs->frozen || !all_closed(n, subst)) return instantiate_rev_eager(e, n, subst);
  return mk_clos(e, g_exprs->mk_env(subst, n, true), 0);
}

Expr expand_closures(Expr e) {
  return replace(e, [&](Expr x, u32) -> Expr { return NIL; });
}
Expr canon(Expr e) { return e; }   // interned handles are canonical modulo materialisation

Expr instantiate_range_rev(Expr e, const std::vector<Expr>& subst, size_t lo, size_t hi) {
  return instantiate_rev(e, hi - lo, subst.data() + lo);
}

Expr abstract_fvars(Expr e, size_t n, const Expr* fvars) {
  if (n == 0 || !has_fvar(e)) return e;
  return replace(e, [&](Expr x, u32 off) -> Expr {
    if (!has_fvar(x)) return x;
    if (is_fvar(x)) {
      for (size_t i = n; i-- > 0;) if (fvars[i] == x) return mk_bvar(off + (u32)(n - 1 - i));
      return x;
    }
    return NIL;
  });
}

// A reusable map Expr -> Expr for one instantiation at a time: open addressing with generation
// stamps, so starting a new instantiation costs nothing and nothing is allocated per entry.
namespace {
struct FlatMemo {
  std::vector<Expr> key, val; std::vector<u32> stamp; u32 gen = 0; size_t used = 0;
  void begin() {
    if (key.empty()) { key.assign(1024, 0); val.assign(1024, 0); stamp.assign(1024, 0); }
    if (++gen == 0) { std::fill(stamp.begin(), stamp.end(), 0); gen = 1; }
    used = 0;
  }
  bool get(Expr k, Expr& v) const {
    size_t mask = key.size() - 1, i = (size_t)mix(k, 0x51) & mask;
    while (stamp[i] == gen) { if (key[i] == k) { v = val[i]; return true; } i = (i + 1) & mask; }
    return false;
  }
  void put(Expr k, Expr v) {
    if ((used + 1) * 2 > key.size()) grow();
    size_t mask = key.size() - 1, i = (size_t)mix(k, 0x51) & mask;
    while (stamp[i] == gen) { if (key[i] == k) { val[i] = v; return; } i = (i + 1) & mask; }
    stamp[i] = gen; key[i] = k; val[i] = v; used++;
  }
  void grow() {
    std::vector<Expr> k2, v2; std::vector<u32> s2;
    size_t n = key.size() * 2;
    k2.assign(n, 0); v2.assign(n, 0); s2.assign(n, 0);
    for (size_t j = 0; j < key.size(); j++) if (stamp[j] == gen) {
      size_t i = (size_t)mix(key[j], 0x51) & (n - 1);
      while (s2[i] == gen) i = (i + 1) & (n - 1);
      s2[i] = gen; k2[i] = key[j]; v2[i] = val[j];
    }
    key.swap(k2); val.swap(v2); stamp.swap(s2);
  }
};
struct LParamInst {
  const std::vector<Name>& ps; const std::vector<Level>& ls; FlatMemo& memo;
  Expr go(Expr x) {
    if (!has_lparam(x)) return x;   // nothing below here mentions a universe parameter
    Expr r;
    if (memo.get(x, r)) return r;
    Expr self = is_clos(x) ? g_exprs->expose(x) : x;
    const ExprNode n = ex(x);   // copy: interning below may grow the node table
    r = self;
    switch (n.kind) {
      case EKind::Sort: r = mk_sort(instantiate_level_params(n.a, ps, ls)); break;
      case EKind::Const: {
        const std::vector<Level> lst = g_levels->list(n.lvls);
        std::vector<Level> nl; nl.reserve(lst.size());
        bool ch = false;
        for (Level l : lst) { Level l2 = instantiate_level_params(l, ps, ls); ch |= (l2 != l); nl.push_back(l2); }
        if (ch) r = mk_const(n.name, g_levels->mk_list(nl));
        break;
      }
      case EKind::App: { Expr a = go(n.a), b = go(n.b); r = (a == n.a && b == n.b) ? self : mk_app(a, b); break; }
      case EKind::Lam: case EKind::Pi: {
        Expr a = go(n.a), b = go(n.b);
        r = (a == n.a && b == n.b) ? self : (n.kind == EKind::Lam ? mk_lam(n.name, a, b, n.binfo) : mk_pi(n.name, a, b, n.binfo)); break;
      }
      case EKind::Let: { Expr a = go(n.a), b = go(n.b), c = go(n.c); r = (a == n.a && b == n.b && c == n.c) ? self : mk_let(n.name, a, b, c); break; }
      case EKind::Proj: { Expr b = go(n.b); r = (b == n.b) ? self : mk_proj(n.name, n.a, b); break; }
      default: break;
    }
    memo.put(x, r);
    return r;
  }
};
thread_local FlatMemo g_lparam_memo;
unsigned g_lparam_depth = 0;
}

Expr instantiate_lparams(Expr e, const std::vector<Name>& ps, const std::vector<Level>& ls) {
  if (ps.empty() || !has_lparam(e)) return e;
  // Instantiating a declaration's parameters by themselves changes nothing.
  if (ps.size() == ls.size()) {
    bool same = true;
    for (size_t i = 0; i < ps.size() && same; i++) same = ls[i] == mk_param(ps[i]);
    if (same) return e;
  }
  // Level instantiation can re-enter itself through an equality test while interning; the
  // shared memo serves only the outermost call, and a nested one gets a memo of its own.
  if (g_lparam_depth > 0) { FlatMemo m; m.begin(); LParamInst in{ps, ls, m}; return in.go(e); }
  g_lparam_depth++;
  g_lparam_memo.begin();
  LParamInst in{ps, ls, g_lparam_memo};
  Expr r = in.go(e);
  g_lparam_depth--;
  return r;
}

Expr head_beta(Expr e) {
  if (!is_app(e) || !is_lam(get_app_fn(e))) return e;
  std::vector<Expr> args;
  Expr f = get_app_args_fn(e, args);
  size_t i = 0;
  while (is_lam(f) && i < args.size()) { f = binding_body(f); i++; }
  f = instantiate_rev(f, i, args.data());
  return head_beta(mk_apps_range(f, args, i, args.size()));
}

// Lean's cheapBetaReduce: beta-reduce the head only when the body has no loose bvars beyond
// the parameters, i.e. when it can be done by a simple instantiate. We use head_beta.
Expr cheap_beta_reduce(Expr e) { return head_beta(e); }

bool occurs_const(Expr e, Name c) {
  bool found = false;
  std::unordered_map<Expr, bool> seen;
  std::function<void(Expr)> go = [&](Expr x) {
    if (found || seen.count(x)) return;
    seen.emplace(x, true);
    const ExprNode n = ex(x);
    switch (n.kind) {
      case EKind::Const: if (n.name == c) found = true; break;
      case EKind::App: case EKind::Lam: case EKind::Pi: go(n.a); go(n.b); break;
      case EKind::Let: go(n.a); go(n.b); go(n.c); break;
      case EKind::Proj: go(n.b); break;
      default: break;
    }
  };
  go(e);
  return found;
}

std::string expr_str(Expr e) {
  const ExprNode n = ex(e);
  switch (n.kind) {
    case EKind::BVar: return "#" + std::to_string(n.a);
    case EKind::FVar: return "$" + std::to_string(n.a);
    case EKind::Sort: return "Sort(" + level_str(n.a) + ")";
    case EKind::Const: {
      std::string s = name_str(n.name);
      const std::vector<Level> ls = g_levels->list(n.lvls);
      if (!ls.empty()) { s += ".{"; for (size_t i = 0; i < ls.size(); i++) s += (i ? ", " : "") + level_str(ls[i]); s += "}"; }
      return s;
    }
    case EKind::App: return "(" + expr_str(n.a) + " " + expr_str(n.b) + ")";
    case EKind::Lam: return "(fun (" + name_str(n.name) + " : " + expr_str(n.a) + ") => " + expr_str(n.b) + ")";
    case EKind::Pi: return "((" + name_str(n.name) + " : " + expr_str(n.a) + ") -> " + expr_str(n.b) + ")";
    case EKind::Let: return "(let " + name_str(n.name) + " : " + expr_str(n.a) + " := " + expr_str(n.b) + "; " + expr_str(n.c) + ")";
    case EKind::Lit: return is_nat_lit(e) ? nat_lit_val(e).get_str() : "\"" + str_lit_val(e) + "\"";
    case EKind::Proj: return expr_str(n.b) + "." + std::to_string(n.a);
  }
  return "?";
}

} // namespace ll
