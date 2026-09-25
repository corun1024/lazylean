// Normalisation-by-evaluation checking engine (see nbe.h).
//
// Values
//   Neu   a head -- a bound variable (a de Bruijn *level*, carrying its type), or a constant
//         with its universe levels -- and a spine of eliminations (arguments and projections),
//         oldest first when read back.  A constant head stays folded: a definition is unfolded
//         only when conversion or a recursor asks for it (lazy delta), and the unfolding is
//         memoised in the value itself.
//   Lam   a closure: binder-type term, environment, body term.
//   Pi    a domain value and a closure.  A Pi built by type inference for a lambda has an
//         *inference* closure (`pinf`): its body is the lambda's body, and instantiating it
//         infers the type of that body rather than evaluating it.
//   Sort, Nat and String literals.
// Environments are cons lists of values, hash-consed, carrying the level substitution of the
// constant being unfolded (if any) at their root.  Neutral applications are hash-consed by
// (function, argument), so equal neutrals built the same way are the same pointer.
//
// Everything lives in a bump arena for a session of many declarations.  Caches are keyed by
// value and environment pointers and by permanent term handles; all of them stay valid for the
// session, because the environment only grows and a value's meaning does not depend on where it
// is used (a fresh variable is identified by its level and its type).
#include "nbe.h"
#include <gmpxx.h>
#include <deque>
#include <cstring>
#include <iostream>
#include <algorithm>
#include <chrono>
#include <sys/mman.h>

namespace ll {

bool g_nbe = !getenv("LL_NBE") || atoi(getenv("LL_NBE")) != 0;

namespace {

[[noreturn]] void nfail(const char* why) { throw NbeFail{why}; }

// Large regions come straight from mmap with a huge-page hint, and are kept for the whole run:
// a session reset zeroes and reuses them, so the kernel's page-fault work is paid once.
void* big_alloc(size_t bytes) {
  // 2 MB aligned, so that the whole region can be backed by huge pages
  const size_t H = (size_t)2 << 20;
  bytes = (bytes + H - 1) & ~(H - 1);
  char* p = (char*)mmap(nullptr, bytes + H, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (p == MAP_FAILED) { std::cerr << "nbe: out of memory\n"; abort(); }
  char* a = (char*)(((uintptr_t)p + H - 1) & ~(uintptr_t)(H - 1));
  if (a > p) munmap(p, a - p);
  if (a + bytes < p + bytes + H) munmap(a + bytes, (p + bytes + H) - (a + bytes));
  madvise(a, bytes, MADV_HUGEPAGE);
  static const bool populate = !getenv("LL_NBE_NOPOPULATE");
  if (populate) madvise(a, bytes, MADV_POPULATE_WRITE);   // fault it all in with one call
  return a;
}
void big_free(void* p, size_t bytes) { const size_t H = (size_t)2 << 20; if (p) munmap(p, (bytes + H - 1) & ~(H - 1)); }

// ---------------------------------------------------------------- small utilities

template <class T, size_t K> struct SVec {   // trivially copyable T
  T inl[K]; T* p = inl; size_t n = 0, cap = K;
  SVec() = default; SVec(const SVec&) = delete; SVec& operator=(const SVec&) = delete;
  ~SVec() { if (p != inl) free(p); }
  void push(T x) { if (n == cap) grow(); p[n++] = x; }
  void grow() { size_t nc = cap * 2; T* q = (T*)malloc(nc * sizeof(T)); memcpy(q, p, n * sizeof(T)); if (p != inl) free(p); p = q; cap = nc; }
  T& operator[](size_t i) { return p[i]; }
  size_t size() const { return n; }
  T* data() { return p; }
  void reverse() { std::reverse(p, p + n); }
};

struct Arena {
  static constexpr size_t BLOCK = (size_t)32 << 20;
  std::vector<char*> blocks; size_t idx = 0; uintptr_t cur = 0, end = 0;
  std::vector<void*> big; size_t bytes = 0;
  void* alloc(size_t n) {
    n = (n + 7) & ~(size_t)7;
    if (__builtin_expect(cur + n > end, 0)) return slow(n);
    void* p = (void*)cur; cur += n; return p;
  }
  void* slow(size_t n) {
    if (n > BLOCK / 8) { void* p = malloc(n); big.push_back(p); bytes += n; return p; }
    char* b;
    if (idx < blocks.size()) b = blocks[idx++];
    else { b = (char*)big_alloc(BLOCK); blocks.push_back(b); idx = blocks.size(); }
    cur = (uintptr_t)b; end = cur + BLOCK; bytes += BLOCK;
    void* p = (void*)cur; cur += n; return p;
  }
  void reset() {
    for (void* p : big) free(p);
    big.clear(); idx = 0; cur = end = 0; bytes = 0;
  }
  template <class T> T* make() { return new (alloc(sizeof(T))) T(); }
};

// Open-addressing map keyed by a pair of u64 (first component never 0).
template <class V> struct PMap {
  // Open addressing with linear probing.
  struct S { u64 a, b; V v; };
  S* t = nullptr; size_t mask = 0, n = 0, gen = 0;   // gen: bumped when the table moves
  static size_t hs(u64 a, u64 b) {
    u64 h = (a ^ (b * 0x9E3779B97F4A7C15ull)) * 0xBF58476D1CE4E5B9ull;
    return (size_t)(h ^ (h >> 29));
  }
  static constexpr size_t BIG = 1 << 16;   // slots; tables at least this large live in mmap'd memory
  static S* alloc_tab(size_t nc) { return nc >= BIG ? (S*)big_alloc(nc * sizeof(S)) : (S*)calloc(nc, sizeof(S)); }
  static void free_tab(S* p, size_t nc) { if (!p) return; if (nc >= BIG) big_free(p, nc * sizeof(S)); else free(p); }
  ~PMap() { free_tab(t, t ? mask + 1 : 0); }
  V* find(u64 a, u64 b) {
    if (!n) return nullptr;
    size_t i = hs(a, b) & mask;
    while (true) {
      S& s = t[i];
      if (s.a == a && s.b == b) return &s.v;
      if (s.a == 0) return nullptr;
      i = (i + 1) & mask;
    }
  }
  void grow() {
    size_t oc = t ? mask + 1 : 0, nc = oc ? oc * 2 : 256;
    S* old = t; t = alloc_tab(nc); mask = nc - 1; gen++;
    for (size_t j = 0; j < oc; j++) if (old[j].a) {
      size_t i = hs(old[j].a, old[j].b) & mask;
      while (t[i].a) i = (i + 1) & mask;
      t[i] = old[j];
    }
    free_tab(old, oc);
  }
  V& put(u64 a, u64 b, V v) {
    if (!t || (n + 1) * 2 > mask + 1) grow();
    size_t i = hs(a, b) & mask;
    while (true) {
      S& s = t[i];
      if (s.a == a && s.b == b) { s.v = v; return s.v; }
      if (s.a == 0) { s.a = a; s.b = b; s.v = v; n++; return s.v; }
      i = (i + 1) & mask;
    }
  }
  // Find the entry for (a, b), or create it (value zeroed) if absent; `created` says which.
  // The pointer is valid until the next insertion.
  V* slot(u64 a, u64 b, bool& created) {
    if (!t || (n + 1) * 2 > mask + 1) grow();
    size_t i = hs(a, b) & mask;
    while (true) {
      S& s = t[i];
      if (s.a == a && s.b == b) { created = false; return &s.v; }
      if (s.a == 0) { s.a = a; s.b = b; s.v = V{}; n++; created = true; return &s.v; }
      i = (i + 1) & mask;
    }
  }
  // Empty the map, keeping its table (zeroing is a string store: cheap in instructions).
  void clear() {
    if (!t || !n) return;
    memset(t, 0, (mask + 1) * sizeof(S)); n = 0;
  }
  size_t size() const { return n; }
};

constexpr u64 HI = 1ull << 63;   // tags integer keys so that they are never 0 and never a pointer

// ---------------------------------------------------------------- values

enum : u8 { V_NEU, V_LAM, V_PI, V_SORT, V_NAT, V_STR };
enum : u8 { H_BVAR, H_AXIOM, H_CTOR, H_INDUCT, H_REC, H_QUOT, H_DEF };

struct Val; struct Env; struct LSub;

// Eliminations: an argument (a Val*, even) or a projection (odd: name and field index).
struct Spine { Spine* prev; u64 e; u32 len; u32 nproj; };
inline bool is_proj_elim(u64 e) { return e & 1; }
inline u64 proj_code(Name s, u32 idx) { return ((u64)idx << 33) | ((u64)s << 1) | 1; }
inline Name proj_name(u64 e) { return (Name)((e >> 1) & 0xffffffffu); }
inline u32 proj_idx(u64 e) { return (u32)(e >> 33); }

struct Val {
  u8 k, hk, pinf, pad;
  u32 a;   // Neu: constant name or bvar level; Sort: level; Str: string index
  union {
    struct { LevelList ls; Spine* sp; Val* bty; Val* red; Val* whnf; } n;
    struct { Expr dom; Env* env; Expr body; Val* domv; } lam;
    struct { Val* dom; Env* env; Expr body; Expr dome; } pi;   // dom: evaluated from dome on demand
    struct { const mpz_class* v; } nat;
  };
};

struct LSub { std::vector<Name> ps; std::vector<Level> vs; Env* root; };

// An environment is a cons list (frame == 0), or a frame (frame == 1): the values of just the
// variables a term uses, at the positions `mask` gives them, looked up by their original index.
// Caches are keyed by frames, so a term's evaluation is shared by every context that agrees on
// the variables it mentions.  `pm`/`pr` memoise the last pruning of this environment.
struct Env { Env* parent; Val* v; LSub* ls; u32 len; u32 frame; u64 mask; u64 pm; Env* pr; };

Val g_stuck_obj;
Val* const STUCK = &g_stuck_obj;
Val g_unused;
const u64 g_nbe_budget = getenv("LL_NBE_BUDGET") ? strtoull(getenv("LL_NBE_BUDGET"), nullptr, 10) : 1000000;
u64 s_hist[8] = {0};   // declarations by steps: <1e3, <1e4, .. <1e9, more   // stands for an argument whose variable the term it is bound in never mentions

const ExprNode* g_nodes = nullptr;   // the expression table, fixed while the engine runs
inline const ExprNode& node(Expr e) { return g_nodes[e]; }

// ---------------------------------------------------------------- statistics

u64 s_accept = 0, s_decline = 0, s_steps = 0, s_sessions = 0;
// cache statistics: calls / hits (compiled in with -DLL_NBE_STATS)
#ifdef LL_NBE_STATS
#define KC(x) (x++)
#else
#define KC(x) ((void)0)
#endif
u64 k_eval = 0, k_eval_hit = 0, k_app = 0, k_app_hit = 0, k_env = 0, k_env_hit = 0, k_infer = 0, k_infer_hit = 0,
    k_conv = 0, k_conv_hit = 0, k_whnf = 0, k_step = 0, k_vtype = 0, k_vtype_hit = 0, k_pirr = 0, k_eval_root = 0, k_pirr_static = 0, k_prune_would_hit = 0, k_infer_root = 0, k_const = 0;
std::vector<std::pair<const char*, u64>> s_reasons;
void note_reason(const char* w) {
  for (auto& p : s_reasons) if (p.first == w) { p.second++; return; }
  s_reasons.emplace_back(w, 1);
}

// ---------------------------------------------------------------- the engine

struct Engine {
  const Environment* E = nullptr;
  Arena ar;
  Env* groot = nullptr;
  // session caches
  PMap<Val*> c_head, c_type, c_unfold, c_rule, c_eval, c_env, c_bvar, c_app, c_lit, c_vtype;
  PMap<u32> c_lvl;                 // level / level-list instantiation under an LSub
  PMap<LSub*> c_lsub;
  PMap<u8> c_pos, c_neg, c_isprop;
  struct IEnt { Val* ty; u32 scope; };
  PMap<IEnt> c_infer;
  std::deque<mpz_class> nats;
  std::deque<LSub> lsubs;
  // persistent (not session) caches
  PMap<u32> p_plist, p_norm;
  PMap<u8> p_var0;
  // per declaration
  const std::vector<Name>* lparams = nullptr;
  u32 scope = 1;
  u64 steps = 0, budget = 0;
  u32 depth = 0;
  bool probing = false, exhausted = false; u32 probe_left = 0;

  struct Guard {
    Engine& g;
    explicit Guard(Engine& e) : g(e) { if (++g.depth > 100000) nfail("recursion depth"); }
    ~Guard() { g.depth--; }
  };
  void tick() { if (++steps > budget) nfail("step budget"); }

  void start_session() {
    ar.reset();
    c_head.clear(); c_type.clear(); c_unfold.clear(); c_rule.clear(); c_eval.clear(); c_env.clear();
    c_bvar.clear(); c_app.clear(); c_lit.clear(); c_vtype.clear(); c_lvl.clear(); c_lsub.clear();
    c_pos.clear(); c_neg.clear(); c_isprop.clear(); c_infer.clear(); c_frame.clear(); memset(prune_dm, 0, sizeof(PruneDM) << PRUNE_DM_BITS);
    nats.clear(); lsubs.clear();
    groot = ar.make<Env>();
    s_sessions++;
  }

  // ---------------------------------------------------------------- levels

  Level norm(Level l) {
    if (u32* c = p_norm.find(HI | l, 1)) return *c;
    Level r = normalize(l);
    p_norm.put(HI | l, 1, r);
    return r;
  }
  // l is zero under every assignment of its parameters (exactly: is_zero(normalize(l)))
  static bool lvl_zero(Level l) {
    while (true) {
      const LevelNode& n = lv(l);
      switch (n.kind) {
        case LKind::Zero: return true;
        case LKind::Succ: case LKind::Param: return false;
        case LKind::Max: if (!lvl_zero(n.a)) return false; l = n.b; continue;
        case LKind::IMax: l = n.b; continue;
      }
      return false;
    }
  }
  bool level_eq(Level a, Level b) { return a == b || norm(a) == norm(b); }
  bool levels_eq(LevelList a, LevelList b) {
    if (a == b) return true;
    const std::vector<Level>& x = g_levels->list_ref(a);
    const std::vector<Level>& y = g_levels->list_ref(b);
    if (x.size() != y.size()) return false;
    for (size_t i = 0; i < x.size(); i++) if (!level_eq(x[i], y[i])) return false;
    return true;
  }
  LevelList plist_of(const ConstInfo& c) {
    if (u32* p = p_plist.find(HI | c.name, 2)) return *p;
    std::vector<Level> ls; for (Name n : c.lparams) ls.push_back(mk_param(n));
    LevelList r = g_levels->mk_list(ls);
    p_plist.put(HI | c.name, 2, r);
    return r;
  }
  LSub* lsub_of(const ConstInfo& c, LevelList ls) {
    if (c.lparams.empty()) return nullptr;
    LevelList pl = plist_of(c);
    if (pl == ls) return nullptr;
    if (LSub** p = c_lsub.find(HI | pl, ls)) return *p;
    lsubs.emplace_back();
    LSub* s = &lsubs.back();
    s->ps = c.lparams; s->vs = g_levels->list(ls);
    s->root = ar.make<Env>(); s->root->ls = s;
    c_lsub.put(HI | pl, ls, s);
    return s;
  }
  Level inst_level(LSub* s, Level l) {
    if (!s || !lv(l).has_param) return l;
    if (u32* c = c_lvl.find((u64)s, l)) return *c;
    Level r = instantiate_level_params(l, s->ps, s->vs);
    c_lvl.put((u64)s, l, r);
    return r;
  }
  LevelList inst_levels(LSub* s, LevelList ls) {
    if (!s || !g_levels->list_has_param(ls)) return ls;
    if (u32* c = c_lvl.find((u64)s, HI | ls)) return *c;
    std::vector<Level> v = g_levels->list(ls);
    for (Level& l : v) l = inst_level(s, l);
    LevelList r = g_levels->mk_list(v);
    c_lvl.put((u64)s, HI | ls, r);
    return r;
  }
  void check_level(Level l) {
    if (get_undef_param(l, *lparams) != NIL) nfail("undefined universe parameter");
  }

  // ---------------------------------------------------------------- constructors

  Env* root_of(Env* e) { return e->ls ? e->ls->root : groot; }
  Env* extend(Env* p, Val* v) {
    KC(k_env);
    bool created; Val** c = c_env.slot((u64)p, (u64)v, created);
    if (!created) { KC(k_env_hit); return (Env*)*c; }
    Env* e = (Env*)ar.alloc(sizeof(Env));   // every field is written below
    e->parent = p; e->v = v; e->ls = p->ls; e->len = p->len + 1; e->frame = 0; e->mask = 0; e->pm = 0; e->pr = nullptr;
    *c = (Val*)e;
    return e;
  }
  Val* lookup(Env* e, u32 i) {
    if (i >= e->len) nfail("loose bound variable");
    while (!e->frame) {
      if (i == 0) return e->v;
      i--; e = e->parent;
    }
    if (i >= 64 || !((e->mask >> i) & 1)) nfail("variable outside its frame");
    return ((Val**)e->v)[__builtin_popcountll(e->mask & ((1ull << i) - 1))];
  }

  // ---- pruning
  u64* fvm = nullptr; size_t fvm_n = 0;   // per permanent term: its loose variables (0: not yet computed)
  inline u64 fv_mask(Expr e) {
    if (e < fvm_n && fvm[e]) return fvm[e];
    return fv_mask_slow(e);
  }
  __attribute__((noinline)) u64 fv_mask_slow(Expr e) {
    const ExprNode& n = node(e);
    if (n.loose_bvar_range == 0) return 0;
    if (n.loose_bvar_range > 64 || e >= fvm_n) return ~0ull;
    // ~0 is "unknown" (a subterm with more than 64 loose variables): it stays unknown upward
    auto sh = [](u64 m) { return m == ~0ull ? ~0ull : m >> 1; };
    auto un = [](u64 a, u64 b) { return (a == ~0ull || b == ~0ull) ? ~0ull : a | b; };
    u64 r;
    switch (n.kind) {
      case EKind::BVar: r = 1ull << n.a; break;
      case EKind::App: r = un(fv_mask(n.a), fv_mask(n.b)); break;
      case EKind::Lam: case EKind::Pi: r = un(fv_mask(n.a), sh(fv_mask(n.b))); break;
      case EKind::Let: r = un(un(fv_mask(n.a), fv_mask(n.b)), sh(fv_mask(n.c))); break;
      case EKind::Proj: r = fv_mask(n.b); break;
      default: r = ~0ull;
    }
    fvm[e] = r;
    return r;
  }
  PMap<Env*> c_frame;
  // the environment to key (and evaluate) e under
  Env* key_env(Env* env, Expr e) {
    const ExprNode& n = node(e);
    if (n.loose_bvar_range == 0) return root_of(env);
    u64 m = fv_mask(e);
    if (m == ~0ull) return env;
    if (env->frame ? env->mask == m : (env->len < 64 && m == (1ull << env->len) - 1)) return env;
    if (env->pm == m && env->pr) return env->pr;
    // a direct-mapped cache of recent prunings, for environments under which several subterms
    // with different variable sets are evaluated in turn
    PruneDM& dm = prune_dm[(((u64)env * 0x9E3779B97F4A7C15ull) ^ (m * 0xD6E8FEB86659FD93ull)) >> (64 - PRUNE_DM_BITS)];
    Env* f;
    if (dm.env == env && dm.mask == m) f = dm.frame;
    else { f = prune(env, m); dm.env = env; dm.mask = m; dm.frame = f; }
    env->pm = m; env->pr = f;
    return f;
  }
  static constexpr unsigned PRUNE_DM_BITS = 16;
  struct PruneDM { Env* env; u64 mask; Env* frame; };
  PruneDM* prune_dm = (PruneDM*)calloc((size_t)1 << PRUNE_DM_BITS, sizeof(PruneDM));
  __attribute__((noinline)) Env* prune(Env* env, u64 m) {
    Val* vs[64]; u32 k = 0;
    u64 h = mix((u64)root_of(env), m);
    Env* c = env; u32 off = 0;
    for (u64 mm = m; mm; mm &= mm - 1) {
      u32 i = (u32)__builtin_ctzll(mm);
      while (!c->frame && off < i) { c = c->parent; off++; }
      Val* v = c->frame ? lookup(c, i - off) : c->v;
      if (!c->frame && off != i) nfail("prune");
      vs[k++] = v; h = mix(h, (u64)v);
    }
    bool created; Env** slot = c_frame.slot(h | 1, m, created);
    if (!created) {
      Env* f = *slot;
      if (f->ls == env->ls && memcmp(f->v, vs, k * sizeof(Val*)) == 0) return f;
    }
    Env* f = ar.make<Env>();
    Val** sl = (Val**)ar.alloc(k * sizeof(Val*));
    memcpy(sl, vs, k * sizeof(Val*));
    f->v = (Val*)sl; f->ls = env->ls; f->frame = 1; f->mask = m; f->len = 64 - (u32)__builtin_clzll(m);
    if (created) *slot = f;
    return f;
  }
  Val* mk_sort(Level l) {
    if (Val** c = c_lit.find(HI | l, 3)) return *c;
    Val* v = ar.make<Val>(); v->k = V_SORT; v->a = l;
    c_lit.put(HI | l, 3, v);
    return v;
  }
  Val* mk_nat(mpz_class&& x) {
    nats.push_back(std::move(x));
    Val* v = ar.make<Val>(); v->k = V_NAT; v->nat.v = &nats.back();
    return v;
  }
  Val* lit_val(Expr e, const ExprNode& n) {
    if (Val** c = c_lit.find(HI | e, 4)) return *c;
    Val* v;
    if (n.b == (u32)LitKind::Nat) v = mk_nat(mpz_class(g_exprs->nat_lits[n.a]));
    else { v = ar.make<Val>(); v->k = V_STR; v->a = n.a; }
    c_lit.put(HI | e, 4, v);
    return v;
  }
  Val* mk_lam(Expr dom, Env* env, Expr body) {
    Val* v = ar.make<Val>(); v->k = V_LAM; v->lam.dom = dom; v->lam.env = env; v->lam.body = body;
    return v;
  }
  // A Pi whose domain is evaluated only when something looks at it: instantiating a telescope
  // argument by argument (inferring the type of an application, of a neutral) needs the
  // codomains, and usually not the domains.
  Val* mk_pi_lazy(Expr dome, Env* env, Expr body) {
    Val* v = ar.make<Val>(); v->k = V_PI; v->pi.dome = dome; v->pi.env = env; v->pi.body = body;
    return v;
  }
  Val* pi_dom(Val* p) {
    if (!p->pi.dom) p->pi.dom = eval(p->pi.env, p->pi.dome);
    return p->pi.dom;
  }
  Val* mk_pi(Val* dom, Env* env, Expr body, bool pinf) {
    Val* v = ar.make<Val>(); v->k = V_PI; v->pinf = pinf; v->pi.dom = dom; v->pi.env = env; v->pi.body = body;
    return v;
  }
  Val* fresh(u32 d, Val* ty) {
    if (Val** c = c_bvar.find(HI | d, (u64)ty)) return *c;
    Val* v = ar.make<Val>(); v->k = V_NEU; v->hk = H_BVAR; v->a = d; v->n.bty = ty;
    c_bvar.put(HI | d, (u64)ty, v);
    return v;
  }
  u8 head_kind(const ConstInfo& c) {
    switch (c.kind) {
      case CKind::Def: case CKind::Thm: return H_DEF;
      case CKind::Ctor: return H_CTOR;
      case CKind::Induct: return H_INDUCT;
      case CKind::Rec: return H_REC;
      case CKind::Quot: return (c.name == N.Quot_lift || c.name == N.Quot_ind) ? H_QUOT : H_AXIOM;
      default: return H_AXIOM;
    }
  }
  Val* const_head(Name n, LevelList ls) {
    if (Val** c = c_head.find(HI | n, ls)) return *c;
    const ConstInfo* ci = E->find(n);
    if (!ci) nfail("unknown constant");
    Val* v = ar.make<Val>(); v->k = V_NEU; v->hk = head_kind(*ci); v->a = n; v->n.ls = ls;
    c_head.put(HI | n, ls, v);
    return v;
  }
  Val* neu_app(Val* f, u64 e) {
    KC(k_app);
    bool created; Val** c = c_app.slot((u64)f, e, created);
    if (!created) { KC(k_app_hit); return *c; }
    struct VS { Val v; Spine s; };
    VS* vs = (VS*)ar.alloc(sizeof(VS));   // every field is written below
    Val* v = &vs->v; *c = v;
    Spine* s = &vs->s;
    Spine* fp = f->n.sp;
    s->prev = fp; s->e = e;
    s->len = (fp ? fp->len : 0) + 1;
    s->nproj = (fp ? fp->nproj : 0) + (u32)(e & 1);
    v->k = V_NEU; v->hk = f->hk; v->pinf = 0; v->pad = 0; v->a = f->a;
    v->n.ls = f->n.ls; v->n.sp = s; v->n.bty = f->n.bty; v->n.red = nullptr; v->n.whnf = nullptr;
    return v;
  }
  // eliminations of a spine, oldest first
  template <size_t K> static void elims(Spine* s, SVec<u64, K>& out) {
    for (; s; s = s->prev) out.push(s->e);
    out.reverse();
  }
  // the neutral with the same head and an empty spine
  Val* head_of(Val* v) {
    if (v->hk == H_BVAR) return fresh(v->a, v->n.bty);
    return const_head(v->a, v->n.ls);
  }

  // ---------------------------------------------------------------- evaluation

  Val* eval_inst(Expr e, const ConstInfo& c, LevelList ls) {
    LSub* s = lsub_of(c, ls);
    return eval(s ? s->root : groot, e);
  }

  Val* eval(Env* env, Expr e) {
    const ExprNode& n = node(e);
    switch (n.kind) {
      case EKind::BVar: return lookup(env, n.a);
      case EKind::Sort: return mk_sort(inst_level(env->ls, n.a));
      case EKind::Const: KC(k_const); if (!env->ls) return const_head(n.name, n.lvls); break;
      case EKind::Lit: return lit_val(e, n);
      case EKind::FVar: case EKind::Clos: nfail("unexpected term");
      default: break;
    }
    Env* ke = key_env(env, e);
    KC(k_eval);
    bool created; Val** slotp = c_eval.slot((u64)ke, e, created);
    if (!created && *slotp) { KC(k_eval_hit); return *slotp; }
    return eval_slow(env, e, ke, slotp);
  }
  // the cache missed: evaluate, and fill the reserved slot
#ifdef LL_NBE_STATS
  int ectx = 0; u64 ectx_miss[16] = {0};
  struct ECtx { Engine& g; int s; ECtx(Engine& e, int c) : g(e), s(e.ectx) { if (!g.ectx) g.ectx = c; } ~ECtx() { g.ectx = s; } };
#define ECTX(c) ECtx ectx_guard(*this, c)
#else
#define ECTX(c) ((void)0)
#endif
  __attribute__((noinline)) Val* eval_slow(Env* env, Expr e, Env* ke, Val** slotp) {
    const ExprNode& n = node(e);
    env = ke;
#ifdef LL_NBE_STATS
    ectx_miss[ectx]++;
#endif   // e's variables have the same values there

    size_t gen0 = c_eval.gen;
    Guard g(*this);
    Val* r;
    switch (n.kind) {
      case EKind::App: {
        SVec<Expr, 16> args; Expr f = e;
        while (node(f).kind == EKind::App) { args.push(node(f).b); f = node(f).a; }
        args.reverse();
        Val* fv = eval(env, f);
        size_t i = 0, m = args.size();
        while (i < m) {
          if (fv->k == V_LAM) {
            Env* e2 = extend(fv->lam.env, eval(env, args[i++]));
            Expr body = fv->lam.body;
            while (i < m && node(body).kind == EKind::Lam) { e2 = extend(e2, eval(env, args[i++])); body = node(body).b; }
            fv = eval(e2, body);
          } else fv = apply(fv, eval(env, args[i++]));
        }
        r = fv; break;
      }
      case EKind::Const: r = const_head(n.name, inst_levels(env->ls, n.lvls)); break;
      case EKind::Lam: r = mk_lam(n.a, env, n.b); break;
      case EKind::Pi: r = mk_pi_lazy(n.a, env, n.b); break;
      case EKind::Let: {
        Env* e2 = env; Expr cur = e;
        while (node(cur).kind == EKind::Let) { e2 = extend(e2, eval(e2, node(cur).b)); cur = node(cur).c; }
        r = eval(e2, cur); break;
      }
      case EKind::Proj: r = do_proj(eval(env, n.b), n.name, n.a); break;
      default: nfail("unexpected term");
    }
    if (c_eval.gen == gen0) *slotp = r; else c_eval.put((u64)ke, e, r);
    return r;
  }

  static bool is_nat_binop(Name n) {
    return n == N.Nat_add || n == N.Nat_sub || n == N.Nat_mul || n == N.Nat_pow || n == N.Nat_gcd || n == N.Nat_mod ||
           n == N.Nat_div || n == N.Nat_beq || n == N.Nat_ble || n == N.Nat_land || n == N.Nat_lor || n == N.Nat_xor ||
           n == N.Nat_shiftLeft || n == N.Nat_shiftRight;
  }

  Val* apply(Val* f, Val* a) {
    switch (f->k) {
      case V_LAM: return eval(extend(f->lam.env, a), f->lam.body);
      case V_NEU:
        if (f->hk == H_CTOR && f->a == N.Nat_succ && !f->n.sp && a->k == V_NAT) return mk_nat(mpz_class(*a->nat.v + 1));
        if (f->hk == H_DEF && a->k == V_NAT && f->n.sp && f->n.sp->len == 1 && !f->n.sp->nproj && is_nat_binop(f->a)) {
          Val* x = (Val*)f->n.sp->e;
          if (x->k == V_NAT) { Val* r = nat_binop(f->a, *x->nat.v, *a->nat.v); if (r) return r; }
        }
        return neu_app(f, (u64)a);
      default: nfail("application of a non-function");
    }
  }
  Val* apply_many(Val* f, Val** args, size_t m) {
    size_t i = 0;
    while (i < m) {
      if (f->k == V_LAM) {
        Env* e2 = extend(f->lam.env, args[i++]);
        Expr body = f->lam.body;
        while (i < m && node(body).kind == EKind::Lam) { e2 = extend(e2, args[i++]); body = node(body).b; }
        f = eval(e2, body);
      } else f = apply(f, args[i++]);
    }
    return f;
  }
  // apply eliminations [lo, hi) of `es` to f
  template <size_t K> Val* apply_elims(Val* f, SVec<u64, K>& es, size_t lo, size_t hi) {
    size_t i = lo;
    while (i < hi) {
      if (is_proj_elim(es[i])) { f = do_proj(f, proj_name(es[i]), proj_idx(es[i])); i++; continue; }
      size_t j = i; while (j < hi && !is_proj_elim(es[j])) j++;
      if (j < hi && f->k == V_LAM) {   // arguments, then a projection: maybe only one field is needed
        if (Val* r = apply_proj_field(f, (Val**)&es[i], j - i, proj_name(es[j]), proj_idx(es[j]))) { f = r; i = j + 1; continue; }
      }
      f = apply_many(f, (Val**)&es[i], j - i);
      i = j;
    }
    return f;
  }
  // (fun x1 .. xm => C.mk p1 .. pk f1 .. fn) a1 .. am, projected to field idx of C's structure:
  // evaluate just that field's term.  (The constructor application is beta-reduced and projected,
  // which is what apply_many followed by do_proj computes, without evaluating the other fields.)
  Val* apply_proj_field(Val* f, Val** args, size_t m, Name s, u32 idx) {
    Env* e2 = f->lam.env; Expr body = f->lam.body; size_t i = 0;
    e2 = extend(e2, args[i++]);
    while (i < m && node(body).kind == EKind::Lam) { e2 = extend(e2, args[i++]); body = node(body).b; }
    if (i != m) return nullptr;
    Expr h = body; u32 nargs = 0;
    while (node(h).kind == EKind::App) { h = node(h).a; nargs++; }
    if (node(h).kind != EKind::Const) return nullptr;
    const ConstInfo* ci = E->find(node(h).name);
    if (!ci || ci->kind != CKind::Ctor || ci->induct != s || nargs != ci->nparams + ci->nfields || idx >= ci->nfields) return nullptr;
    if (g_levels->list_size(node(h).lvls) != ci->lparams.size()) return nullptr;
    Expr a = body;
    for (u32 k = nargs - 1; k > ci->nparams + idx; k--) a = node(a).a;
    return eval(e2, node(a).b);
  }
  Val* inst_pi(u32 d, Val* p, Val* a) {   // instantiate a Pi's closure with a (nullptr: body does not use it)
    ECTX(p->pinf ? 7 : 5);
    Env* e2 = a ? extend(p->pi.env, a) : p->pi.env;
    if (!a && node(p->pi.body).loose_bvar_range != 0) nfail("inst_pi without argument");
    if (!p->pinf) return eval(e2, p->pi.body);
    return infer(false, e2, d, p->pi.body);
  }
  Val* lam_dom(Val* l) {
    ECTX(10);
    if (!l->lam.domv) l->lam.domv = eval(l->lam.env, l->lam.dom);
    return l->lam.domv;
  }

  // ---- literals

  Val* nat_binop(Name fn, const mpz_class& a, const mpz_class& b) {
    mpz_class r;
    if (fn == N.Nat_add) r = a + b;
    else if (fn == N.Nat_sub) r = a >= b ? mpz_class(a - b) : mpz_class(0);
    else if (fn == N.Nat_mul) r = a * b;
    else if (fn == N.Nat_pow) { if (b > (1u << 24)) return nullptr; mpz_pow_ui(r.get_mpz_t(), a.get_mpz_t(), b.get_ui()); }
    else if (fn == N.Nat_gcd) mpz_gcd(r.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
    else if (fn == N.Nat_mod) r = b == 0 ? a : mpz_class(a % b);
    else if (fn == N.Nat_div) r = b == 0 ? mpz_class(0) : mpz_class(a / b);
    else if (fn == N.Nat_beq) return const_head(a == b ? N.Bool_true : N.Bool_false, 0);
    else if (fn == N.Nat_ble) return const_head(a <= b ? N.Bool_true : N.Bool_false, 0);
    else if (fn == N.Nat_land) r = a & b;
    else if (fn == N.Nat_lor) r = a | b;
    else if (fn == N.Nat_xor) r = a ^ b;
    else if (fn == N.Nat_shiftLeft) { if (!b.fits_ulong_p() || b > (1u << 26)) return nullptr; mpz_mul_2exp(r.get_mpz_t(), a.get_mpz_t(), b.get_ui()); }
    else if (fn == N.Nat_shiftRight) { if (!b.fits_ulong_p()) r = 0; else mpz_fdiv_q_2exp(r.get_mpz_t(), a.get_mpz_t(), b.get_ui()); }
    else return nullptr;
    return mk_nat(std::move(r));
  }
  // v as a numeral, after reduction: a literal, Nat.zero, or Nat.succ of a numeral
  bool as_nat(u32 d, Val* v, mpz_class& out) {
    unsigned long succs = 0;
    while (true) {
      v = whnf(d, v);
      if (v->k == V_NAT) { out = *v->nat.v; out += succs; return true; }
      if (v->k != V_NEU || v->hk != H_CTOR) return false;
      if (v->a == N.Nat_zero && !v->n.sp) { out = succs; return true; }
      if (v->a == N.Nat_succ && v->n.sp && v->n.sp->len == 1 && !v->n.sp->nproj) { succs++; v = (Val*)v->n.sp->e; continue; }
      return false;
    }
  }
  Val* nat_to_ctor(Val* v) {
    const mpz_class& x = *v->nat.v;
    if (x == 0) return const_head(N.Nat_zero, 0);
    return neu_app(const_head(N.Nat_succ, 0), (u64)mk_nat(mpz_class(x - 1)));
  }
  Val* str_to_ctor(Val* v) {
    const std::string& s = g_exprs->str_lits[v->a];
    std::vector<u32> cps;
    for (size_t i = 0; i < s.size();) {
      unsigned char c = s[i]; u32 cp; int k;
      if (c < 0x80) { cp = c; k = 1; } else if ((c >> 5) == 6) { cp = c & 0x1F; k = 2; }
      else if ((c >> 4) == 14) { cp = c & 0x0F; k = 3; } else { cp = c & 0x07; k = 4; }
      for (int j = 1; j < k && i + j < s.size(); j++) cp = (cp << 6) | (s[i + j] & 0x3F);
      cps.push_back(cp); i += k;
    }
    LevelList l0 = g_levels->mk_list({LZERO});
    Val* charT = const_head(N.Char, 0);
    Val* r = apply(const_head(N.List_nil, l0), charT);
    Val* cons = apply(const_head(N.List_cons, l0), charT);
    Val* ofNat = const_head(N.Char_ofNat, 0);
    for (size_t i = cps.size(); i-- > 0;) r = apply(apply(cons, apply(ofNat, mk_nat(mpz_class(cps[i])))), r);
    return apply(const_head(N.String_ofList, 0), r);
  }

  // ---- projections

  Val* do_proj(Val* v, Name s, u32 idx) {
    ECTX(12);
    if (v->k == V_STR) v = whnf(0, str_to_ctor(v));
    if (v->k != V_NEU) nfail("projection of a non-structure value");
    if (v->hk == H_CTOR && (!v->n.sp || !v->n.sp->nproj)) {
      const ConstInfo* ci = E->find(v->a);
      if (ci && ci->induct == s) {
        u32 len = v->n.sp ? v->n.sp->len : 0;
        u32 want = ci->nparams + idx;
        if (want < len) {
          Spine* sp = v->n.sp;
          for (u32 k = len - 1; k > want; k--) sp = sp->prev;
          return (Val*)sp->e;
        }
      }
    }
    return neu_app(v, proj_code(s, idx));   // stuck, or waiting for its head to reduce
  }

  // ---------------------------------------------------------------- weak-head reduction

  Val* whnf(u32 d, Val* v) {
    if (v->k != V_NEU) return v;
    if (v->n.whnf) return v->n.whnf;
    Val* cur = v;
    while (cur->k == V_NEU) {
      if (cur->n.whnf) { cur = cur->n.whnf; break; }
      Val* r = step(d, cur);
      if (!r) break;
      cur = r;
    }
    v->n.whnf = cur;
    return cur;
  }
  // one head reduction step (delta, iota, quotient), or nullptr
  Val* step(u32 d, Val* v) {
    if (v->hk != H_DEF && v->hk != H_REC && v->hk != H_QUOT) return nullptr;
    if (v->n.red) return v->n.red == STUCK ? nullptr : v->n.red;
    KC(k_step);
    tick();
    Val* r = v->hk == H_DEF ? unfold_nc(d, v) : v->hk == H_REC ? iota_nc(d, v) : quot_nc(d, v);
    v->n.red = r ? r : STUCK;
    return r;
  }
  Val* unfold_const(const ConstInfo& c, LevelList ls) {
    if (Val** p = c_unfold.find(HI | c.name, ls)) return *p;
    Val* v = eval_inst(c.value, c, ls);
    c_unfold.put(HI | c.name, ls, v);
    return v;
  }
  Val* unfold_nc(u32 d, Val* v) {
    if (is_nat_binop(v->a) && v->n.sp && v->n.sp->len == 2 && !v->n.sp->nproj) {
      mpz_class x, y;
      if (as_nat(d, (Val*)v->n.sp->prev->e, x) && as_nat(d, (Val*)v->n.sp->e, y)) {
        if (Val* r = nat_binop(v->a, x, y)) return r;
      }
    }
    const ConstInfo* c = E->find(v->a);
    if (!c || !c->is_delta() || c->lparams.size() != g_levels->list_size(v->n.ls)) return nullptr;
    ECTX(2);
    Val* h = unfold_const(*c, v->n.ls);
    if (!v->n.sp) return h;
    SVec<u64, 16> es; elims(v->n.sp, es);
    return apply_elims(h, es, 0, es.size());
  }
  Val* rule_rhs(const ConstInfo& rec, const RecRule& rule, LevelList ls) {
    if (Val** p = c_rule.find(HI | rule.rhs, ls)) return *p;
    Val* v = eval_inst(rule.rhs, rec, ls);
    c_rule.put(HI | rule.rhs, ls, v);
    return v;
  }
  Val* iota_nc(u32 d, Val* v) {
    ECTX(3);
    const ConstInfo* rp = E->find(v->a);
    if (!rp || rp->kind != CKind::Rec) return nullptr;
    const ConstInfo& rec = *rp;
    SVec<u64, 16> es; elims(v->n.sp, es);
    size_t m = 0; while (m < es.size() && !is_proj_elim(es[m])) m++;
    u32 mi = rec.rec_major_idx();
    if (m <= mi) return nullptr;
    if (rec.lparams.size() != g_levels->list_size(v->n.ls)) return nullptr;
    Val* major = (Val*)es[mi];
    if (rec.k) { if (Val* kc = to_ctor_when_k(d, rec, major)) major = kc; }
    major = whnf(d, major);
    if (major->k == V_NAT) major = nat_to_ctor(major);
    else if (major->k == V_STR) major = whnf(d, str_to_ctor(major));
    else major = to_ctor_when_struct(d, rec.major_induct, major);
    if (major->k != V_NEU || major->hk != H_CTOR) return nullptr;
    const RecRule* rule = nullptr;
    for (const RecRule& r : rec.rules) if (r.ctor == major->a) { rule = &r; break; }
    if (!rule) return nullptr;
    SVec<u64, 16> margs; elims(major->n.sp, margs);
    if (major->n.sp && major->n.sp->nproj) return nullptr;
    if (rule->nfields > margs.size()) return nullptr;
    Val* r = rule_rhs(rec, *rule, v->n.ls);
    r = apply_many(r, (Val**)&es[0], rec.rec_first_index_idx());
    r = apply_many(r, (Val**)&margs[margs.size() - rule->nfields], rule->nfields);
    return apply_elims(r, es, mi + 1, es.size());
  }
  Val* to_ctor_when_k(u32 d, const ConstInfo& rec, Val* major) {
    Val* t = whnf(d, value_type(d, major));
    if (t->k != V_NEU || t->hk != H_INDUCT || t->a != rec.major_induct) return nullptr;
    if (t->n.sp && t->n.sp->nproj) return nullptr;
    const ConstInfo* ind = E->find(t->a);
    if (!ind || ind->ctors.empty()) return nullptr;
    SVec<u64, 16> targs; elims(t->n.sp, targs);
    if (targs.size() < rec.nparams) return nullptr;
    Val* ctor = apply_many(const_head(ind->ctors[0], t->n.ls), (Val**)targs.data(), rec.nparams);
    if (!conv_types(d, t, value_type(d, ctor))) return nullptr;
    return ctor;
  }
  Val* to_ctor_when_struct(u32 d, Name induct, Val* major) {
    if (!E->is_structure_like(induct)) return major;
    if (major->k == V_NEU && major->hk == H_CTOR) return major;
    Val* t = whnf(d, value_type(d, major));
    if (t->k != V_NEU || t->hk != H_INDUCT || t->a != induct) return major;
    if (t->n.sp && t->n.sp->nproj) return major;
    if (is_prop_type(d, t)) return major;
    const ConstInfo& ind = *E->find(induct);
    const ConstInfo* ctor = E->find(ind.ctors[0]);
    if (!ctor) return major;
    SVec<u64, 16> targs; elims(t->n.sp, targs);
    if (targs.size() < ctor->nparams) return major;
    Val* r = apply_many(const_head(ctor->name, t->n.ls), (Val**)targs.data(), ctor->nparams);
    for (u32 i = 0; i < ctor->nfields; i++) r = apply(r, do_proj(major, induct, i));
    return r;
  }
  Val* quot_nc(u32 d, Val* v) {
    u32 mk_pos = v->a == N.Quot_lift ? 5 : 4;
    SVec<u64, 16> es; elims(v->n.sp, es);
    size_t m = 0; while (m < es.size() && !is_proj_elim(es[m])) m++;
    if (m <= mk_pos) return nullptr;
    Val* mk = whnf(d, (Val*)es[mk_pos]);
    if (mk->k != V_NEU || mk->a != N.Quot_mk || mk->hk != H_AXIOM || !mk->n.sp || mk->n.sp->len != 3 || mk->n.sp->nproj) return nullptr;
    Val* r = apply((Val*)es[3], (Val*)mk->n.sp->e);
    return apply_elims(r, es, mk_pos + 1, es.size());
  }

  // ---------------------------------------------------------------- types of values

  Val* value_type(u32 d, Val* v) {
    switch (v->k) {
      case V_SORT: return mk_sort(mk_succ(v->a));
      case V_NAT: return const_head(N.Nat, 0);
      case V_STR: return const_head(N.String, 0);
      case V_PI: return mk_sort(level_of_type(d, v));
      case V_LAM: return mk_pi(lam_dom(v), v->lam.env, v->lam.body, true);
      default: break;
    }
    if (v->hk == H_BVAR && !v->n.sp) return v->n.bty;
    KC(k_vtype);
    if (Val** c = c_vtype.find((u64)v, 5)) { KC(k_vtype_hit); return *c; }
    Guard g(*this);
    Val* head = head_of(v);
    Val* t = v->hk == H_BVAR ? v->n.bty : const_type(v->a, v->n.ls);
    SVec<u64, 16> es; elims(v->n.sp, es);
    bool track = v->n.sp && v->n.sp->nproj;
    Val* cur = head;
    for (size_t i = 0; i < es.size();) {
      u64 e = es[i];
      if (is_proj_elim(e)) {
        t = proj_type(d, cur, t, proj_name(e), proj_idx(e), false);
        if (track) cur = neu_app(cur, e);
        i++; continue;
      }
      size_t j = i; while (j < es.size() && !is_proj_elim(es[j])) j++;
      t = tele_apply(d, t, (Val**)&es[i], j - i);
      if (track) for (size_t k = i; k < j; k++) cur = neu_app(cur, es[k]);
      i = j;
    }
    c_vtype.put((u64)v, 5, t);
    return t;
  }
  // The type t instantiated with args (inference only): the telescope walk of infer's App case.
  Val* tele_apply(u32 d, Val* t, Val** args, size_t m) {
    Env* tenv = nullptr; Expr texpr = NIL;
    for (size_t i = 0; i < m; i++) {
      Expr body; Env* benv;
      if (tenv) { body = node(texpr).b; benv = tenv; }
      else {
        Val* p = whnf(d, t);
        if (p->k != V_PI) nfail("function expected");
        if (p->pinf) { t = inst_pi(d, p, args[i]); continue; }
        body = p->pi.body; benv = p->pi.env;
      }
      Env* e2 = extend(benv, (fv_mask(body) & 1) ? args[i] : &g_unused);
      if (node(body).kind == EKind::Pi && i + 1 < m) { tenv = e2; texpr = body; }
      else { tenv = nullptr; t = eval(e2, body); }
    }
    return t;
  }
  Val* const_type(Name n, LevelList ls) {
    if (Val** p = c_type.find(HI | n, ls)) return *p;
    ECTX(4);
    const ConstInfo* c = E->find(n);
    if (!c) nfail("unknown constant");
    Val* t = eval_inst(c->type, *c, ls);
    c_type.put(HI | n, ls, t);
    return t;
  }
  // does term e mention bound variable i (at its top level)?
  bool uses_var(Expr e, u32 i) {
    const ExprNode& n = node(e);
    if (n.loose_bvar_range <= i) return false;
    if (u8* c = p_var0.find(HI | e, i)) return *c;
    bool r;
    switch (n.kind) {
      case EKind::BVar: r = n.a == i; break;
      case EKind::App: r = uses_var(n.a, i) || uses_var(n.b, i); break;
      case EKind::Lam: case EKind::Pi: r = uses_var(n.a, i) || uses_var(n.b, i + 1); break;
      case EKind::Let: r = uses_var(n.a, i) || uses_var(n.b, i) || uses_var(n.c, i + 1); break;
      case EKind::Proj: r = uses_var(n.b, i); break;
      default: r = true; break;
    }
    p_var0.put(HI | e, i, r);
    return r;
  }
  Val* proj_type(u32 d, Val* sv, Val* st, Name sname, u32 idx, bool chk) {
    Val* t = whnf(d, st);
    if (t->k != V_NEU || t->hk != H_INDUCT || t->a != sname || (t->n.sp && t->n.sp->nproj)) nfail("invalid projection");
    const ConstInfo* I = E->find(sname);
    if (!I || I->kind != CKind::Induct || I->ctors.size() != 1) nfail("invalid projection");
    SVec<u64, 16> args; elims(t->n.sp, args);
    if (args.size() != I->nparams + I->nindices) nfail("invalid projection");
    bool prop = chk ? is_prop_type(d, t) : false;
    Val* r = const_type(I->ctors[0], t->n.ls);
    for (u32 i = 0; i < I->nparams; i++) {
      Val* w = whnf(d, r);
      if (w->k != V_PI) nfail("invalid projection");
      r = inst_pi(d, w, (Val*)args[i]);
    }
    for (u32 i = 0; i < idx; i++) {
      Val* w = whnf(d, r);
      if (w->k != V_PI) nfail("invalid projection");
      if (chk && prop && (w->pinf || uses_var(w->pi.body, 0)) && !is_prop_type(d, pi_dom(w))) nfail("invalid projection");
      r = inst_pi(d, w, do_proj(sv, sname, i));
    }
    Val* w = whnf(d, r);
    if (w->k != V_PI) nfail("invalid projection");
    if (chk && prop && !is_prop_type(d, pi_dom(w))) nfail("invalid projection");
    return pi_dom(w);
  }
  Level level_of_type(u32 d, Val* T) {
    Guard g(*this);
    T = whnf(d, T);
    switch (T->k) {
      case V_SORT: return mk_succ(T->a);
      case V_PI: {
        Level l1 = level_of_type(d, pi_dom(T));
        Level l2 = level_of_type(d + 1, inst_pi(d + 1, T, fresh(d, pi_dom(T))));
        return mk_imax_s(l1, l2);
      }
      case V_NEU: {
        Val* s = whnf(d, value_type(d, T));
        if (s->k != V_SORT) nfail("type expected");
        return s->a;
      }
      default: nfail("type expected");
    }
  }
  // Whether T is a proposition.  T must be a type: a T whose sort does not reduce to a Sort is
  // an error, not "no" (lean4#14807; the arena's bugs/proj-of-subst-prop is the reason).
  bool is_prop_type(u32 d, Val* T) {
    T = whnf(d, T);
    switch (T->k) {
      case V_SORT: return false;
      case V_NAT: case V_STR: case V_LAM: nfail("type expected");
      case V_PI: {
        if (u8* c = c_isprop.find((u64)T, 6)) return *c;
        Guard g(*this);
        bool r = is_prop_type(d + 1, inst_pi(d + 1, T, fresh(d, pi_dom(T))));
        c_isprop.put((u64)T, 6, r);
        return r;
      }
      default: break;
    }
    if (u8* c = c_isprop.find((u64)T, 6)) return *c;
    Val* s = whnf(d, value_type(d, T));
    if (s->k != V_SORT) nfail("type expected");
    bool r = lvl_zero(s->a);
    c_isprop.put((u64)T, 6, r);
    return r;
  }

  // ---------------------------------------------------------------- definitional equality

  struct ProbeSave {   // conversion outside any argument probe, restoring the probe state on exit
    Engine& g; bool sp, se; u32 sl;
    explicit ProbeSave(Engine& e) : g(e), sp(e.probing), se(e.exhausted), sl(e.probe_left) { g.probing = false; g.exhausted = false; }
    ~ProbeSave() { g.probing = sp; g.exhausted = se; g.probe_left = sl; }
  };
  bool conv_types(u32 d, Val* a, Val* b) {
    ECTX(13);
    ProbeSave ps(*this);
    return conv(d, a, b);
  }

  // ---- relevance signatures
  // For a constant at given universe levels, from its type alone: which argument positions are
  // propositions (arg_prop), and whether an application to exactly k arguments is a proof
  // (res_prop, where res_known says the answer is known).  A proof argument need not be
  // compared when the arguments before it were found equal (the two proofs then have
  // definitionally equal types), and a term that is statically not a proof needs no type
  // inference for proof irrelevance.  Levels do not depend on terms, so the sorts computed on
  // fresh variables are the sorts at any arguments.
  struct Sig { u64 arg_prop = 0, res_prop = 0, res_known = 0; u32 arity = 0; };
  PMap<Sig*> c_sig;
  Sig no_sig;
  const Sig* sig_of(Name n, LevelList ls) {
    // Signatures are plain bits keyed by permanent handles, so they outlive sessions.
    if (Sig** p = c_sig.find(HI | n, ls)) return *p;
    Sig* sg = new Sig();
    c_sig.put(HI | n, ls, sg);   // (re-entrant use during computation sees the empty signature)
    Level dom[64]; bool dk[64]; u32 k = 0;
    Level res = 0; bool rk = false;
    u32 saved_depth = depth; bool sp = probing, se = exhausted; u32 sl = probe_left;
    try {
      ProbeSave ps(*this);
      Val* t = const_type(n, ls);
      const u32 base = 1u << 30;   // fresh levels no real context reaches
      while (k < 64) {
        Val* w = whnf(base + k, t);
        if (w->k != V_PI) break;
        dk[k] = true; dom[k] = level_of_type(base + k, pi_dom(w));
        t = inst_pi(base + k + 1, w, fresh(base + k, pi_dom(w)));
        k++;
      }
      if (k < 64) { res = level_of_type(base + k, t); rk = true; }
    } catch (NbeFail&) {
      depth = saved_depth; probing = sp; exhausted = se; probe_left = sl;
      return sg;   // nothing known
    }
    sg->arity = k;
    for (u32 i = 0; i < k; i++) if (dk[i] && lvl_zero(dom[i])) sg->arg_prop |= 1ull << i;
    if (rk) {
      Level r = res;
      if (k < 64) { sg->res_known |= 1ull << k; if (lvl_zero(r)) sg->res_prop |= 1ull << k; }
      for (u32 i = k; i-- > 0;) {
        r = mk_imax_s(dom[i], r);
        sg->res_known |= 1ull << i; if (lvl_zero(r)) sg->res_prop |= 1ull << i;
      }
    }
    return sg;
  }
  // 1: statically a proof, 0: statically not a proof, -1: unknown
  int static_proof(Val* v) {
    static const bool off = getenv("LL_NBE_NOSTATIC") != nullptr;
    if (off || v->k != V_NEU || v->hk == H_BVAR) return -1;
    Spine* sp = v->n.sp;
    if (sp && sp->nproj) return -1;
    u32 k = sp ? sp->len : 0;
    if (k >= 64) return -1;
    const Sig* sg = sig_of(v->a, v->n.ls);
    if (!((sg->res_known >> k) & 1)) return -1;
    return (sg->res_prop >> k) & 1;
  }
  static bool reducible(Val* v) { return v->k == V_NEU && (v->hk == H_DEF || v->hk == H_REC || v->hk == H_QUOT); }

  bool conv(u32 d, Val* x, Val* y) {
    if (x == y) return true;
    if (probing) { if (probe_left == 0) { exhausted = true; return false; } probe_left--; }
    tick();
    Guard g(*this);
    u64 ka = (u64)x < (u64)y ? (u64)x : (u64)y, kb = (u64)x < (u64)y ? (u64)y : (u64)x;
    bool cache = !(x->k == V_SORT || x->k == V_NAT || x->k == V_STR) || !(y->k == V_SORT || y->k == V_NAT || y->k == V_STR);
    KC(k_conv);
    if (cache) {
      if (c_pos.find(ka, kb)) { KC(k_conv_hit); return true; }
      if (c_neg.find(ka, kb)) { KC(k_conv_hit); return false; }
    }
    bool r = conv_nc(d, x, y);
    if (cache) { if (r) c_pos.put(ka, kb, 1); else if (!exhausted) c_neg.put(ka, kb, 1); }
    return r;
  }
  bool conv_binder(u32 d, Val* x, Val* y) {
    Val* dx = x->k == V_LAM ? lam_dom(x) : pi_dom(x);
    Val* dy = y->k == V_LAM ? lam_dom(y) : pi_dom(y);
    if (!conv(d, dx, dy)) return false;
    Val* v = fresh(d, dx);
    Val* bx = x->k == V_LAM ? apply(x, v) : inst_pi(d + 1, x, v);
    Val* by = y->k == V_LAM ? apply(y, v) : inst_pi(d + 1, y, v);
    return conv(d + 1, bx, by);
  }
  static bool nat_like(Val* v) { return v->k == V_NAT || (v->k == V_NEU && v->hk == H_CTOR && (v->a == N.Nat_zero || v->a == N.Nat_succ)); }
  bool nat_zero(Val* v) {
    return (v->k == V_NAT && *v->nat.v == 0) || (v->k == V_NEU && v->hk == H_CTOR && v->a == N.Nat_zero && !v->n.sp);
  }
  Val* nat_pred(Val* v) {
    if (v->k == V_NAT) return *v->nat.v == 0 ? nullptr : mk_nat(mpz_class(*v->nat.v - 1));
    if (v->k == V_NEU && v->hk == H_CTOR && v->a == N.Nat_succ && v->n.sp && v->n.sp->len == 1 && !v->n.sp->nproj) return (Val*)v->n.sp->e;
    return nullptr;
  }
  bool same_head(Val* x, Val* y) {
    if (x->hk != y->hk || x->a != y->a) return false;
    if (x->hk == H_BVAR) return true;
    return levels_eq(x->n.ls, y->n.ls);
  }
  // Compare two spines of the same head.  `skip` marks argument positions holding proofs
  // (from the head's signature); they are only skipped while every elimination so far is an
  // argument, since after a projection the positions no longer line up with the signature.
  bool conv_spine(u32 d, Spine* a, Spine* b, u64 skip = 0) {
    if (a == b) return true;
    u32 la = a ? a->len : 0, lb = b ? b->len : 0;
    if (la != lb) return false;
    SVec<u64, 16> ea, eb; elims(a, ea); elims(b, eb);
    for (size_t i = 0; i < ea.size(); i++) {
      bool pa = is_proj_elim(ea[i]), pb = is_proj_elim(eb[i]);
      if (pa != pb) return false;
      if (pa) { if (ea[i] != eb[i]) return false; skip = 0; continue; }
      if (i < 64 && ((skip >> i) & 1)) continue;
      if (!conv(d, (Val*)ea[i], (Val*)eb[i])) return false;
    }
    return true;
  }
  u64 skip_mask(Val* x) {
    static const bool off = getenv("LL_NBE_NOSKIP") != nullptr;
    if (off || x->k != V_NEU || x->hk == H_BVAR) return 0;
    return sig_of(x->a, x->n.ls)->arg_prop;
  }
  bool probe_spine(u32 d, Spine* a, Spine* b, u64 skip) {
    if (a == b) return true;
    if (probing) return conv_spine(d, a, b, skip);
    probing = true; exhausted = false; probe_left = 2048;
    bool r;
    try { r = conv_spine(d, a, b, skip); } catch (...) { probing = false; exhausted = false; throw; }
    probing = false; exhausted = false;
    return r;
  }
  int hint_cmp(Name a, Name b) {
    const ConstInfo* ca = E->find(a); const ConstInfo* cb = E->find(b);
    HintKind ha = ca->kind == CKind::Def ? ca->hint : HintKind::Opaque, hb = cb->kind == CKind::Def ? cb->hint : HintKind::Opaque;
    if (ha == hb) {
      if (ha == HintKind::Regular) return ca->height == cb->height ? 0 : (ca->height > cb->height ? -1 : 1);
      return 0;
    }
    if (ha == HintKind::Opaque) return 1;
    if (hb == HintKind::Opaque) return -1;
    if (ha == HintKind::Abbrev) return -1;
    return 1;
  }

  bool conv_nc(u32 d, Val* x, Val* y) {
    if (x->k == y->k) {
      switch (x->k) {
        case V_SORT: return level_eq(x->a, y->a);
        case V_NAT: return *x->nat.v == *y->nat.v;
        case V_STR: return x->a == y->a || g_exprs->str_lits[x->a] == g_exprs->str_lits[y->a];
        case V_PI: case V_LAM: return conv_binder(d, x, y);
        default: break;
      }
    }
    if (nat_like(x) && nat_like(y)) {
      if (nat_zero(x) && nat_zero(y)) return true;
      Val* px = nat_pred(x); Val* py = px ? nat_pred(y) : nullptr;
      if (px && py) return conv(d, px, py);
    }
    if (x->k == V_NEU && y->k == V_NEU && !reducible(x) && same_head(x, y) && conv_spine(d, x->n.sp, y->n.sp, skip_mask(x))) return true;
    if (reducible(x) || reducible(y)) return conv_delta(d, x, y);
    return conv_cold(d, x, y);
  }
  bool conv_delta(u32 d, Val* x, Val* y) {
    bool same = x->k == V_NEU && y->k == V_NEU && same_head(x, y);
    if (same && probe_spine(d, x->n.sp, y->n.sp, skip_mask(x))) return true;
    int pi = proof_irrel(d, x, y);
    if (pi >= 0) return pi;
    bool xi = x->k == V_NEU && (x->hk == H_REC || x->hk == H_QUOT), yi = y->k == V_NEU && (y->hk == H_REC || y->hk == H_QUOT);
    if (xi) { if (Val* r = step(d, x)) return conv(d, r, y); }
    if (yi) { if (Val* r = step(d, y)) return conv(d, x, r); }
    bool xd = x->k == V_NEU && x->hk == H_DEF, yd = y->k == V_NEU && y->hk == H_DEF;
    if (xd && yd) {
      int c = x->a == y->a ? 0 : hint_cmp(x->a, y->a);
      if (c < 0) {
        if (Val* r = step(d, x)) return conv(d, r, y);
        if (Val* r = step(d, y)) return conv(d, x, r);
      } else if (c > 0) {
        if (Val* r = step(d, y)) return conv(d, x, r);
        if (Val* r = step(d, x)) return conv(d, r, y);
      } else {
        Val* rx = step(d, x); Val* ry = step(d, y);
        if (rx || ry) return conv(d, rx ? rx : x, ry ? ry : y);
      }
    } else if (xd) {
      if (Val* r = step(d, x)) return conv(d, r, y);
    } else if (yd) {
      if (Val* r = step(d, y)) return conv(d, x, r);
    }
    if (same && conv_spine(d, x->n.sp, y->n.sp, skip_mask(x))) return true;
    return conv_cold(d, x, y);
  }
  bool conv_cold(u32 d, Val* x, Val* y) {
    int pi = proof_irrel(d, x, y);
    if (pi >= 0) return pi;
    if (x->k == V_LAM && y->k != V_LAM) return eta(d, x, y);
    if (y->k == V_LAM && x->k != V_LAM) return eta(d, y, x);
    if (eta_struct(d, x, y) || eta_struct(d, y, x)) return true;
    if (x->k == V_STR && y->k == V_NEU) return conv(d, whnf(d, str_to_ctor(x)), y);
    if (y->k == V_STR && x->k == V_NEU) return conv(d, x, whnf(d, str_to_ctor(y)));
    return unit_like(d, x, y);
  }
  bool eta(u32 d, Val* lam, Val* other) {
    if (other->k != V_NEU) return false;
    Val* v = fresh(d, lam_dom(lam));
    return conv(d + 1, apply(lam, v), apply(other, v));
  }
  bool eta_struct(u32 d, Val* x, Val* y) {
    if (y->k != V_NEU || y->hk != H_CTOR || (y->n.sp && y->n.sp->nproj)) return false;
    const ConstInfo* c = E->find(y->a);
    if (!c) return false;
    u32 len = y->n.sp ? y->n.sp->len : 0;
    if (len != c->nparams + c->nfields) return false;
    if (!E->is_structure_like(c->induct)) return false;
    if (x->k == V_SORT || x->k == V_PI) return false;
    if (!conv_types(d, value_type(d, x), value_type(d, y))) return false;
    SVec<u64, 16> ys; elims(y->n.sp, ys);
    for (u32 i = 0; i < c->nfields; i++)
      if (!conv(d, do_proj(x, c->induct, i), (Val*)ys[c->nparams + i])) return false;
    return true;
  }
  bool unit_like(u32 d, Val* x, Val* y) {
    if (x->k == V_SORT || x->k == V_PI || y->k == V_SORT || y->k == V_PI) return false;
    Val* t = whnf(d, value_type(d, x));
    if (t->k != V_NEU || t->hk != H_INDUCT) return false;
    const ConstInfo* I = E->find(t->a);
    if (!I || I->is_rec || I->ctors.size() != 1 || I->nindices != 0) return false;
    const ConstInfo* c = E->find(I->ctors[0]);
    if (!c || c->nfields != 0) return false;
    return conv_types(d, t, value_type(d, y));
  }
  // 1: equal as proofs of the same proposition; 0: proofs of different propositions; -1: not proofs
  int proof_irrel(u32 d, Val* x, Val* y) {
    KC(k_pirr);
    if (x->k == V_SORT || x->k == V_PI || x->k == V_NAT || x->k == V_STR) return -1;
    if (y->k == V_SORT || y->k == V_PI || y->k == V_NAT || y->k == V_STR) return -1;
    if (static_proof(x) == 0 || static_proof(y) == 0) { KC(k_pirr_static); return -1; }
    Val* tx = value_type(d, x);
    if (!is_prop_type(d, tx)) return -1;
    return conv_types(d, tx, value_type(d, y)) ? 1 : 0;
  }

  // ---------------------------------------------------------------- type inference

  Level sort_level(u32 d, Val* t) {
    Val* s = whnf(d, t);
    if (s->k != V_SORT) nfail("type expected");
    return s->a;
  }

  Val* infer(bool chk, Env* env, u32 d, Expr e) {
    const ExprNode& n = node(e);
    switch (n.kind) {
      case EKind::BVar: return value_type(d, lookup(env, n.a));
      case EKind::Sort:
        if (chk) check_level(n.a);
        return mk_sort(mk_succ(inst_level(env->ls, n.a)));
      case EKind::Const: {
        const ConstInfo* c = E->find(n.name);
        if (!c) nfail("unknown constant");
        LevelList ls = inst_levels(env->ls, n.lvls);
        if (g_levels->list_size(ls) != c->lparams.size()) nfail("wrong number of universe levels");
        if (chk) {
          if (c->is_unsafe) nfail("unsafe constant");
          if (c->kind == CKind::Def && c->safety == Safety::Partial) nfail("partial constant");
          for (Level l : g_levels->list_ref(n.lvls)) check_level(l);
        }
        return const_type(n.name, ls);
      }
      case EKind::Lit:
        if (n.b == (u32)LitKind::Nat) { if (!E->find(N.Nat)) nfail("no Nat"); return const_head(N.Nat, 0); }
        if (!E->find(N.String) || !E->find(N.Char_ofNat) || !E->find(N.String_ofList)) nfail("no String");
        return const_head(N.String, 0);
      case EKind::FVar: case EKind::Clos: nfail("unexpected term");
      default: break;
    }
    Env* ke = key_env(env, e);
    IEnt* ce = c_infer.find((u64)ke, e);
    KC(k_infer);
    if (ce && (!chk || ce->scope == scope)) { KC(k_infer_hit); return ce->ty; }
    return infer_slow(chk, env, d, e, ke);
  }
  __attribute__((noinline)) Val* infer_slow(bool chk, Env* env, u32 d, Expr e, Env* ke) {
    const ExprNode& n = node(e);
    env = ke;
    IEnt* ce;
    Guard g(*this);
    Val* r;
    switch (n.kind) {
      case EKind::App: {
        SVec<Expr, 16> args; Expr f = e;
        while (node(f).kind == EKind::App) { args.push(node(f).b); f = node(f).a; }
        args.reverse();
        // The function's type is walked as a telescope.  While it is literally a chain of Pi
        // terms under an environment (tenv, texpr), each argument just extends the environment:
        // no intermediate Pi value is built, a domain is evaluated only to be compared with the
        // argument's type, and an argument the rest of the type does not mention is not
        // evaluated at all (a placeholder keeps the de Bruijn positions; the free-variable masks
        // are exact, so it is never looked up).
        Val* ft = infer(chk, env, d, f);
        Env* tenv = nullptr; Expr texpr = NIL;
        for (size_t i = 0; i < args.size(); i++) {
          Val* dom; Expr body; Env* benv; bool pinf = false;
          if (tenv) {
            const ExprNode& pn = node(texpr);
            body = pn.b; benv = tenv;
            { ECTX(8); dom = chk ? eval(tenv, pn.a) : nullptr; }
          } else {
            Val* p = whnf(d, ft);
            if (p->k != V_PI) nfail("function expected");
            body = p->pi.body; benv = p->pi.env; pinf = p->pinf;
            { ECTX(8); dom = chk ? pi_dom(p) : nullptr; }
            if (pinf) {   // an inference closure: instantiate it as a value
              if (chk) { Val* at = infer(true, env, d, args[i]); if (!conv_types(d, dom, at)) nfail("application type mismatch"); }
              Val* av; { ECTX(1); av = node(body).loose_bvar_range == 0 ? nullptr : eval(env, args[i]); }
              ft = inst_pi(d, p, av);
              continue;
            }
          }
          if (chk) {
            Val* at = infer(true, env, d, args[i]);
            if (!conv_types(d, dom, at)) nfail("application type mismatch");
          }
          Val* av; { ECTX(1); av = (fv_mask(body) & 1) ? eval(env, args[i]) : &g_unused; }
          Env* e2 = extend(benv, av);
          if (node(body).kind == EKind::Pi && i + 1 < args.size()) { tenv = e2; texpr = body; }
          else { tenv = nullptr; ft = eval(e2, body); }
        }
        r = ft; break;
      }
      case EKind::Lam: {
        if (chk) sort_level(d, infer(true, env, d, n.a));
        Val* dom; { ECTX(9); dom = eval(env, n.a); }
        if (chk) infer(true, extend(env, fresh(d, dom)), d + 1, n.b);
        r = mk_pi(dom, env, n.b, true);
        break;
      }
      case EKind::Pi: {
        Level l1 = sort_level(d, infer(chk, env, d, n.a));
        Val* dom; { ECTX(9); dom = eval(env, n.a); }
        Level l2 = sort_level(d + 1, infer(chk, extend(env, fresh(d, dom)), d + 1, n.b));
        r = mk_sort(mk_imax_s(l1, l2));
        break;
      }
      case EKind::Let: {
        if (chk) {
          sort_level(d, infer(true, env, d, n.a));
          Val* vt = infer(true, env, d, n.b);
          if (!conv_types(d, eval(env, n.a), vt)) nfail("let value type mismatch");
        }
        r = infer(chk, extend(env, eval(env, n.b)), d, n.c);
        break;
      }
      case EKind::Proj: {
        ECTX(14);
        Val* st = infer(chk, env, d, n.b);
        r = proj_type(d, eval(env, n.b), st, n.name, n.a, chk);
        break;
      }
      default: nfail("unexpected term");
    }
    ce = c_infer.find((u64)ke, e);
    if (!ce || chk) c_infer.put((u64)ke, e, IEnt{r, chk ? scope : 0u});
    return r;
  }

  // ---------------------------------------------------------------- declarations

  // the three phases of checking a definition (separate functions, for profiles)
  __attribute__((noinline)) Val* phase_type(Expr t) { return infer(true, groot, 0, t); }
  __attribute__((noinline)) Val* phase_value(Expr v) { return infer(true, groot, 0, v); }
  __attribute__((noinline)) bool phase_conv(Val* vt, Expr t) { Val* tv; { ECTX(11); tv = eval(groot, t); } return conv_types(0, vt, tv); }
  bool check(const Environment& env, const Decl& dcl) {
    if (dcl.kind != Decl::Axiom && dcl.kind != Decl::Def && dcl.kind != Decl::Thm && dcl.kind != Decl::Opaque) return false;
    const ConstInfo& c = dcl.consts[0];
    if (c.is_unsafe || (c.kind == CKind::Def && c.safety != Safety::Safe)) return false;
    if (has_loose_bvars(c.type) || has_fvar(c.type)) return false;
    if (c.value != NIL && (has_loose_bvars(c.value) || has_fvar(c.value))) return false;
    if (dcl.kind != Decl::Axiom && c.value == NIL) return false;
    for (size_t i = 0; i < c.lparams.size(); i++) for (size_t j = i + 1; j < c.lparams.size(); j++) if (c.lparams[i] == c.lparams[j]) return false;
    if (env.contains(c.name)) return false;
    if (!groot) start_session();
    E = &env;
    g_nodes = g_exprs->nodes.data();
    if (!fvm) {   // sized to the permanent tier; pages are touched only for terms actually met
      fvm_n = g_exprs->wm_nodes ? g_exprs->wm_nodes : g_exprs->nodes.size();
      void* p = mmap(nullptr, fvm_n * sizeof(u64) + 8, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
      if (p == MAP_FAILED) { std::cerr << "nbe: out of memory\n"; abort(); }
      fvm = (u64*)p;
    }
    lparams = &c.lparams;
    scope = plist_of(c) + 2;   // an inference checked under these universe parameters
    steps = 0; budget = g_nbe_budget; depth = 0; probing = false; exhausted = false;
    try {
      Val* s = whnf(0, phase_type(c.type));
      if (s->k != V_SORT) nfail("type expected");
      if (dcl.kind == Decl::Thm && !lvl_zero(s->a)) nfail("theorem type is not a proposition");
      if (c.value != NIL) {
        Val* vt = phase_value(c.value);
        if (!phase_conv(vt, c.type)) nfail("type mismatch");
      }
    } catch (NbeFail& f) {
      static const bool trace = getenv("LL_NBE_TRACE") != nullptr;
      if (trace) std::cerr << "nbe declined " << name_str(c.name) << ": " << f.why << "\n";
      s_steps += steps; s_decline++; note_reason(f.why);
      probing = false; exhausted = false; depth = 0;
      return false;
    }
    s_steps += steps; s_accept++;
    { u64 b = 0, x = steps; while (x >= 1000 && b < 7) { x /= 10; b++; } s_hist[b]++; }
    return true;
  }
};

Engine* g_engine_nbe = nullptr;
size_t g_session_bytes = getenv("LL_NBE_SESSION_MB") ? (size_t)atol(getenv("LL_NBE_SESSION_MB")) << 20 : (size_t)1536 << 20;

} // namespace

bool nbe_check(const Environment& env, const Decl& d) {
  if (!g_engine_nbe) g_engine_nbe = new Engine();
  return g_engine_nbe->check(env, d);
}

void nbe_between_decls() {
  if (g_engine_nbe && g_engine_nbe->groot && g_engine_nbe->ar.bytes > g_session_bytes) g_engine_nbe->start_session();
}

void nbe_report() {
  if (!g_engine_nbe) return;
  std::cerr << "nbe: " << s_accept << " accepted, " << s_decline << " declined; " << s_steps << " steps; " << s_sessions << " sessions\n";
  for (auto& p : s_reasons) std::cerr << "  declined (" << p.first << "): " << p.second << "\n";
  std::cerr << "nbe steps per accepted declaration: <1e3 " << s_hist[0] << ", <1e4 " << s_hist[1] << ", <1e5 " << s_hist[2] << ", <1e6 " << s_hist[3]
            << ", <1e7 " << s_hist[4] << ", <1e8 " << s_hist[5] << ", more " << s_hist[6] + s_hist[7] << "\n";
#ifdef LL_NBE_STATS
  { Engine& g = *g_engine_nbe; auto cap = [](size_t m) { return (m + 1) * 24 >> 20; };
    std::cerr << "table MB: eval " << cap(g.c_eval.mask) << " app " << cap(g.c_app.mask) << " env " << cap(g.c_env.mask) << " infer " << cap(g.c_infer.mask)
              << " pos " << cap(g.c_pos.mask) << " neg " << cap(g.c_neg.mask) << " vtype " << cap(g.c_vtype.mask) << " frame " << cap(g.c_frame.mask)
              << " arena blocks " << g.ar.blocks.size() * 32 << "\n"; }
  std::cerr << "eval misses by origin: other " << g_engine_nbe->ectx_miss[0] << ", infer-arg " << g_engine_nbe->ectx_miss[1] << ", unfold " << g_engine_nbe->ectx_miss[2]
            << ", iota " << g_engine_nbe->ectx_miss[3] << ", const-type " << g_engine_nbe->ectx_miss[4] << ", pi-inst " << g_engine_nbe->ectx_miss[5] << ", decl-type " << g_engine_nbe->ectx_miss[6] << ", lambda-type-inst " << g_engine_nbe->ectx_miss[7] << ", app-domain " << g_engine_nbe->ectx_miss[8] << ", binder-domain " << g_engine_nbe->ectx_miss[9] << ", lam-dom " << g_engine_nbe->ectx_miss[10] << ", decl-conv " << g_engine_nbe->ectx_miss[11] << ", proj " << g_engine_nbe->ectx_miss[12] << ", conv " << g_engine_nbe->ectx_miss[13] << ", infer-proj " << g_engine_nbe->ectx_miss[14] << "\n";
#endif
  std::cerr << "nbe caches (calls/hits): eval " << k_eval << "/" << k_eval_hit << ", app " << k_app << "/" << k_app_hit
            << ", env " << k_env << "/" << k_env_hit << ", infer " << k_infer << "/" << k_infer_hit << ", conv " << k_conv << "/" << k_conv_hit
            << ", vtype " << k_vtype << "/" << k_vtype_hit << "; eval at root " << k_eval_root << ", infer at root " << k_infer_root << ", const evals " << k_const << ", eval misses a pruned key would hit " << k_prune_would_hit << "; reduction steps " << k_step << ", proof-irrelevance tests " << k_pirr << " (" << k_pirr_static << " decided statically)" << "\n";
}

} // namespace ll
