#pragma once
#include "common.h"
#include "name.h"

namespace ll {

enum class LKind : u8 { Zero = 0, Succ = 1, Max = 2, IMax = 3, Param = 4 };

struct LevelNode {
  LKind kind;
  bool has_param;
  Level a, b;   // succ: a; max/imax: a, b
  Name param;
  u64 hash;
};

struct LevelTable {
  std::vector<LevelNode> nodes;
  std::vector<std::vector<Level>> lists;  // interned level lists; lists[0] = {}
  LevelTable();
  const LevelNode& operator[](Level l) const { return nodes[l]; }
  Level mk_succ(Level a);
  Level mk_max(Level a, Level b);     // no simplification
  Level mk_imax(Level a, Level b);    // no simplification
  Level mk_param(Name n);
  LevelList mk_list(const std::vector<Level>& ls);
  std::vector<Level> list(LevelList i) const { return lists[i]; }  // by value: `lists` may reallocate
  size_t list_size(LevelList i) const { return lists[i].size(); }
private:
  Level intern(LevelNode nd);
  struct H { LevelTable* t; u64 operator()(u32 h) const { return t->nodes[h].hash; } };
  struct E { LevelTable* t; bool operator()(u32 x, u32 y) const {
    auto& a = t->nodes[x]; auto& b = t->nodes[y];
    return a.kind == b.kind && a.a == b.a && a.b == b.b && a.param == b.param; } };
  struct LH { LevelTable* t; u64 operator()(u32 h) const {
    u64 r = 7; for (Level l : t->lists[h]) r = mix(r, l); return r; } };
  struct LE { LevelTable* t; bool operator()(u32 x, u32 y) const { return t->lists[x] == t->lists[y]; } };
  InternTable<H, E>* table;
  InternTable<LH, LE>* ltable;
};

extern LevelTable* g_levels;
constexpr Level LZERO = 0;

inline const LevelNode& lv(Level l) { return (*g_levels)[l]; }
inline bool is_zero(Level l) { return l == LZERO; }
inline bool is_succ(Level l) { return lv(l).kind == LKind::Succ; }
inline bool is_max(Level l) { return lv(l).kind == LKind::Max; }
inline bool is_imax(Level l) { return lv(l).kind == LKind::IMax; }
inline bool is_param(Level l) { return lv(l).kind == LKind::Param; }

Level mk_succ(Level l);
Level mk_succ_n(Level l, unsigned n);
// Smart constructors with the kernel's simplifications (`mk_max`/`mk_imax` in level.cpp).
Level mk_max_s(Level a, Level b);
Level mk_imax_s(Level a, Level b);
Level mk_level_nat(unsigned n);
inline Level mk_param(Name n) { return g_levels->mk_param(n); }
inline Level mk_max_raw(Level a, Level b) { return g_levels->mk_max(a, b); }
inline Level mk_imax_raw(Level a, Level b) { return g_levels->mk_imax(a, b); }

// (base, offset) with offset = number of leading succs.
std::pair<Level, unsigned> to_offset(Level l);
bool is_explicit(Level l);          // succ^k zero
bool is_never_zero(Level l);
Level normalize(Level l);
bool is_equivalent(Level a, Level b);
bool is_geq(Level a, Level b);
inline bool is_always_zero(Level l) { return is_zero(normalize(l)); }
bool is_equiv_list(LevelList a, LevelList b);
// Instantiate level parameters `ps` by `ls`.
Level instantiate_level_params(Level l, const std::vector<Name>& ps, const std::vector<Level>& ls);
// Returns NIL if all params of l occur in ps, else the offending param name.
Name get_undef_param(Level l, const std::vector<Name>& ps);
std::string level_str(Level l);

} // namespace ll
