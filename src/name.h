#pragma once
#include "common.h"
#include <functional>

namespace ll {

struct NameNode {
  Name parent;
  bool is_str;
  u64 num;        // for numeric components
  std::string str;
  u64 hash;
};

struct NameTable {
  std::vector<NameNode> nodes;
  NameTable();
  void reserve(size_t n);   // size for a load of about n names
  Name mk_str(Name parent, std::string_view s);
  Name mk_num(Name parent, u64 n);
  const NameNode& operator[](Name n) const { return nodes[n]; }
  std::string to_string(Name n) const;
  // Parse a dotted name like "Nat.add" (string components only).
  Name of_string(std::string_view s);
  // Lexicographic comparison used by level normalization (Lean's `Name.lt`).
  bool lt(Name a, Name b) const;
private:
  struct H { NameTable* t; u64 operator()(u32 h) const { return t->nodes[h].hash; } };
  struct E { NameTable* t; bool operator()(u32 a, u32 b) const {
    auto& x = t->nodes[a]; auto& y = t->nodes[b];
    return x.parent == y.parent && x.is_str == y.is_str && x.num == y.num && x.str == y.str; } };
  InternTable<H, E>* table;
};

extern NameTable* g_names;

inline Name mk_name(std::string_view dotted) { return g_names->of_string(dotted); }
inline std::string name_str(Name n) { return g_names->to_string(n); }

// Well-known names, interned at startup (see name.cpp).
struct Names {
  Name Nat, Nat_zero, Nat_succ, Nat_add, Nat_sub, Nat_mul, Nat_pow, Nat_gcd, Nat_mod, Nat_div,
       Nat_beq, Nat_ble, Nat_land, Nat_lor, Nat_xor, Nat_shiftLeft, Nat_shiftRight,
       Bool, Bool_true, Bool_false, String, String_mk, String_ofList, Char, Char_ofNat,
       List, List_nil, List_cons, Eq, Eq_refl, Quot, Quot_mk, Quot_lift, Quot_ind,
       eagerReduce, reduceBool, reduceNat, u, v, motive, t, anonymous;
};
extern Names N;
void init_names();

} // namespace ll
