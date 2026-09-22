#include "name.h"

namespace ll {

NameTable* g_names = nullptr;
Names N;

NameTable::NameTable() {
  nodes.push_back(NameNode{0, true, 0, "", 0});  // anonymous
  table = new InternTable<H, E>(H{this}, E{this});
}

Name NameTable::mk_str(Name parent, std::string_view s) {
  u64 h = mix(mix(nodes[parent].hash, 1), hash_str(s));
  nodes.push_back(NameNode{parent, true, 0, std::string(s), h});
  u32 cand = (u32)nodes.size() - 1;
  u32 r = table->intern(cand);
  if (r != cand) nodes.pop_back();
  return r;
}

Name NameTable::mk_num(Name parent, u64 n) {
  u64 h = mix(mix(nodes[parent].hash, 2), n);
  nodes.push_back(NameNode{parent, false, n, "", h});
  u32 cand = (u32)nodes.size() - 1;
  u32 r = table->intern(cand);
  if (r != cand) nodes.pop_back();
  return r;
}

std::string NameTable::to_string(Name n) const {
  if (n == 0) return "[anonymous]";
  const NameNode& nd = nodes[n];
  std::string p = nd.parent == 0 ? "" : to_string(nd.parent) + ".";
  return p + (nd.is_str ? nd.str : std::to_string(nd.num));
}

Name NameTable::of_string(std::string_view s) {
  Name n = 0;
  size_t i = 0;
  while (i <= s.size()) {
    size_t j = s.find('.', i);
    if (j == std::string_view::npos) j = s.size();
    n = mk_str(n, s.substr(i, j - i));
    i = j + 1;
  }
  return n;
}

// Lean's Name.cmp: compare component lists from the root; str < num? In Lean,
// `Name.cmp` orders: anonymous first; then by prefix, then by the last component, with
// numeric components before string components.
bool NameTable::lt(Name a, Name b) const {
  if (a == b) return false;
  std::vector<Name> ca, cb;
  for (Name x = a; x != 0; x = nodes[x].parent) ca.push_back(x);
  for (Name x = b; x != 0; x = nodes[x].parent) cb.push_back(x);
  size_t i = ca.size(), j = cb.size();
  while (i > 0 && j > 0) {
    const NameNode& x = nodes[ca[i - 1]]; const NameNode& y = nodes[cb[j - 1]];
    if (x.is_str != y.is_str) return !x.is_str;  // num < str
    if (x.is_str) { if (x.str != y.str) return x.str < y.str; }
    else if (x.num != y.num) return x.num < y.num;
    i--; j--;
  }
  return i == 0 && j > 0;
}

void init_names() {
  g_names = new NameTable();
  auto s = [](const char* x) { return mk_name(x); };
  N.anonymous = 0;
  N.Nat = s("Nat"); N.Nat_zero = s("Nat.zero"); N.Nat_succ = s("Nat.succ");
  N.Nat_add = s("Nat.add"); N.Nat_sub = s("Nat.sub"); N.Nat_mul = s("Nat.mul"); N.Nat_pow = s("Nat.pow");
  N.Nat_gcd = s("Nat.gcd"); N.Nat_mod = s("Nat.mod"); N.Nat_div = s("Nat.div"); N.Nat_beq = s("Nat.beq");
  N.Nat_ble = s("Nat.ble"); N.Nat_land = s("Nat.land"); N.Nat_lor = s("Nat.lor"); N.Nat_xor = s("Nat.xor");
  N.Nat_shiftLeft = s("Nat.shiftLeft"); N.Nat_shiftRight = s("Nat.shiftRight");
  N.Bool = s("Bool"); N.Bool_true = s("Bool.true"); N.Bool_false = s("Bool.false");
  N.String = s("String"); N.String_mk = s("String.mk"); N.String_ofList = s("String.ofList");
  N.Char = s("Char"); N.Char_ofNat = s("Char.ofNat");
  N.List = s("List"); N.List_nil = s("List.nil"); N.List_cons = s("List.cons");
  N.Eq = s("Eq"); N.Eq_refl = s("Eq.refl");
  N.Quot = s("Quot"); N.Quot_mk = s("Quot.mk"); N.Quot_lift = s("Quot.lift"); N.Quot_ind = s("Quot.ind");
  N.eagerReduce = s("eagerReduce"); N.reduceBool = s("Lean.reduceBool"); N.reduceNat = s("Lean.reduceNat");
  N.u = s("u"); N.v = s("v"); N.motive = s("motive"); N.t = s("t");
}

} // namespace ll
