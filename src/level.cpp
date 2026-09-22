#include "level.h"
#include <algorithm>

namespace ll {

LevelTable* g_levels = nullptr;

LevelTable::LevelTable() {
  nodes.push_back(LevelNode{LKind::Zero, false, 0, 0, 0, 12345});
  lists.push_back({});
  table = new InternTable<H, E>(H{this}, E{this});
  ltable = new InternTable<LH, LE>(LH{this}, LE{this});
  // intern the zero node and empty list
  table->intern(0); ltable->intern(0);
}

Level LevelTable::intern(LevelNode nd) {
  nodes.push_back(nd);
  u32 cand = (u32)nodes.size() - 1;
  u32 r = table->intern(cand);
  if (r != cand) nodes.pop_back();
  return r;
}
Level LevelTable::mk_succ(Level a) {
  return intern(LevelNode{LKind::Succ, nodes[a].has_param, a, 0, 0, mix(nodes[a].hash, 11)});
}
Level LevelTable::mk_max(Level a, Level b) {
  return intern(LevelNode{LKind::Max, nodes[a].has_param || nodes[b].has_param, a, b, 0,
                          mix(mix(nodes[a].hash, 13), nodes[b].hash)});
}
Level LevelTable::mk_imax(Level a, Level b) {
  return intern(LevelNode{LKind::IMax, nodes[a].has_param || nodes[b].has_param, a, b, 0,
                          mix(mix(nodes[a].hash, 17), nodes[b].hash)});
}
Level LevelTable::mk_param(Name n) {
  return intern(LevelNode{LKind::Param, true, 0, 0, n, mix(19, (*g_names)[n].hash)});
}
LevelList LevelTable::mk_list(const std::vector<Level>& ls) {
  if (ls.empty()) return 0;
  lists.push_back(ls);
  u32 cand = (u32)lists.size() - 1;
  u32 r = ltable->intern(cand);
  if (r != cand) lists.pop_back();
  return r;
}

Level mk_succ(Level l) { return g_levels->mk_succ(l); }
Level mk_succ_n(Level l, unsigned n) { while (n--) l = mk_succ(l); return l; }
Level mk_level_nat(unsigned n) { return mk_succ_n(LZERO, n); }

std::pair<Level, unsigned> to_offset(Level l) {
  unsigned k = 0;
  while (is_succ(l)) { l = lv(l).a; k++; }
  return {l, k};
}
bool is_explicit(Level l) { return is_zero(to_offset(l).first); }

bool is_never_zero(Level l) {
  switch (lv(l).kind) {
    case LKind::Zero: return false;
    case LKind::Param: return false;
    case LKind::Succ: return true;
    case LKind::Max: return is_never_zero(lv(l).a) || is_never_zero(lv(l).b);
    case LKind::IMax: return is_never_zero(lv(l).b);
  }
  return false;
}

// Kernel smart constructors (level.cpp mk_max / mk_imax).
Level mk_max_s(Level a, Level b) {
  if (is_explicit(a) && is_explicit(b)) return to_offset(a).second >= to_offset(b).second ? a : b;
  if (a == b) return a;
  if (is_zero(a)) return b;
  if (is_zero(b)) return a;
  if (is_max(b) && (lv(b).a == a || lv(b).b == a)) return b;
  auto pa = to_offset(a), pb = to_offset(b);
  if (pa.first == pb.first) return pa.second > pb.second ? a : b;
  return mk_max_raw(a, b);
}
Level mk_imax_s(Level a, Level b) {
  if (is_never_zero(b)) return mk_max_s(a, b);
  if (is_zero(b)) return b;
  if (is_zero(a)) return b;
  if (is_succ(a) && is_zero(lv(a).a)) return b;   // imax 1 u = u
  if (a == b) return a;
  return mk_imax_raw(a, b);
}

static void push_max_args(Level l, std::vector<Level>& out) {
  if (is_max(l)) { push_max_args(lv(l).a, out); push_max_args(lv(l).b, out); }
  else out.push_back(l);
}

static bool is_norm_lt(Level a, Level b) {
  if (a == b) return false;
  auto p1 = to_offset(a), p2 = to_offset(b);
  Level l1 = p1.first, l2 = p2.first;
  if (l1 != l2) {
    if (lv(l1).kind != lv(l2).kind) return (int)lv(l1).kind < (int)lv(l2).kind;
    switch (lv(l1).kind) {
      case LKind::Param: return g_names->lt(lv(l1).param, lv(l2).param);
      case LKind::Max: case LKind::IMax:
        if (lv(l1).a != lv(l2).a) return is_norm_lt(lv(l1).a, lv(l2).a);
        return is_norm_lt(lv(l1).b, lv(l2).b);
      default: return false;
    }
  }
  return p1.second < p2.second;
}

static Level mk_max_list(const std::vector<Level>& args) {
  Level r = args.back();
  for (size_t i = args.size() - 1; i-- > 0;) r = mk_max_s(args[i], r);
  return r;
}

Level normalize(Level l) {
  auto p = to_offset(l);
  Level r = p.first;
  switch (lv(r).kind) {
    case LKind::Succ: fail("unreachable in normalize");
    case LKind::Zero: case LKind::Param: return l;
    case LKind::IMax: {
      Level l1 = normalize(lv(r).a), l2 = normalize(lv(r).b);
      return mk_succ_n(mk_imax_s(l1, l2), p.second);
    }
    case LKind::Max: {
      std::vector<Level> todo, args;
      push_max_args(r, todo);
      for (Level a : todo) push_max_args(normalize(a), args);
      std::sort(args.begin(), args.end(), is_norm_lt);
      std::vector<Level> rargs;
      size_t i = 0;
      if (is_explicit(args[i])) {
        while (i + 1 < args.size() && is_explicit(args[i + 1])) i++;
        unsigned k = to_offset(args[i]).second;
        size_t j = i + 1;
        for (; j < args.size(); j++) if (to_offset(args[j]).second >= k) break;
        if (j < args.size()) i++;
      }
      rargs.push_back(args[i]);
      auto prev = to_offset(args[i]); i++;
      for (; i < args.size(); i++) {
        auto curr = to_offset(args[i]);
        if (prev.first == curr.first) {
          if (prev.second < curr.second) { prev = curr; rargs.back() = args[i]; }
        } else { prev = curr; rargs.push_back(args[i]); }
      }
      for (Level& a : rargs) a = mk_succ_n(a, p.second);
      return mk_max_list(rargs);
    }
  }
  return l;
}

bool is_equivalent(Level a, Level b) { return a == b || normalize(a) == normalize(b); }

static bool is_geq_core(Level l1, Level l2) {
  if (l1 == l2 || is_zero(l2)) return true;
  if (is_max(l2)) return is_geq(l1, lv(l2).a) && is_geq(l1, lv(l2).b);
  if (is_max(l1) && (is_geq(lv(l1).a, l2) || is_geq(lv(l1).b, l2))) return true;
  if (is_imax(l2)) return is_geq(l1, lv(l2).a) && is_geq(l1, lv(l2).b);
  if (is_imax(l1)) return is_geq(lv(l1).b, l2);
  auto p1 = to_offset(l1), p2 = to_offset(l2);
  if (p1.first == p2.first || is_zero(p2.first)) return p1.second >= p2.second;
  if (p1.second == p2.second && p1.second > 0) return is_geq(p1.first, p2.first);
  return false;
}
bool is_geq(Level a, Level b) { return is_geq_core(normalize(a), normalize(b)); }

bool is_equiv_list(LevelList a, LevelList b) {
  if (a == b) return true;
  const std::vector<Level> la = g_levels->list(a), lb = g_levels->list(b);
  if (la.size() != lb.size()) return false;
  for (size_t i = 0; i < la.size(); i++) if (!is_equivalent(la[i], lb[i])) return false;
  return true;
}

Level instantiate_level_params(Level l, const std::vector<Name>& ps, const std::vector<Level>& ls) {
  if (!lv(l).has_param) return l;
  switch (lv(l).kind) {
    case LKind::Zero: return l;
    case LKind::Succ: return mk_succ(instantiate_level_params(lv(l).a, ps, ls));
    case LKind::Max: return mk_max_s(instantiate_level_params(lv(l).a, ps, ls), instantiate_level_params(lv(l).b, ps, ls));
    case LKind::IMax: return mk_imax_s(instantiate_level_params(lv(l).a, ps, ls), instantiate_level_params(lv(l).b, ps, ls));
    case LKind::Param:
      for (size_t i = 0; i < ps.size(); i++) if (ps[i] == lv(l).param) return ls[i];
      return l;
  }
  return l;
}

Name get_undef_param(Level l, const std::vector<Name>& ps) {
  if (!lv(l).has_param) return NIL;
  switch (lv(l).kind) {
    case LKind::Zero: return NIL;
    case LKind::Succ: return get_undef_param(lv(l).a, ps);
    case LKind::Max: case LKind::IMax: {
      Name r = get_undef_param(lv(l).a, ps);
      return r != NIL ? r : get_undef_param(lv(l).b, ps);
    }
    case LKind::Param:
      for (Name p : ps) if (p == lv(l).param) return NIL;
      return lv(l).param;
  }
  return NIL;
}

std::string level_str(Level l) {
  auto p = to_offset(l);
  std::string base;
  switch (lv(p.first).kind) {
    case LKind::Zero: return std::to_string(p.second);
    case LKind::Param: base = name_str(lv(p.first).param); break;
    case LKind::Max: base = "(max " + level_str(lv(p.first).a) + " " + level_str(lv(p.first).b) + ")"; break;
    case LKind::IMax: base = "(imax " + level_str(lv(p.first).a) + " " + level_str(lv(p.first).b) + ")"; break;
    default: base = "?";
  }
  return p.second ? base + "+" + std::to_string(p.second) : base;
}

} // namespace ll
