#pragma once
#include "expr.h"
#include <unordered_map>
#include <optional>
#include <algorithm>

namespace ll {

enum class CKind : u8 { Axiom, Def, Thm, Opaque, Quot, Induct, Ctor, Rec };
enum class HintKind : u8 { Opaque, Abbrev, Regular };
enum class Safety : u8 { Unsafe, Safe, Partial };
enum class QuotKind : u8 { Type, Ctor, Lift, Ind };

struct RecRule { Name ctor; u32 nfields; Expr rhs; };

struct ConstInfo {
  CKind kind;
  Name name;
  std::vector<Name> lparams;
  Expr type;
  Expr value = NIL;           // def/thm/opaque
  HintKind hint = HintKind::Opaque;
  u32 height = 0;
  Safety safety = Safety::Safe;
  bool is_unsafe = false;
  std::vector<Name> all;
  // inductive
  u32 nparams = 0, nindices = 0, nnested = 0;
  std::vector<Name> ctors;
  bool is_rec = false, is_reflexive = false;
  // ctor
  Name induct = 0; u32 cidx = 0, nfields = 0;
  // rec
  u32 nmotives = 0, nminors = 0; bool k = false;
  std::vector<RecRule> rules;
  QuotKind quot_kind = QuotKind::Type;
  mutable int fix_idx = -1;   // fix.cpp: index of the definition's fixpoint-rule slot, -1 unknown

  bool has_value() const { return kind == CKind::Def || kind == CKind::Thm || kind == CKind::Opaque; }
  // Constants the kernel may delta-unfold: definitions and theorems (not opaque).
  bool is_delta() const { return kind == CKind::Def || kind == CKind::Thm; }
  u32 rec_major_idx() const { return nparams + nmotives + nminors + nindices; }
  u32 rec_first_index_idx() const { return nparams + nmotives + nminors; }
  Name rec_major_induct() const;  // set by loader: the inductive of the major premise
  Name major_induct = 0;
};

struct Environment {
  std::vector<ConstInfo> consts;
  std::unordered_map<Name, u32> index;
  std::vector<u32> by_name;     // Name handle -> index+1 (0 = absent); names are dense u32s
  bool quot_init = false;
  const ConstInfo* find(Name n) const {
    if (n < by_name.size()) { u32 i = by_name[n]; return i ? &consts[i - 1] : nullptr; }
    return nullptr;
  }
  const ConstInfo& get(Name n) const {
    const ConstInfo* c = find(n); if (!c) fail("unknown constant '" + name_str(n) + "'"); return *c;
  }
  bool contains(Name n) const { return find(n) != nullptr; }
  size_t mark() const { return consts.size(); }
  void rollback(size_t m) { while (consts.size() > m) { by_name[consts.back().name] = 0; index.erase(consts.back().name); consts.pop_back(); } }
  // Make a constant unreachable again so that checking the declaration that introduces it can
  // add it as usual.  Used when the whole environment was built before the workers forked: the
  // entry stays in `consts` but nothing can find it, and `add` then appends the checked one.
  void hide(Name n) {
    if (n < by_name.size()) by_name[n] = 0;
    index.erase(n);
  }
  void add(ConstInfo c) {
    if (contains(c.name)) fail("constant already declared: " + name_str(c.name));
    if (c.name >= by_name.size()) by_name.resize(std::max<size_t>(c.name + 1, by_name.size() * 2 + 1024), 0);
    by_name[c.name] = (u32)consts.size() + 1;
    index.emplace(c.name, (u32)consts.size());
    consts.push_back(std::move(c));
  }
  // A non-recursive inductive with one constructor and no indices (kernel `is_non_rec_structure`).
  bool is_structure_like(Name n) const {
    const ConstInfo* c = find(n);
    return c && c->kind == CKind::Induct && !c->is_rec && c->ctors.size() == 1 && c->nindices == 0;
  }
};

// One declaration as it appears in the export, in file order.
struct Decl {
  enum Kind { Axiom, Def, Thm, Opaque, Quot, Inductive } kind;
  std::vector<ConstInfo> consts;  // Inductive: all types, then ctors, then recs
  u32 nparams = 0;                // Inductive
  size_t ntypes = 0, nctors = 0, nrecs = 0;
  size_t line = 0;
};

struct ExportFile {
  std::vector<Decl> decls;
  size_t nnames = 0, nlevels = 0, nexprs = 0;
};

// Load an NDJSON export (format 3.x). Expressions are interned as they are read.
ExportFile load_export(const std::string& path, bool verbose);

} // namespace ll
