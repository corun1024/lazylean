#include "env.h"
#include "json.h"
#include <fstream>
#include <iostream>
#include <cstring>

namespace ll {

namespace {
struct Loader {
  std::vector<Name> names{0};      // export index -> Name
  std::vector<Level> levels{0};    // export index -> Level
  std::vector<Expr> exprs;         // export index -> Expr
  ExportFile out;
  size_t line = 0;

  Name nm(const JVal& v) { u64 i = v.num(); if (i >= names.size()) fail("name index out of range"); return names[i]; }
  Level lvl(const JVal& v) { u64 i = v.num(); if (i >= levels.size()) fail("level index out of range"); return levels[i]; }
  Expr ex_(const JVal& v) { u64 i = v.num(); if (i >= exprs.size()) fail("expr index out of range"); return exprs[i]; }
  std::vector<Name> nms(const JVal& v) { std::vector<Name> r; for (auto& x : v.arr) r.push_back(nm(x)); return r; }
  std::vector<Level> lvls(const JVal& v) { std::vector<Level> r; for (auto& x : v.arr) r.push_back(lvl(x)); return r; }

  static void set_at(std::vector<u32>& vec, u64 idx, u32 val) {
    if (idx != vec.size()) {
      if (idx > vec.size()) vec.resize(idx + 1, NIL);
      if (idx < vec.size() && vec[idx] != NIL && vec[idx] != val && idx < vec.size()) {
        // duplicate index with different value: export files are expected to be dense/unique
      }
    }
    if (idx == vec.size()) vec.push_back(val); else vec[idx] = val;
  }

  BInfo binfo(const JVal& v) {
    if (v.s == "default") return BInfo::Default;
    if (v.s == "implicit") return BInfo::Implicit;
    if (v.s == "strictImplicit") return BInfo::StrictImplicit;
    if (v.s == "instImplicit") return BInfo::InstImplicit;
    fail("bad binderInfo " + v.s);
  }

  void const_common(ConstInfo& c, const JVal& o) {
    c.name = nm(o.at("name"));
    c.lparams = nms(o.at("levelParams"));
    c.type = ex_(o.at("type"));
  }

  void handle(const JVal& o) {
    if (const JVal* v = o.get("in")) {
      u64 idx = v->num();
      Name n;
      if (const JVal* s = o.get("str")) n = g_names->mk_str(nm(s->at("pre")), s->at("str").s);
      else if (const JVal* s = o.get("num")) n = g_names->mk_num(nm(s->at("pre")), s->at("i").num());
      else fail("bad name line");
      set_at(names, idx, n); out.nnames++; return;
    }
    if (const JVal* v = o.get("il")) {
      u64 idx = v->num();
      Level l;
      if (const JVal* s = o.get("succ")) l = mk_succ(lvl(*s));
      else if (const JVal* s = o.get("max")) l = mk_max_raw(lvl(s->arr.at(0)), lvl(s->arr.at(1)));
      else if (const JVal* s = o.get("imax")) l = mk_imax_raw(lvl(s->arr.at(0)), lvl(s->arr.at(1)));
      else if (const JVal* s = o.get("param")) l = mk_param(nm(*s));
      else fail("bad level line");
      set_at(levels, idx, l); out.nlevels++; return;
    }
    if (const JVal* v = o.get("ie")) {
      u64 idx = v->num();
      Expr e;
      if (const JVal* s = o.get("bvar")) e = mk_bvar((u32)s->num());
      else if (const JVal* s = o.get("sort")) e = mk_sort(lvl(*s));
      else if (const JVal* s = o.get("const")) e = mk_const(nm(s->at("name")), g_levels->mk_list(lvls(s->at("us"))));
      else if (const JVal* s = o.get("app")) e = mk_app(ex_(s->at("fn")), ex_(s->at("arg")));
      else if (const JVal* s = o.get("lam")) e = mk_lam(nm(s->at("name")), ex_(s->at("type")), ex_(s->at("body")), binfo(s->at("binderInfo")));
      else if (const JVal* s = o.get("forallE")) e = mk_pi(nm(s->at("name")), ex_(s->at("type")), ex_(s->at("body")), binfo(s->at("binderInfo")));
      else if (const JVal* s = o.get("letE")) e = mk_let(nm(s->at("name")), ex_(s->at("type")), ex_(s->at("value")), ex_(s->at("body")));
      else if (const JVal* s = o.get("proj")) e = mk_proj(nm(s->at("typeName")), (u32)s->at("idx").num(), ex_(s->at("struct")));
      else if (const JVal* s = o.get("natVal")) e = mk_nat_lit(mpz_class(s->s, 0));   // base 0: decimal, or 0x-prefixed hex
      else if (const JVal* s = o.get("strVal")) e = mk_str_lit(s->s);
      else if (const JVal* s = o.get("mdata")) e = ex_(s->at("expr"));
      else fail("bad expr line");
      set_at(exprs, idx, e); out.nexprs++; return;
    }
    if (o.get("meta")) return;
    Decl d; d.line = line;
    if (const JVal* s = o.get("axiom")) {
      d.kind = Decl::Axiom; ConstInfo c; c.kind = CKind::Axiom; const_common(c, *s);
      c.is_unsafe = s->at("isUnsafe").b; d.consts.push_back(c);
    } else if (const JVal* s = o.get("def")) {
      d.kind = Decl::Def; ConstInfo c; c.kind = CKind::Def; const_common(c, *s);
      c.value = ex_(s->at("value"));
      const JVal& h = s->at("hints");
      if (h.t == JVal::Str) c.hint = h.s == "opaque" ? HintKind::Opaque : HintKind::Abbrev;
      else { c.hint = HintKind::Regular; c.height = (u32)h.at("regular").num(); }
      const std::string& sf = s->at("safety").s;
      c.safety = sf == "unsafe" ? Safety::Unsafe : sf == "partial" ? Safety::Partial : Safety::Safe;
      c.is_unsafe = c.safety == Safety::Unsafe;
      c.all = nms(s->at("all")); d.consts.push_back(c);
    } else if (const JVal* s = o.get("thm")) {
      d.kind = Decl::Thm; ConstInfo c; c.kind = CKind::Thm; const_common(c, *s);
      c.value = ex_(s->at("value")); c.all = nms(s->at("all")); d.consts.push_back(c);
    } else if (const JVal* s = o.get("opaque")) {
      d.kind = Decl::Opaque; ConstInfo c; c.kind = CKind::Opaque; const_common(c, *s);
      c.value = ex_(s->at("value")); c.all = nms(s->at("all")); c.is_unsafe = s->at("isUnsafe").b;
      d.consts.push_back(c);
    } else if (const JVal* s = o.get("quot")) {
      d.kind = Decl::Quot; ConstInfo c; c.kind = CKind::Quot; const_common(c, *s);
      const std::string& k = s->at("kind").s;
      c.quot_kind = k == "type" ? QuotKind::Type : k == "ctor" ? QuotKind::Ctor : k == "lift" ? QuotKind::Lift : QuotKind::Ind;
      d.consts.push_back(c);
    } else if (const JVal* s = o.get("inductive")) {
      d.kind = Decl::Inductive;
      for (auto& t : s->at("types").arr) {
        ConstInfo c; c.kind = CKind::Induct; const_common(c, t);
        c.nparams = (u32)t.at("numParams").num(); c.nindices = (u32)t.at("numIndices").num();
        c.all = nms(t.at("all")); c.ctors = nms(t.at("ctors")); c.nnested = (u32)t.at("numNested").num();
        c.is_rec = t.at("isRec").b; c.is_reflexive = t.at("isReflexive").b; c.is_unsafe = t.at("isUnsafe").b;
        d.consts.push_back(c); d.ntypes++;
        d.nparams = c.nparams;
      }
      for (auto& t : s->at("ctors").arr) {
        ConstInfo c; c.kind = CKind::Ctor; const_common(c, t);
        c.induct = nm(t.at("induct")); c.cidx = (u32)t.at("cidx").num();
        c.nparams = (u32)t.at("numParams").num(); c.nfields = (u32)t.at("numFields").num();
        c.is_unsafe = t.at("isUnsafe").b; d.consts.push_back(c); d.nctors++;
      }
      for (auto& t : s->at("recs").arr) {
        ConstInfo c; c.kind = CKind::Rec; const_common(c, t);
        c.all = nms(t.at("all")); c.nparams = (u32)t.at("numParams").num(); c.nindices = (u32)t.at("numIndices").num();
        c.nmotives = (u32)t.at("numMotives").num(); c.nminors = (u32)t.at("numMinors").num();
        c.k = t.at("k").b; c.is_unsafe = t.at("isUnsafe").b;
        for (auto& r : t.at("rules").arr) c.rules.push_back(RecRule{nm(r.at("ctor")), (u32)r.at("nfields").num(), ex_(r.at("rhs"))});
        d.consts.push_back(c); d.nrecs++;
      }
    } else {
      fail("unknown line kind");
    }
    out.decls.push_back(std::move(d));
  }
};
} // namespace

ExportFile load_export(const std::string& path, bool verbose) {
  std::ifstream in(path, std::ios::binary);
  if (!in) fail("cannot open " + path);
  Loader L;
  std::string buf;
  while (std::getline(in, buf)) {
    L.line++;
    if (buf.empty()) continue;
    try {
      JParser p(buf.data(), buf.data() + buf.size());
      JVal v = p.parse();
      L.handle(v);
    } catch (KernelError& e) {
      fail("line " + std::to_string(L.line) + ": " + e.what());
    }
    if (verbose && L.line % 1000000 == 0) std::cerr << "  ... " << L.line << " lines\n";
  }
  return std::move(L.out);
}

} // namespace ll
