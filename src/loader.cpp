#include "env.h"
#include "json.h"
#include <fstream>
#include <iostream>
#include <cstring>
#include <cstdlib>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

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


  // ---- fast path --------------------------------------------------------------------------
  // lean4export writes a handful of line shapes with sorted keys and no whitespace, and nearly
  // every line is one of them.  They are recognised byte by byte here, with no allocation;
  // anything that does not match exactly (an escape in a string, an unexpected key, a
  // declaration) goes through the general JSON reader instead, so the fast path can only
  // decline a line, never misread one.
  struct Cur {
    const char* p; const char* e;
    template <size_t N> bool lit(const char (&s)[N]) {
      constexpr size_t n = N - 1;
      if ((size_t)(e - p) < n || memcmp(p, s, n) != 0) return false;
      p += n; return true;
    }
    bool num(u64& v) {
      if (p >= e || *p < '0' || *p > '9') return false;
      u64 x = 0;
      while (p < e && *p >= '0' && *p <= '9') { x = x * 10 + (u64)(*p - '0'); p++; }
      v = x; return true;
    }
    bool at_end() const { return p == e; }
  };
  bool binfo_fast(Cur& c, BInfo& bi) {
    if (c.lit("default\"")) { bi = BInfo::Default; return true; }
    if (c.lit("implicit\"")) { bi = BInfo::Implicit; return true; }
    if (c.lit("instImplicit\"")) { bi = BInfo::InstImplicit; return true; }
    if (c.lit("strictImplicit\"")) { bi = BInfo::StrictImplicit; return true; }
    return false;
  }
  Expr exi(u64 i) { if (i >= exprs.size()) fail("expr index out of range"); return exprs[i]; }
  Name nmi(u64 i) { if (i >= names.size()) fail("name index out of range"); return names[i]; }
  Level lvi(u64 i) { if (i >= levels.size()) fail("level index out of range"); return levels[i]; }
  void put_expr(u64 idx, Expr e) { set_at(exprs, idx, e); out.nexprs++; }

  bool fast(const char* b, const char* e) {
    Cur c{b, e};
    u64 n, a, f, t, bd, nm_;
    BInfo bi;
    if (c.lit("{\"app\":{\"arg\":")) {
      if (c.num(a) && c.lit(",\"fn\":") && c.num(f) && c.lit("},\"ie\":") && c.num(n) && c.lit("}") && c.at_end()) {
        put_expr(n, mk_app(exi(f), exi(a))); return true;
      }
      return false;
    }
    if (c.lit("{\"ie\":")) {
      if (!c.num(n)) return false;
      if (c.lit(",\"lam\":{\"binderInfo\":\"")) {
        if (binfo_fast(c, bi) && c.lit(",\"body\":") && c.num(bd) && c.lit(",\"name\":") && c.num(nm_) &&
            c.lit(",\"type\":") && c.num(t) && c.lit("}}") && c.at_end()) {
          put_expr(n, mk_lam(nmi(nm_), exi(t), exi(bd), bi)); return true;
        }
        return false;
      }
      if (c.lit(",\"sort\":")) {
        if (c.num(a) && c.lit("}") && c.at_end()) { put_expr(n, mk_sort(lvi(a))); return true; }
        return false;
      }
      return false;
    }
    if (c.lit("{\"forallE\":{\"binderInfo\":\"")) {
      if (binfo_fast(c, bi) && c.lit(",\"body\":") && c.num(bd) && c.lit(",\"name\":") && c.num(nm_) &&
          c.lit(",\"type\":") && c.num(t) && c.lit("},\"ie\":") && c.num(n) && c.lit("}") && c.at_end()) {
        put_expr(n, mk_pi(nmi(nm_), exi(t), exi(bd), bi)); return true;
      }
      return false;
    }
    if (c.lit("{\"const\":{\"name\":")) {
      if (!c.num(nm_) || !c.lit(",\"us\":[")) return false;
      lv_scratch.clear();
      if (!c.lit("]")) {
        while (true) {
          if (!c.num(a)) return false;
          lv_scratch.push_back(lvi(a));
          if (c.lit(",")) continue;
          if (c.lit("]")) break;
          return false;
        }
      }
      if (c.lit("},\"ie\":") && c.num(n) && c.lit("}") && c.at_end()) {
        put_expr(n, mk_const(nmi(nm_), g_levels->mk_list(lv_scratch))); return true;
      }
      return false;
    }
    if (c.lit("{\"bvar\":")) {
      if (c.num(a) && c.lit(",\"ie\":") && c.num(n) && c.lit("}") && c.at_end()) {
        put_expr(n, mk_bvar((u32)a)); return true;
      }
      return false;
    }
    if (c.lit("{\"in\":")) {
      if (!c.num(n)) return false;
      if (c.lit(",\"str\":{\"pre\":")) {
        if (!c.num(a) || !c.lit(",\"str\":\"")) return false;
        const char* s0 = c.p;
        while (c.p < c.e && *c.p != '"' && *c.p != '\\') c.p++;
        if (c.p >= c.e || *c.p != '"') return false;   // an escape: let the JSON reader decode it
        std::string_view sv(s0, (size_t)(c.p - s0));
        c.p++;
        if (!c.lit("}}") || !c.at_end()) return false;
        set_at(names, n, g_names->mk_str(nmi(a), sv)); out.nnames++; return true;
      }
      if (c.lit(",\"num\":{\"i\":")) {
        if (c.num(a) && c.lit(",\"pre\":") && c.num(f) && c.lit("}}") && c.at_end()) {
          set_at(names, n, g_names->mk_num(nmi(f), a)); out.nnames++; return true;
        }
        return false;
      }
      return false;
    }
    return false;
  }
  std::vector<Level> lv_scratch;

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

static ExportFile load_once(const std::string& path, bool verbose, bool bulk);

// lean4export writes every expression exactly once, so the permanent tier is built by appending
// nodes and indexing them in parallel afterwards.  Should two turn out equal, the file is loaded
// again with ordinary interning, which is what gives equal terms a single handle.
ExportFile load_export(const std::string& path, bool verbose) {
  static const bool no_bulk = getenv("LL_LOAD_SEQUENTIAL") != nullptr;
  if (!no_bulk) {
    ExportFile ef = load_once(path, verbose, true);
    if (g_exprs->build_index(8)) return ef;
    std::cerr << "note: the export repeats an expression; loading it again with ordinary interning\n";
    g_exprs->reset_permanent();
  }
  return load_once(path, verbose, false);
}

static ExportFile load_once(const std::string& path, bool verbose, bool bulk) {
  int fd = open(path.c_str(), O_RDONLY);
  if (fd < 0) fail("cannot open " + path);
  struct stat stt; if (fstat(fd, &stt) != 0) { close(fd); fail("cannot stat " + path); }
  size_t sz = (size_t)stt.st_size;
  Loader L;
  if (sz == 0) { close(fd); return std::move(L.out); }
  const char* base = (const char*)mmap(nullptr, sz, PROT_READ, MAP_PRIVATE, fd, 0);
  close(fd);
  if (base == MAP_FAILED) fail("cannot map " + path);
  madvise((void*)base, sz, MADV_SEQUENTIAL);
  const char* end = base + sz;
  // Size the tables once, from the line count: nearly every line of an export is an expression,
  // and growing an intern table of tens of millions of entries rehashes all of them each time.
  // An export line is rarely under 30 bytes, so this bounds the number of expressions from above
  // without reading the file twice.  Only address space is reserved: pages are touched as they
  // fill, and the permanent hash table is sized exactly, from the node count, when it is built.
  size_t lines = sz / 30 + 1024;
  g_exprs->reserve_permanent(lines, !bulk);
  g_exprs->bulk = bulk;
  g_names->reserve(lines / 40);
  L.exprs.reserve(lines);
  advise_huge(L.exprs.data(), lines * sizeof(Expr));
  L.names.reserve(lines / 8);
  static const bool no_fast = getenv("LL_LOAD_SLOW") != nullptr;   // testing: force the JSON reader
  // The mapped file would otherwise stay resident for the whole load (gigabytes for Mathlib), on
  // top of what the load builds; pages already read are handed back as the cursor moves on.
  const size_t page = (size_t)sysconf(_SC_PAGESIZE), window = (size_t)64 << 20;
  const char* released = base;
  for (const char* q = base; q < end; ) {
    if ((size_t)(q - released) > window) {
      const char* upto = base + (((size_t)(q - base)) / page) * page;
      madvise((void*)released, (size_t)(upto - released), MADV_DONTNEED);
      released = upto;
    }
    const char* nl = (const char*)memchr(q, '\n', (size_t)(end - q));
    const char* le = nl ? nl : end;
    L.line++;
    const char* lb = q;
    const char* lx = le;
    if (lx > lb && lx[-1] == '\r') lx--;
    q = nl ? nl + 1 : end;
    if (lx == lb) continue;
    try {
      if (no_fast || !L.fast(lb, lx)) {
        JParser pz(lb, lx);
        JVal v = pz.parse();
        L.handle(v);
      }
    } catch (KernelError& e) {
      munmap((void*)base, sz);
      fail("line " + std::to_string(L.line) + ": " + e.what());
    }
    if (verbose && L.line % 1000000 == 0) std::cerr << "  ... " << L.line << " lines\n";
  }
  munmap((void*)base, sz);
  if (getenv("LL_LOAD_CHECKSUM")) {
    // testing: a digest of everything the load produced, in index order, to compare loaders
    u64 h = 0x9E3779B97F4A7C15ull;
    for (Expr e : L.exprs) h = mix(h, e == NIL ? 0 : raw(e).hash);
    for (Name n : L.names) h = mix(h, n == NIL ? 0 : (*g_names)[n].hash);
    for (Level l : L.levels) h = mix(h, l);
    std::cerr << "load checksum " << std::hex << h << std::dec << " exprs " << L.exprs.size()
              << " names " << L.names.size() << " levels " << L.levels.size() << "\n";
  }
  return std::move(L.out);
}

} // namespace ll
