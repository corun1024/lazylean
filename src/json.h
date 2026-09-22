// Minimal JSON reader for the NDJSON export: one line = one object.
#pragma once
#include "common.h"
#include <map>
#include <memory>

namespace ll {

struct JVal {
  enum T { Null, Bool, Num, Str, Arr, Obj } t = Null;
  bool b = false;
  std::string s;           // Num keeps its textual form (may be a big integer)
  std::vector<JVal> arr;
  std::vector<std::pair<std::string, JVal>> obj;
  const JVal* get(const char* k) const {
    for (auto& p : obj) if (p.first == k) return &p.second;
    return nullptr;
  }
  const JVal& at(const char* k) const {
    const JVal* v = get(k); if (!v) fail(std::string("missing JSON field ") + k); return *v;
  }
  u64 num() const {
    if (t != Num) fail("JSON: expected number");
    return std::stoull(s);
  }
};

struct JParser {
  const char* p; const char* end;
  JParser(const char* b, const char* e) : p(b), end(e) {}
  void ws() { while (p < end && (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n')) p++; }
  [[noreturn]] void err(const char* m) { fail(std::string("JSON parse error: ") + m); }
  JVal parse() { ws(); JVal v = value(); return v; }
  JVal value() {
    ws();
    if (p >= end) err("unexpected end");
    JVal v;
    switch (*p) {
      case '{': {
        v.t = JVal::Obj; p++; ws();
        if (p < end && *p == '}') { p++; return v; }
        while (true) {
          ws(); std::string k = string(); ws();
          if (p >= end || *p != ':') err("expected ':'");
          p++;
          JVal x = value();
          v.obj.emplace_back(std::move(k), std::move(x));
          ws();
          if (p < end && *p == ',') { p++; continue; }
          if (p < end && *p == '}') { p++; return v; }
          err("expected ',' or '}'");
        }
      }
      case '[': {
        v.t = JVal::Arr; p++; ws();
        if (p < end && *p == ']') { p++; return v; }
        while (true) {
          v.arr.push_back(value()); ws();
          if (p < end && *p == ',') { p++; continue; }
          if (p < end && *p == ']') { p++; return v; }
          err("expected ',' or ']'");
        }
      }
      case '"': v.t = JVal::Str; v.s = string(); return v;
      case 't': if (end - p >= 4 && std::string_view(p, 4) == "true") { p += 4; v.t = JVal::Bool; v.b = true; return v; } err("bad literal");
      case 'f': if (end - p >= 5 && std::string_view(p, 5) == "false") { p += 5; v.t = JVal::Bool; v.b = false; return v; } err("bad literal");
      case 'n': if (end - p >= 4 && std::string_view(p, 4) == "null") { p += 4; return v; } err("bad literal");
      default: {
        const char* s = p;
        if (*p == '-') p++;
        while (p < end && ((*p >= '0' && *p <= '9') || *p == '.' || *p == 'e' || *p == 'E' || *p == '+' || *p == '-')) p++;
        if (s == p) err("unexpected character");
        v.t = JVal::Num; v.s.assign(s, p - s); return v;
      }
    }
  }
  static void put_utf8(std::string& out, u32 cp) {
    if (cp < 0x80) out += (char)cp;
    else if (cp < 0x800) { out += (char)(0xC0 | (cp >> 6)); out += (char)(0x80 | (cp & 0x3F)); }
    else if (cp < 0x10000) { out += (char)(0xE0 | (cp >> 12)); out += (char)(0x80 | ((cp >> 6) & 0x3F)); out += (char)(0x80 | (cp & 0x3F)); }
    else { out += (char)(0xF0 | (cp >> 18)); out += (char)(0x80 | ((cp >> 12) & 0x3F)); out += (char)(0x80 | ((cp >> 6) & 0x3F)); out += (char)(0x80 | (cp & 0x3F)); }
  }
  std::string string() {
    if (p >= end || *p != '"') err("expected string");
    p++;
    std::string out;
    while (p < end && *p != '"') {
      if (*p == '\\') {
        p++; if (p >= end) err("bad escape");
        char c = *p++;
        switch (c) {
          case '"': out += '"'; break; case '\\': out += '\\'; break; case '/': out += '/'; break;
          case 'b': out += '\b'; break; case 'f': out += '\f'; break; case 'n': out += '\n'; break;
          case 'r': out += '\r'; break; case 't': out += '\t'; break;
          case 'u': {
            auto hex4 = [&]() { u32 v = 0; for (int i = 0; i < 4; i++) { char h = *p++; v <<= 4;
              if (h >= '0' && h <= '9') v |= h - '0'; else if (h >= 'a' && h <= 'f') v |= h - 'a' + 10;
              else if (h >= 'A' && h <= 'F') v |= h - 'A' + 10; else err("bad \\u"); } return v; };
            u32 cp = hex4();
            if (cp >= 0xD800 && cp < 0xDC00 && end - p >= 6 && p[0] == '\\' && p[1] == 'u') {
              p += 2; u32 lo = hex4(); cp = 0x10000 + ((cp - 0xD800) << 10) + (lo - 0xDC00);
            }
            put_utf8(out, cp); break;
          }
          default: err("bad escape");
        }
      } else out += *p++;
    }
    if (p >= end) err("unterminated string");
    p++;
    return out;
  }
};

} // namespace ll
