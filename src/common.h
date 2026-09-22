// Common definitions for lazylean, an external type checker for Lean 4 exports.
#pragma once
#include <cstdint>
#include <cstddef>
#include <string>
#include <string_view>
#include <vector>
#include <stdexcept>
#include <utility>

namespace ll {

using u8 = uint8_t;
using u32 = uint32_t;
using u64 = uint64_t;

// All interned objects are identified by a 32-bit index into a global table.
using Name = u32;    // 0 = anonymous
using Level = u32;   // 0 = zero
using Expr = u32;
using LevelList = u32; // index into the interned level-list table; 0 = empty list

constexpr u32 NIL = 0xFFFFFFFFu;

struct KernelError : std::runtime_error {
  using std::runtime_error::runtime_error;
};

[[noreturn]] inline void fail(const std::string& msg) { throw KernelError(msg); }

// 64-bit mixing for hash combination.
inline u64 mix(u64 h, u64 k) {
  k *= 0x9E3779B97F4A7C15ull;
  k ^= k >> 29;
  h ^= k;
  h *= 0xBF58476D1CE4E5B9ull;
  h ^= h >> 32;
  return h;
}
inline u64 hash_str(std::string_view s) {
  u64 h = 1469598103934665603ull;
  for (unsigned char c : s) { h ^= c; h *= 1099511628211ull; }
  return h;
}

// Open-addressing set of u32 handles keyed by a user-supplied hash/equality on the handle.
// Used to hash-cons names, levels and expressions: the candidate node is appended to the
// node table first, then looked up; if an equal node exists the candidate is popped.
template <class HashFn, class EqFn>
struct InternTable {
  // Open addressing, linear probing.  Each slot packs the upper 32 bits of the hash with the
  // handle, so a probe only touches the element (a random access into the node table) when the
  // tag matches.
  static constexpr u64 EMPTY = ~0ull;
  std::vector<u64> slots;
  size_t count = 0;
  HashFn hashfn; EqFn eqfn;
  InternTable(HashFn h, EqFn e, size_t cap = 1 << 16) : hashfn(h), eqfn(e) { slots.assign(cap, EMPTY); }
  static u64 pack(u64 hv, u32 h) { return (hv & 0xffffffff00000000ull) | h; }
  // Returns existing equal handle, or inserts h and returns h.
  size_t gen = 0;   // bumped by grow(); an equality test may intern recursively
  u32 intern(u32 h) {
    if ((count + 1) * 4 >= slots.size() * 3) grow();
    u64 hv = hashfn(h), tag = hv & 0xffffffff00000000ull;
  restart:
    size_t mask = slots.size() - 1;
    size_t i = hv & mask;
    size_t g0 = gen;
    while (true) {
      u64 s = slots[i];
      if (s == EMPTY) { slots[i] = pack(hv, h); count++; return h; }
      if ((s & 0xffffffff00000000ull) == tag) {
        bool eq = eqfn((u32)s, h);
        if (eq) return (u32)s;
        if (gen != g0) goto restart;
      }
      i = (i + 1) & mask;
    }
  }
  // Returns the existing equal handle or NIL; never inserts.
  u32 find(u32 h) const {
    u64 hv = hashfn(h), tag = hv & 0xffffffff00000000ull;
    size_t mask = slots.size() - 1;
    size_t i = hv & mask;
    while (true) {
      u64 s = slots[i];
      if (s == EMPTY) return NIL;
      if ((s & 0xffffffff00000000ull) == tag && eqfn((u32)s, h)) return (u32)s;
      i = (i + 1) & mask;
    }
  }
  void grow() {
    gen++;
    std::vector<u64> old; old.swap(slots);
    slots.assign(old.size() * 2, EMPTY);
    size_t mask = slots.size() - 1;
    for (u64 s : old) if (s != EMPTY) {
      size_t i = hashfn((u32)s) & mask;
      while (slots[i] != EMPTY) i = (i + 1) & mask;
      slots[i] = s;
    }
  }
};

} // namespace ll
