// Common definitions for lazylean, an external type checker for Lean 4 exports.
#pragma once
#include <cstdint>
#include <cstddef>
#include <string>
#include <string_view>
#include <vector>
#include <stdexcept>
#include <utility>
#include <type_traits>

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
// Open-addressing maps for the checker's per-declaration caches.  std::unordered_map
// allocates a node for every entry and frees them all when a declaration ends; these keep keys
// and values in flat arrays.  Entries move when the table grows, so an iterator must not be
// held across an insertion into the same map (no caller does).  Keys must not be NIL.
template <class V> struct FlatMap {
  struct Slot { u32 first; V second; };
  std::vector<Slot> tab; size_t n = 0;
  static size_t slot_of(u32 k, size_t mask) { return (size_t)((k * 0x9E3779B97F4A7C15ull) >> 29) & mask; }
  Slot* end() { return nullptr; }
  Slot* find(u32 k) {
    if (n == 0) return nullptr;
    size_t m = tab.size() - 1, i = slot_of(k, m);
    while (true) {
      Slot& s = tab[i];
      if (s.first == k) return &s;
      if (s.first == NIL) return nullptr;
      i = (i + 1) & m;
    }
  }
  size_t count(u32 k) { return find(k) ? 1 : 0; }
  void grow() {
    std::vector<Slot> old; old.swap(tab);
    tab.assign(old.empty() ? 64 : old.size() * 2, Slot{NIL, V{}});
    size_t m = tab.size() - 1;
    for (Slot& s : old) if (s.first != NIL) {
      size_t i = slot_of(s.first, m);
      while (tab[i].first != NIL) i = (i + 1) & m;
      tab[i] = std::move(s);
    }
  }
  // insert if absent (like unordered_map::emplace, whose result no caller uses)
  void emplace(u32 k, const V& v) {
    if ((n + 1) * 2 > tab.size()) grow();
    size_t m = tab.size() - 1, i = slot_of(k, m);
    while (true) {
      Slot& s = tab[i];
      if (s.first == k) return;
      if (s.first == NIL) { s.first = k; s.second = v; n++; return; }
      i = (i + 1) & m;
    }
  }
  V& operator[](u32 k) {
    if ((n + 1) * 2 > tab.size()) grow();
    size_t m = tab.size() - 1, i = slot_of(k, m);
    while (true) {
      Slot& s = tab[i];
      if (s.first == k) return s.second;
      if (s.first == NIL) { s.first = k; s.second = V{}; n++; return s.second; }
      i = (i + 1) & m;
    }
  }
  size_t size() const { return n; }
  void clear() { tab.clear(); n = 0; }
};

struct FlatSet64 {
  static constexpr u64 EMPTY = ~0ull;
  std::vector<u64> tab; size_t n = 0;
  static size_t slot_of(u64 k, size_t mask) { return (size_t)((k * 0x9E3779B97F4A7C15ull) >> 29) & mask; }
  size_t count(u64 k) const {
    if (n == 0) return 0;
    size_t m = tab.size() - 1, i = slot_of(k, m);
    while (true) { if (tab[i] == k) return 1; if (tab[i] == EMPTY) return 0; i = (i + 1) & m; }
  }
  void insert(u64 k) {
    if (k == EMPTY) return;
    if ((n + 1) * 2 > tab.size()) {
      std::vector<u64> old; old.swap(tab);
      tab.assign(old.empty() ? 64 : old.size() * 2, EMPTY);
      size_t m = tab.size() - 1;
      for (u64 x : old) if (x != EMPTY) { size_t i = slot_of(x, m); while (tab[i] != EMPTY) i = (i + 1) & m; tab[i] = x; }
    }
    size_t m = tab.size() - 1, i = slot_of(k, m);
    while (true) { if (tab[i] == k) return; if (tab[i] == EMPTY) { tab[i] = k; n++; return; } i = (i + 1) & m; }
  }
  size_t size() const { return n; }
};

// Ask for 2 MB pages on a large, not yet touched region.  The permanent tier is gigabytes of
// data read in random order, and with 4 KB pages nearly every lookup also misses the TLB.
void advise_huge(void* p, size_t bytes);

template <class HashFn, class EqFn, bool Compact = false>
struct InternTable {
  // Open addressing, linear probing.  Each slot packs the upper 32 bits of the hash with the
  // handle, so a probe only touches the element (a random access into the node table) when the
  // tag matches.  A Compact table stores the bare handle (4 bytes a slot, half the memory), and
  // every probe of an occupied slot compares the element: for the permanent expression index,
  // which after loading is probed only when the kernel builds a term.
  using Slot = std::conditional_t<Compact, u32, u64>;
  static constexpr Slot EMPTY = (Slot)~(Slot)0;
  std::vector<Slot> slots;
  size_t count = 0;
  HashFn hashfn; EqFn eqfn;
  InternTable(HashFn h, EqFn e, size_t cap = 1 << 16) : hashfn(h), eqfn(e) { slots.assign(cap, EMPTY); }
  static Slot pack(u64 hv, u32 h) { if constexpr (Compact) { (void)hv; return h; } else return (hv & 0xffffffff00000000ull) | h; }
  // a cheap filter before the equality test: the tag, or (compact) the element's own hash
  bool tag_ok(Slot s, u64 hv) const { if constexpr (Compact) return hashfn((u32)s) == hv; else return (s & 0xffffffff00000000ull) == (hv & 0xffffffff00000000ull); }
  // Returns existing equal handle, or inserts h and returns h.
  size_t gen = 0;   // bumped by grow(); an equality test may intern recursively
  // A temporary table records the slots it fills, so that emptying it after a declaration
  // costs the entries that declaration made rather than the table's whole capacity.
  bool track = false;
  std::vector<u32> dirty;
  void clear_used() {
    for (u32 i : dirty) slots[i] = EMPTY;
    dirty.clear(); count = 0;
  }
  u32 intern(u32 h) {
    if ((count + 1) * 4 >= slots.size() * 3) grow();
    u64 hv = hashfn(h);
  restart:
    size_t mask = slots.size() - 1;
    size_t i = hv & mask;
    size_t g0 = gen;
    while (true) {
      Slot s = slots[i];
      if (s == EMPTY) { slots[i] = pack(hv, h); count++; if (track) dirty.push_back((u32)i); return h; }
      if (tag_ok(s, hv)) {
        bool eq = eqfn((u32)s, h);
        if (eq) return (u32)s;
        if (gen != g0) goto restart;
      }
      i = (i + 1) & mask;
    }
  }
  // Returns the existing equal handle or NIL; never inserts.
  u32 find(u32 h) const {
    u64 hv = hashfn(h);
    size_t mask = slots.size() - 1;
    size_t i = hv & mask;
    while (true) {
      Slot s = slots[i];
      if (s == EMPTY) return NIL;
      if (tag_ok(s, hv) && eqfn((u32)s, h)) return (u32)s;
      i = (i + 1) & mask;
    }
  }
  // Insert handles [lo, hi) that are known to be distinct, from several threads at once.  An
  // entry that compares equal to one already present sets *dup and is not inserted: the caller
  // then has to fall back to ordinary interning, which maps equal terms to one handle.
  void bulk_insert(u32 lo, u32 hi, bool* dup) {
    const size_t mask = slots.size() - 1;
    for (u32 h = lo; h < hi; h++) {
      u64 hv = hashfn(h); Slot want = pack(hv, h);
      size_t i = hv & mask;
      while (true) {
        Slot s = __atomic_load_n(&slots[i], __ATOMIC_RELAXED);
        if (s == EMPTY) {
          Slot exp = EMPTY;
          if (__atomic_compare_exchange_n(&slots[i], &exp, want, false, __ATOMIC_RELAXED, __ATOMIC_RELAXED)) break;
          continue;   // lost the race for this slot: look at it again
        }
        if (tag_ok(s, hv) && eqfn((u32)s, h)) { __atomic_store_n(dup, true, __ATOMIC_RELAXED); break; }
        i = (i + 1) & mask;
      }
    }
  }
  // Size the table for n entries up front, so that a bulk load never pays for rehashing.
  void reserve(size_t n) {
    size_t want = slots.size();
    while (n * 4 >= want * 3) want *= 2;
    if (want == slots.size()) return;
    if (count == 0) {
      std::vector<Slot>().swap(slots);
      slots.reserve(want);
      advise_huge(slots.data(), want * sizeof(Slot));
      slots.assign(want, EMPTY);
      return;
    }
    while (slots.size() < want) grow();
  }
  void grow() {
    gen++;
    std::vector<Slot> old; old.swap(slots);
    slots.assign(old.size() * 2, EMPTY);
    size_t mask = slots.size() - 1;
    if (track) dirty.clear();
    for (Slot s : old) if (s != EMPTY) {
      size_t i = hashfn((u32)s) & mask;
      while (slots[i] != EMPTY) i = (i + 1) & mask;
      slots[i] = s;
      if (track) dirty.push_back((u32)i);
    }
  }
};

} // namespace ll
