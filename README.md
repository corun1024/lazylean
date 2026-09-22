# lazylean

A type checker for Lean 4 that reduces terms the way the Coq kernel does.

It reads the standard `lean4export` format and re-checks every declaration: definitions,
theorems, axioms, quotients, and inductive types with their recursors re-derived from scratch.
The type-checking algorithm is the one in Lean's own kernel. The reduction engine is not. Where
Lean's kernel rewrites terms by substitution, lazylean runs a Krivine machine with call-by-need
thunks, after Coq's `cClosure`.

The difference shows up on proofs that compute. On the Lean Kernel Arena's performance suite
lazylean is the fastest checker on 23 tests taken together, on one thread, in a fifth of the
memory; on whole-library corpora such as Mathlib it is faster than Lean's kernel and slower
than the multi-threaded specialised checkers. On the Four Colour Theorem's 201 672-declaration
dependency closure it needs 3.9
core-hours where Lean's kernel needs 7.5, and where Lean's kernel dies at 178 GB on a raw port
of Gonthier's reducibility check, lazylean finishes it in 21 GB.

```
lean4export Foo -- Foo.theorem > foo.ndjson
lazylean foo.ndjson        # exit 0: every declaration accepted
```

## Contents

- [Why a lazy kernel](#why-a-lazy-kernel)
- [How it works](#how-it-works)
- [Performance](#performance)
- [How it was tested](#how-it-was-tested)
- [Building and running](#building-and-running)
- [Limitations](#limitations)
- [Provenance and license](#provenance-and-license)

## Why a lazy kernel

A kernel spends its time deciding whether two terms are definitionally equal, and most of that
is weak-head normalisation: unfold a definition, β-reduce, fire a recursor, repeat until a
constructor or a stuck head appears.

Lean's kernel does this by substitution. A β step instantiates the body, copying its spine.
A recursive function unfolds through the chain the equation compiler produced, and every
intermediate term is a fresh tree. Sharing comes from hash caches keyed by term, and those
caches live for the whole declaration, so memory grows with the total amount of work done, not
with the amount of data alive.

Coq's kernel, since Barras's work in the nineties, does it with an abstract machine. A closure
is a term plus an environment giving values to its bound variables. β is a cons onto the
environment. An argument is a *thunk*, and the first time a thunk is forced it is overwritten
with its value, so every other reference to it sees the result: call by need. Nothing is copied,
nothing is rewritten, and whatever is unreferenced is garbage.

On ordinary library code the two designs are hard to tell apart. On a proof that evaluates a
decision procedure over a large search space they differ by one to two orders of magnitude, in
time and especially in memory. The Four Colour Theorem is the canonical example: Gonthier's
Coq proof checks 633 configurations by running a Kempe-chain closure inside the kernel. A Lean
port of that check makes Lean's kernel unusable past ring size 12, at 166 GB. lazylean was
written to close that gap while keeping Lean's logic and Lean's verdicts.

## How it works

### The data

Everything is interned. Names, universe levels and expressions live in tables and are referred
to by 32-bit handles, so structural equality is an integer comparison and hashing is free.

```
   names    ┌────┬──────────┐        exprs    ┌──────┬────┬────┬────┬──────┐
   u32 ───► │ .. │ Nat.succ │        u32 ───► │ kind │ a  │ b  │ c  │ hash │
            └────┴──────────┘                 ├──────┼────┼────┼────┼──────┤
                                              │ App  │ f  │ x  │    │  ..  │
   levels   ┌────┬──────────┐                 │ Lam  │ ty │ bd │    │  ..  │
   u32 ───► │ .. │ succ u   │                 │ Clos │ t  │env │ p  │  ..  │
            └────┴──────────┘                 └──────┴────┴────┴────┴──────┘
```

The expression table has two tiers. Everything the loader creates is permanent. Everything
created while checking a declaration goes into a temporary tier that is truncated when the
declaration is done, so a 700 000-declaration export runs at a flat memory profile.

One node kind, `Clos`, is a suspended substitution: a term, an environment of values for its
bound variables, and a prefix depth below which nothing is substituted. `instantiate` on a
large body returns a `Clos` in constant time. The node exposes itself one level at a time when
something looks at it, and it is hash-consed *modulo materialisation*: a closure and its
materialised form intern to the same handle, so identity survives.

### The type checker

`src/tc.cpp` is a re-implementation of the algorithm in Lean's C++ kernel, checked against
lean4lean as a second reference: the same order of checks in `is_def_eq`, the same lazy delta
reduction driven by reducibility hints, the same treatment of `Nat` and `String` literals,
proof irrelevance, eta for functions and structures, unit-like types and K-like recursors.
`src/inductive.cpp` re-checks inductive blocks the way `add_inductive` does, including the
elimination of nested inductives, and derives the recursors itself; the derived recursors are
then compared with the ones in the export.

Two caches were added that Lean does not keep. One is a union-find over terms already found
convertible, consulted by the quick structural check. The other is a negative cache of pairs
already found *not* convertible. A handful of Mathlib declarations compare the same failing pair
millions of times, and without the second cache one of them takes 9.6 million conversion calls
and 2.5 GB where it now takes eleven thousand.

### The machine

A machine state is a head term under an environment, plus a stack of frames.

```
    head: (fun x => f x x)      env: [ a ↦ thunk ]
                                     │
   stack (top first)                 ▼
   ┌─────┬──────────────┐      ┌──────────────────────────┐
   │ Arg │ thunk(b, env)│      │ thunk                    │
   ├─────┼──────────────┤      │  state: delayed | forced │
   │ Upd │ thunk #17    │◄───┐ │  term, env       (closure)│
   ├─────┼──────────────┤    │ │  vterm, venv, args (value)│
   │ RecK│ List.rec …   │    │ └──────────────────────────┘
   └─────┴──────────────┘    │
                             └── overwritten with the value when the head above it is a whnf
```

- `Arg` frames carry pending arguments as thunks.
- `Upd` frames mark a thunk whose value is being computed. When the head above the mark
  reaches weak-head normal form, the thunk is overwritten with it. Every other pointer to the
  thunk now sees the value, which is what makes the machine call-by-need rather than
  call-by-name.
- `RecK`, `ProjK`, `NatK` and `QuotK` frames are continuations waiting on an argument: a
  recursor's major premise, a projection's structure, a `Nat` primitive's operand, a
  quotient's `Quot.mk`.

β pushes the argument thunk onto the environment. δ replaces the head with the definition's
body, universe-instantiated and cached. ι forces the major premise, looks up the constructor's
rule and binds the fields. `Nat.add`, `Nat.mul`, `Nat.ble` and friends run in GMP once both
operands are literals, which is how million-bit literals are handled. A bound variable in
argument position is resolved to its environment entry instead of getting a closure of its own.
The loop never recurses in C++: a reduction of any length runs in constant stack.

Thunks and environments are reference counted. The structures are acyclic by construction (a
thunk can only refer to thunks created before it), so there is no cycle collector, and memory
tracks the live data. One rule turned out to matter more than any other for memory: a value
keeps its environment only if its head still has free variables. A constructor cell that keeps
the environment it was created in pins everything that environment can reach, for as long as
the cell lives; fixing that alone cut the peak of the Four Colour check by 3 to 4×.

When Lean's algorithm needs the *type* of something mid-conversion (proof irrelevance, structure
eta, K-like reduction) the machine reads the relevant value back into an expression and the type
checker carries on as usual.

### Lean has no `match` and no `fix`

This is the part that took the longest to get right, and it is specific to Lean.

Coq's kernel has primitive `match` and `fix` nodes. Lean's kernel has only recursors, and the
equation compiler turns source into layers of definitions:

```
   if c then a else b          ite  →  Decidable.casesOn  →  Decidable.rec
   x == y  (on Bool)           instDecidableEqBool  →  Bool.decEq  →  Bool.decEq.match_1  →  Bool.casesOn  →  Bool.rec
   match xs with | [] => … | a :: l => …
                               f.match_1  →  List.casesOn  →  List.rec
   structural recursion        f  →  List.brecOn  →  List.brecOn.go  →  List.rec, building a
                               course-of-values table of PProd pairs that the body reads with
                               projections to get its recursive results
```

A machine that unfolds these one at a time pays two to eight δ steps, a dozen β steps and as
many argument thunks for every step of a Coq `match`. Profiled on the raw Four Colour check,
that was three quarters of all machine steps, and the course-of-values tables were most of the
memory. Three mechanisms take it back.

**Fusion.** A definition's body is pre-reduced once per declaration: matcher, `casesOn`,
`brecOn`, projection-function and instance heads are unfolded under every binder, the β-redexes
that exposes are contracted, and ι and projection steps whose major premise is already a
constructor are performed. Each step is a β/δ/ι/projection reduction of a well-typed closed
term, so the fused body is definitionally equal to the original. Both engines unfold through
the same fused cache and `is_def_eq_core` fuses both of its operands, which keeps the *shape*
of a term canonical whichever route produced it. That matters: a hand-written `Nat.rec` body
and its fused twin reached by unfolding are equal, but if only one side is fused the kernel can
only find that out by unfolding a million steps of fuel.

**Fixpoint rules.** A structurally recursive definition gets Coq's `fix` semantics. From the
shape of its fused body, `(T.rec … x).1 args`, the machine derives one arm per constructor with
the table accesses that stand for recursive calls turned back into calls of the definition,
let-bound so that a result used twice is computed once. The derivation is a guess. Before a
rule is installed the kernel checks `f x⃗ (c fields) ≡ arm` on fresh variables with its ordinary
`is_def_eq`, so an installed rule is a definitional equation no matter what the derivation did.
The rule fires when the recursive argument is a constructor and the definition unfolds as usual
otherwise, so stuck terms keep the shape the reference algorithm gives them.

**Branch selection.** When a recursor fires and the selected minor premise is a lambda, the
constructor's fields are bound straight into the lambda's environment, Coq's `Zcase`. An
induction hypothesis the body never mentions is not built at all, which is every `casesOn`.

On ring size 10 of the Four Colour check these took the machine from 393 million steps to 57
million.

### Two engines

`--engine subst` is the substitution-based reference, Lean's algorithm as such. `--engine kam`
is the machine and the default. `--engine both` runs both on every `whnf` and reports any
structural difference between their results. By default the machine computes `whnf` and the
reference keeps `whnf_core`: Lean's recursive `whnf_core` caches every sub-result it visits and
later "cheap" calls rely on that to keep lazy delta short, and a machine that takes a spine in
one go cannot reproduce it. On a handful of Mathlib declarations lazy delta then unfolds without
end.

## Performance

All measurements below are on one machine, a 32-core AMD Threadripper 3970X with 126 GB of RAM.
lazylean is single-threaded throughout. Peak memory is the maximum resident set of the process.

### The Lean Kernel Arena

The [Lean Kernel Arena](https://github.com/leanprover/lean-kernel-arena) is a shared benchmark
for external Lean checkers. lazylean's checker definition for it is
[`checkers/lazylean.yaml`](https://github.com/corun1024/lean-kernel-arena/blob/lazylean/checkers/lazylean.yaml)
on the `lazylean` branch of a fork, and the arena's own runner produces the numbers there. The
table below is the arena's performance suite, 23 tests, each checker run as the arena configures
it: Lean's own kernel through the arena's official checker, eink0rn (the fastest checker on the
arena's public results; 8 threads), nanoclo (the other closure-based checker; 4 threads), and
lazylean. Every checker accepts every test.

| test | Lean kernel | eink0rn | nanoclo | lazylean |
|---|---|---|---|---|
| app-lam | 4.75 s / 1427 MB | 0.14 s / 58 MB | 0.02 s / 86 MB | 1.36 s / 77 MB |
| beta-ladder | 1.58 / 500 | 0.53 / 92 | 0.01 / 70 | 0.38 / 47 |
| let-ladder | 0.86 / 317 | 0.92 / 544 | 0.01 / 68 | 0.21 / 38 |
| discarded-argument-match | 0.09 / 68 | 0.14 / 106 | 0.00 / 52 | 0.02 / 24 |
| fueled-chain | 0.09 / 73 | 12.57 / 723 | 0.01 / 82 | 0.13 / 27 |
| grind-ring-5 | 1.93 / 228 | 0.97 / 344 | 0.54 / 287 | 1.04 / 83 |
| magma-list-deep-n21 | 2.26 / 556 | 1.25 / 612 | 0.99 / 431 | 0.24 / 30 |
| magma-list-deep-n36 | 34.34 / 6514 | 15.64 / 3823 | 48.87 / 3924 | 2.72 / 45 |
| magma-list-pair-n21 | 20.72 / 3657 | 16.41 / 4614 | 28.28 / 5477 | 6.42 / 1359 |
| magma-list-pair-n7 | 1.71 / 384 | 1.45 / 753 | 1.15 / 665 | 0.49 / 125 |
| magma-string-n4 | 3.18 / 120 | 0.88 / 400 | 0.32 / 230 | 2.08 / 51 |
| magma-string-pair-n9 | 7.93 / 998 | 3.74 / 1069 | 2.50 / 942 | 3.15 / 151 |
| 11 small tests | 0.03 to 0.11 | 0.01 to 0.09 | 0.00 to 0.01 | 0.01 to 0.03 |
| **total** | **79.9 s** | **54.9 s** | **82.7 s** | **18.4 s** |
| peak memory | 6.5 GB | 4.6 GB | 5.5 GB | 1.4 GB |

The computation-heavy tests are where the machine wins, and they are most of the suite. The
losses are honest ones: app-lam and beta-ladder are DAG-shaped terms where the hash of a lazy
closure is recomputed too often, grind-ring-5 is dominated by the per-declaration setup on 2 185
small declarations, and the two string tests spend their time interning `String.mk` character
lists.

The arena's own harness, run from the fork on a 64-thread EPYC 7B13 on 22 September 2026
(`results/lazylean-2026-09-22.json` on the branch), agrees on the suite and adds the whole-library
corpora, which are a different kind of work: hundreds of thousands of small declarations and
almost no computation. There the two specialised checkers, which also use several threads, are
ahead, and lazylean sits between them and Lean's kernel. No checker gave a wrong verdict on any
of the 218 tests.

| | Lean kernel | eink0rn (8 threads) | nanoclo (4 threads) | lazylean (1 thread) |
|---|---|---|---|---|
| 25 performance tests, total | 80.7 s | 51.2 s | 86.9 s | 19.0 s |
| Init (58 135 declarations) | 57 s | 13 s | 7 s | 47 s |
| Std | 99 s | 23 s | 12 s | 87 s |
| con-leche | 100 s | 301 s | 16 s | 78 s |
| CSLib | 415 s | 91 s | 56 s | 396 s |
| Mathlib (701 682 declarations) | 2436 s | 335 s | 192 s | 1853 s |

### The Four Colour Theorem

The Lean formalisation of the Four Colour Theorem exports a dependency closure of 201 672
declarations, 1.44 GB of NDJSON, with `Nat` literals of up to a million bits.

| checker | wall clock | CPU | peak memory |
|---|---|---|---|
| Lean's kernel, in the repository's own build | | 7.5 core-hours | 20 GB per module |
| Lean's kernel, replaying the export (arena checker, single-threaded) | 7 h 46 min | 7.8 core-hours | 22.4 GB |
| lazylean, 8 shards, `--memo` | 33.5 min | 3.9 core-hours | 7.6 GB |

Per certificate the ratio is larger: Lean's kernel takes 7 to 10 s and 1.2 to 1.7 GB on each of
the reducibility certificates, lazylean 2.3 to 3.2 s and 230 to 320 MB.

### A raw port of Gonthier's `check_reducible`

[4ct_direct_lean](https://github.com/corun1024/4ct_direct_lean) is a port of Gonthier's Coq
proof that keeps its computational method: reducibility is settled by running the Kempe-chain
closure `check_reducible` on each of the 633 configurations inside the kernel, with lazylean as
the kernel, since Lean's own cannot get past ring size 12 on that computation (166 GB, then
killed at 178 GB). That repository holds the ladder of timings against Coq's lazy kernel and
Coq's VM. The headline: on the largest configuration, ring size 14, Coq's lazy kernel takes
260 s, lazylean 18 minutes and 21 GB, and Lean's kernel does not finish. The fusion, fixpoint
rule and branch-selection work described above came out of that comparison; it took ring 10
from 393 million machine steps to 57 million and brought it level with Coq, and from ring 12 on
lazylean is about 4× behind, all of it the machine's per-step constant.

## How it was tested

A kernel is only useful if its verdicts can be trusted, so the testing is more of the project
than the machine is.

**The arena.** The Lean Kernel Arena's test suite is 189 exports: every `good/` export must
be accepted and every `bad/` one rejected, and the `bad/` set includes 18 real soundness bugs
found in other checkers, such as orphan recursors, missing induction hypotheses, K-like lies,
projections out of propositions and universe-level normalisation mistakes. lazylean passes 189
of 189, run through the arena's own harness from the fork linked above.

**Whole libraries.** Every declaration of the following was checked with zero failures: `Init`
(58 135 declarations), `Std` (98 047), the `Lean` package itself (164 584), all of Mathlib
(701 682 declarations, 7.4 minutes wall on 8 shards, 43 CPU-minutes, 9 GB peak), CSLib
(370 939), Cedar (133 845) and con-leche (26 561), across Lean versions 4.29 to 4.34.

**Lean's own test suite.** 3 085 files of Lean 4's `tests/elab` were exported and checked. 44
do not compile standalone. Exactly one is rejected: `kernelProjSname`, which deliberately
plants an ill-typed declaration with `debug.skipKernelTC`, and rejecting it is the correct
verdict.

**Differential execution.** `--engine both` runs the substitution-based reference and the
machine on every `whnf` call and reports any structural difference in the results. Every
change to the machine is gated on this mode staying silent over `Init.Prelude`.

**A mutation fuzzer.** `tests/fuzz_diff.py` takes an export, applies one of twenty kinds of
corruption (swap a constructor's field count, drop a minor premise, change a universe level,
lie about a recursor's K-target, insert a loose bound variable, alter an `isUnsafe` flag, and so
on) and compares lazylean's verdict with the official checker's. It ran about 7 000 mutations
without a remaining disagreement, after fixing the ones it found: a segfault on loose bound
variables, over-strict checks on derived inductive metadata, an accepted block with
inconsistent `isUnsafe` flags, and quotient types.

**Verified shortcuts.** Anything the machine does that is not a plain β/δ/ι step is either
sound by construction or checked by the kernel. Fusion is built only from β/δ/ι/projection
reductions. Every fixpoint rule is verified with `is_def_eq` on fresh variables before it is
used, and a rule that fails the check is simply not installed. The recursors derived for every
inductive block are compared with the ones in the export.

## Building and running

```
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release && cmake --build build -j
build/lazylean export.ndjson
```

GMP is the only dependency (`libgmp-dev`). Exit status 0 means every declaration was accepted,
1 that one was rejected, 2 that one was declined (see Limitations).

```
lazylean -k -v --slow 1 export.ndjson        keep going after a failure, log each declaration,
                                             list the ones slower than 1 s
lazylean --shard 3/8 export.ndjson           check every 8th declaration starting at the 4th;
                                             the others are added unchecked, for running one
                                             export as 8 processes
lazylean --max-rss 12000 export.ndjson       fail a declaration that exceeds 12 GB instead of
                                             letting the process be killed
lazylean --progress p.txt export.ndjson      rewrite a one-line status file per declaration
lazylean --memo export.ndjson                memoise open applications by their read-back
                                             (the Four Colour Theorem's certificates want this)
lazylean --engine both export.ndjson         differential mode, see above
lazylean --print Nat.add export.ndjson       print a declaration's type and value
```

To produce an export: `lean4export Module -- decl > out.ndjson` from the
[lean4export](https://github.com/leanprover/lean4export) tool, at the toolchain version of the
project. `Nat` literals beyond a few thousand bits make its decimal printer quadratic;
`scripts/hexparse_patch.py` teaches it hexadecimal.

Reproducing the numbers: the arena fork runs the arena suite (`uv run lka.py run lazylean`),
`scripts/` holds the remote recipes used for Mathlib, Std and Lean's test suite on a rented
machine, and `tests/fuzz_diff.py` needs an arena checkout for the official checker it uses as
its oracle.

## Limitations

`Lean.reduceBool` and `Lean.reduceNat`, Lean's hook for native evaluation inside the kernel, are
declined (exit status 2) rather than trusted. Everything else in the export format is
implemented.

Fixpoint rules cover self-recursion over one inductive type. Mutual and nested structural
recursion fall back to the ordinary `brecOn` unfolding, which is correct and slower.

The machine is single-threaded. Large exports are checked as independent shards.

## Provenance and license

lazylean was built in September 2026 by Claude (Anthropic's Claude Code) working under the
direction of Chris Emery, who set the goals, reviewed the design and the results, and ran the
comparisons; the code, the tests and this text were produced in that collaboration.

The type-checking algorithm follows Lean 4's kernel and lean4lean, both Apache 2.0, and the
machine follows the design of Coq's `cClosure`; no code was copied from any of them. The arena
test suite is redistributed under its Apache 2.0 license. Details are in `NOTICE.md`.

Copyright (c) 2026 Chris Emery. Released under the MIT License.
