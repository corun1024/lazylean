# lazylean

A type checker for Lean 4: one kernel, a normalisation-by-evaluation checker, with a Coq-style
lazy abstract machine as its engine for computation.

It reads the standard `lean4export` format and re-checks every declaration: definitions,
theorems, axioms, quotients, and inductive types with their recursors re-derived from scratch.
Every verdict comes from one type checker, which turns terms into semantic values (closures over
environments, neutral terms with a spine of eliminations) and decides definitional equality on
those, as smalltt and sokonanoda do. When a declaration computes -- a proof by `decide`, a
certificate checked by running a program -- the checker hands the closed terms it has to reduce
to a Krivine machine with call-by-need thunks, after Coq's `cClosure`, and carries on with the
machine's result. The checks on inductive types, quotients and fixpoint rules ask the same
checker for types, weak-head normal forms and definitional equality.

On the Lean Kernel Arena's ranking measure, the instructions executed to check all of Mathlib,
lazylean 0.5.0 needs 0.54 × 10¹² instructions for 654 504 declarations, on one core, in about
four and a half minutes, and at most 4.7 GB of memory: a quarter fewer instructions than the fastest
checker of the 2026-09 round, less memory than any of them, and ten times fewer instructions
than lazylean 0.3.0. On the Four Colour Theorem's 201 672-declaration dependency closure the
lazy machine needs 3.9 core-hours where Lean's kernel needs 7.5, and where Lean's kernel dies at
178 GB on a raw port of Gonthier's reducibility check, it finishes in 21 GB.

```
lean4export Foo -- Foo.theorem > foo.ndjson
lazylean foo.ndjson        # exit 0: every declaration accepted
```

## Contents

- [Why a lazy kernel](#why-a-lazy-kernel)
- [The evaluation engine](#the-evaluation-engine)
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

## The evaluation engine

The arena ranks checkers by the number of instructions they execute on Mathlib. Mathlib is
650 000 small declarations and almost no computation, so what that measures is the constant
cost of checking an ordinary declaration: building terms, instantiating binders, looking things
up. lazylean's first checker, a re-implementation of Lean's substitution-based kernel, spent
most of its time on exactly that -- every `instantiate` interns new terms, and every
declaration starts with empty caches -- and on Mathlib it executed 5.5 × 10¹² instructions.
`src/nbe.cpp` is the checker built for the other end of the trade-off, and since 0.5.0 the only
one.

**Values, not terms.** A term is evaluated against an environment into a value: a closure for
a λ or a Π, a *neutral* for anything headed by a variable or a constant, with the arguments and
projections applied to it kept as a spine, and sorts and literals. β is an extension of the
environment. A variable entering scope is a fresh de Bruijn *level*, identified by its level and
its type. Constants stay folded: a definition is unfolded only when conversion or a recursor
needs it, and the unfolding is stored in the value. Nothing is substituted and no term is built;
type inference runs on values too, and the type of a λ is a Π whose body is *inferred* when it is
instantiated.

**Hash-consing and pruned environments.** Neutral applications are hash-consed by
(function, argument), environments by (parent, value), fresh variables by (level, type), so the
same value built twice is the same pointer and most conversion checks end on a pointer
comparison. The caches for evaluation and inference are keyed by (environment, term), where the
environment is first *pruned* to the variables the term actually mentions (a 64-bit mask per term,
computed once), so a subterm's value is shared by every context that agrees on its free
variables. Measured on Std, pruning turned 41% of evaluation misses into hits. A mask cannot
describe a term more than 64 binders deep, and an unknown mask used to propagate to every term
above it; now a term whose own variables fit gets its exact mask from the variable sets of the
deep terms under it. A con-leche proof 73 binders deep had re-inferred the same subterms ninety
thousand times each, in 31 million conversion steps; it now takes 200 thousand.

**Sessions.** Values live in a bump arena, and the arena and every cache last for a *session*
of values -- 128 MB for Mathlib, less for smaller exports, thousands of declarations -- rather
than for one declaration. The environment only grows and a value means the same thing wherever it is used, so
a constant's type, an instance's unfolding or a conversion already decided is paid for once per
session. The caches are open-addressing tables whose memory is mapped once, 2 MB-aligned and
pre-faulted, and reused across sessions, so the kernel's page-fault work is paid once too.

**Conversion** follows Lean's `is_def_eq` in substance: lazy δ by reducibility hints, same-head
arguments compared before unfolding (with a step budget, after sokonanoda), ι, projections, K,
structure η, η, proof irrelevance, unit-like types, `Nat` literals with GMP, `String` literals,
and positive and negative caches. *Relevance signatures*, computed once per constant and
universe instantiation from its type alone, say which argument positions hold proofs (they need
not be compared once the arguments before them agree) and whether an application is a proof at
all (then proof irrelevance needs no type inference).

**Two sessions, one checker.** Ordinary declarations are checked in the main session, whose
values and caches are shared by thousands of declarations. A declaration that takes more than a
million evaluation steps there, or allocates more than 64 MB of values, is one that computes: it
is checked again, by the same checker, in a scratch session that is emptied afterwards, with the
lazy machine reducing every closed term the checker would otherwise unfold step by step. The
machine is the better engine for computation and frugal with memory, and the long-lived main
session stays free of a computation's values. The checks on inductive types, quotients and
unsafe or partial definitions, which build terms of their own, run in the scratch session too.

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

### Inductive types and the term-level interface

`src/inductive.cpp` re-checks inductive blocks the way Lean's `add_inductive` does, including
the elimination of nested inductives, and derives the recursors itself; the derived recursors are
then compared with the ones in the export, and the types go into the environment with the
metadata derived here rather than the export's. It works on terms with free variables, as Lean's
kernel does, and asks its questions -- infer this type, reduce this to weak-head normal form, are
these convertible -- through a term-level interface (`src/kernel.h`) that evaluates the terms in
the scratch session and reads the answers back. Free variables become neutral values that carry
their type (and a `let` variable its value), and nothing that mentions one is cached.

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

When the machine needs the *type* of something mid-reduction (K-like reduction, structure eta)
it reads the relevant value back into an expression and asks the checker through the same
term-level interface.

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
term, so the fused body is definitionally equal to the original. The machine unfolds through a
fused cache, and the term the checker hands it is fused first, so the shape of a term is the
same whichever route produced it.

**Fixpoint rules.** A structurally recursive definition gets Coq's `fix` semantics. From the
shape of its fused body, `(T.rec … x).1 args`, the machine derives one arm per constructor with
the table accesses that stand for recursive calls turned back into calls of the definition,
let-bound so that a result used twice is computed once. The derivation is a guess. Before a
rule is installed the kernel checks `f x⃗ (c fields) ≡ arm` on fresh variables with its ordinary
conversion check, so an installed rule is a definitional equation no matter what the derivation
did. The arms are read off the body by head reduction alone, which leaves the `let`s of the
body in place: a derivation that normalised the body instead would inline them, and the rule
would then recompute what it was meant to share (on ring size 9 of the Four Colour check, 111
million machine steps instead of 32).
The rule fires when the recursive argument is a constructor and the definition unfolds as usual
otherwise, so stuck terms keep the shape unfolding gives them.

**Branch selection.** When a recursor fires and the selected minor premise is a lambda, the
constructor's fields are bound straight into the lambda's environment, Coq's `Zcase`. An
induction hypothesis the body never mentions is not built at all, which is every `casesOn`.

On ring size 10 of the Four Colour check these took the machine from 393 million steps to 57
million.

**Only where they pay.** On a library, fusion and fixpoint rules cost more than they save, since
most declarations evaluate nothing. They belong to the machine, and the machine only runs for a
declaration that has already shown, by exceeding the main session's budget, that it computes.

### Loading and interning

Checking a library is mostly building terms. On Mathlib the checker interns about 7 000 new
nodes per declaration, and before this was tuned, two thirds of all checking time went to the
expression table rather than to reduction. Three things made it cheap.

A node whose child is a temporary term cannot equal anything in the permanent tier, because a
temporary handle only exists when no equal permanent node did. So the probe into the
permanent table, a gigabyte of random access for Mathlib, is skipped for it. The same holds for
a closure whose materialisation contains a temporary term, typically the free variable a binder
was just instantiated with, and the semantic hash already visits exactly those positions, so it
reports the fact for free. On a sixteenth of Mathlib this cut permanent probes from 124 million
to 58 million with the number of hits unchanged to the last digit: every probe skipped was a
miss. The permanent tier also sits on 2 MB pages, since with 4 KB pages nearly every lookup in it
missed the TLB as well as the cache.

The per-declaration caches are flat open-addressing tables instead of `std::unordered_map`,
which allocated and freed a node per entry, and a temporary intern table is emptied by the
slots it used rather than by its capacity. Universe instantiation, which Mathlib does millions
of times, skips every subterm that mentions no universe parameter, using a flag each node
carries.

Loading reads the export through a memory map with a scanner for the line shapes lean4export
actually writes, falling back to a general JSON reader for anything else. The export writes each
expression once, so nodes are appended without lookup and the permanent hash table is built
afterwards by eight threads with compare-and-swap. If two nodes ever turn out equal, the file is
loaded again with ordinary interning, so equal terms still get one handle. Mathlib's 95 million
nodes load in 11 seconds.

### Checking declarations in parallel

Reducing one term is sequential: each step depends on the last, and no amount of hardware
changes that. Checking a library is not. Declarations are independent once the ones they cite
have been established, so `--jobs N` checks them N at a time.

The export is parsed once. After the parse the environment is built and the expression table is
frozen, and only then does the process fork N workers, so the parsed export and the interned
permanent tier are shared by every worker through copy-on-write rather than parsed N times. A
worker walks the declaration list and claims declarations as it reaches them with an atomic
exchange on a shared flag: it checks what it claims and skips what it does not. Every
declaration is checked by exactly one worker, and a worker held up by an expensive declaration
simply claims fewer, so the load balances itself without a scheduler.

Processes rather than threads is a deliberate choice. What threads would buy is shared caches,
and there is almost nothing to share: the conversion caches are built and discarded per
declaration, so a worker's own are all it ever uses. What processes buy instead is that no two
workers can race, in a program whose whole job is to be trusted. The only writable shared
memory is the array of claim flags.

Parallel checking needs one guarantee that a single process gets for free. Checking a
declaration against an environment that also holds *later* declarations would accept a circular
export, where A's proof cites B and B's cites A and neither is ever established; running in
order, A simply cannot see B. So the order is verified before the workers start: no constant a
declaration mentions may be introduced by a later declaration. Because the export writes a
term's parts before the term, one pass over the nodes in order records, for each, the latest
declaration any constant inside it comes from, and each declaration is then one comparison;
for Mathlib that is under a second. `--shard` was exposed to the same gap and gets the same
check.

## Performance

### Version 0.4: instructions, the arena's measure, and memory

The Lean Kernel Arena ranks checkers first by their verdicts and then by the number of
instructions (`perf stat -e instructions`, summed over every thread and process) they execute
on the Mathlib export; its time columns are that count divided by 6 × 10⁹. Wall clock does not
enter the ranking, and neither does the number of cores, which is why 0.4 runs as a single
process. Billions of instructions, all declarations accepted in every run:

| corpus | declarations | lazylean 0.3.0 | mathgraph | sokonanoda | nanoclo | Lean's kernel | lazylean 0.4.1 | lazylean 0.4.2 | lazylean 0.5.0 |
|---|---|---|---|---|---|---|---|---|---|
| Init | 53 093 | 213 | 37 | 39 | 121 | 367 | 21 | 27 | **29** |
| Std | 90 778 | 351 | 62 | 65 | 201 | 617 | 36 | 47 | **48** |
| con-leche | 26 819 | 457 | 157 | 162 | 315 | 665 | 75 | 108 | **92** |
| CSLib | 370 939 | 1 248 | 237 | 249 | 775 | 2 428 | 141 | 174 | **183** |
| Mathlib | 654 504 | 5 529 | 709 | 745 | 3 064 | 11 832 | 464 | 519 | **543** |

Peak memory (resident set, GB, as the arena measures it with GNU `time`):

| corpus | lowest other checker in 2026-09 | mathgraph | sokonanoda | Lean's kernel | lazylean 0.4.1 | lazylean 0.4.2 | lazylean 0.5.0 |
|---|---|---|---|---|---|---|---|
| Init | 0.43 (still-nanoda) | 0.60 | 0.72 | 0.56 | 4.0 | 0.39 | **0.41** |
| Std | 0.68 (still-nanoda) | 0.92 | 1.06 | 0.92 | 4.9 | 0.64 | **0.60** |
| con-leche | 0.75 (still-nanoda) | 3.55 | 4.49 | 0.90 | 5.7 | 0.70 | **0.74** |
| CSLib | 2.43 (still-nanoda) | 2.87 | 3.07 | 3.31 | 7.3 | 1.93 | **1.92** |
| Mathlib | 5.61 (still-nanoda) | 6.07 | 6.36 | 8.16 | 11.2 | 4.77 | **4.71** |

The other columns are the arena's own figures from round 2026-09; lazylean was measured the
same way (`perf stat -e instructions`, GNU `time`, single process, `-k`) on 64-core AMD EPYC
VMs. 0.4.2 traded a little of 0.4.1's speed for memory. 0.5.0 replaces the two engines with
one kernel (above) at about the same cost: on Mathlib 90 s of the arena's virtual time against
118 s for the round's fastest checker, and 4.71 GB at the peak. It gives back 3 to 5% on the
libraries, where the checks on inductive types now go through the evaluator's term-level
interface rather than a checker of their own, and gains 15% on con-leche, whose proofs more than
64 binders deep the evaluator now caches properly.

Where the memory went in 0.4.2, on Mathlib: expression nodes shrink from 40 to 32 bytes (a
32-bit hash), and the permanent intern index stores 4-byte handles rather than 8-byte
tag-and-handle slots (together −1.3 GB); the loose-variable masks the evaluation engine keys its
caches with live in node fields that only constants and lets otherwise use, instead of a
separate array (−0.36 GB); sessions shrink to 128 MB of values with tables allowed to fill to
three quarters and trimmed after a large session (−5 GB); declarations that compute are handed
to the lazy machine once they allocate 64 MB (they had been the peak); and the export's copy of
each constant is released once the environment has its own, and name strings are pooled.

Where the eleven-fold reduction on Mathlib came from, in the order it was made: the evaluation
engine itself (5.5 → 0.92 × 10¹²), reusing its memory across sessions instead of returning it
to the kernel (→ 0.71), pruned environments as cache keys (→ 0.69), a loader that parses each
line in one pass and appends nodes without a lookup, and memoised universe-level normalisation,
which had been a fifth of the time on late Mathlib because it compared parameter names through
heap-allocated vectors (→ 0.58), and walking a function's type as a telescope without building
the intermediate Π values (→ 0.49), and in 0.4.1 reading the export's numbers eight bytes at a
time and longer sessions (→ 0.46). 0.4.2 gives back some of that for memory (→ 0.52).


### Version 0.3.0 (wall clock)

Version 0.3.0 is three times faster than 0.2.0 on Mathlib at the same eight workers, and two
and a half to three and a half times faster on every other library. Both versions below ran on
one machine, a 64-thread AMD EPYC 7C13, with the arena's own command line
(`-j 8 --max-rss 14000`), one after the other. Seconds of wall clock, and no declaration failed
in any run.

| corpus | declarations | 0.2.0 | 0.3.0 | |
|---|---|---|---|---|
| Init | 53 093 | 10.2 | 3.8 | 2.7× |
| Std | 90 778 | 18.3 | 6.5 | 2.8× |
| con-leche | 26 819 | 17.7 | 7.5 | 2.4× |
| CSLib | 370 939 | 86.6 | 25.2 | 3.4× |
| Mathlib | 654 504 | 323.5 | 102.0 | 3.2× |

On Mathlib the gain splits into loading, 81.5 s to 11.1 s, and checking, 239.5 s to 91.3 s of
wall time. The design notes above say where each part came from; in order of what they were
worth on Mathlib, they are the skipped permanent-table probes, checking without fusion unless a
declaration evaluates, the flat caches, 2 MB pages, the bulk loader, and the cheaper universe
instantiation. The performance suite did not give anything back: 17.9 s with 0.2.0 and 16.2 s
now, single process, fastest of three runs. The arena's harness, run on 0.3.0 over all 218
tests, returns 200 correct verdicts and 18 on the corner cases it scores either way, the same
as before.

### The Lean Kernel Arena, with 0.2.0

These comparisons predate 0.3.0 and were made on a different machine, a 64-thread AMD EPYC
7B13, so they understate lazylean on the library corpora; on Mathlib 0.3.0 is three times
faster than the figure below. Reduction inside a declaration is single-threaded in every one of
these checkers; what differs is how many declarations each checks at once. The Four Colour
measurements after them are from a 32-core Threadripper 3970X with 126 GB of RAM.

The [Lean Kernel Arena](https://github.com/leanprover/lean-kernel-arena) is a shared benchmark
for external Lean checkers: 218 tests, from single-feature cases and known soundness bugs up to
Mathlib. lazylean's definition for it is
[`checkers/lazylean.yaml`](https://github.com/corun1024/lean-kernel-arena/blob/lazylean/checkers/lazylean.yaml)
on the `lazylean` branch of a fork, and everything below is the arena's own harness, run on a
64-thread AMD EPYC 7B13 on 22 September 2026. The raw
[`results.json`](https://github.com/corun1024/lean-kernel-arena/tree/lazylean/results) is on
that branch.

Six checkers: Lean's own kernel through the arena's official checker, and the five fastest of
the twenty-five others, chosen by measuring every one that builds rather than by reputation.
Each runs as its own arena definition configures it, which is where the thread counts come
from: eink0rn 8, nanoclo 4, lazylean 8, nanoda and still-nanoda 1. Seconds of wall clock.

The performance suite is 25 small inputs built to expose algorithmic problems in a reduction
engine, and it is what the lazy machine is for.

| test | Lean kernel | eink0rn | nanoclo | nanoda | still-nanoda | lazylean |
|---|---|---|---|---|---|---|
| app-lam | 4.82 | 0.19 | 0.06 | 12 | 11 | 1.58 |
| beta-ladder | 1.54 | 0.60 | 0.05 | 2.85 | 2.64 | 0.48 |
| fueled-chain | 0.13 | 14 | 0.05 | 0.10 | 0.11 | 0.12 |
| grind-ring-5 | 1.84 | 1.08 | 0.61 | 1.13 | 1.07 | 0.54 |
| let-ladder | 0.75 | 1.10 | 0.05 | 1.27 | 1.16 | 0.28 |
| magma-list-deep-n21 | 2.15 | 1.36 | 0.95 | 1.85 | 1.72 | 0.26 |
| magma-list-deep-n36 | 36 | 17 | 49 | 48 | 45 | 2.68 |
| magma-list-pair-n21 | 20 | 18 | 29 | 28 | 27 | 6.36 |
| magma-list-pair-n7 | 1.58 | 1.63 | 1.23 | 1.78 | 1.70 | 0.51 |
| magma-string-n4 | 2.78 | 0.99 | 0.39 | 0.70 | 0.96 | 0.55 |
| magma-string-pair-n9 | 7.02 | 3.73 | 2.68 | 5.27 | 4.93 | 1.57 |
| 14 small tests | 0.07–0.16 | 0.05–0.19 | 0.04–0.05 | 0.04–0.06 | 0.04–0.09 | 0.06–0.09 |
| **total** | **79.8** | **60.1** | **85.4** | **102.7** | **97.9** | **15.9** |

Four times faster than the next checker, and the margin comes from the computation-heavy tests,
which are most of the suite's time. The one real loss is app-lam, a DAG-shaped term where the
hash of a lazy closure gets recomputed far too often; nanoclo does it in 0.06 s.

The whole-library corpora are the opposite kind of work: hundreds of thousands of small
declarations and almost no computation, so they measure per-declaration overhead and how well a
checker uses more than one core.

| corpus | Lean kernel | eink0rn | nanoclo | nanoda | still-nanoda | lazylean |
|---|---|---|---|---|---|---|
| Init.Prelude | 0.32 | 0.26 | 0.08 | 0.10 | 0.10 | 0.16 |
| Init | 58 | 15 | 6.60 | 11 | 13 | 10 |
| Std | 97 | 26 | 12 | 18 | 20 | 19 |
| con-leche | 99 | 327 | 15 | 33 | 26 | 18 |
| CSLib | 403 | 105 | 52 | 85 | 72 | 82 |
| Mathlib | 2336 | 357 | 184 | 415 | 268 | 313 |

On Mathlib lazylean is third. It is well ahead of Lean's own kernel and of eink0rn at the same
eight workers, and nanoclo is genuinely faster on four threads, which is worth saying plainly:
its per-declaration constant is lower than ours. still-nanoda's 268 s comes with six wrong
answers, below.

**Verdicts.** Over 218 tests, lazylean was correct on every one, as were Lean's kernel, eink0rn
and nanoclo. nanoda declined two tests about the export format. still-nanoda *accepted* six of
the arena's known soundness bugs — a constructor with a false field count, an orphan recursor,
an extra recursor, a projection out of a non-structure, a projection out of a substituted
proposition, and a K-like lie — and rejected the two export-format tests. That is the arena
doing its job, and it is the reason a speed table alone is not a ranking.

**Memory** is missing from this run: the arena's runner reported peak resident set as zero for
every checker on that machine. Measured directly on the earlier suite, lazylean peaked at
1.4 GB against 4.6 GB for eink0rn, 5.5 GB for nanoclo and 6.5 GB for Lean's kernel.

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

**The arena.** Every `good/` export must be accepted and every `bad/` one rejected, and the
`bad/` set includes real soundness bugs found in other checkers: orphan recursors, missing
induction hypotheses, K-like lies, projections out of propositions, universe-level
normalisation mistakes. Run through the arena's own harness, lazylean's verdict was correct on
all 218 tests, including the 18 corner cases the arena scores either way. One of the five other
checkers in that run accepted six of the soundness bugs.

**Whole libraries.** Every declaration of the following was checked with zero failures: `Init`
(58 135 declarations), `Std` (98 047), the `Lean` package itself (164 584), all of Mathlib
(701 682 declarations, 7.4 minutes wall on 8 shards, 43 CPU-minutes, 9 GB peak), CSLib
(370 939), Cedar (133 845) and con-leche (26 561), across Lean versions 4.29 to 4.34.

**Lean's own test suite.** 3 085 files of Lean 4's `tests/elab` were exported and checked. 44
do not compile standalone. Exactly one is rejected: `kernelProjSname`, which deliberately
plants an ill-typed declaration with `debug.skipKernelTC`, and rejecting it is the correct
verdict.

**Differential execution.** Up to 0.4, the machine was developed against a substitution-based
reference that ran beside it on every `whnf` call and reported any structural difference in the
results; every change to the machine was gated on that staying silent over `Init.Prelude`.

**A mutation fuzzer.** `tests/fuzz_diff.py` takes an export, applies one of twenty kinds of
corruption (swap a constructor's field count, drop a minor premise, change a universe level,
lie about a recursor's K-target, insert a loose bound variable, alter an `isUnsafe` flag, and so
on) and compares lazylean's verdict with the official checker's. It ran about 7 000 mutations
without a remaining disagreement, after fixing the ones it found: a segfault on loose bound
variables, over-strict checks on derived inductive metadata, an accepted block with
inconsistent `isUnsafe` flags, and quotient types.

**The single kernel** of 0.5.0 was held to all of the above before it replaced the two-engine
design: the arena suite, every corpus with zero failures, the Four Colour ladder, and 4 000
further mutations of `Init.Prelude` with no disagreement with the official checker. The
evaluator's acceptances were already final in 0.4 (nothing re-checked them); the arena's
`bugs/proj-of-subst-prop` caught it once, in its first version (it answered "not a proposition"
for a type whose sort is stuck, where lean4#14807 makes that an error), which is fixed. Earlier
fuzzing found five disagreements the other way, all mutated inductive metadata (`numIndices`),
which the old checker recomputed but then added from the export; the kernel now adds the values
it derives, as Lean's does, and checks that each constructor names its own inductive type.

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
LL_MEMREPORT=1 lazylean export.ndjson        report resident memory and the engine's table sizes
lazylean --from-line L --count N export.ndjson   check N declarations starting at line L
lazylean -k -v --slow 1 export.ndjson        keep going after a failure, log each declaration,
                                             list the ones slower than 1 s
lazylean -j 8 export.ndjson                  check with 8 worker processes: the export is
                                             parsed once and the workers share it
lazylean --shard 3/8 export.ndjson           check every 8th declaration starting at the 4th,
                                             for splitting an export over several machines
lazylean --max-rss 12000 export.ndjson       fail a declaration that exceeds 12 GB instead of
                                             letting the process be killed
lazylean --progress p.txt export.ndjson      rewrite a one-line status file per declaration
lazylean --memo export.ndjson                memoise open applications by their read-back
                                             (the Four Colour Theorem's certificates want this)
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

Reduction is sequential: one enormous term reduces at the speed of one core, and `--jobs` only
helps an export that has many declarations in it.

## Provenance and license

lazylean was built in September 2026 by Claude (Anthropic's Claude Code) working under the
direction of Chris Emery, who set the goals, reviewed the design and the results, and ran the
comparisons; the code, the tests and this text were produced in that collaboration.

The type-checking algorithm follows Lean 4's kernel and lean4lean, both Apache 2.0, and the
machine follows the design of Coq's `cClosure`; no code was copied from any of them. The arena
test suite is redistributed under its Apache 2.0 license. Details are in `NOTICE.md`.

Copyright (c) 2026 Chris Emery. Released under the MIT License.
