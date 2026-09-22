# Notices

lazylean is Copyright (c) 2026 Chris Emery and is released under the MIT
License (see `LICENSE`). Everything under `src/`, `scripts/` and the test
scripts was written for this project. The following should be acknowledged:

- The type-checking algorithm in `src/tc.cpp` and the inductive-type and
  recursor construction in `src/inductive.cpp` are re-implementations of the
  algorithm of the Lean 4 kernel (`src/kernel/` in
  [leanprover/lean4](https://github.com/leanprover/lean4), Apache License 2.0,
  Copyright Microsoft Corporation and the Lean FRO) and were cross-checked
  against [lean4lean](https://github.com/digama0/lean4lean) (Apache License
  2.0, Copyright Mario Carneiro). No source code was copied from either; the
  order of the checks, the reducibility-hint heuristics and the recursor
  construction follow theirs so that lazylean accepts and rejects the same
  declarations.
- The lazy machine in `src/kam.cpp` follows the design of the Coq kernel's
  `kernel/cClosure.ml` (Bruno Barras, LGPL 2.1) as described in the Coq
  sources and in Barras's thesis. It shares no code with it.
- `scripts/hexparse_patch.py` patches three lines of
  [lean4export](https://github.com/leanprover/lean4export) (Apache License
  2.0) so that it reads hexadecimal `Nat` literals; the patch reproduces those
  three lines.
- `tests/exports/` holds `lean4export` output of `Init.Prelude` from the Lean
  4 standard library (Apache License 2.0) and of this project's own benchmark
  programs.
- The checker links against GMP (LGPL 3.0 / GPL 2.0 dual licence), which is
  used as a system library and is not redistributed here.
