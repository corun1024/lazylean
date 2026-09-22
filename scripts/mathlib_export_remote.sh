#!/usr/bin/env bash
export PATH="$HOME/.elan/bin:$PATH"
cd ~/4ct
M=$(ls .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/*.olean 2>/dev/null | wc -l); echo "mathlib top-level oleans: $M"
ls .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean && git -C .lake/packages/mathlib log --oneline -1
mkdir -p ~/mathlib-export
date; echo "== export Mathlib (whole module closure)"
/usr/bin/time -v lake env ~/lean4export/.lake/build/bin/lean4export Mathlib > ~/mathlib-export/mathlib.ndjson 2> ~/mathlib-export/export.log; echo "EXPORT_RC=$?"
ls -la ~/mathlib-export/mathlib.ndjson; wc -l ~/mathlib-export/mathlib.ndjson; grep -E "Elapsed|Maximum resident" ~/mathlib-export/export.log
date; echo "== MATHLIB EXPORT DONE"
