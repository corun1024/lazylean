#!/usr/bin/env bash
# On a machine with the 4ct repository built (see ~/4ct, built by its build.sh):
#   1. build lean4export for the repository's toolchain,
#   2. export the dependency closure of the theorem (and of the audit checks),
#   3. build lazylean and check the export.
# Usage: remote_export_4ct.sh [repo=~/4ct] [out=~/4ct-export]
set -euo pipefail
REPO=${1:-$HOME/4ct}; OUT=${2:-$HOME/4ct-export}
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p "$OUT"
TC=$(cat "$REPO/lean-toolchain")           # leanprover/lean4:vX
TAG=${TC#leanprover/lean4:}
if [ ! -x "$HOME/lean4export/.lake/build/bin/lean4export" ]; then
  git clone -q --depth 1 --branch "$TAG" https://github.com/leanprover/lean4export.git "$HOME/lean4export"
  (cd "$HOME/lean4export" && lake build 2>&1 | tail -2)
fi
cd "$REPO"
date; echo "== export FourColor.fourColorTheorem closure"
lake env "$HOME/lean4export/.lake/build/bin/lean4export" FourColor.Complete -- FourColor.fourColorTheorem > "$OUT/fourcolor.ndjson"
ls -la "$OUT/fourcolor.ndjson"; wc -l "$OUT/fourcolor.ndjson"
date; echo "== export done"
if [ -d "$HOME/lazylean" ]; then
  (cd "$HOME/lazylean" && cmake -S . -B build -DCMAKE_BUILD_TYPE=Release > /dev/null && cmake --build build -j > /dev/null)
  N=${SHARDS:-8}
  echo "== lazylean check, $N shards"
  seq 0 $((N-1)) | xargs -P $N -I{} sh -c "/usr/bin/time -v $HOME/lazylean/build/lazylean -k --slow 5 --shard {}/$N $OUT/fourcolor.ndjson > $OUT/lazylean.{}.log 2>&1"
  grep -hE "checked|FAIL|Maximum resident|Elapsed" "$OUT"/lazylean.*.log | head -40
fi
