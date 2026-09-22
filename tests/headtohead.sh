#!/usr/bin/env bash
# Time the arena's official checker (Lean's kernel via lean4export parse + replay) and lazylean on the same exports.
OFF=${OFF:-$HOME/dev/lean-kernel-arena/checkers/official/.lake/build/bin/kernel}
LL=${LL:-$(cd "$(dirname "$0")" && pwd)/../build/lazylean}
OUT=${OUT:-/tmp/headtohead.tsv}
echo -e "test\tofficial_s\tofficial_mb\tofficial_rc\tlazylean_s\tlazylean_mb\tlazylean_rc" > $OUT
run() { # binary file -> "secs mb rc"
  systemd-run --user --scope -q -p MemoryMax=${CAP:-4500M} -p MemorySwapMax=0 /usr/bin/time -f '%e %M' -o /tmp/hh.time timeout ${TMO:-900} "$1" "$2" > /dev/null 2>&1; rc=$?
  read s kb < <(tail -1 /tmp/hh.time); echo "$s $(( ${kb:-0} / 1024 )) $rc"
}
for f in "$@"; do
  n=$(basename $f .ndjson)
  if [ -n "${ONLY_LL:-}" ]; then o="- - -"; else o=$(run $OFF "$f"); fi; l=$(run $LL "$f")
  printf "%s\t%s\t%s\n" "$n" "${o// /	}" "${l// /	}" | tee -a $OUT
done
