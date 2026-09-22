#!/usr/bin/env bash
# Time a checker on the arena perf suite (bundle perf dir + the two string tests) under a memory
# cap; min of N runs per test; prints a table and the total.   Usage: perfsuite.sh [binary] [N]
T0=$(cd "$(dirname "$0")" && pwd); CHK=${1:-$T0/../build/lazylean}; N=${2:-2}
T=$T0
files=$(ls $T/arena-bundle/good/perf/*.ndjson $T/arena-cache/perf_magma-string-n4.ndjson $T/arena-cache/perf_magma-string-pair-n9.ndjson 2>/dev/null)
total=0
for f in $files; do
  n=$(basename $f .ndjson); n=${n#perf_}
  best=; bmem=; brc=
  for i in $(seq $N); do
    systemd-run --user --scope -q -p MemoryMax=${CAP:-4G} -p MemorySwapMax=0 /usr/bin/time -f '%e %M' -o /tmp/ps.time timeout ${TMO:-600} $CHK $f > /dev/null 2>&1; rc=$?
    read s kb < <(tail -1 /tmp/ps.time)
    if [ -z "$best" ] || awk "BEGIN{exit !($s < $best)}"; then best=$s; bmem=$((kb/1024)); brc=$rc; fi
  done
  printf "%-28s %8.2f s %6d MB rc=%s\n" "$n" "$best" "$bmem" "$brc"
  total=$(awk "BEGIN{print $total + $best}")
done
printf "%-28s %8.2f s\n" "TOTAL" "$total"
