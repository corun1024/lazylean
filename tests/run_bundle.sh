#!/usr/bin/env bash
# Run the Lean Kernel Arena's pre-generated bundle: every export under good/ must be accepted
# (exit 0) and every one under bad/ rejected (exit 1).  The bundle ships as tests.tar.gz and is
# unpacked on first use.  CHK=path/to/lazylean to test another build; TMO=seconds per test.
T=$(cd "$(dirname "$0")" && pwd)
B=${1:-$T/arena-bundle}; CHK=${CHK:-$T/../build/lazylean}
[ -d "$B/good" ] || tar xzf "$B/tests.tar.gz" -C "$B"
cap() { if command -v systemd-run >/dev/null 2>&1 && systemd-run --user --scope -q true 2>/dev/null; then systemd-run --user --scope -q -p MemoryMax=${MEM:-3G} -p MemorySwapMax=0 "$@"; else "$@"; fi; }
pass=0; fail=0; log=$(mktemp)
for f in $(find "$B/good" "$B/bad" -name '*.ndjson' | sort); do
  exp=$([[ $f == */good/* ]] && echo 0 || echo 1)
  cap timeout ${TMO:-120} "$CHK" "$f" > "$log" 2>&1; rc=$?
  ok=$([[ $rc == $exp || ( $exp == 1 && $rc != 0 && $rc != 2 && $rc != 124 ) ]] && echo 1 || echo 0)
  if [[ $ok == 1 ]]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL ${f#$B/} expected $exp got $rc: $(tail -1 "$log" | cut -c1-200)"; fi
done
rm -f "$log"
echo "bundle: $pass passed, $fail failed"
[[ $fail == 0 ]]
