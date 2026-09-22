#!/usr/bin/env bash
# Export the paired micro-benchmarks (kernel variants) as NDJSON, and derive larger sizes by
# substituting the size literal, which needs no Lean run.
set -u
B=${1:-/home/chris/4ct-kernel-bench/bench}
OUT=$(cd "$(dirname "$0")" && pwd)/exports/bench; mkdir -p $OUT
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin
EXP=$HOME/dev/lean4export
export PATH=$HOME/.elan/bin:$PATH
cap() { timeout 600 "$@"; }
TD=$(mktemp -d); cp $B/Common.lean $TD/
( cd $TD && cap $TC/lean -o $TD/Common.olean $TD/Common.lean ) > $TD/common.log 2>&1 || { echo "Common failed"; cat $TD/common.log; exit 1; }
for name in loop14 fib18 search8; do
  cp $B/lean/${name}_kernel.lean $TD/Bench.lean
  ( cd $TD && LEAN_PATH=$TD cap $TC/lean -o $TD/Bench.olean $TD/Bench.lean ) > $TD/bench.log 2>&1
  test -f $TD/Bench.olean || { echo "compile of $name failed"; cat $TD/bench.log | head -5; continue; }
  ( cd $EXP && LEAN_PATH=$TD lake env .lake/build/bin/lean4export Bench -- t > $OUT/$name.ndjson 2> $TD/exp.log ) || cat $TD/exp.log | head -3
  rm -f $TD/Bench.olean
  echo "$name: $(wc -l < $OUT/$name.ndjson) lines"
done
# derived sizes
python3 - "$OUT" <<'PY'
import sys, re, os
out=sys.argv[1]
def derive(base, subs, name):
    s=open(f"{out}/{base}.ndjson").read()
    for a,b in subs:
        pat=f'"natVal":"{a}"'
        assert s.count(pat)==1, (base,a,s.count(pat))
        s=s.replace(pat, f'"natVal":"{b}"')
    open(f"{out}/{name}.ndjson","w").write(s)
for k in [16,18,20,22,24]: derive("loop14", [("14",str(k))], f"loop{k}")
for n in [20,22,24,26,28,30]: derive("fib18", [("18",str(n))], f"fib{n}")
for n in [9,10,11,12,13]: derive("search8", [("8",str(n)),("384",str(3*2**(n-1)))], f"search{n}")
print("derived")
PY
rm -rf $TD; ls $OUT | tr '\n' ' '
