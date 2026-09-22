#!/usr/bin/env bash
# Same-machine timing of the arena perf suite: official (Lean kernel), eink0rn (-j8), nanoclo (4 threads), lazylean.
# Waits for the 4CT shard run to finish first.  Output: ~/suite/results.tsv  (checker test seconds MB rc)
export PATH="$HOME/.cargo/bin:$PATH"
while ! grep -q "CLOS CHECK DONE" ~/clos_check.log 2>/dev/null; do sleep 30; done
S=~/suite; mkdir -p $S; : > $S/results.tsv
t() { /usr/bin/time -f '%e %M' -o $S/t.txt timeout 1200 "$@" > $S/run.log 2>&1; rc=$?; read s kb < <(tail -1 $S/t.txt); echo "$s $((kb/1024)) $rc"; }
for f in $S/tests/*.ndjson; do
  n=$(basename $f .ndjson)
  dec=$S/dec/$n.ndjson; mkdir -p $S/dec; [ -s $dec ] || python3 ~/hex2dec.py $f $dec > /dev/null
  r=$(t ~/official/.lake/build/bin/kernel $f);                                   printf "official\t%s\t%s\n" "$n" "${r// /	}" | tee -a $S/results.tsv
  r=$(cd ~/eink0rn && t ./arena/eink0rn --enforce-mutual-univ --mem=4000 -j8 $dec +RTS -A32m -M13g -RTS); printf "eink0rn\t%s\t%s\n" "$n" "${r// /	}" | tee -a $S/results.tsv
  r=$(cd ~/nanoclo && t sh -c "target/release/nanoclo config.json < $dec");        printf "nanoclo\t%s\t%s\n" "$n" "${r// /	}" | tee -a $S/results.tsv
  r=$(t ~/lazylean/build/lazylean $f);                                            printf "lazylean\t%s\t%s\n" "$n" "${r// /	}" | tee -a $S/results.tsv
done
echo "== SUITE DONE"
