#!/usr/bin/env bash
# Whole arena bundle (good/ and bad/: bugs, corner-cases, perf) on one machine: official, eink0rn, nanoclo, lazylean.
export PATH="$HOME/.cargo/bin:$PATH"
S=~/suite; : > $S/results_all.tsv
t() { /usr/bin/time -f '%e %M' -o $S/ta.txt timeout 1200 "$@" > $S/runa.log 2>&1; rc=$?; read s kb < <(tail -1 $S/ta.txt); echo "$s $((kb/1024)) $rc"; }
for f in $(find $S/bundle -name '*.ndjson' | sort); do
  n=${f#$S/bundle/}; exp=$([[ $n == good/* ]] && echo 0 || echo 1)
  dec=$S/decb/$n; mkdir -p $(dirname $dec); [ -s $dec ] || python3 ~/hex2dec.py $f $dec > /dev/null
  r=$(t ~/official/.lake/build/bin/kernel $f);                                   printf "official\t%s\t%s\t%s\n" "$n" "$exp" "${r// /	}" >> $S/results_all.tsv
  r=$(cd ~/eink0rn && t ./arena/eink0rn --enforce-mutual-univ --mem=4000 -j8 $dec +RTS -A32m -M13g -RTS); printf "eink0rn\t%s\t%s\t%s\n" "$n" "$exp" "${r// /	}" >> $S/results_all.tsv
  r=$(cd ~/nanoclo && t sh -c "target/release/nanoclo config.json < $dec");        printf "nanoclo\t%s\t%s\t%s\n" "$n" "$exp" "${r// /	}" >> $S/results_all.tsv
  r=$(t ~/lazylean/build/lazylean $f);                                            printf "lazylean\t%s\t%s\t%s\n" "$n" "$exp" "${r// /	}" >> $S/results_all.tsv
done
echo "== ALL DONE"
