#!/usr/bin/env bash
# Like-for-like on the slowest declarations: export each one's closure, time Lean's kernel
# (arena official checker) and lazylean with and without --memo.
export PATH="$HOME/.elan/bin:$PATH"
OUT=~/4ct-export/samples; mkdir -p $OUT
DECLS="FourColor.Cfg629.part0._proof_1 FourColor.Cfg453.part2._proof_1 FourColor.Cfg082.part4._proof_1 FourColor.Cfg151.part1._proof_1 FourColor.Cfg574.part0._proof_1 FourColor.Bulk.Hyb218.hok_2._proof_1 FourColor.Bulk.Hyb218.hctr._proof_1 FourColor.c7_3989_4._proof_1 FourColor.Bulk.Hyb561.hctr._proof_1 FourColor.c7_4673_6._proof_1"
printf "decl\tdecls\tofficial_s\tofficial_MB\tofficial_rc\tll_s\tll_MB\tll_rc\tll_memo_s\tll_memo_MB\tll_memo_rc\n" > $OUT/results.tsv
t() { # label binary args... -> "s MB rc"
  /usr/bin/time -f '%e %M' -o $OUT/t.txt timeout 1800 "$@" > $OUT/run.log 2>&1; rc=$?; read s kb < <(tail -1 $OUT/t.txt); echo "$s $((kb/1024)) $rc"
}
for D in $DECLS; do
  f=$OUT/$D.ndjson
  [ -s $f ] || (cd ~/4ct && lake env ~/lean4export/.lake/build/bin/lean4export FourColor.Complete -- $D > $f 2> $OUT/$D.export.log)
  n=$(grep -c '"thm"\|"def"\|"opaque"\|"axiom"\|"inductive"\|"quot"' $f)
  o=$(t ~/official/.lake/build/bin/kernel $f)
  l=$(t ~/lazylean/build/lazylean $f)
  m=$(LL_MEMO=1 t ~/lazylean/build/lazylean $f)
  printf "%s\t%s\t%s\t%s\t%s\n" "$D" "$n" "${o// /	}" "${l// /	}" "${m// /	}" | tee -a $OUT/results.tsv
done
echo "== SAMPLES DONE"
