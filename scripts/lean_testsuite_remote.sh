#!/usr/bin/env bash
# Lean 4's own test suite (tests/elab/*.lean) as a positive kernel suite: compile each file with the
# toolchain, export the module, check it with lazylean trusting Init.  Results in ~/leantests/results.tsv:
#   file  status(compile-fail|export-fail|accept|reject|declined|error|timeout)  seconds  MB  last-line
export PATH="$HOME/.elan/bin:$PATH"
LEAN=$(ls -d ~/.elan/toolchains/leanprover--lean4---v4.34.0-rc2)/bin/lean
R=~/leantests; mkdir -p $R/work $R/exports; : > $R/results.tsv
one() {
  f=$1; b=$(basename $f .lean); w=$R/work/$b; mkdir -p $w; cp $f $w/Test.lean
  cd $w
  if ! timeout 300 $LEAN -o Test.olean Test.lean > compile.log 2>&1; then printf "%s\tcompile-fail\t0\t0\t%s\n" "$b" "$(tail -1 compile.log | cut -c1-120)" >> $R/results.tsv; return; fi
  if ! (cd ~/4ct && LEAN_PATH="$w:$(lake env printenv LEAN_PATH)" timeout 600 ~/lean4export/.lake/build/bin/lean4export Test > $R/exports/$b.ndjson 2> $w/export.log); then printf "%s\texport-fail\t0\t0\t%s\n" "$b" "$(tail -1 $w/export.log | cut -c1-120)" >> $R/results.tsv; rm -f $R/exports/$b.ndjson; return; fi
  /usr/bin/time -f '%e %M' -o $w/time.txt timeout 900 ~/lazylean/build/lazylean --trust-file ~/init_names.txt --max-rss 8000 $R/exports/$b.ndjson > $w/check.log 2>&1; rc=$?
  read s kb < <(tail -1 $w/time.txt)
  st=$([ $rc = 0 ] && echo accept || { [ $rc = 1 ] && echo reject || { [ $rc = 2 ] && echo declined || { [ $rc = 124 ] && echo timeout || echo "error($rc)"; }; }; })
  printf "%s\t%s\t%s\t%s\t%s\n" "$b" "$st" "$s" "$((kb/1024))" "$(grep -m1 -E "^FAIL|error" $w/check.log | cut -c1-160)" >> $R/results.tsv
  rm -f $R/exports/$b.ndjson $w/Test.olean $w/Test.ilean
}
export -f one; export R LEAN
date; echo "== lean tests: $(ls ~/lean-tests/*.lean | wc -l) files"
ls ~/lean-tests/*.lean | xargs -P ${JOBS:-24} -I{} bash -c 'one {}'
date; echo "== LEANTESTS DONE"
cut -f2 $R/results.tsv | sort | uniq -c
