#!/usr/bin/env bash
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p ~/std-export; cd ~/4ct
date; echo "== export Std"
/usr/bin/time -v lake env ~/lean4export/.lake/build/bin/lean4export Std > ~/std-export/std.ndjson 2> ~/std-export/export.log; echo "EXPORT_RC=$?"
ls -la ~/std-export/std.ndjson; grep -E "Elapsed|Maximum resident" ~/std-export/export.log
date; echo "== check Std (4 shards)"
seq 0 3 | xargs -P 4 -I{} sh -c "/usr/bin/time -v ~/lazylean/build/lazylean -k --slow 5 --max-rss 20000 --progress ~/std-export/progress.{}.txt --shard {}/4 ~/std-export/std.ndjson > ~/std-export/check.{}.log 2>&1"
grep -hE "^checked|^FAIL|Elapsed|Maximum" ~/std-export/check.*.log | cut -c1-160
date; echo "== STD DONE"
