#!/bin/zsh
# Scratch compile of the official closure of model/task/arrival/example.v under rocq93rc1,
# with the accepted rocq93 compatibility patches that touch files in the closure.
P=/Users/shunqiwang/CityuHK/Research/Lean/TranslationProof/Prosa-Shunqi/Validation
W=/private/tmp/claude-501/-Users-shunqiwang-CityuHK-Research-Lean-TranslationProof/9a8848ea-c9e8-497f-a3b2-26bf9a253005/scratchpad/finsum/exclosure; rm -rf $W; mkdir -p $W; cp -R $P/.work/prosa-v06-414e667/. $W/src; rm -rf $W/src/.git
cd $W/src
for p in util-tactics util-div-mod util-seqset analysis-schedule-prefix; do patch -p1 < $P/patches/prosa-v06-rocq93-$p.patch > $W/patch_$p.log 2>&1 && echo "patched $p" >> $W/summary.txt || echo "PATCH_FAIL $p" >> $W/summary.txt; done
patch -p1 < $P/patches/analysis_facts_behavior_supply_rocq93_source_compat.patch > $W/patch_supply.log 2>&1 && echo "patched supply" >> $W/summary.txt || echo "PATCH_FAIL supply" >> $W/summary.txt
ulimit -s 65520
for f in $(cat /private/tmp/claude-501/-Users-shunqiwang-CityuHK-Research-Lean-TranslationProof/9a8848ea-c9e8-497f-a3b2-26bf9a253005/scratchpad/finsum/example_closure.txt); do
  s=$(date +%s)
  perl -e 'alarm shift; exec @ARGV' 900 opam exec --switch=rocq93rc1 -- rocq c -R . prosa $f > $W/log_${f//\//_}.log 2>&1
  rc=$?; echo "$f rc=$rc secs=$(($(date +%s)-s))" >> $W/summary.txt
  if [ $rc -ne 0 ]; then echo "FIRST_FAILURE $f" >> $W/summary.txt; break; fi
done
echo DONE >> $W/summary.txt
