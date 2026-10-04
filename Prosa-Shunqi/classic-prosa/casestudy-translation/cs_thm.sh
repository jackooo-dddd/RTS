#!/usr/bin/env zsh
# usage: cs_thm.sh CASE THEOREM [from-line] [to-line]  -- print the elaborated contract of the case study's theorem
grep -v "incompatible prefixes\|defined at level\|^with arguments\|^File\|have incompatible\|One of them\|_scope" contracts/$1.txt | grep -v "^\s*$" | awk -v t="@ResponseTimeAnalysisFP.$2" -v t2="$2" '($0 ~ "^@" && index($0,t2)) {p=1} p' | sed -n "${3:-1},${4:-400}p"
