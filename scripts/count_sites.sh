#!/usr/bin/env bash
# Count the application sites of the library whose domain-membership obligation is discharged
# by `zdom` (Table 2 / Sec. 6 of the paper). The population of the measurement is the 74
# application sites whose domain proof had been written by hand before the tactic existed;
# the sites that stay manual are listed by `grep -n "rw \[is_func_dom_eq" ZFLean/*.lean`.
cd "$(dirname "$0")/.."
for f in ZFLean/Functions.lean ZFLean/Recursion.lean ZFLean/Sum.lean ZFLean/Isomorphisms.lean \
         ZFLean/Embeddings.lean ZFLean/Naturals.lean ZFLean/Integers.lean ZFLean/Rationals.lean \
         ZFLean/Booleans.lean ZFLean/Quotient.lean ZFLean/Basic.lean ZFLean/Def.lean; do
  n=$(grep -o "by zdom" "$f" | wc -l | tr -d ' ')
  printf "%4d  %s\n" "$n" "$f"
done
auto="$(cat ZFLean/Functions.lean ZFLean/Recursion.lean ZFLean/Sum.lean ZFLean/Isomorphisms.lean \
       ZFLean/Embeddings.lean ZFLean/Naturals.lean ZFLean/Integers.lean ZFLean/Rationals.lean \
       ZFLean/Booleans.lean ZFLean/Quotient.lean ZFLean/Basic.lean ZFLean/Def.lean | grep -o "by zdom" | wc -l | tr -d ' ')"
printf "%4d automatic + 1 manual (the Cantor–Schröder–Bernstein site in Isomorphisms.lean,\n" "$auto"
printf "      which destructures an existential hypothesis) = %d total, the population of Sec. 6.2\n" "$((auto+1))"
