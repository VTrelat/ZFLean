#!/usr/bin/env bash
# Elaboration time of every library module, the protocol of the paper's size/time table:
# each module is rebuilt from scratch three times (its build artifacts deleted, the rest of
# the library and Mathlib cached), the median is taken, and medians are summed per component.
# Raw `time` logs go to `scripts/timings/library.log` and the per-component summary to
# `scripts/timings/library-summary.txt`; neither is tracked. Takes
# about ten minutes. Requires `bc` and `/usr/bin/time`. Portable to bash 3 (macOS's default
# shell).
#
#   bash scripts/time_components.sh
set -euo pipefail
cd "$(dirname "$0")/.."
for tool in bc /usr/bin/time; do
  command -v "$tool" > /dev/null || { echo "missing prerequisite: $tool" >&2; exit 1; }
done
LOG=scripts/timings/library.log
SUMMARY=scripts/timings/library-summary.txt
mkdir -p scripts/timings
lake build > /dev/null                      # warm everything once
: > "$LOG"
: > "$SUMMARY"

component() {
  case "$1" in
    Functions) echo 1 ;;
    Embeddings|Isomorphisms) echo 2 ;;
    Naturals|Recursion) echo 3 ;;
    Integers) echo 4 ;;
    Booleans|Sum|Quotient|Rationals) echo 5 ;;
    Transfer|TransferAlgebra|Examples) echo 6 ;;
    Basic|Def|Tactics) echo 7 ;;
  esac
}
NAMES=("" "Relational calculus" "Embeddings, isomorphisms" "Naturals, set-level recursion" \
       "Integers, integer division" "Booleans, sums, quotients, rationals" \
       "Transfer tactic, lemma sets, examples" "Core glue and automation")
SUM=(0 0 0 0 0 0 0 0)

for m in Functions Embeddings Isomorphisms Naturals Recursion Integers Booleans Sum Quotient \
         Rationals Transfer TransferAlgebra Examples Basic Def Tactics; do
  times=""
  for i in 1 2 3; do
    rm -f .lake/build/lib/lean/ZFLean/$m.* .lake/build/ir/ZFLean/$m.*
    { /usr/bin/time -p lake build ZFLean.$m > /dev/null ; } 2> .time.tmp
    t=$(grep '^real' .time.tmp | awk '{print $2}')
    echo "$m run$i $t" >> "$LOG"
    times="$times$t
"
  done
  med=$(printf "%s" "$times" | sort -n | sed -n 2p)
  echo "$m median $med" >> "$LOG"
  printf "%-16s median %6.1f s\n" "$m" "$med" | tee -a "$SUMMARY"
  c=$(component "$m")
  SUM[$c]=$(echo "${SUM[$c]} + $med" | bc)
done
rm -f .time.tmp
echo "--- per component (sum of module medians) ---" | tee -a "$SUMMARY"
total=0
for c in 1 2 3 4 5 6 7; do
  printf "%-40s %6.1f s\n" "${NAMES[$c]}" "${SUM[$c]}" | tee -a "$SUMMARY"
  total=$(echo "$total + ${SUM[$c]}" | bc)
done
printf "%-40s %6.1f s\n" "Total" "$total" | tee -a "$SUMMARY"
