#!/usr/bin/env bash
# Median-of-three clean elaboration time of the case-study module (the protocol of the paper's
# size/time table). Only `casestudy/Imp.lean` is rebuilt; the library and Mathlib stay cached.
# Raw `time` logs go to `scripts/timings/imp.log`, which is not tracked.
# Requires `/usr/bin/time`.
set -euo pipefail
cd "$(dirname "$0")/.."
command -v /usr/bin/time > /dev/null || { echo "missing prerequisite: /usr/bin/time" >&2; exit 1; }
LOG=scripts/timings/imp.log
mkdir -p scripts/timings
lake build Imp > /dev/null            # warm the library once
: > "$LOG"
for i in 1 2 3; do
  rm -f .lake/build/lib/lean/Imp.* .lake/build/ir/Imp.*
  { /usr/bin/time -p lake build Imp > /dev/null ; } 2>> "$LOG"
done
grep '^real' "$LOG" | sort -n -k2 \
  | awk -v logf="$LOG" 'NR==2 {print "median of three clean builds of Imp:", $2, "s (raw logs in " logf ")"}'
