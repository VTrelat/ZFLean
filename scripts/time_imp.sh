#!/usr/bin/env bash
# Median-of-three clean elaboration time of the case-study module (the protocol of the paper's
# size/time table). Only `casestudy/Imp.lean` is rebuilt; the library and Mathlib stay cached.
# Raw logs are archived in `timings.log`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Imp > /dev/null            # warm the library once
: > timings.log
for i in 1 2 3; do
  rm -f .lake/build/lib/lean/Imp.* .lake/build/ir/Imp.*
  { /usr/bin/time -p lake build Imp > /dev/null ; } 2>> timings.log
done
grep '^real' timings.log | sort -n -k2 \
  | awk 'NR==2 {print "median of three clean builds of Imp:", $2, "s (raw logs in timings.log)"}'
