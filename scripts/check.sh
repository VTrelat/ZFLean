#!/usr/bin/env bash
# Build the library and refuse admitted declarations and non-standard axioms.
#
#   scripts/check.sh            # from the repository root, after `lake exe cache get`
#
# 1. `lake build` compiles every module, the examples and the case study included.
# 2. The build log must not contain `declaration uses 'sorry'` (an admitted proof).
# 3. `scripts/audit_axioms.lean` prints the axioms of the headline results; only
#    `propext`, `Classical.choice` and `Quot.sound` are allowed.
set -euo pipefail
cd "$(dirname "$0")/.."

lake build 2>&1 | tee build.log
if grep -q "declaration uses .sorry." build.log; then
  echo "check.sh: FAIL — admitted declarations in the build log" >&2
  exit 1
fi

lake env lean scripts/audit_axioms.lean 2>&1 | tee axioms.log
if grep -q "sorryAx" axioms.log; then
  echo "check.sh: FAIL — a headline result depends on sorryAx" >&2
  exit 1
fi
if grep -v "depends on axioms: \[propext, Classical.choice, Quot.sound\]" axioms.log | grep -q "depends on axioms"; then
  echo "check.sh: FAIL — a headline result depends on a non-standard axiom" >&2
  exit 1
fi
echo "== obligation harness (Sec. 6.2) — self-verifying, the build asserts every count =="
lake build ImpObligations

echo "== size table (Sec. 6.3) =="
python3 scripts/count_loc.py

echo "== zdom sweep (Sec. 6.2) =="
scripts/count_sites.sh

echo "check.sh: OK — 0 admitted declarations, standard axioms only, obligation harness verified"
echo "          (timings: scripts/time_imp.sh reproduces the case-study entry)"
