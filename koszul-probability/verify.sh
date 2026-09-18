#!/usr/bin/env bash
# Formal verification of the Koszul probability theorems.
#
# Builds the Lean project and checks the axiom dependencies of every
# audited theorem. Exits nonzero if the build fails, if any proof uses
# sorry/admit, or if any audited theorem depends on an axiom outside
# Lean's standard three (propext, Classical.choice, Quot.sound).
#
# Usage:  ./verify.sh            # full check
#         ./verify.sh --no-cache # skip downloading mathlib's compiled cache
set -euo pipefail
cd "$(dirname "$0")"

USE_CACHE=1
[[ "${1:-}" == "--no-cache" ]] && USE_CACHE=0

step() { printf '\n==> %s\n' "$*"; }

command -v lake >/dev/null 2>&1 || {
  echo "error: 'lake' not found. Install elan: https://github.com/leanprover/elan" >&2
  exit 1
}

step "Toolchain: $(cat lean-toolchain)"
lean --version

step "Checking sources for sorry / admit"
if grep -rnE '\bsorry\b|\badmit\b' --include='*.lean' KoszulProbability KoszulProbability.lean Audit.lean; then
  echo "error: found sorry/admit in sources" >&2
  exit 1
fi
echo "none found"

step "Fetching dependencies (pinned in lake-manifest.json)"
lake update >/dev/null

if [[ $USE_CACHE -eq 1 ]]; then
  step "Downloading mathlib compiled cache"
  lake exe cache get
fi

step "Building all proof files"
lake build

step "Auditing axiom dependencies"
lake env lean Audit.lean | tee axiom-audit.txt

step "Checking audit output"
if grep -q 'sorryAx' axiom-audit.txt; then
  echo "error: some theorem depends on sorryAx" >&2
  exit 1
fi
BAD=$(grep 'depends on axioms' axiom-audit.txt \
      | sed -E 's/.*depends on axioms: \[(.*)\]/\1/' \
      | tr ',' '\n' | sed 's/^ *//' | sort -u \
      | grep -vxE 'propext|Classical\.choice|Quot\.sound' || true)
if [[ -n "$BAD" ]]; then
  echo "error: nonstandard axioms in use:" >&2
  echo "$BAD" >&2
  exit 1
fi
N=$(grep -c 'depends on axioms' axiom-audit.txt)
echo "OK: $N theorems verified; each depends only on propext, Classical.choice, Quot.sound."
