#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

DELEGATED_FILES=(
  "Littlewood/Aristotle/Standalone/B2TailVdcDeepLeaf.lean"
  "Littlewood/Aristotle/Standalone/B2StationaryWindowLeaves.lean"
  "Littlewood/Aristotle/Standalone/HardyAfeSignedGapDeepLeaf.lean"
  "Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean"
  "Littlewood/Aristotle/RSBlockBounds.lean"
  "Littlewood/Aristotle/ErrorTermExpansion.lean"
  "Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean"
)

echo "== Delegated Frontier Report =="
echo "repo: $ROOT"
echo

echo "-- Frontier groups --"
echo "B2 tail VdC deep leaf:"
echo "  Littlewood/Aristotle/Standalone/B2TailVdcDeepLeaf.lean"
echo "B2 assembly wrapper:"
echo "  Littlewood/Aristotle/Standalone/B2StationaryWindowLeaves.lean"
echo "B1 signed AFE leaf:"
echo "  Littlewood/Aristotle/Standalone/HardyAfeSignedGapDeepLeaf.lean"
echo "B5a shifted remainder leaf:"
echo "  Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean"
echo "RS7 cluster:"
echo "  Littlewood/Aristotle/ErrorTermExpansion.lean"
echo "  Littlewood/Aristotle/RSBlockBounds.lean"
echo "RH-pi exact-seed cluster:"
echo "  Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean"
echo

total_sorries=0

for f in "${DELEGATED_FILES[@]}"; do
  echo "-- $f"
  if [[ ! -f "$f" ]]; then
    echo "missing file"
    echo
    continue
  fi

  count="$( (rg -n "^[[:space:]]*sorry$" "$f" || true) | wc -l | tr -d ' ' )"
  total_sorries=$((total_sorries + count))
  echo "sorry_count=$count"

  if [[ "$count" -gt 0 ]]; then
    awk '
      /^[[:space:]]*(private[[:space:]]+)?(theorem|lemma|def|instance|class)[[:space:]]+/ {decl=$0}
      /^[[:space:]]*sorry$/ {printf("  %s:%d :: %s\n", FILENAME, NR, decl)}
    ' "$f"
  fi
  echo
done

echo "-- Structural blocker signals --"
echo "RS principal-branch incompatibility markers:"
rg -n "stirling_arg_gamma_asymp_false|stirling_arg_gamma_false" \
  "Littlewood/Aristotle/StirlingArgGamma.lean" || true
echo

echo "RH-pi class constructors for TruncatedExplicitFormulaPiHyp:"
rg -n "class TruncatedExplicitFormulaPiHyp|instance .*TruncatedExplicitFormulaPiHyp|truncatedExplicitFormulaPi_unconditional" \
  "Littlewood/Bridge/PiLiDirectOscillation.lean" \
  "Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean" \
  "Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean" || true
echo

echo "RH-pi exact-seed constructor sites:"
rg -n "targetTowerExactSeedAbovePerronThreshold_unconditional|antiTargetTowerExactSeedAbovePerronThreshold_unconditional" \
  "Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean" \
  "Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean" || true
echo

echo "== Summary =="
echo "delegated_sorries_total=$total_sorries"
if [[ "$total_sorries" -eq 0 ]]; then
  echo "frontier_status=clean"
else
  echo "frontier_status=open"
fi
