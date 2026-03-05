#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

DO_BUILD=0
if [[ "${1:-}" == "--build" ]]; then
  DO_BUILD=1
fi

FILES=(
  "Littlewood/Aristotle/Standalone/HardyMeanSquareAsymptoticFromZetaMoment.lean"
  "Littlewood/Aristotle/Standalone/HardyAfeSignedGapAtomic.lean"
  "Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean"
  "Littlewood/Aristotle/Standalone/RSCompleteBlockAsymptotic.lean"
  "Littlewood/Aristotle/Standalone/ExplicitFormulaPsiSkeleton.lean"
  "Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aComponents.lean"
  "Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundAtomic.lean"
  "Littlewood/Aristotle/DeepSorries.lean"
)

TARGET_MODULES=(
  "Littlewood.Aristotle.Standalone.HardyMeanSquareAsymptoticFromZetaMoment"
  "Littlewood.Aristotle.Standalone.RSCompleteBlockAsymptotic"
  "Littlewood.Aristotle.Standalone.ExplicitFormulaPsiSkeleton"
  "Littlewood.Aristotle.Standalone.DeepBlockersResolved"
  "Littlewood.Aristotle.DeepSorries"
)

echo "== Critical Path (5) Status =="
echo "repo: $ROOT"
echo

echo "-- Active-path sorry lines --"
rg -n "^[[:space:]]*sorry$" "${FILES[@]}" || true
SORRY_COUNT="$( (rg -n "^[[:space:]]*sorry$" "${FILES[@]}" || true) | wc -l | tr -d ' ')"
echo "total_active_sorries=$SORRY_COUNT"
echo

echo "-- Active-path axiom/postulate lines --"
rg -n "\\baxiom\\b|\\bpostulate\\b" "${FILES[@]}" || true
AXIOM_COUNT="$( (rg -n "\\baxiom\\b|\\bpostulate\\b" "${FILES[@]}" || true) | wc -l | tr -d ' ')"
echo "total_active_axiom_postulate_lines=$AXIOM_COUNT"
echo

if [[ "$DO_BUILD" -eq 1 ]]; then
  echo "-- Targeted builds --"
  for mod in "${TARGET_MODULES[@]}"; do
    echo "building: $mod"
    if lake build "$mod"; then
      echo "ok: $mod"
    else
      echo "fail: $mod"
      exit 1
    fi
  done
  echo
fi

echo "== Summary =="
echo "active_sorries: $SORRY_COUNT"
echo "active_axiom_postulate_lines: $AXIOM_COUNT"
