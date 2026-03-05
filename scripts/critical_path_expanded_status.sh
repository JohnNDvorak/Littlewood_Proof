#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

DO_BUILD_MAIN=0
DO_BUILD_EXPANDED=0

case "${1:-}" in
  "--build")
    DO_BUILD_MAIN=1
    ;;
  "--build-expanded")
    DO_BUILD_MAIN=1
    DO_BUILD_EXPANDED=1
    ;;
  "")
    ;;
  *)
    echo "usage: $0 [--build|--build-expanded]"
    exit 2
    ;;
esac

MAIN_FILES=(
  "Littlewood/Aristotle/Standalone/HardyMeanSquareAsymptoticFromZetaMoment.lean"
  "Littlewood/Aristotle/Standalone/HardyAfeSignedGapAtomic.lean"
  "Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean"
  "Littlewood/Aristotle/Standalone/RSCompleteBlockAsymptotic.lean"
  "Littlewood/Aristotle/Standalone/ExplicitFormulaPsiSkeleton.lean"
  "Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aComponents.lean"
  "Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundAtomic.lean"
  "Littlewood/Aristotle/DeepSorries.lean"
)

DELEGATED_FILES=(
  "Littlewood/Aristotle/Standalone/B2StationaryWindowLeaves.lean"
  "Littlewood/Aristotle/Standalone/B2TailVdcDeepLeaf.lean"
  "Littlewood/Aristotle/Standalone/HardyAfeSignedGapDeepLeaf.lean"
  "Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean"
  "Littlewood/Aristotle/RSBlockBounds.lean"
  "Littlewood/Aristotle/ErrorTermExpansion.lean"
  "Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean"
)

MAIN_TARGETS=(
  "Littlewood.Aristotle.Standalone.HardyMeanSquareAsymptoticFromZetaMoment"
  "Littlewood.Aristotle.Standalone.DeepBlockersResolved"
  "Littlewood.Aristotle.Standalone.RSCompleteBlockAsymptotic"
  "Littlewood.Aristotle.Standalone.ExplicitFormulaPsiSkeleton"
  "Littlewood.Aristotle.DeepSorries"
)

EXPANDED_TARGETS=(
  "Littlewood.Aristotle.Standalone.B2StationaryWindowLeaves"
  "Littlewood.Aristotle.Standalone.B2TailVdcDeepLeaf"
  "Littlewood.Aristotle.Standalone.HardyAfeSignedGapDeepLeaf"
  "Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf"
  "Littlewood.Aristotle.RSBlockBounds"
  "Littlewood.Aristotle.ErrorTermExpansion"
  "Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedExistence"
)

count_matches() {
  local pattern="$1"
  shift
  (rg -n "$pattern" "$@" || true) | wc -l | tr -d ' '
}

print_section() {
  local label="$1"
  local pattern="$2"
  shift 2
  local files=("$@")
  echo "$label"
  rg -n "$pattern" "${files[@]}" || true
}

echo "== Critical Path Expanded Status =="
echo "repo: $ROOT"
echo

print_section "-- Main-path sorry lines --" "^[[:space:]]*sorry$" "${MAIN_FILES[@]}"
MAIN_SORRY_COUNT="$(count_matches "^[[:space:]]*sorry$" "${MAIN_FILES[@]}")"
echo "main_sorries=$MAIN_SORRY_COUNT"
echo

print_section "-- Delegated-leaf sorry lines --" "^[[:space:]]*sorry$" "${DELEGATED_FILES[@]}"
DELEGATED_SORRY_COUNT="$(count_matches "^[[:space:]]*sorry$" "${DELEGATED_FILES[@]}")"
echo "delegated_sorries=$DELEGATED_SORRY_COUNT"
echo

print_section "-- Main-path axiom/postulate lines --" "\\baxiom\\b|\\bpostulate\\b" "${MAIN_FILES[@]}"
MAIN_AXIOM_COUNT="$(count_matches "\\baxiom\\b|\\bpostulate\\b" "${MAIN_FILES[@]}")"
echo "main_axiom_postulate_lines=$MAIN_AXIOM_COUNT"
echo

print_section "-- Delegated-leaf axiom/postulate lines --" "\\baxiom\\b|\\bpostulate\\b" "${DELEGATED_FILES[@]}"
DELEGATED_AXIOM_COUNT="$(count_matches "\\baxiom\\b|\\bpostulate\\b" "${DELEGATED_FILES[@]}")"
echo "delegated_axiom_postulate_lines=$DELEGATED_AXIOM_COUNT"
echo

if [[ "$DO_BUILD_MAIN" -eq 1 ]]; then
  echo "-- Main target builds --"
  for mod in "${MAIN_TARGETS[@]}"; do
    echo "building: $mod"
    lake build "$mod"
    echo "ok: $mod"
  done
  echo
fi

if [[ "$DO_BUILD_EXPANDED" -eq 1 ]]; then
  echo "-- Delegated target builds --"
  for mod in "${EXPANDED_TARGETS[@]}"; do
    echo "building: $mod"
    lake build "$mod"
    echo "ok: $mod"
  done
  echo
fi

echo "== Summary =="
echo "main_sorries: $MAIN_SORRY_COUNT"
echo "delegated_sorries: $DELEGATED_SORRY_COUNT"
echo "total_main_plus_delegated_sorries: $((MAIN_SORRY_COUNT + DELEGATED_SORRY_COUNT))"
echo "main_axiom_postulate_lines: $MAIN_AXIOM_COUNT"
echo "delegated_axiom_postulate_lines: $DELEGATED_AXIOM_COUNT"
echo "total_main_plus_delegated_axiom_postulate_lines: $((MAIN_AXIOM_COUNT + DELEGATED_AXIOM_COUNT))"
