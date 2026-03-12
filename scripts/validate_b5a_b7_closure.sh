#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

WITNESS_MODULE="${1:-Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTConcreteGlobalWitnessUnconditional}"

fail() {
  echo "ERROR: $*" >&2
  exit 1
}

check_no_target_sorry_block() {
  local file="$1"
  local theorem_name="$2"
  local pattern="theorem ${theorem_name}[\\s\\S]*?sorry"
  if rg -qUP "$pattern" "$file"; then
    echo "Found unresolved sorry block for ${theorem_name} in ${file}:" >&2
    rg -nUP "$pattern" "$file" | sed -n '1,20p' >&2
    fail "target theorem still contains sorry"
  fi
}

echo "== B5a+B7 Closure Gate =="
echo "repo: $ROOT"
echo "witness_module: $WITNESS_MODULE"
echo

echo "-- Precheck: target theorem bodies are sorry-free --"
check_no_target_sorry_block \
  "Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean" \
  "shifted_remainder_bound_leaf"
check_no_target_sorry_block \
  "Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean" \
  "truncatedExplicitFormulaPi_unconditional"
check_no_target_sorry_block \
  "Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean" \
  "targetTowerExactSeedAbovePerronThreshold_unconditional"
check_no_target_sorry_block \
  "Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean" \
  "antiTargetTowerExactSeedAbovePerronThreshold_unconditional"
echo "precheck_ok=true"
echo

echo "-- Build sequence --"
lake build "$WITNESS_MODULE"
lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf
lake build Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedExistence
lake build Littlewood.Aristotle.Standalone.RHPiDeepCoeffControlWitnesses
lake build Littlewood.Aristotle.Standalone.DeepBlockersResolved
lake build Littlewood.Aristotle.DeepSorries
echo "build_sequence_ok=true"
echo

echo "-- Critical path status --"
CRIT_OUT="$(./scripts/critical_path_expanded_status.sh)"
echo "$CRIT_OUT"

if ! echo "$CRIT_OUT" | rg -q "delegated_axiom_postulate_lines=0"; then
  fail "delegated_axiom_postulate_lines is nonzero"
fi

if echo "$CRIT_OUT" | rg -q "ExplicitFormulaPsiB5aShiftedBoundDeepLeaf\\.lean:.*sorry"; then
  fail "B5a deep leaf still appears in delegated sorry frontier"
fi

if echo "$CRIT_OUT" | rg -q "RHPiUnconditionalExactSeedExistence\\.lean:.*sorry"; then
  fail "RH-pi exact-seed file still appears in delegated sorry frontier"
fi

if ! echo "$CRIT_OUT" | rg -q "main_sorries=0"; then
  fail "main_sorries is nonzero"
fi

echo "critical_path_ok=true"
echo

echo "-- Root constructor check (targeted) --"
ROOT_OUT="$(./scripts/root_constructor_status.sh 2>&1 || true)"
echo "$ROOT_OUT" | sed -n '1,260p'

for target in \
  "Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp" \
  "Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries.ExplicitFormulaPsiGeneralHyp" \
  "Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra.RHPiUnconditionalExactSeedRootPayload"
do
  if echo "$ROOT_OUT" | rg -Fq "missing: $target"; then
    fail "target root constructor still missing: $target"
  fi
done

echo "root_constructor_targets_ok=true"
echo

echo "== PASS: B5a+B7 closure gate satisfied =="
