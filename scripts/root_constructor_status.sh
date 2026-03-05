#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

TMP="$(mktemp /tmp/root_constructor_status.XXXXXX.lean)"
trap 'rm -f "$TMP"' EXIT

cat > "$TMP" <<'LEAN'
import Littlewood.Aristotle.Standalone.DeepBlockersResolved
import Littlewood.Aristotle.Standalone.B2VdcFirstDerivTailRootInfra
import Littlewood.Aristotle.Standalone.B2SupportPhaseRootInfra

-- B1 root constructor
#synth ZetaMeanSquareHalfBound

-- B2 root constructor
#synth Aristotle.Standalone.B2TailVdcRootInfra.B2TailVdcRootPayload
#synth Aristotle.Standalone.B2VdcFirstDerivTailRootInfra.B2VdcFirstDerivTailRootPayload
#synth Aristotle.Standalone.B2SupportPhaseRootInfra.B2SupportPhaseRootPayload

-- B2 upstream class chain
#synth HardyFirstMomentWiring.HardyThetaDifferentiableOnSupportHyp
#synth HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp
#synth HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp
#synth HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp
#synth HardyFirstMomentWiring.HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp
#synth HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp
#synth HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp
#synth HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp

-- B5a roots
#synth Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp
#synth Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries.ExplicitFormulaPsiGeneralHyp

-- RH-pi exact-seed root payload
#synth Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra.RHPiUnconditionalExactSeedRootPayload
LEAN

echo "== Root Constructor Status =="
echo "repo: $ROOT"
echo

if OUT="$(lake env lean "$TMP" 2>&1)"; then
  echo "All root constructors synthesized."
  exit 0
fi

echo "$OUT" | sed -n '1,240p'
echo

echo "-- Summary --"
for target in \
  "ZetaMeanSquareHalfBound" \
  "Aristotle.Standalone.B2TailVdcRootInfra.B2TailVdcRootPayload" \
  "Aristotle.Standalone.B2VdcFirstDerivTailRootInfra.B2VdcFirstDerivTailRootPayload" \
  "Aristotle.Standalone.B2SupportPhaseRootInfra.B2SupportPhaseRootPayload" \
  "HardyFirstMomentWiring.HardyThetaDifferentiableOnSupportHyp" \
  "HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp" \
  "HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp" \
  "HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp" \
  "HardyFirstMomentWiring.HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp" \
  "HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp" \
  "HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp" \
  "HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp" \
  "Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp" \
  "Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries.ExplicitFormulaPsiGeneralHyp" \
  "Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra.RHPiUnconditionalExactSeedRootPayload"
do
  if echo "$OUT" | rg -Fq "$target"; then
    echo "missing: $target"
  else
    echo "present: $target"
  fi
done

exit 1
