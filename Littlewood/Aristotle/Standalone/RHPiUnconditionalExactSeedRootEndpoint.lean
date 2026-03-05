import Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiUnconditionalExactSeedRootEndpoint

open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra

/-- Canonical root-infra endpoint for the truncated explicit-formula payload.

This is the theorem path intended to close
`RHPiUnconditionalExactSeedExistence.truncatedExplicitFormulaPi_unconditional`.
-/
theorem truncatedExplicitFormulaPi_unconditional_from_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] : TruncatedExplicitFormulaPiHyp :=
  truncatedExplicitFormulaPi_of_rootPayload

/-- Canonical root-infra endpoint for the positive exact-seed payload.

This is the theorem path intended to close
`RHPiUnconditionalExactSeedExistence.targetTowerExactSeedAbovePerronThreshold_unconditional`.
-/
theorem targetTowerExactSeedAbovePerronThreshold_unconditional_from_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] :
    TargetTowerExactSeedAbovePerronThreshold :=
  targetTowerExactSeedAbovePerronThreshold_of_rootPayload

/-- Canonical root-infra endpoint for the anti-target exact-seed payload.

This is the theorem path intended to close
`RHPiUnconditionalExactSeedExistence.antiTargetTowerExactSeedAbovePerronThreshold_unconditional`.
-/
theorem antiTargetTowerExactSeedAbovePerronThreshold_unconditional_from_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] :
    AntiTargetTowerExactSeedAbovePerronThreshold :=
  antiTargetTowerExactSeedAbovePerronThreshold_of_rootPayload

/-- Package the three endpoint payloads at once from the bundled root payload class. -/
theorem exactSeedUnconditionalTriple_from_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] :
    TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact
    ⟨truncatedExplicitFormulaPi_unconditional_from_rootPayload,
      targetTowerExactSeedAbovePerronThreshold_unconditional_from_rootPayload,
      antiTargetTowerExactSeedAbovePerronThreshold_unconditional_from_rootPayload⟩

end Aristotle.Standalone.RHPiUnconditionalExactSeedRootEndpoint
