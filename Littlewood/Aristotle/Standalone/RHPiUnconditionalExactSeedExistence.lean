import Littlewood.Bridge.PiLiDirectOscillation
import Littlewood.Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiUnconditionalExactSeedExistence

open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox

/--
Hard-specified exact-seed + truncated explicit-formula payload for RH-`pi`.

These are intentionally explicit assumptions for the deep-leaf boundary.
-/
axiom truncatedExplicitFormulaPi_unconditional : TruncatedExplicitFormulaPiHyp

/-- Global instance for the explicit-formula payload. -/
instance : TruncatedExplicitFormulaPiHyp := truncatedExplicitFormulaPi_unconditional

axiom targetTowerExactSeedAbovePerronThreshold_unconditional :
    TargetTowerExactSeedAbovePerronThreshold

axiom antiTargetTowerExactSeedAbovePerronThreshold_unconditional :
    AntiTargetTowerExactSeedAbovePerronThreshold

/-- Global target/anti target exact-seed phase classes at the Perron threshold level. -/
instance targetTowerExactSeedAbovePerronThresholdHyp_unconditional :
    TargetTowerExactSeedAbovePerronThresholdHyp := by
  exact ⟨targetTowerExactSeedAbovePerronThreshold_unconditional⟩

instance antiTargetTowerExactSeedAbovePerronThresholdHyp_unconditional :
    AntiTargetTowerExactSeedAbovePerronThresholdHyp := by
  exact ⟨antiTargetTowerExactSeedAbovePerronThreshold_unconditional⟩

end Aristotle.Standalone.RHPiUnconditionalExactSeedExistence
