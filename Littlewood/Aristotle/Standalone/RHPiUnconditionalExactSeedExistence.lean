import Littlewood.Bridge.PiLiDirectOscillation
import Littlewood.Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
import Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
import Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedRootEndpoint

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiUnconditionalExactSeedExistence

open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootEndpoint

/-- Candidate closure route for the truncated explicit-formula payload from the
bundled RH-`pi` root payload class. -/
theorem truncatedExplicitFormulaPi_unconditional_of_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] :
    TruncatedExplicitFormulaPiHyp := by
  exact truncatedExplicitFormulaPi_unconditional_from_rootPayload

/-- Candidate closure route for the positive exact-seed payload from the bundled
RH-`pi` root payload class. -/
theorem targetTowerExactSeedAbovePerronThreshold_unconditional_of_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] :
    TargetTowerExactSeedAbovePerronThreshold := by
  exact targetTowerExactSeedAbovePerronThreshold_unconditional_from_rootPayload

/-- Candidate closure route for the anti-target exact-seed payload from the bundled
RH-`pi` root payload class. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_unconditional_of_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] :
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact antiTargetTowerExactSeedAbovePerronThreshold_unconditional_from_rootPayload

/--
Hard-specified exact-seed + truncated explicit-formula payload for RH-`pi`.

These are currently unresolved proof obligations.
-/
theorem truncatedExplicitFormulaPi_unconditional : TruncatedExplicitFormulaPiHyp := by
  sorry

/-- Global instance for the explicit-formula payload. -/
instance : TruncatedExplicitFormulaPiHyp := truncatedExplicitFormulaPi_unconditional

theorem targetTowerExactSeedAbovePerronThreshold_unconditional :
    TargetTowerExactSeedAbovePerronThreshold := by
  sorry

theorem antiTargetTowerExactSeedAbovePerronThreshold_unconditional :
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  sorry

/-- Global target/anti target exact-seed phase classes at the Perron threshold level. -/
instance targetTowerExactSeedAbovePerronThresholdHyp_unconditional :
    TargetTowerExactSeedAbovePerronThresholdHyp := by
  exact ⟨targetTowerExactSeedAbovePerronThreshold_unconditional⟩

instance antiTargetTowerExactSeedAbovePerronThresholdHyp_unconditional :
    AntiTargetTowerExactSeedAbovePerronThresholdHyp := by
  exact ⟨antiTargetTowerExactSeedAbovePerronThreshold_unconditional⟩

end Aristotle.Standalone.RHPiUnconditionalExactSeedExistence
