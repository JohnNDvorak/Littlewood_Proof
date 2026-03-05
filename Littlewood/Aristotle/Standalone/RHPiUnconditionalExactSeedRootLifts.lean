import Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedRootEndpoint

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiUnconditionalExactSeedRootLifts

open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootEndpoint

/-- Package the three exact-seed endpoint classes into the root payload witness. -/
theorem rootPayload_of_exactSeedAboveThresholdHyp
    [TruncatedExplicitFormulaPiHyp]
    [TargetTowerExactSeedAbovePerronThresholdHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdHyp] :
    RHPiUnconditionalExactSeedRootPayload := by
  refine ⟨inferInstance, ?_, ?_⟩
  · exact TargetTowerExactSeedAbovePerronThresholdHyp.witness
  · exact AntiTargetTowerExactSeedAbovePerronThresholdHyp.witness

/-- Build the root payload witness from explicit exact-seed terms. -/
theorem rootPayload_of_exactSeedAboveThreshold
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget : TargetTowerExactSeedAbovePerronThreshold)
    (hAntiTarget : AntiTargetTowerExactSeedAbovePerronThreshold) :
    RHPiUnconditionalExactSeedRootPayload := by
  letI : TruncatedExplicitFormulaPiHyp := hTruncated
  letI : TargetTowerExactSeedAbovePerronThresholdHyp := ⟨hTarget⟩
  letI : AntiTargetTowerExactSeedAbovePerronThresholdHyp := ⟨hAntiTarget⟩
  exact rootPayload_of_exactSeedAboveThresholdHyp

/-- Recover all three unconditional endpoint payloads from class-level exact-seed
hypotheses. -/
theorem exactSeedUnconditionalTriple_from_exactSeedAboveThresholdHyp
    [TruncatedExplicitFormulaPiHyp]
    [TargetTowerExactSeedAbovePerronThresholdHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdHyp] :
    TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  letI : RHPiUnconditionalExactSeedRootPayload :=
    rootPayload_of_exactSeedAboveThresholdHyp
  exact exactSeedUnconditionalTriple_from_rootPayload

/-- Recover all three unconditional endpoint payloads from explicit exact-seed
terms. -/
theorem exactSeedUnconditionalTriple_from_exactSeedAboveThreshold
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget : TargetTowerExactSeedAbovePerronThreshold)
    (hAntiTarget : AntiTargetTowerExactSeedAbovePerronThreshold) :
    TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  letI : RHPiUnconditionalExactSeedRootPayload :=
    rootPayload_of_exactSeedAboveThreshold hTruncated hTarget hAntiTarget
  exact exactSeedUnconditionalTriple_from_rootPayload

/-- Component extraction: truncated explicit-formula payload from class-level
exact-seed hypotheses. -/
theorem truncatedExplicitFormulaPi_from_exactSeedAboveThresholdHyp
    [TruncatedExplicitFormulaPiHyp]
    [TargetTowerExactSeedAbovePerronThresholdHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdHyp] :
    TruncatedExplicitFormulaPiHyp := by
  exact
    (exactSeedUnconditionalTriple_from_exactSeedAboveThresholdHyp).1

/-- Component extraction: positive exact-seed payload from class-level
exact-seed hypotheses. -/
theorem targetTowerExactSeedAbovePerronThreshold_from_exactSeedAboveThresholdHyp
    [TruncatedExplicitFormulaPiHyp]
    [TargetTowerExactSeedAbovePerronThresholdHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdHyp] :
    TargetTowerExactSeedAbovePerronThreshold := by
  exact
    (exactSeedUnconditionalTriple_from_exactSeedAboveThresholdHyp).2.1

/-- Component extraction: anti-target exact-seed payload from class-level
exact-seed hypotheses. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_from_exactSeedAboveThresholdHyp
    [TruncatedExplicitFormulaPiHyp]
    [TargetTowerExactSeedAbovePerronThresholdHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdHyp] :
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact
    (exactSeedUnconditionalTriple_from_exactSeedAboveThresholdHyp).2.2

end Aristotle.Standalone.RHPiUnconditionalExactSeedRootLifts
