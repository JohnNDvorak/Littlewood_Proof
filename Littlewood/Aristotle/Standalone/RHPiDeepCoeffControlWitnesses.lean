import Littlewood.Aristotle.Standalone.RHPiCoeffControlClassInstances
import Littlewood.Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold
import Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedExistence

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiDeepCoeffControlWitnesses

open Aristotle.Standalone.RHPiWitnessFromExplicitFormula
open Aristotle.Standalone.RHPiCoeffControlClassInstances
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open PiLiDirectOscillationBridge

/-!
Deep constructive closure targets for Blocker-7 coefficient-control payloads.

This file is intentionally conditional: it exposes B7a/B7b from the three deep
upstream payloads

* truncated explicit formula for `pi`
* positive/negative phase-above-Perron-threshold families
* positive exact-seed-above-threshold family
* negative exact-seed-above-threshold family

without introducing any new axioms.
-/

/-- Positive B7 coeff-control payload from phase-above-threshold classes. -/
theorem target_height_coeff_control_of_phaseAboveThresholdHyp
    [TruncatedExplicitFormulaPiHyp]
    [Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.TargetTowerPhaseAbovePerronThresholdHyp] :
    RhPiTargetHeightCoeffControlHyp := by
  infer_instance

/-- Negative B7 coeff-control payload from phase-above-threshold classes. -/
theorem antitarget_height_coeff_control_of_phaseAboveThresholdHyp
    [TruncatedExplicitFormulaPiHyp]
    [Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.AntiTargetTowerPhaseAbovePerronThresholdHyp] :
    RhPiAntiTargetHeightCoeffControlHyp := by
  infer_instance

/-- Bundled Blocker-7 pair from phase-above-threshold classes. -/
theorem coeffControlClasses_of_phaseAboveThresholdHyp
    [TruncatedExplicitFormulaPiHyp]
    [Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.TargetTowerPhaseAbovePerronThresholdHyp]
    [Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.AntiTargetTowerPhaseAbovePerronThresholdHyp] :
    RhPiTargetHeightCoeffControlHyp ∧ RhPiAntiTargetHeightCoeffControlHyp := by
  exact
    ⟨target_height_coeff_control_of_phaseAboveThresholdHyp,
      antitarget_height_coeff_control_of_phaseAboveThresholdHyp⟩

/-- Positive B7 coeff-control payload from exact-seed-above-threshold classes. -/
theorem target_height_coeff_control_of_exactSeedAboveThresholdHyp
    [TruncatedExplicitFormulaPiHyp]
    [TargetTowerExactSeedAbovePerronThresholdHyp] :
    RhPiTargetHeightCoeffControlHyp := by
  infer_instance

/-- Negative B7 coeff-control payload from exact-seed-above-threshold classes. -/
theorem antitarget_height_coeff_control_of_exactSeedAboveThresholdHyp
    [TruncatedExplicitFormulaPiHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdHyp] :
    RhPiAntiTargetHeightCoeffControlHyp := by
  infer_instance

/-- Bundled Blocker-7 pair from exact-seed-above-threshold classes. -/
theorem coeffControlClasses_of_exactSeedAboveThresholdHyp
    [TruncatedExplicitFormulaPiHyp]
    [TargetTowerExactSeedAbovePerronThresholdHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdHyp] :
    RhPiTargetHeightCoeffControlHyp ∧ RhPiAntiTargetHeightCoeffControlHyp := by
  exact
    ⟨target_height_coeff_control_of_exactSeedAboveThresholdHyp,
      antitarget_height_coeff_control_of_exactSeedAboveThresholdHyp⟩

/-- Positive B7 coeff-control payload from explicit deep witness terms. -/
theorem target_height_coeff_control_of_exactSeedAboveThreshold
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget : TargetTowerExactSeedAbovePerronThreshold) :
    RhPiTargetHeightCoeffControlHyp := by
  letI : TruncatedExplicitFormulaPiHyp := hTruncated
  letI : TargetTowerExactSeedAbovePerronThresholdHyp := ⟨hTarget⟩
  exact target_height_coeff_control_of_exactSeedAboveThresholdHyp

/-- Negative B7 coeff-control payload from explicit deep witness terms. -/
theorem antitarget_height_coeff_control_of_exactSeedAboveThreshold
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hAntiTarget : AntiTargetTowerExactSeedAbovePerronThreshold) :
    RhPiAntiTargetHeightCoeffControlHyp := by
  letI : TruncatedExplicitFormulaPiHyp := hTruncated
  letI : AntiTargetTowerExactSeedAbovePerronThresholdHyp := ⟨hAntiTarget⟩
  exact antitarget_height_coeff_control_of_exactSeedAboveThresholdHyp

/-- Bundled Blocker-7 pair from explicit deep witness terms. -/
theorem coeffControlClasses_of_exactSeedAboveThreshold
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget : TargetTowerExactSeedAbovePerronThreshold)
    (hAntiTarget : AntiTargetTowerExactSeedAbovePerronThreshold) :
    RhPiTargetHeightCoeffControlHyp ∧ RhPiAntiTargetHeightCoeffControlHyp := by
  exact
    ⟨target_height_coeff_control_of_exactSeedAboveThreshold hTruncated hTarget,
      antitarget_height_coeff_control_of_exactSeedAboveThreshold hTruncated hAntiTarget⟩

/-- Positive B7 coeff-control payload from an explicit phase-above-threshold
deep witness term. -/
theorem target_height_coeff_control_of_phaseAboveThreshold
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget :
      Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.TargetTowerPhaseAbovePerronThreshold) :
    RhPiTargetHeightCoeffControlHyp := by
  letI : TruncatedExplicitFormulaPiHyp := hTruncated
  letI :
      Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.TargetTowerPhaseAbovePerronThresholdHyp :=
    ⟨hTarget⟩
  exact target_height_coeff_control_of_phaseAboveThresholdHyp

/-- Negative B7 coeff-control payload from an explicit anti-phase-above-threshold
deep witness term. -/
theorem antitarget_height_coeff_control_of_phaseAboveThreshold
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hAntiTarget :
      Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.AntiTargetTowerPhaseAbovePerronThreshold) :
    RhPiAntiTargetHeightCoeffControlHyp := by
  letI : TruncatedExplicitFormulaPiHyp := hTruncated
  letI :
      Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.AntiTargetTowerPhaseAbovePerronThresholdHyp :=
    ⟨hAntiTarget⟩
  exact antitarget_height_coeff_control_of_phaseAboveThresholdHyp

/-- Bundled Blocker-7 pair from explicit phase-above-threshold deep witness
terms. -/
theorem coeffControlClasses_of_phaseAboveThreshold
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget :
      Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.TargetTowerPhaseAbovePerronThreshold)
    (hAntiTarget :
      Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.AntiTargetTowerPhaseAbovePerronThreshold) :
    RhPiTargetHeightCoeffControlHyp ∧ RhPiAntiTargetHeightCoeffControlHyp := by
  exact
    ⟨target_height_coeff_control_of_phaseAboveThreshold hTruncated hTarget,
      antitarget_height_coeff_control_of_phaseAboveThreshold hTruncated hAntiTarget⟩

/-- Unconditional bundled B7 coefficient-control payload from the hard exact-seed
boundary assumptions. -/
theorem coeffControlClasses_unconditional :
    Aristotle.Standalone.RHPiWitnessFromExplicitFormula.RhPiTargetHeightCoeffControlHyp ∧
      Aristotle.Standalone.RHPiWitnessFromExplicitFormula.RhPiAntiTargetHeightCoeffControlHyp := by
  letI : TruncatedExplicitFormulaPiHyp :=
    RHPiUnconditionalExactSeedExistence.truncatedExplicitFormulaPi_unconditional
  letI : TargetTowerExactSeedAbovePerronThresholdHyp :=
    ⟨RHPiUnconditionalExactSeedExistence.targetTowerExactSeedAbovePerronThreshold_unconditional⟩
  letI : AntiTargetTowerExactSeedAbovePerronThresholdHyp :=
    ⟨RHPiUnconditionalExactSeedExistence.antiTargetTowerExactSeedAbovePerronThreshold_unconditional⟩
  exact
    coeffControlClasses_of_exactSeedAboveThresholdHyp

end Aristotle.Standalone.RHPiDeepCoeffControlWitnesses
