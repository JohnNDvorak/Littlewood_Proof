import Littlewood.Aristotle.Standalone.RHPiCoeffControlClassInstances
import Littlewood.Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiDeepCoeffControlWitnesses

open Aristotle.Standalone.RHPiWitnessFromExplicitFormula
open Aristotle.Standalone.RHPiCoeffControlClassInstances
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiPerronFromTruncatedPiBridge
open PiLiDirectOscillationBridge

/-!
Deep constructive closure targets for Blocker-7 coefficient-control payloads.

This file is intentionally conditional: it exposes B7a/B7b from the three deep
upstream payloads

* fixed-height Perron error control for `pi`
* positive/negative phase-above-Perron-threshold families
* positive exact-seed-above-threshold family
* negative exact-seed-above-threshold family

without introducing any new axioms.
-/

/-- Positive B7 coeff-control payload from phase-above-threshold classes. -/
theorem target_height_coeff_control_of_phaseAboveThresholdHyp
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.TargetTowerPhaseAbovePerronThresholdHyp] :
    RhPiTargetHeightCoeffControlHyp := by
  infer_instance

/-- Negative B7 coeff-control payload from phase-above-threshold classes. -/
theorem antitarget_height_coeff_control_of_phaseAboveThresholdHyp
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.AntiTargetTowerPhaseAbovePerronThresholdHyp] :
    RhPiAntiTargetHeightCoeffControlHyp := by
  infer_instance

/-- Bundled Blocker-7 pair from phase-above-threshold classes. -/
theorem coeffControlClasses_of_phaseAboveThresholdHyp
    [PerronSqrtErrorEventuallyAtHeightHyp]
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

/-- Positive B7 coeff-control payload from Perron-only exact-seed classes. -/
theorem target_height_coeff_control_of_exactSeedAboveThresholdPerronHyp
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [TargetTowerExactSeedAbovePerronThresholdPerronHyp] :
    RhPiTargetHeightCoeffControlHyp := by
  infer_instance

/-- Negative B7 coeff-control payload from Perron-only exact-seed classes. -/
theorem antitarget_height_coeff_control_of_exactSeedAboveThresholdPerronHyp
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp] :
    RhPiAntiTargetHeightCoeffControlHyp := by
  infer_instance

/-- Bundled Blocker-7 pair from Perron-only exact-seed classes. -/
theorem coeffControlClasses_of_exactSeedAboveThresholdPerronHyp
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [TargetTowerExactSeedAbovePerronThresholdPerronHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp] :
    RhPiTargetHeightCoeffControlHyp ∧ RhPiAntiTargetHeightCoeffControlHyp := by
  exact
    ⟨target_height_coeff_control_of_exactSeedAboveThresholdPerronHyp,
      antitarget_height_coeff_control_of_exactSeedAboveThresholdPerronHyp⟩

/-- Positive B7 coeff-control payload from explicit deep witness terms. -/
theorem target_height_coeff_control_of_exactSeedAboveThreshold
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget : @TargetTowerExactSeedAbovePerronThreshold hTruncated) :
    RhPiTargetHeightCoeffControlHyp := by
  letI : TruncatedExplicitFormulaPiHyp := hTruncated
  letI : TargetTowerExactSeedAbovePerronThresholdHyp := ⟨hTarget⟩
  exact target_height_coeff_control_of_exactSeedAboveThresholdHyp

/-- Negative B7 coeff-control payload from explicit deep witness terms. -/
theorem antitarget_height_coeff_control_of_exactSeedAboveThreshold
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hAntiTarget : @AntiTargetTowerExactSeedAbovePerronThreshold hTruncated) :
    RhPiAntiTargetHeightCoeffControlHyp := by
  letI : TruncatedExplicitFormulaPiHyp := hTruncated
  letI : AntiTargetTowerExactSeedAbovePerronThresholdHyp := ⟨hAntiTarget⟩
  exact antitarget_height_coeff_control_of_exactSeedAboveThresholdHyp

/-- Bundled Blocker-7 pair from explicit deep witness terms. -/
theorem coeffControlClasses_of_exactSeedAboveThreshold
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget : @TargetTowerExactSeedAbovePerronThreshold hTruncated)
    (hAntiTarget : @AntiTargetTowerExactSeedAbovePerronThreshold hTruncated) :
    RhPiTargetHeightCoeffControlHyp ∧ RhPiAntiTargetHeightCoeffControlHyp := by
  exact
    ⟨target_height_coeff_control_of_exactSeedAboveThreshold hTruncated hTarget,
      antitarget_height_coeff_control_of_exactSeedAboveThreshold hTruncated hAntiTarget⟩

/-- Positive B7 coeff-control payload from an explicit Perron-only exact-seed
term. -/
theorem target_height_coeff_control_of_exactSeedAboveThresholdPerron
    (hPerron : PerronSqrtErrorEventuallyAtHeightHyp)
    (hTarget : @TargetTowerExactSeedAbovePerronThresholdPerron hPerron) :
    RhPiTargetHeightCoeffControlHyp := by
  letI : PerronSqrtErrorEventuallyAtHeightHyp := hPerron
  letI : TargetTowerExactSeedAbovePerronThresholdPerronHyp := ⟨hTarget⟩
  exact target_height_coeff_control_of_exactSeedAboveThresholdPerronHyp

/-- Negative B7 coeff-control payload from an explicit Perron-only exact-seed
term. -/
theorem antitarget_height_coeff_control_of_exactSeedAboveThresholdPerron
    (hPerron : PerronSqrtErrorEventuallyAtHeightHyp)
    (hAntiTarget : @AntiTargetTowerExactSeedAbovePerronThresholdPerron hPerron) :
    RhPiAntiTargetHeightCoeffControlHyp := by
  letI : PerronSqrtErrorEventuallyAtHeightHyp := hPerron
  letI : AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp := ⟨hAntiTarget⟩
  exact antitarget_height_coeff_control_of_exactSeedAboveThresholdPerronHyp

/-- Bundled Blocker-7 pair from explicit Perron-only exact-seed terms. -/
theorem coeffControlClasses_of_exactSeedAboveThresholdPerron
    (hPerron : PerronSqrtErrorEventuallyAtHeightHyp)
    (hTarget : @TargetTowerExactSeedAbovePerronThresholdPerron hPerron)
    (hAntiTarget : @AntiTargetTowerExactSeedAbovePerronThresholdPerron hPerron) :
    RhPiTargetHeightCoeffControlHyp ∧ RhPiAntiTargetHeightCoeffControlHyp := by
  exact
    ⟨target_height_coeff_control_of_exactSeedAboveThresholdPerron hPerron hTarget,
      antitarget_height_coeff_control_of_exactSeedAboveThresholdPerron hPerron hAntiTarget⟩

/-- Positive B7 coeff-control payload from an explicit phase-above-threshold
deep witness term. -/
theorem target_height_coeff_control_of_phaseAboveThreshold
    (hPerron : PerronSqrtErrorEventuallyAtHeightHyp)
    (hTarget :
      @Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.TargetTowerPhaseAbovePerronThreshold
        hPerron) :
    RhPiTargetHeightCoeffControlHyp := by
  letI : PerronSqrtErrorEventuallyAtHeightHyp := hPerron
  letI :
      Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.TargetTowerPhaseAbovePerronThresholdHyp :=
    ⟨hTarget⟩
  exact target_height_coeff_control_of_phaseAboveThresholdHyp

/-- Negative B7 coeff-control payload from an explicit anti-phase-above-threshold
deep witness term. -/
theorem antitarget_height_coeff_control_of_phaseAboveThreshold
    (hPerron : PerronSqrtErrorEventuallyAtHeightHyp)
    (hAntiTarget :
      @Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.AntiTargetTowerPhaseAbovePerronThreshold
        hPerron) :
    RhPiAntiTargetHeightCoeffControlHyp := by
  letI : PerronSqrtErrorEventuallyAtHeightHyp := hPerron
  letI :
      Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.AntiTargetTowerPhaseAbovePerronThresholdHyp :=
    ⟨hAntiTarget⟩
  exact antitarget_height_coeff_control_of_phaseAboveThresholdHyp

/-- Bundled Blocker-7 pair from explicit phase-above-threshold deep witness
terms. -/
theorem coeffControlClasses_of_phaseAboveThreshold
    (hPerron : PerronSqrtErrorEventuallyAtHeightHyp)
    (hTarget :
      @Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.TargetTowerPhaseAbovePerronThreshold
        hPerron)
    (hAntiTarget :
      @Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold.AntiTargetTowerPhaseAbovePerronThreshold
        hPerron) :
    RhPiTargetHeightCoeffControlHyp ∧ RhPiAntiTargetHeightCoeffControlHyp := by
  exact
    ⟨target_height_coeff_control_of_phaseAboveThreshold hPerron hTarget,
      antitarget_height_coeff_control_of_phaseAboveThreshold hPerron hAntiTarget⟩

/-- Bundled B7 coefficient-control payload from the hard exact-seed boundary
classes. This is a conditional endpoint, not a provider for those classes. -/
theorem coeffControlClasses_of_exactSeedBoundaryHyp
    [TruncatedExplicitFormulaPiHyp]
    [TargetTowerExactSeedAbovePerronThresholdHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdHyp] :
    Aristotle.Standalone.RHPiWitnessFromExplicitFormula.RhPiTargetHeightCoeffControlHyp ∧
      Aristotle.Standalone.RHPiWitnessFromExplicitFormula.RhPiAntiTargetHeightCoeffControlHyp := by
  exact
    coeffControlClasses_of_exactSeedAboveThresholdHyp

/-- Bundled B7 coefficient-control payload from the Perron-only exact-seed
boundary classes. This is a conditional endpoint, not a provider for those
classes. -/
theorem coeffControlClasses_of_exactSeedBoundaryPerronHyp
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [TargetTowerExactSeedAbovePerronThresholdPerronHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp] :
    Aristotle.Standalone.RHPiWitnessFromExplicitFormula.RhPiTargetHeightCoeffControlHyp ∧
      Aristotle.Standalone.RHPiWitnessFromExplicitFormula.RhPiAntiTargetHeightCoeffControlHyp := by
  exact
    coeffControlClasses_of_exactSeedAboveThresholdPerronHyp

end Aristotle.Standalone.RHPiDeepCoeffControlWitnesses
