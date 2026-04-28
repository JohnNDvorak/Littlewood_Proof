import Littlewood.Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt
import Littlewood.Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase
import Littlewood.Aristotle.Standalone.RHPiTargetPhaseArgReduction
import Littlewood.Aristotle.Standalone.RHPiArgApproxFromPerronThreshold
import Littlewood.Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
import Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge
import Littlewood.Aristotle.Standalone.RHPiCorrectedCanonicalWitnessClasses
import Littlewood.Aristotle.Standalone.RHPiCorrectedToLegacyPhaseCouplingBridge

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiCoeffControlClassInstances

open Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.RHPiWitnessFromExplicitFormula
open Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt
open Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase
open Aristotle.Standalone.RHPiPerronFromTruncatedPiBridge
open Aristotle.Standalone.RHPiTargetPhaseArgReduction
open Aristotle.Standalone.RHPiArgApproxFromPerronThreshold
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge
open Aristotle.Standalone.RHPiCorrectedCanonicalWitnessClasses

/-!
Concrete class-instance endpoints for the RH-`pi` Blocker-7 payload.

This file contains only deterministic instance-bridge proofs (no `sorry`, no
axioms). It exposes the two class instances:

* `RhPiTargetHeightCoeffControlHyp`
* `RhPiAntiTargetHeightCoeffControlHyp`

from progressively weaker upstream payload classes already present in the
standalone RH-`pi` chain.
-/

/-- Direct endpoint: phase-coupling payload classes imply the positive
coefficient-control class. -/
instance (priority := 100)
    [TargetTowerPhaseCouplingFamilyHyp] :
    RhPiTargetHeightCoeffControlHyp := by
  infer_instance

/-- Direct endpoint: phase-coupling payload classes imply the negative
coefficient-control class. -/
instance (priority := 100)
    [AntiTargetTowerPhaseCouplingFamilyHyp] :
    RhPiAntiTargetHeightCoeffControlHyp := by
  infer_instance

/-- Endpoint from argument-approximation payload classes to both requested
coefficient-control classes. -/
theorem coeffControlClasses_of_argApproxHyp
    [TargetTowerArgApproxFamilyHyp]
    [AntiTargetTowerArgApproxFamilyHyp] :
    RhPiTargetHeightCoeffControlHyp ∧ RhPiAntiTargetHeightCoeffControlHyp := by
  exact ⟨inferInstance, inferInstance⟩

/-- Endpoint from above-threshold argument-approximation payload classes to
both requested coefficient-control classes. -/
theorem coeffControlClasses_of_argApproxAboveThresholdHyp
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [TargetTowerArgApproxAbovePerronThresholdHyp]
    [AntiTargetTowerArgApproxAbovePerronThresholdHyp] :
    RhPiTargetHeightCoeffControlHyp ∧ RhPiAntiTargetHeightCoeffControlHyp := by
  exact ⟨inferInstance, inferInstance⟩

/-- Direct instance endpoint: exact-seed-above-threshold payload class implies
the positive coeff-control class. -/
instance (priority := 100)
    [PiLiDirectOscillationBridge.TruncatedExplicitFormulaPiHyp]
    [TargetTowerExactSeedAbovePerronThresholdHyp] :
    RhPiTargetHeightCoeffControlHyp where
  witness :=
    target_height_coeff_control_of_target_tower_sqrt
      (positive_target_tower_sqrt_witness_of_perron_and_phase
        (targetTowerPhaseCouplingFamily_of_argApprox
          (targetTowerArgApproxFamily_of_above_threshold
            (target_argAboveThreshold_of_exactSeedFamily
              TargetTowerExactSeedAbovePerronThresholdHyp.witness))))

/-- Direct instance endpoint: exact-seed-above-threshold payload class implies
the negative coeff-control class. -/
instance (priority := 100)
    [PiLiDirectOscillationBridge.TruncatedExplicitFormulaPiHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdHyp] :
    RhPiAntiTargetHeightCoeffControlHyp where
  witness :=
    antitarget_height_coeff_control_of_target_tower_sqrt
      (antitarget_tower_sqrt_witness_of_perron_and_phase
        (antiTargetTowerPhaseCouplingFamily_of_argApprox
          (antiTargetTowerArgApproxFamily_of_above_threshold
            (antiTarget_argAboveThreshold_of_exactSeedFamily
              AntiTargetTowerExactSeedAbovePerronThresholdHyp.witness))))

/-- Endpoint from exact-seed-above-threshold payload classes to both requested
coefficient-control classes. -/
theorem coeffControlClasses_of_exactSeedAboveThresholdHyp
    [PiLiDirectOscillationBridge.TruncatedExplicitFormulaPiHyp]
    [TargetTowerExactSeedAbovePerronThresholdHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdHyp] :
    RhPiTargetHeightCoeffControlHyp ∧ RhPiAntiTargetHeightCoeffControlHyp := by
  exact ⟨inferInstance, inferInstance⟩

/-- Endpoint from Perron-only exact-seed-above-threshold payload classes to both
requested coefficient-control classes. -/
theorem coeffControlClasses_of_exactSeedAboveThresholdPerronHyp
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [TargetTowerExactSeedAbovePerronThresholdPerronHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp] :
    RhPiTargetHeightCoeffControlHyp ∧ RhPiAntiTargetHeightCoeffControlHyp := by
  exact ⟨inferInstance, inferInstance⟩

/-- Endpoint from corrected canonical phase-coupling classes to both requested
coefficient-control classes. -/
theorem coeffControlClasses_of_correctedPhaseCouplingHyp
    [TargetTowerPhaseCouplingFamilyHyp_corrected]
    [AntiTargetTowerPhaseCouplingFamilyHyp_corrected] :
    RhPiTargetHeightCoeffControlHyp ∧ RhPiAntiTargetHeightCoeffControlHyp := by
  exact ⟨inferInstance, inferInstance⟩

end Aristotle.Standalone.RHPiCoeffControlClassInstances
