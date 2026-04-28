import Littlewood.Aristotle.Standalone.RHPiTargetPhaseArgReduction
import Littlewood.Aristotle.Standalone.RHPiArgApproxFromPerronThreshold
import Littlewood.Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiCorrectedCanonicalWitnessClasses

open Filter Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.RHPiPerronTruncatedWitness
open Aristotle.Standalone.RHPiPerronFromTruncatedPiBridge
open Aristotle.Standalone.RHPiPerronTowerWitness
open Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase
open Aristotle.Standalone.RHPiTargetPhaseArgReduction
open Aristotle.Standalone.RHPiArgApproxFromPerronThreshold
open Aristotle.Standalone.CombinedAtomsFromDeepBlockers

/--
Canonical RH-`pi` Perron witness family at baseline `sqrt/log` scale.

This is the corrected canonical interface for the finite-zero Perron payload.
-/
abbrev PerronSqrtErrorThresholdFamily_corrected : Prop :=
  PerronSqrtErrorThresholdFamily

/--
Canonical RH-`pi` positive phase-coupled tower family.
-/
abbrev TargetTowerPhaseCouplingFamily_corrected : Prop :=
  TargetTowerPhaseCouplingFamily

/--
Canonical RH-`pi` negative phase-coupled tower family.
-/
abbrev AntiTargetTowerPhaseCouplingFamily_corrected : Prop :=
  AntiTargetTowerPhaseCouplingFamily

/-- Corrected canonical typeclass for the Perron threshold family. -/
class PerronSqrtErrorThresholdFamilyHyp_corrected : Prop where
  witness : PerronSqrtErrorThresholdFamily_corrected

/-- Corrected canonical typeclass for the positive phase-coupled family. -/
class TargetTowerPhaseCouplingFamilyHyp_corrected : Prop where
  witness : TargetTowerPhaseCouplingFamily_corrected

/-- Corrected canonical typeclass for the negative phase-coupled family. -/
class AntiTargetTowerPhaseCouplingFamilyHyp_corrected : Prop where
  witness : AntiTargetTowerPhaseCouplingFamily_corrected

/-- Bridge: positive arg-approximation payload class yields corrected canonical
positive phase-coupling payload. -/
instance
    [TargetTowerArgApproxFamilyHyp] :
    TargetTowerPhaseCouplingFamilyHyp_corrected where
  witness :=
    targetTowerPhaseCouplingFamily_of_argApprox
      TargetTowerArgApproxFamilyHyp.witness

/-- Bridge: negative arg-approximation payload class yields corrected canonical
negative phase-coupling payload. -/
instance
    [AntiTargetTowerArgApproxFamilyHyp] :
    AntiTargetTowerPhaseCouplingFamilyHyp_corrected where
  witness :=
    antiTargetTowerPhaseCouplingFamily_of_argApprox
      AntiTargetTowerArgApproxFamilyHyp.witness

/-- Compatibility bridge: above-threshold positive arg-approximation payloads
plus fixed-height Perron error input instantiate the corrected canonical
positive phase-coupling payload. -/
instance
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [TargetTowerArgApproxAbovePerronThresholdHyp] :
    TargetTowerPhaseCouplingFamilyHyp_corrected where
  witness :=
    targetTowerPhaseCouplingFamily_of_argApprox
      TargetTowerArgApproxFamilyHyp.witness

/-- Compatibility bridge: above-threshold negative arg-approximation payloads
plus fixed-height Perron error input instantiate the corrected canonical
negative phase-coupling payload. -/
instance
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [AntiTargetTowerArgApproxAbovePerronThresholdHyp] :
    AntiTargetTowerPhaseCouplingFamilyHyp_corrected where
  witness :=
    antiTargetTowerPhaseCouplingFamily_of_argApprox
      AntiTargetTowerArgApproxFamilyHyp.witness

/-- Package explicit positive arg-approximation data as corrected canonical
positive phase-coupling payload. -/
theorem targetPhaseCouplingFamilyHyp_corrected_of_argApprox
    (hTarget : TargetTowerArgApproxFamily) :
    TargetTowerPhaseCouplingFamilyHyp_corrected := by
  exact ⟨targetTowerPhaseCouplingFamily_of_argApprox hTarget⟩

/-- Package explicit negative arg-approximation data as corrected canonical
negative phase-coupling payload. -/
theorem antiTargetPhaseCouplingFamilyHyp_corrected_of_argApprox
    (hAntiTarget : AntiTargetTowerArgApproxFamily) :
    AntiTargetTowerPhaseCouplingFamilyHyp_corrected := by
  exact ⟨antiTargetTowerPhaseCouplingFamily_of_argApprox hAntiTarget⟩

/-- Corrected canonical endpoint: once both corrected phase-coupling payload
classes are available, full RH-`pi` witness data follows. -/
theorem rhPiWitnessData_of_correctedHyp
    [TargetTowerPhaseCouplingFamilyHyp_corrected]
    [AntiTargetTowerPhaseCouplingFamilyHyp_corrected] :
    RhPiWitnessData := by
  exact rhPiWitnessData_of_perron_and_phase_payloads
    TargetTowerPhaseCouplingFamilyHyp_corrected.witness
    AntiTargetTowerPhaseCouplingFamilyHyp_corrected.witness

end Aristotle.Standalone.RHPiCorrectedCanonicalWitnessClasses
