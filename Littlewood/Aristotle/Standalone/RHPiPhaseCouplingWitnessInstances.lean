import Littlewood.Aristotle.Standalone.RHPiArgApproxFromPerronThreshold
import Littlewood.Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiPhaseCouplingWitnessInstances

open Complex ZetaZeros
open GrowthDomination
open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiPerronFromTruncatedPiBridge
open Aristotle.Standalone.RHPiTargetPhaseArgReduction
open Aristotle.Standalone.RHPiArgApproxFromPerronThreshold
open Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase

/-- Direct constructor for the positive phase-coupling payload class from an
explicit positive witness family. -/
theorem targetPhaseCouplingHyp_of_witness
    (hTarget : TargetTowerPhaseCouplingFamily) :
    TargetTowerPhaseCouplingFamilyHyp :=
  ⟨hTarget⟩

/-- Direct constructor for the negative phase-coupling payload class from an
explicit negative witness family. -/
theorem antiTargetPhaseCouplingHyp_of_witness
    (hAntiTarget : AntiTargetTowerPhaseCouplingFamily) :
    AntiTargetTowerPhaseCouplingFamilyHyp :=
  ⟨hAntiTarget⟩

/-- Package both phase-coupling payload classes at once from explicit witness
families. -/
theorem phaseCouplingHyps_of_witnesses
    (hTarget : TargetTowerPhaseCouplingFamily)
    (hAntiTarget : AntiTargetTowerPhaseCouplingFamily) :
    TargetTowerPhaseCouplingFamilyHyp ∧ AntiTargetTowerPhaseCouplingFamilyHyp := by
  exact ⟨targetPhaseCouplingHyp_of_witness hTarget,
    antiTargetPhaseCouplingHyp_of_witness hAntiTarget⟩

/-- Build the requested phase-coupling payload classes from explicit
arg-approximation witness families. -/
theorem phaseCouplingHyps_of_argApproxFamilies
    (hTargetArg : TargetTowerArgApproxFamily)
    (hAntiTargetArg : AntiTargetTowerArgApproxFamily) :
    TargetTowerPhaseCouplingFamilyHyp ∧ AntiTargetTowerPhaseCouplingFamilyHyp := by
  refine ⟨?_, ?_⟩
  · exact targetTowerPhaseCouplingFamilyHyp_of_argApprox hTargetArg
  · exact antiTargetTowerPhaseCouplingFamilyHyp_of_argApprox hAntiTargetArg

/-- Build the requested phase-coupling payload classes from above-threshold
arg-approximation witness families (with fixed-height Perron error available). -/
theorem phaseCouplingHyps_of_argAboveThresholdFamilies
    [PerronSqrtErrorEventuallyAtHeightHyp]
    (hTargetAbove : TargetTowerArgApproxAbovePerronThreshold)
    (hAntiTargetAbove : AntiTargetTowerArgApproxAbovePerronThreshold) :
    TargetTowerPhaseCouplingFamilyHyp ∧ AntiTargetTowerPhaseCouplingFamilyHyp := by
  refine phaseCouplingHyps_of_argApproxFamilies
    (targetTowerArgApproxFamily_of_above_threshold hTargetAbove)
    (antiTargetTowerArgApproxFamily_of_above_threshold hAntiTargetAbove)

/-- Positive direct instance from a `Fact` witness of the arg-approximation
family. -/
instance (priority := 100)
    [Fact TargetTowerArgApproxFamily] :
    TargetTowerPhaseCouplingFamilyHyp :=
  targetPhaseCouplingHyp_of_witness
    (targetTowerPhaseCouplingFamily_of_argApprox Fact.out)

/-- Negative direct instance from a `Fact` witness of the arg-approximation
family. -/
instance (priority := 100)
    [Fact AntiTargetTowerArgApproxFamily] :
    AntiTargetTowerPhaseCouplingFamilyHyp :=
  antiTargetPhaseCouplingHyp_of_witness
    (antiTargetTowerPhaseCouplingFamily_of_argApprox Fact.out)

/-- Positive direct instance from a `Fact` witness of the above-threshold
arg-approximation family. -/
instance (priority := 100)
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [Fact TargetTowerArgApproxAbovePerronThreshold] :
    TargetTowerPhaseCouplingFamilyHyp :=
  targetPhaseCouplingHyp_of_witness
    (targetTowerPhaseCouplingFamily_of_argApprox
      (targetTowerArgApproxFamily_of_above_threshold Fact.out))

/-- Negative direct instance from a `Fact` witness of the above-threshold
arg-approximation family. -/
instance (priority := 100)
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [Fact AntiTargetTowerArgApproxAbovePerronThreshold] :
    AntiTargetTowerPhaseCouplingFamilyHyp :=
  antiTargetPhaseCouplingHyp_of_witness
    (antiTargetTowerPhaseCouplingFamily_of_argApprox
      (antiTargetTowerArgApproxFamily_of_above_threshold Fact.out))

/-- Endpoint: explicit arg-approximation witness families give both requested
phase-coupling payload classes. -/
theorem requested_phaseCouplingPayloads_from_argApprox
    (hTargetArg : TargetTowerArgApproxFamily)
    (hAntiTargetArg : AntiTargetTowerArgApproxFamily) :
    TargetTowerPhaseCouplingFamily ∧ AntiTargetTowerPhaseCouplingFamily := by
  refine ⟨targetTowerPhaseCouplingFamily_of_argApprox hTargetArg,
    antiTargetTowerPhaseCouplingFamily_of_argApprox hAntiTargetArg⟩

end Aristotle.Standalone.RHPiPhaseCouplingWitnessInstances
