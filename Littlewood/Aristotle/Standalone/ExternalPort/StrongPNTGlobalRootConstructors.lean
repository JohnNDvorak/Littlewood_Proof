import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadConcreteLane
import Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open PiLiDirectOscillationBridge
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadAutoInstances
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadConcreteLane

/-- Unified concrete payload class carrying both constructor roots needed by the
B5a and RH-pi endpoint files.

A single instance of this class is enough to auto-synthesize:
* `Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp`
* `ExplicitFormulaPsiGeneralHyp`
* `RHPiUnconditionalExactSeedRootPayload`
through the existing StrongPNT global payload wiring.
-/
class StrongPNTConcreteGlobalWitnessPayload : Prop where
  legacyLinearLogWitness :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)
  truncatedPi : TruncatedExplicitFormulaPiHyp
  targetSeed :
    letI : TruncatedExplicitFormulaPiHyp := truncatedPi
    TargetTowerExactSeedAbovePerronThreshold
  antiTargetSeed :
    letI : TruncatedExplicitFormulaPiHyp := truncatedPi
    AntiTargetTowerExactSeedAbovePerronThreshold

/-- Build the global StrongPNT payload from one concrete constructor payload
instance. -/
instance (priority := 100)
    [StrongPNTConcreteGlobalWitnessPayload] :
    StrongPNTGlobalPayload where
  b5aLegacyWitness :=
    strongpnt_legacy_bundle_of_witness
      StrongPNTConcreteGlobalWitnessPayload.legacyLinearLogWitness
  rhpiExactSeed :=
    strongpnt_exactSeed_bundle_of_witness
      StrongPNTConcreteGlobalWitnessPayload.truncatedPi
      StrongPNTConcreteGlobalWitnessPayload.targetSeed
      StrongPNTConcreteGlobalWitnessPayload.antiTargetSeed

/-- Root-constructor endpoint for the legacy explicit-formula class. -/
def explicitFormulaPsiHyp_of_strongpnt_global_payload
    [StrongPNTGlobalPayload] :
    Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp := by
  infer_instance

/-- Root-constructor endpoint for the standalone general explicit-formula class. -/
theorem explicitFormulaPsiGeneralHyp_of_strongpnt_global_payload
    [StrongPNTGlobalPayload] :
    ExplicitFormulaPsiGeneralHyp := by
  infer_instance

/-- Root-constructor endpoint for the bundled RH-pi exact-seed payload class. -/
theorem rhpi_rootPayload_of_strongpnt_global_payload
    [StrongPNTGlobalPayload] :
    RHPiUnconditionalExactSeedRootPayload := by
  infer_instance

/-- One-shot constructor bundle endpoint from a global StrongPNT payload instance. -/
theorem root_constructor_bundle_of_strongpnt_global_payload
    [StrongPNTGlobalPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  refine ⟨explicitFormulaPsiHyp_of_strongpnt_global_payload, ?_⟩
  exact ⟨inferInstance, inferInstance⟩

/-- One-shot constructor bundle endpoint from the concrete global witness
payload class. -/
theorem root_constructor_bundle_of_concrete_global_witness_payload
    [StrongPNTConcreteGlobalWitnessPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact root_constructor_bundle_of_strongpnt_global_payload

/-- Endpoint bundle from the concrete global witness payload class to the
canonical B5a shifted-remainder bound and RH-pi exact-seed triple. -/
theorem b5a_and_rhpi_endpoints_of_concrete_global_witness_payload
    [StrongPNTConcreteGlobalWitnessPayload] :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  refine ⟨shifted_remainder_bound_of_strongpnt_global_payload, ?_⟩
  exact
    ⟨truncatedExplicitFormulaPi_of_strongpnt_global_payload,
      targetTowerExactSeedAbovePerronThreshold_of_strongpnt_global_payload,
      antiTargetTowerExactSeedAbovePerronThreshold_of_strongpnt_global_payload⟩

/-- Concrete term constructor for `StrongPNTConcreteGlobalWitnessPayload` from
one linear-log witness theorem and one RH-pi exact-seed witness triple. -/
def concrete_global_witness_payload_of_witnesses
    (hWitness :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x))
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      TargetTowerExactSeedAbovePerronThreshold)
    (hAntiTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      AntiTargetTowerExactSeedAbovePerronThreshold) :
    StrongPNTConcreteGlobalWitnessPayload where
  legacyLinearLogWitness := hWitness
  truncatedPi := hTruncated
  targetSeed := by
    letI : TruncatedExplicitFormulaPiHyp := hTruncated
    simpa using hTarget
  antiTargetSeed := by
    letI : TruncatedExplicitFormulaPiHyp := hTruncated
    simpa using hAntiTarget

end Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors
