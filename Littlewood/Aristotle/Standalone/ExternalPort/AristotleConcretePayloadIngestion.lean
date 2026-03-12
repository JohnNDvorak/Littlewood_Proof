import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.AristotleConcretePayloadIngestion

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open PiLiDirectOscillationBridge
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors

/--
Concrete ingress payload that packages exactly the four witness terms needed to
synthesize all B5a/B7 constructor roots.
-/
class AristotleConcreteB5aB7Payload : Prop where
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

/-- Build the ingress payload from raw concrete witness terms. -/
def concretePayload_of_witnesses
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
    AristotleConcreteB5aB7Payload where
  legacyLinearLogWitness := hWitness
  truncatedPi := hTruncated
  targetSeed := by
    letI : TruncatedExplicitFormulaPiHyp := hTruncated
    simpa using hTarget
  antiTargetSeed := by
    letI : TruncatedExplicitFormulaPiHyp := hTruncated
    simpa using hAntiTarget

/-- Auto-wire the ingress payload into the existing global concrete constructor class. -/
instance (priority := 100)
    [AristotleConcreteB5aB7Payload] :
    StrongPNTConcreteGlobalWitnessPayload where
  legacyLinearLogWitness := AristotleConcreteB5aB7Payload.legacyLinearLogWitness
  truncatedPi := AristotleConcreteB5aB7Payload.truncatedPi
  targetSeed := by
    letI : TruncatedExplicitFormulaPiHyp := AristotleConcreteB5aB7Payload.truncatedPi
    simpa using AristotleConcreteB5aB7Payload.targetSeed
  antiTargetSeed := by
    letI : TruncatedExplicitFormulaPiHyp := AristotleConcreteB5aB7Payload.truncatedPi
    simpa using AristotleConcreteB5aB7Payload.antiTargetSeed

/-- Root constructor bundle endpoint from the ingress payload. -/
theorem root_constructor_bundle_of_aristotle_concrete_payload
    [AristotleConcreteB5aB7Payload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact root_constructor_bundle_of_concrete_global_witness_payload

/-- Canonical B5a+B7 endpoint bundle from the ingress payload. -/
theorem b5a_and_rhpi_endpoints_of_aristotle_concrete_payload
    [AristotleConcreteB5aB7Payload] :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact b5a_and_rhpi_endpoints_of_concrete_global_witness_payload

/-- B5a deep-leaf payload endpoint from the ingress payload. -/
theorem shifted_remainder_bound_of_aristotle_concrete_payload
    [AristotleConcreteB5aB7Payload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact (b5a_and_rhpi_endpoints_of_aristotle_concrete_payload).1

/-- RH-pi truncated explicit-formula endpoint from the ingress payload. -/
theorem truncatedExplicitFormulaPi_of_aristotle_concrete_payload
    [AristotleConcreteB5aB7Payload] :
    TruncatedExplicitFormulaPiHyp := by
  exact (b5a_and_rhpi_endpoints_of_aristotle_concrete_payload).2.1

/-- RH-pi target exact-seed endpoint from the ingress payload. -/
theorem targetTowerExactSeedAbovePerronThreshold_of_aristotle_concrete_payload
    [AristotleConcreteB5aB7Payload] :
    TargetTowerExactSeedAbovePerronThreshold := by
  exact (b5a_and_rhpi_endpoints_of_aristotle_concrete_payload).2.2.1

/-- RH-pi anti-target exact-seed endpoint from the ingress payload. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_of_aristotle_concrete_payload
    [AristotleConcreteB5aB7Payload] :
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact (b5a_and_rhpi_endpoints_of_aristotle_concrete_payload).2.2.2

end Aristotle.Standalone.ExternalPort.AristotleConcretePayloadIngestion
