import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTB5aComponentBundleCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedBundleCompat

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundlePayloadAutoInstances

open PiLiDirectOscillationBridge
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.ExternalPort.StrongPNTB5aComponentBundleCompat
open Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedBundleCompat
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors

/-- One bundled payload class carrying the two StrongPNT-style bundle terms
needed to synthesize the concrete global root-constructor payload. -/
class StrongPNTConcreteGlobalBundlePayload : Type where
  b5aBundle : StrongPNTB5aComponentBundle
  rhpiBundle : StrongPNTRHPiExactSeedBundle

/-- Auto-build the concrete global root-constructor payload from one bundled
StrongPNT-style pair. -/
instance (priority := 100)
    [StrongPNTConcreteGlobalBundlePayload] :
    StrongPNTConcreteGlobalWitnessPayload where
  legacyLinearLogWitness :=
    legacy_linear_log_bound_of_strongpnt_bundle
      StrongPNTConcreteGlobalBundlePayload.b5aBundle
  truncatedPi :=
    StrongPNTConcreteGlobalBundlePayload.rhpiBundle.truncatedPiFormula
  targetSeed := by
    letI : TruncatedExplicitFormulaPiHyp :=
      StrongPNTConcreteGlobalBundlePayload.rhpiBundle.truncatedPiFormula
    simpa using
      StrongPNTConcreteGlobalBundlePayload.rhpiBundle.targetSeedAbovePerron
  antiTargetSeed := by
    letI : TruncatedExplicitFormulaPiHyp :=
      StrongPNTConcreteGlobalBundlePayload.rhpiBundle.truncatedPiFormula
    simpa using
      StrongPNTConcreteGlobalBundlePayload.rhpiBundle.antiTargetSeedAbovePerron

/-- Root-constructor bundle endpoint from the bundled StrongPNT payload class. -/
theorem root_constructor_bundle_of_concrete_global_bundle_payload
    [StrongPNTConcreteGlobalBundlePayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact root_constructor_bundle_of_concrete_global_witness_payload

/-- Canonical B5a+RH-pi endpoint bundle from the bundled StrongPNT payload class. -/
theorem b5a_and_rhpi_endpoints_of_concrete_global_bundle_payload
    [StrongPNTConcreteGlobalBundlePayload] :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact b5a_and_rhpi_endpoints_of_concrete_global_witness_payload

/-- Package concrete StrongPNT-style bundle terms as a single global bundled
payload class term. -/
def concrete_global_bundle_payload_of_bundles
    (hB5a : StrongPNTB5aComponentBundle)
    (hRhPi : StrongPNTRHPiExactSeedBundle) :
    StrongPNTConcreteGlobalBundlePayload where
  b5aBundle := hB5a
  rhpiBundle := hRhPi

/-- One-shot endpoint bundle from concrete StrongPNT-style bundle terms. -/
theorem b5a_and_rhpi_endpoints_of_strongpnt_bundles
    (hB5a : StrongPNTB5aComponentBundle)
    (hRhPi : StrongPNTRHPiExactSeedBundle) :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      (letI : TruncatedExplicitFormulaPiHyp := hRhPi.truncatedPiFormula
       TargetTowerExactSeedAbovePerronThreshold ∧
       AntiTargetTowerExactSeedAbovePerronThreshold) := by
  letI : StrongPNTConcreteGlobalBundlePayload :=
    concrete_global_bundle_payload_of_bundles hB5a hRhPi
  refine ⟨(b5a_and_rhpi_endpoints_of_concrete_global_bundle_payload).1, ?_⟩
  refine ⟨hRhPi.truncatedPiFormula, ?_⟩
  letI : TruncatedExplicitFormulaPiHyp := hRhPi.truncatedPiFormula
  exact
    ⟨by simpa using hRhPi.targetSeedAbovePerron,
      by simpa using hRhPi.antiTargetSeedAbovePerron⟩

/-- One-shot root-constructor bundle from concrete StrongPNT-style bundle terms. -/
theorem root_constructor_bundle_of_strongpnt_bundles
    (hB5a : StrongPNTB5aComponentBundle)
    (hRhPi : StrongPNTRHPiExactSeedBundle) :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  letI : StrongPNTConcreteGlobalBundlePayload :=
    concrete_global_bundle_payload_of_bundles hB5a hRhPi
  exact root_constructor_bundle_of_concrete_global_bundle_payload

end Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundlePayloadAutoInstances
