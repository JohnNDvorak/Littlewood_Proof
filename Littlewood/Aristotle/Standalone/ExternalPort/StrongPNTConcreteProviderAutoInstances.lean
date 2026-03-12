import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalConcreteProvider
import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider
import Littlewood.Aristotle.Standalone.ExternalPort.ExternalRefactorProviderAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundlePayloadAutoInstances

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTConcreteProviderAutoInstances

open PiLiDirectOscillationBridge
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.ExternalPort.ExternalRefactorProviderAutoInstances
open Aristotle.Standalone.ExternalPort.B5aExternalConcreteProvider
open Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundlePayloadAutoInstances

/-- Auto-wire the consolidated B5a concrete provider payload from one concrete
global StrongPNT witness payload. -/
instance (priority := 100)
    [StrongPNTConcreteGlobalWitnessPayload] :
    B5aConcreteProviderPayload where
  witness := StrongPNTConcreteGlobalWitnessPayload.legacyLinearLogWitness

/-- Auto-wire the consolidated RH-`pi` concrete provider payload from one
concrete global StrongPNT witness payload. -/
instance (priority := 100)
    [StrongPNTConcreteGlobalWitnessPayload] :
    RHPiConcreteProviderPayload where
  truncatedBundle :=
    truncatedPiWitnessBundle_of_hyp
      StrongPNTConcreteGlobalWitnessPayload.truncatedPi
  targetSeed := by
    letI : TruncatedExplicitFormulaPiHyp :=
      StrongPNTConcreteGlobalWitnessPayload.truncatedPi
    simpa using StrongPNTConcreteGlobalWitnessPayload.targetSeed
  antiTargetSeed := by
    letI : TruncatedExplicitFormulaPiHyp :=
      StrongPNTConcreteGlobalWitnessPayload.truncatedPi
    simpa using StrongPNTConcreteGlobalWitnessPayload.antiTargetSeed

/-- Constructor-root bundle endpoint from one concrete global StrongPNT witness
payload class instance. -/
theorem root_constructor_bundle_of_strongpnt_concrete_witness_payload
    [StrongPNTConcreteGlobalWitnessPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  rcases b5a_constructor_bundle_of_concrete_provider with ⟨hPsi, hGeneral, _hRoot⟩
  exact ⟨hPsi, ⟨hGeneral, rhpi_rootPayload_of_concrete_provider⟩⟩

/-- Canonical B5a+RH-`pi` endpoint bundle from one concrete global StrongPNT
witness payload class instance. -/
theorem b5a_and_rhpi_endpoints_of_strongpnt_concrete_witness_payload
    [StrongPNTConcreteGlobalWitnessPayload] :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact
    ⟨shifted_remainder_bound_of_concrete_provider,
      truncatedExplicitFormulaPi_of_concrete_provider,
      targetTowerExactSeedAbovePerronThreshold_of_concrete_provider,
      antiTargetTowerExactSeedAbovePerronThreshold_of_concrete_provider⟩

/-- Constructor-root bundle endpoint from one bundled StrongPNT global payload
class instance. -/
theorem root_constructor_bundle_of_strongpnt_concrete_bundle_payload
    [StrongPNTConcreteGlobalBundlePayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact root_constructor_bundle_of_strongpnt_concrete_witness_payload

/-- Canonical B5a+RH-`pi` endpoint bundle from one bundled StrongPNT global
payload class instance. -/
theorem b5a_and_rhpi_endpoints_of_strongpnt_concrete_bundle_payload
    [StrongPNTConcreteGlobalBundlePayload] :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact b5a_and_rhpi_endpoints_of_strongpnt_concrete_witness_payload

end Aristotle.Standalone.ExternalPort.StrongPNTConcreteProviderAutoInstances
