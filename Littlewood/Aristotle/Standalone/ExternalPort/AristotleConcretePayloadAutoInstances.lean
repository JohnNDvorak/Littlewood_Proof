import Littlewood.Aristotle.Standalone.ExternalPort.AristotleConcretePayloadIngestion
import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalConcreteProvider
import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalLegacyWitnessPayload
import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider
import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload
import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalTruncatedPiBuilder

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.AristotleConcretePayloadAutoInstances

open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.ExternalPort.B5aExternalLegacyWitnessPayload
open Aristotle.Standalone.ExternalPort.B5aExternalConcreteProvider
open Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload
open Aristotle.Standalone.ExternalPort.RHPiExternalTruncatedPiBuilder
open Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider
open Aristotle.Standalone.ExternalPort.AristotleConcretePayloadIngestion

/-- Repackage the truncated explicit-formula witness carried by the external
exact-seed payload into the field-level concrete bundle used by the RH-pi
concrete-provider lane. -/
def truncatedPiWitnessBundle_of_externalExactSeedPayload
    [ExternalExactSeedPayload] :
    TruncatedPiWitnessBundle where
  piApprox := ExternalExactSeedPayload.truncated.pi_approx
  zeroSumNegFrequently := ExternalExactSeedPayload.truncated.zero_sum_neg_frequently

/-- Auto-wire the consolidated B5a concrete provider from the external legacy
linear-log witness payload lane. -/
instance (priority := 95)
    [ExternalLegacyLinearLogWitnessPayload] :
    B5aConcreteProviderPayload where
  witness := ExternalLegacyLinearLogWitnessPayload.witness

/-- Auto-wire the consolidated RH-pi concrete provider from the external
exact-seed payload lane. -/
instance (priority := 95)
    [ExternalExactSeedPayload] :
    RHPiConcreteProviderPayload where
  truncatedBundle := truncatedPiWitnessBundle_of_externalExactSeedPayload
  targetSeed := by
    letI : TruncatedExplicitFormulaPiHyp :=
      truncatedExplicitFormulaPiHyp_of_bundle
        truncatedPiWitnessBundle_of_externalExactSeedPayload
    simpa using ExternalExactSeedPayload.target
  antiTargetSeed := by
    letI : TruncatedExplicitFormulaPiHyp :=
      truncatedExplicitFormulaPiHyp_of_bundle
        truncatedPiWitnessBundle_of_externalExactSeedPayload
    simpa using ExternalExactSeedPayload.antiTarget

/-- Fuse consolidated B5a and RH-pi concrete providers into the top ingress
payload class used by the B5a/B7 closure endpoints. -/
instance (priority := 90)
    [B5aConcreteProviderPayload]
    [RHPiConcreteProviderPayload] :
    AristotleConcreteB5aB7Payload where
  legacyLinearLogWitness := B5aConcreteProviderPayload.witness
  truncatedPi :=
    truncatedExplicitFormulaPiHyp_of_bundle
      RHPiConcreteProviderPayload.truncatedBundle
  targetSeed := by
    letI : TruncatedExplicitFormulaPiHyp :=
      truncatedExplicitFormulaPiHyp_of_bundle
        RHPiConcreteProviderPayload.truncatedBundle
    simpa using RHPiConcreteProviderPayload.targetSeed
  antiTargetSeed := by
    letI : TruncatedExplicitFormulaPiHyp :=
      truncatedExplicitFormulaPiHyp_of_bundle
        RHPiConcreteProviderPayload.truncatedBundle
    simpa using RHPiConcreteProviderPayload.antiTargetSeed

/-- Root-constructor bundle endpoint from the fused concrete-provider pair. -/
theorem root_constructor_bundle_of_provider_pair
    [B5aConcreteProviderPayload]
    [RHPiConcreteProviderPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries.ExplicitFormulaPsiGeneralHyp ∧
      Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra.RHPiUnconditionalExactSeedRootPayload := by
  exact root_constructor_bundle_of_aristotle_concrete_payload

/-- Canonical B5a+B7 endpoint bundle from the fused concrete-provider pair. -/
theorem b5a_and_rhpi_endpoints_of_provider_pair
    [B5aConcreteProviderPayload]
    [RHPiConcreteProviderPayload] :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.Standalone.ExplicitFormulaPsiSkeleton.shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact b5a_and_rhpi_endpoints_of_aristotle_concrete_payload

end Aristotle.Standalone.ExternalPort.AristotleConcretePayloadAutoInstances
