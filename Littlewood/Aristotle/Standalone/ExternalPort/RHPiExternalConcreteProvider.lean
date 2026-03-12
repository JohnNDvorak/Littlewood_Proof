import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalTruncatedPiBuilder
import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalSplitExactSeedPayloads

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider

open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.ExternalPort.RHPiExternalTruncatedPiBuilder
open Aristotle.Standalone.ExternalPort.RHPiExternalSplitExactSeedPayloads

/-- Consolidated concrete provider class for RH-`pi` exact-seed integration.
This packages one truncated explicit-formula theorem bundle and both exact-seed
payload terms (target and anti-target). -/
class RHPiConcreteProviderPayload : Prop where
  truncatedBundle : TruncatedPiWitnessBundle
  targetSeed :
    letI : TruncatedExplicitFormulaPiHyp :=
      truncatedExplicitFormulaPiHyp_of_bundle truncatedBundle
    TargetTowerExactSeedAbovePerronThreshold
  antiTargetSeed :
    letI : TruncatedExplicitFormulaPiHyp :=
      truncatedExplicitFormulaPiHyp_of_bundle truncatedBundle
    AntiTargetTowerExactSeedAbovePerronThreshold

/-- Auto-wire the concrete truncated builder payload from the consolidated
RH-`pi` provider payload. -/
instance (priority := 100)
    [RHPiConcreteProviderPayload] :
    ExternalTruncatedPiWitnessPayload where
  bundle := RHPiConcreteProviderPayload.truncatedBundle

/-- Auto-wire the split target lane from the consolidated RH-`pi` provider
payload. -/
instance (priority := 95)
    [RHPiConcreteProviderPayload] :
    ExternalTargetExactSeedPayload where
  witness := by
    letI : TruncatedExplicitFormulaPiHyp :=
      truncatedExplicitFormulaPiHyp_of_bundle
        RHPiConcreteProviderPayload.truncatedBundle
    exact RHPiConcreteProviderPayload.targetSeed

/-- Auto-wire the split anti-target lane from the consolidated RH-`pi` provider
payload. -/
instance (priority := 95)
    [RHPiConcreteProviderPayload] :
    ExternalAntiTargetExactSeedPayload where
  witness := by
    letI : TruncatedExplicitFormulaPiHyp :=
      truncatedExplicitFormulaPiHyp_of_bundle
        RHPiConcreteProviderPayload.truncatedBundle
    exact RHPiConcreteProviderPayload.antiTargetSeed

/-- Root-payload endpoint from the consolidated RH-`pi` provider class. -/
theorem rhpi_rootPayload_of_concrete_provider
    [RHPiConcreteProviderPayload] :
    RHPiUnconditionalExactSeedRootPayload := by
  exact rhpi_rootPayload_of_external_split_payloads

/-- Exact-seed triple endpoint from the consolidated RH-`pi` provider class. -/
theorem exactSeedUnconditionalTriple_of_concrete_provider
    [RHPiConcreteProviderPayload] :
    TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact exactSeedUnconditionalTriple_of_external_split_payloads

/-- Component endpoint for the truncated explicit-formula payload from the
consolidated RH-`pi` provider class. -/
theorem truncatedExplicitFormulaPi_of_concrete_provider
    [RHPiConcreteProviderPayload] :
    TruncatedExplicitFormulaPiHyp := by
  exact truncatedExplicitFormulaPi_of_external_split_payloads

/-- Component endpoint for the target exact-seed payload from the consolidated
RH-`pi` provider class. -/
theorem targetTowerExactSeedAbovePerronThreshold_of_concrete_provider
    [RHPiConcreteProviderPayload] :
    TargetTowerExactSeedAbovePerronThreshold := by
  exact targetTowerExactSeedAbovePerronThreshold_of_external_split_payloads

/-- Component endpoint for the anti-target exact-seed payload from the
consolidated RH-`pi` provider class. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_of_concrete_provider
    [RHPiConcreteProviderPayload] :
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact antiTargetTowerExactSeedAbovePerronThreshold_of_external_split_payloads

/-- Constructor-bundle endpoint from the consolidated RH-`pi` provider class. -/
theorem rhpi_constructor_bundle_of_concrete_provider
    [RHPiConcreteProviderPayload] :
    ∃ _ : TruncatedExplicitFormulaPiHyp,
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  refine ⟨truncatedExplicitFormulaPi_of_concrete_provider, ?_⟩
  exact
    ⟨targetTowerExactSeedAbovePerronThreshold_of_concrete_provider,
      antiTargetTowerExactSeedAbovePerronThreshold_of_concrete_provider⟩

end Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider
