import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedRefactor
import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTRHPiRefactorProviderPayload

open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.ExternalPort.RHPiExternalTruncatedPiBuilder
open Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider
open Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedRefactor

/-- Field-level repackage from one `TruncatedExplicitFormulaPiHyp` term to the
external truncated witness bundle used by the RH-`pi` concrete provider lane. -/
def truncatedPiWitnessBundle_of_hyp
    (hTruncated : TruncatedExplicitFormulaPiHyp) :
    TruncatedPiWitnessBundle where
  piApprox := hTruncated.pi_approx
  zeroSumNegFrequently := hTruncated.zero_sum_neg_frequently

/-- Split concrete provider lane for RH-`pi`: one refactored exact-seed bundle
is enough to synthesize the consolidated RH-`pi` concrete provider payload. -/
class RHPiExactSeedRefactorProviderPayload : Type where
  rhpi : RHPiExactSeedRefactorBundle

/-- Auto-wire the consolidated RH-`pi` concrete provider payload from one
refactored exact-seed bundle. -/
instance (priority := 100)
    [RHPiExactSeedRefactorProviderPayload] :
    RHPiConcreteProviderPayload where
  truncatedBundle :=
    truncatedPiWitnessBundle_of_hyp
      RHPiExactSeedRefactorProviderPayload.rhpi.truncatedPiFormula
  targetSeed := by
    letI : TruncatedExplicitFormulaPiHyp :=
      RHPiExactSeedRefactorProviderPayload.rhpi.truncatedPiFormula
    simpa using RHPiExactSeedRefactorProviderPayload.rhpi.targetSeedAbovePerron
  antiTargetSeed := by
    letI : TruncatedExplicitFormulaPiHyp :=
      RHPiExactSeedRefactorProviderPayload.rhpi.truncatedPiFormula
    simpa using RHPiExactSeedRefactorProviderPayload.rhpi.antiTargetSeedAbovePerron

/-- Constructor endpoint for the bundled RH-`pi` root payload class from the
split refactored exact-seed provider class. -/
theorem rhpi_rootPayload_of_refactor_provider_payload
    [RHPiExactSeedRefactorProviderPayload] :
    RHPiUnconditionalExactSeedRootPayload := by
  exact rhpi_rootPayload_of_concrete_provider

/-- Canonical RH-`pi` exact-seed triple endpoint from the split refactored
exact-seed provider class. -/
theorem rhpi_exactSeedTriple_of_refactor_provider_payload
    [RHPiExactSeedRefactorProviderPayload] :
    TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact exactSeedUnconditionalTriple_of_concrete_provider

/-- Package one refactored RH-`pi` exact-seed bundle as a split RH-`pi`
provider payload term. -/
def rhpi_refactor_provider_payload_of_bundle
    (hRhPi : RHPiExactSeedRefactorBundle) :
    RHPiExactSeedRefactorProviderPayload where
  rhpi := hRhPi

end Aristotle.Standalone.ExternalPort.StrongPNTRHPiRefactorProviderPayload
