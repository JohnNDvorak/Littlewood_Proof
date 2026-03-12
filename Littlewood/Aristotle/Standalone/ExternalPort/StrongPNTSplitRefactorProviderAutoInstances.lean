import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTPNT5RefactorProviderPayload
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRHPiRefactorProviderPayload
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTPNT5AndRHPiProviderAutoInstances

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTSplitRefactorProviderAutoInstances

open PiLiDirectOscillationBridge
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.ExternalPort.StrongPNTPNT5RefactorProviderPayload
open Aristotle.Standalone.ExternalPort.StrongPNTRHPiRefactorProviderPayload
open Aristotle.Standalone.ExternalPort.StrongPNTPNT5AndRHPiProviderAutoInstances

/-- Auto-fuse the split refactored B5a and RH-`pi` provider lanes into the
existing consolidated `PNT5`+RH-`pi` provider class. -/
instance (priority := 100)
    [PNT5StrongRefactorProviderPayload]
    [RHPiExactSeedRefactorProviderPayload] :
    PNT5AndRHPiRefactorProviderPayload where
  pnt5 := PNT5StrongRefactorProviderPayload.pnt5
  rhpi := RHPiExactSeedRefactorProviderPayload.rhpi

/-- Constructor-root bundle endpoint from the split refactored provider lanes. -/
theorem root_constructor_bundle_of_split_refactor_provider_payload
    [PNT5StrongRefactorProviderPayload]
    [RHPiExactSeedRefactorProviderPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact root_constructor_bundle_of_pnt5_and_rhpi_provider_payload

/-- Canonical B5a+RH-`pi` endpoint bundle from the split refactored provider
lanes. -/
theorem b5a_and_rhpi_endpoints_of_split_refactor_provider_payload
    [PNT5StrongRefactorProviderPayload]
    [RHPiExactSeedRefactorProviderPayload] :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact b5a_and_rhpi_endpoints_of_pnt5_and_rhpi_provider_payload

end Aristotle.Standalone.ExternalPort.StrongPNTSplitRefactorProviderAutoInstances
