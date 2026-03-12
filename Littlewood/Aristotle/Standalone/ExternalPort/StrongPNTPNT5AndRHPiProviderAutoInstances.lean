import Littlewood.Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourRefactorBundle
import Littlewood.Aristotle.Standalone.ExternalPort.ExternalRefactorProviderAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTPNT5StrongRefactor
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedRefactor
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTB5aComponentBundleCompat
import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalLegacyComponentsPayload
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundlePayloadAutoInstances

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTPNT5AndRHPiProviderAutoInstances

open PiLiDirectOscillationBridge
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourRefactorBundle
open Aristotle.Standalone.ExternalPort.StrongPNTPNT5StrongRefactor
open Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedRefactor
open Aristotle.Standalone.ExternalPort.StrongPNTB5aComponentBundleCompat
open Aristotle.Standalone.ExternalPort.B5aExternalLegacyComponentsPayload
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundlePayloadAutoInstances
open Aristotle.Standalone.ExternalPort.ExternalRefactorProviderAutoInstances

/-- Convert one `PNT5StrongRefactorBundle` directly into the
`PrimeNumberTheoremAndContourRefactorPayload` used by the consolidated
refactor-provider lane. -/
def pntContourRefactorPayload_of_pnt5Refactor
    (hPNT5 : PNT5StrongRefactorBundle) :
    PrimeNumberTheoremAndContourRefactorPayload := by
  letI : ExternalLegacyLinearLogComponentsPayload :=
    externalLegacyComponentsPayload_of_strongpnt_bundle
      (toComponentBundle hPNT5)
  exact of_external_legacy_components_payload

/-- Consolidated provider class for the external integration route where B5a is
given in `PNT5_Strong`-style refactor form and RH-`pi` is given in refactored
exact-seed bundle form. -/
class PNT5AndRHPiRefactorProviderPayload : Type where
  pnt5 : PNT5StrongRefactorBundle
  rhpi : RHPiExactSeedRefactorBundle

/-- Auto-wire the bundled StrongPNT global payload class from the consolidated
`PNT5`+RH-`pi` refactor-provider class. -/
instance (priority := 100)
    [PNT5AndRHPiRefactorProviderPayload] :
    StrongPNTConcreteGlobalBundlePayload where
  b5aBundle :=
    toComponentBundle PNT5AndRHPiRefactorProviderPayload.pnt5
  rhpiBundle :=
    toStrongPNTBundle PNT5AndRHPiRefactorProviderPayload.rhpi

/-- Auto-wire the consolidated refactor-provider class from one
`PNT5`+RH-`pi` refactor-provider class instance. -/
instance (priority := 100)
    [PNT5AndRHPiRefactorProviderPayload] :
    RefactoredPNTContourAndRHPiProviderPayload where
  pntContour :=
    pntContourRefactorPayload_of_pnt5Refactor
      PNT5AndRHPiRefactorProviderPayload.pnt5
  rhpi :=
    PNT5AndRHPiRefactorProviderPayload.rhpi

/-- Constructor-root bundle endpoint from one consolidated
`PNT5`+RH-`pi` refactor-provider class instance. -/
theorem root_constructor_bundle_of_pnt5_and_rhpi_provider_payload
    [PNT5AndRHPiRefactorProviderPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact root_constructor_bundle_of_refactored_provider_payload

/-- Canonical B5a+RH-`pi` endpoint bundle from one consolidated
`PNT5`+RH-`pi` refactor-provider class instance. -/
theorem b5a_and_rhpi_endpoints_of_pnt5_and_rhpi_provider_payload
    [PNT5AndRHPiRefactorProviderPayload] :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact b5a_and_rhpi_endpoints_of_refactored_provider_payload

end Aristotle.Standalone.ExternalPort.StrongPNTPNT5AndRHPiProviderAutoInstances
