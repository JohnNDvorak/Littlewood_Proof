import Littlewood.Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourRefactorBundle
import Littlewood.Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourToStrongPNTRefactor
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTPNT5StrongRefactor
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedRefactor
import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalConcreteProvider
import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundlePayloadAutoInstances

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.ExternalRefactorProviderAutoInstances

open PiLiDirectOscillationBridge
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourRefactorBundle
open Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourToStrongPNTRefactor
open Aristotle.Standalone.ExternalPort.StrongPNTPNT5StrongRefactor
open Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedRefactor
open Aristotle.Standalone.ExternalPort.RHPiExternalTruncatedPiBuilder
open Aristotle.Standalone.ExternalPort.B5aExternalConcreteProvider
open Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundlePayloadAutoInstances

/-- Repackage one `TruncatedExplicitFormulaPiHyp` term as the concrete
`TruncatedPiWitnessBundle` used by the external RH-`pi` provider lane. -/
def truncatedPiWitnessBundle_of_hyp
    (hTruncated : TruncatedExplicitFormulaPiHyp) :
    TruncatedPiWitnessBundle where
  piApprox := hTruncated.pi_approx
  zeroSumNegFrequently := hTruncated.zero_sum_neg_frequently

/-- Consolidated refactor-provider class: one refactored PNT/contour payload
plus one refactored RH-`pi` exact-seed bundle. -/
class RefactoredPNTContourAndRHPiProviderPayload : Type where
  pntContour : PrimeNumberTheoremAndContourRefactorPayload
  rhpi : RHPiExactSeedRefactorBundle

/-- Auto-wire the consolidated B5a concrete provider from the refactored
PNT/contour payload. -/
instance (priority := 100)
    [RefactoredPNTContourAndRHPiProviderPayload] :
    B5aConcreteProviderPayload where
  witness :=
    legacy_linear_log_bound_of_refactored_payload
      RefactoredPNTContourAndRHPiProviderPayload.pntContour

/-- Auto-wire the consolidated RH-`pi` concrete provider from the refactored
RH-`pi` exact-seed bundle. -/
instance (priority := 100)
    [RefactoredPNTContourAndRHPiProviderPayload] :
    RHPiConcreteProviderPayload where
  truncatedBundle :=
    truncatedPiWitnessBundle_of_hyp
      RefactoredPNTContourAndRHPiProviderPayload.rhpi.truncatedPiFormula
  targetSeed := by
    letI : TruncatedExplicitFormulaPiHyp :=
      RefactoredPNTContourAndRHPiProviderPayload.rhpi.truncatedPiFormula
    simpa using
      RefactoredPNTContourAndRHPiProviderPayload.rhpi.targetSeedAbovePerron
  antiTargetSeed := by
    letI : TruncatedExplicitFormulaPiHyp :=
      RefactoredPNTContourAndRHPiProviderPayload.rhpi.truncatedPiFormula
    simpa using
      RefactoredPNTContourAndRHPiProviderPayload.rhpi.antiTargetSeedAbovePerron

/-- Auto-wire the bundled StrongPNT global payload class from the consolidated
refactor-provider class. -/
instance (priority := 100)
    [RefactoredPNTContourAndRHPiProviderPayload] :
    StrongPNTConcreteGlobalBundlePayload where
  b5aBundle :=
    toComponentBundle
      (toPNT5StrongRefactorBundle
        RefactoredPNTContourAndRHPiProviderPayload.pntContour)
  rhpiBundle :=
    toStrongPNTBundle
      RefactoredPNTContourAndRHPiProviderPayload.rhpi

/-- Constructor-root bundle endpoint from the consolidated refactor-provider
class. -/
theorem root_constructor_bundle_of_refactored_provider_payload
    [RefactoredPNTContourAndRHPiProviderPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact root_constructor_bundle_of_concrete_global_bundle_payload

/-- Canonical B5a+RH-`pi` endpoint bundle from the consolidated
refactor-provider class. -/
theorem b5a_and_rhpi_endpoints_of_refactored_provider_payload
    [RefactoredPNTContourAndRHPiProviderPayload] :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact b5a_and_rhpi_endpoints_of_concrete_global_bundle_payload

end Aristotle.Standalone.ExternalPort.ExternalRefactorProviderAutoInstances
