import Littlewood.Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourRefactorBundle
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTPNT5StrongRefactor
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedRefactor
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadConcreteLane
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourToStrongPNTRefactor

open PiLiDirectOscillationBridge
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourRefactorBundle
open Aristotle.Standalone.ExternalPort.StrongPNTPNT5StrongRefactor
open Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedRefactor
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadAutoInstances
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadConcreteLane
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors

/-- Convert one refactored `PrimeNumberTheoremAndContour` payload into the
canonical `PNT5StrongRefactorBundle` used by the global StrongPNT wiring. -/
def toPNT5StrongRefactorBundle
    (hPayload : PrimeNumberTheoremAndContourRefactorPayload) :
    PNT5StrongRefactorBundle where
  perronIntegralRe := hPayload.perronIntegralRe
  contourRemainderRe := hPayload.contourRemainderRe
  SmoothedChebyshevPull1 := hPayload.perronPullLog
  SmoothedChebyshevPull2 := hPayload.residuePull
  ZetaBoxEval := hPayload.contourBoundLog
  SmoothedChebyshevClose :=
    legacy_linear_log_bound_of_refactored_payload hPayload

/-- Canonical B5a shifted bound from one refactored
`PrimeNumberTheoremAndContour` payload. -/
theorem shifted_remainder_bound_of_refactored_pnt_contour_payload
    (hPayload : PrimeNumberTheoremAndContourRefactorPayload) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_remainder_bound_of_refactored_pnt5 (toPNT5StrongRefactorBundle hPayload)

/-- Constructor endpoint: recover the legacy explicit-formula class from one
refactored `PrimeNumberTheoremAndContour` payload. -/
def explicitFormulaPsiHyp_of_refactored_pnt_contour_payload
    (hPayload : PrimeNumberTheoremAndContourRefactorPayload) :
    Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp := by
  exact explicitFormulaPsiHyp_of_refactored_pnt5 (toPNT5StrongRefactorBundle hPayload)

/-- Constructor endpoint: recover the B5a root payload class from one refactored
`PrimeNumberTheoremAndContour` payload. -/
theorem b5a_rootPayload_of_refactored_pnt_contour_payload
    (hPayload : PrimeNumberTheoremAndContourRefactorPayload) :
    ExplicitFormulaPsiB5aRootPayload := by
  exact b5a_rootPayload_of_refactored_pnt5 (toPNT5StrongRefactorBundle hPayload)

/-- Build one global StrongPNT payload from a refactored
`PrimeNumberTheoremAndContour` payload and a refactored RH-`pi` exact-seed
bundle. -/
def strongpnt_global_payload_of_refactored_pnt_contour_and_rhpi
    (hPayload : PrimeNumberTheoremAndContourRefactorPayload)
    (hRhPi : RHPiExactSeedRefactorBundle) :
    StrongPNTGlobalPayload :=
  strongpnt_global_payload_of_refactored_bundles
    (toPNT5StrongRefactorBundle hPayload)
    hRhPi

/-- Canonical B5a shifted bound and RH-`pi` exact-seed obligations from one
refactored `PrimeNumberTheoremAndContour` payload and one refactored RH-`pi`
exact-seed bundle. -/
theorem b5a_and_rhpi_endpoints_of_refactored_pnt_contour_and_rhpi
    (hPayload : PrimeNumberTheoremAndContourRefactorPayload)
    (hRhPi : RHPiExactSeedRefactorBundle) :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      (letI : TruncatedExplicitFormulaPiHyp := hRhPi.truncatedPiFormula
       TargetTowerExactSeedAbovePerronThreshold ∧
       AntiTargetTowerExactSeedAbovePerronThreshold) := by
  exact
    b5a_and_rhpi_endpoints_of_refactored_bundles
      (toPNT5StrongRefactorBundle hPayload)
      hRhPi

/-- Unified constructor-root bundle endpoint from one refactored
`PrimeNumberTheoremAndContour` payload and one refactored RH-`pi` exact-seed
bundle. -/
theorem root_constructor_bundle_of_refactored_pnt_contour_and_rhpi
    (hPayload : PrimeNumberTheoremAndContourRefactorPayload)
    (hRhPi : RHPiExactSeedRefactorBundle) :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  letI : StrongPNTGlobalPayload :=
    strongpnt_global_payload_of_refactored_pnt_contour_and_rhpi hPayload hRhPi
  exact root_constructor_bundle_of_strongpnt_global_payload

end Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourToStrongPNTRefactor
