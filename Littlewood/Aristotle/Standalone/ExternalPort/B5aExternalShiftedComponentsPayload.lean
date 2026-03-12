import Littlewood.Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourCompat
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.B5aExternalShiftedComponentsPayload

open Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourCompat
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra

/-- External payload class for exact B5a shifted-contour component data.
This is the direct component shape needed by
`shifted_contours_bound_of_components_port`. -/
class ExternalShiftedBoundComponentsPayload : Type where
  perronIntegralRe : ℝ → ℝ → ℝ
  contourRemainderRe : ℝ → ℝ → ℝ
  hPerronRaw :
    ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
        Cₚ * (Real.log x) ^ 2
  hResidue :
    ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T
  hContour :
    ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |contourRemainderRe x T| ≤
        Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)

/-- Promote external shifted components directly to the bundled B5a root payload. -/
instance (priority := 100)
    [ExternalShiftedBoundComponentsPayload] :
    ExplicitFormulaPsiB5aRootPayload where
  shiftedBound := by
    exact shifted_contours_bound_of_components_port
      ExternalShiftedBoundComponentsPayload.perronIntegralRe
      ExternalShiftedBoundComponentsPayload.contourRemainderRe
      ExternalShiftedBoundComponentsPayload.hPerronRaw
      ExternalShiftedBoundComponentsPayload.hResidue
      ExternalShiftedBoundComponentsPayload.hContour

/-- Endpoint theorem exported from the external shifted-component payload. -/
theorem shifted_remainder_bound_of_external_shifted_components_payload
    [ExternalShiftedBoundComponentsPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_remainder_bound_of_rootPayload

/-- Export the general truncated explicit-formula class from the same payload. -/
theorem explicitFormulaPsiGeneralHyp_of_external_shifted_components_payload
    [ExternalShiftedBoundComponentsPayload] :
    Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries.ExplicitFormulaPsiGeneralHyp := by
  exact explicitFormulaPsiGeneralHyp_of_rootPayload

end Aristotle.Standalone.ExternalPort.B5aExternalShiftedComponentsPayload
