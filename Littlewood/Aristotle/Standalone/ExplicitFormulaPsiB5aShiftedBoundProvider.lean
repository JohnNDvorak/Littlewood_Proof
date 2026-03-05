import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aRootLifts
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aContourBounds

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundProvider

open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootLifts
open Aristotle.Standalone.ExplicitFormulaPsiB5aContourBounds

/-- Root-payload endpoint for the B5a shifted-remainder bound. -/
theorem shifted_remainder_bound_provider_of_rootPayload
    [ExplicitFormulaPsiB5aRootPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) :=
  shifted_remainder_bound_of_rootPayload

/-- Register the bundled B5a root payload from the legacy Dirichlet-phase
explicit-formula class witness. -/
instance (priority := 100)
    [Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp] :
    ExplicitFormulaPsiB5aRootPayload :=
  rootPayload_of_legacy_explicit_formula

/-- Provider endpoint sourced from the legacy explicit-formula class bridge. -/
theorem shifted_remainder_bound_provider_of_legacy_explicit_formula
    [Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_remainder_bound_provider_of_rootPayload

/-- Same legacy provider endpoint rebuilt explicitly through the
Perron/residue/contour component combiners. -/
theorem shifted_remainder_bound_provider_of_legacy_components
    [Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  rcases shifted_contours_components_of_legacy_explicit_formula with
    ⟨perronIntegralRe, contourRemainderRe, hPerronRaw, hResidue, hContour⟩
  exact
    shifted_contours_bound_of_components
      perronIntegralRe contourRemainderRe hPerronRaw hResidue hContour

end Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundProvider
