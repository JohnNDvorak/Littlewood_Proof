import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiB5aRootLifts

open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries

/-- Lift the standalone general truncated explicit-formula class witness into the
bundled B5a root payload. -/
theorem rootPayload_of_general_hyp
    [ExplicitFormulaPsiGeneralHyp] :
    ExplicitFormulaPsiB5aRootPayload := by
  exact ⟨shifted_remainder_bound_of_general_hyp⟩

/-- Lift an explicit standalone general truncated explicit-formula theorem into the
bundled B5a root payload. -/
theorem rootPayload_of_general_formula
    (hGeneral :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ Aristotle.DirichletPhaseAlignment.ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) :
    ExplicitFormulaPsiB5aRootPayload := by
  exact ⟨shifted_remainder_bound_of_general_formula hGeneral⟩

/-- Lift the legacy Dirichlet-phase explicit-formula class witness into the bundled
B5a root payload. -/
theorem rootPayload_of_legacy_explicit_formula
    [Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp] :
    ExplicitFormulaPsiB5aRootPayload := by
  exact ⟨shifted_remainder_bound_of_legacy_explicit_formula⟩

/-- Recover the shifted-remainder endpoint from the bundled B5a root payload. -/
theorem shifted_remainder_bound_from_rootPayload
    [ExplicitFormulaPsiB5aRootPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_remainder_bound_of_rootPayload

/-- Recover the standalone general truncated explicit-formula class from the bundled
B5a root payload. -/
theorem explicitFormulaPsiGeneralHyp_from_rootPayload
    [ExplicitFormulaPsiB5aRootPayload] :
    ExplicitFormulaPsiGeneralHyp := by
  exact explicitFormulaPsiGeneralHyp_of_rootPayload

end Aristotle.Standalone.ExplicitFormulaPsiB5aRootLifts
