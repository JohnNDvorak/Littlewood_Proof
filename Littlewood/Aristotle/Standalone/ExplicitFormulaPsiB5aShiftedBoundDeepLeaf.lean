/- 
Delegated deep leaf for B5a (shifted remainder bound).

This file carries the analytic Perron/residue/contour payload:
`|shiftedRemainderRe x T| ≤ C₂ * (sqrt/log + log^2)` uniformly for `x,T ≥ 2`.

The main-chain atomic theorem in `ExplicitFormulaPsiB5aShiftedBoundAtomic.lean`
is now a sorry-free wrapper that references this leaf theorem.
-/

import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aDefs
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf

open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries

/-- **Delegated B5a deep leaf**: truncated explicit-formula shifted remainder
bound with variable truncation height `T`. -/
theorem shifted_remainder_bound_leaf :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  sorry

/-- Candidate closure route for this deep leaf from the standalone
general truncated explicit-formula class. -/
theorem shifted_remainder_bound_candidate_of_general_hyp
    [ExplicitFormulaPsiGeneralHyp] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra.shifted_remainder_bound_of_general_hyp

/-- Candidate closure route from the legacy Dirichlet-phase explicit-formula
class used elsewhere in the project. -/
theorem shifted_remainder_bound_candidate_of_legacy_explicit_formula
    [Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact
    Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra.shifted_remainder_bound_of_legacy_explicit_formula

/-- Candidate closure route from an explicit (non-typeclass) general truncated
explicit-formula theorem. -/
theorem shifted_remainder_bound_candidate_of_general_formula
    (hGeneral :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ Aristotle.DirichletPhaseAlignment.ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact
    Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra.shifted_remainder_bound_of_general_formula
      hGeneral

/-- Candidate closure route from the bundled B5a root payload class. -/
theorem shifted_remainder_bound_candidate_of_rootPayload
    [Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra.ExplicitFormulaPsiB5aRootPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra.shifted_remainder_bound_of_rootPayload

end Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf
