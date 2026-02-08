import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Bridge.HardyChainHyp

/-!
Bridge plumbing for Hardy's first-moment hypothesis.

This module is sorry-free and does not add new axioms. It isolates the exact
remaining analytic obligations:

1. a `MainTerm` integral bound at scale `T^(1/2+ε)`
2. an `ErrorTerm` integral bound at scale `T^(1/2+ε)`

Once those are available, the final `HardyFirstMomentUpperHyp` statement follows
immediately from `HardyZFirstMoment.hardyZ_first_moment_bound_conditional_two_bounds`.
-/

noncomputable section

open Complex Real Set Filter MeasureTheory

namespace HardyFirstMomentWiring

/-- Missing main-term estimate in the Hardy first-moment chain. -/
class MainTermFirstMomentBoundHyp : Prop where
  bound : ∀ ε : ℝ, ε > 0 →
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, HardyEstimatesPartial.MainTerm t| ≤ C * T ^ (1 / 2 + ε)

/-- Missing error-term estimate in the Hardy first-moment chain. -/
class ErrorTermFirstMomentBoundHyp : Prop where
  bound : ∀ ε : ℝ, ε > 0 →
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, HardyEstimatesPartial.ErrorTerm t| ≤ C * T ^ (1 / 2 + ε)

/-- If the two remaining integral bounds are available, the Hardy first-moment hypothesis follows. -/
theorem hardyFirstMomentUpper_from_two_bounds
    [MainTermFirstMomentBoundHyp] [ErrorTermFirstMomentBoundHyp] :
    HardyFirstMomentUpperHyp := by
  refine ⟨?_⟩
  intro ε hε
  obtain ⟨C₁, hC₁, hMain⟩ := MainTermFirstMomentBoundHyp.bound ε hε
  obtain ⟨C₂, hC₂, hErr⟩ := ErrorTermFirstMomentBoundHyp.bound ε hε
  obtain ⟨C, hC, T₀, hT₀, hHardy⟩ :=
    HardyEstimatesPartial.hardyZ_first_moment_bound_conditional_two_bounds ε hε
      ⟨C₁, hC₁, hMain⟩ ⟨C₂, hC₂, hErr⟩
  refine ⟨C, hC, max 2 T₀, le_max_left _ _, ?_⟩
  intro T hT
  exact hHardy T (le_trans (le_max_right _ _) hT)

end HardyFirstMomentWiring
