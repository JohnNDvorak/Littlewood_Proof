import Mathlib
import Littlewood.Bridge.HardyFirstMomentWiring

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.HardyFirstMomentUpperLeaf

open MeasureTheory Set

/-- Importable leaf theorem for the Hardy `first_moment_upper` atom.

This gives the exact field shape needed at
`DeepSorries.combined_atoms` line 229, assuming only the two bridge
hypotheses:
* `HardyFirstMomentWiring.MainTermFirstMomentBoundHyp`
* `HardyFirstMomentWiring.ErrorTermFirstMomentBoundHyp` -/
theorem hardy_first_moment_upper_for_setup_v2
    [HardyFirstMomentWiring.MainTermFirstMomentBoundHyp]
    [HardyFirstMomentWiring.ErrorTermFirstMomentBoundHyp] :
    ∀ ε : ℝ, ε > 0 →
      ∃ C : ℝ, C > 0 ∧ ∃ T₀ : ℝ, T₀ ≥ 2 ∧ ∀ T : ℝ, T ≥ T₀ →
        |∫ t in Ioc 1 T, HardyEstimatesPartial.hardyZ t| ≤ C * T ^ (1 / 2 + ε) := by
  let _ : HardyFirstMomentUpperHyp :=
    HardyFirstMomentWiring.hardyFirstMomentUpper_from_two_bounds
  simpa using HardyFirstMomentUpperHyp.bound

end Aristotle.HardyFirstMomentUpperLeaf

