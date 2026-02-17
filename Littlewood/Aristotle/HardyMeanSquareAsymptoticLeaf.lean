import Mathlib
import Littlewood.Aristotle.HardyMeanSquareLeafFromAsymptotic

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.HardyMeanSquareAsymptoticLeaf

open Filter Asymptotics MeasureTheory Set

/-- Standalone hypothesis packaging for the Hardy-Littlewood mean-square asymptotic
used in `DeepSorries.combined_atoms` as the remaining mean-square asymptotic input. -/
class HardyMeanSquareAsymptoticHyp : Prop where
  bound :
    (fun T : ℝ =>
      (∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t)^2) - T * Real.log T)
      =O[atTop] (fun T : ℝ => T)

/-- Importable leaf theorem producing the exact
`HardySetupV2.mean_square_lower` field from the asymptotic hypothesis. -/
theorem hardy_mean_square_lower_for_setup_v2
    [HardyMeanSquareAsymptoticHyp] :
    ∃ c : ℝ, c > 0 ∧ ∃ T₀ : ℝ, T₀ ≥ 2 ∧ ∀ T : ℝ, T ≥ T₀ →
      c * T * Real.log T ≤ ∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t)^2 :=
  Aristotle.HardyMeanSquareLeafFromAsymptotic.hardy_mean_square_lower_of_asymptotic
    HardyMeanSquareAsymptoticHyp.bound

end Aristotle.HardyMeanSquareAsymptoticLeaf
