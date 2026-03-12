import Mathlib
import Littlewood.Aristotle.StationaryPhaseDecomposition
import Littlewood.Bridge.HardyFirstMomentWiring

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.StationaryPhaseDecompositionLeaf

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

/-- Importable leaf theorem for the deep stationary-phase atom.

This re-exports the current sum-level bound from
`Aristotle.StationaryPhaseDecomposition`, under the existing
`HardyCosIntegralSqrtModeBoundHyp` assumption. -/
theorem hardy_cos_integral_weighted_sum_bound
    [HardyFirstMomentWiring.HardyCosIntegralSqrtModeBoundHyp] :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∑ n ∈ Finset.range (hardyN T),
          ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
            ∫ t in Ioc (hardyStart n) T,
              hardyCos n t|
        ≤ C * ((hardyN T : ℝ) + 1) := by
  exact StationaryPhaseDecomposition.hardy_cos_integral_weighted_sum_bound

end Aristotle.StationaryPhaseDecompositionLeaf
