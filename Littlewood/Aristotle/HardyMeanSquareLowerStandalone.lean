import Mathlib
import Littlewood.Aristotle.HardyMeanSquareAsymptoticLeaf

/-
Standalone Hardy mean-square lower bound in the exact shape needed by
`HardyInfiniteZerosV2.HardySetupV2.mean_square_lower`.

This file is intentionally not imported by `Littlewood.lean`.
-/

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.HardyMeanSquareLowerStandalone

open Complex Real Set Filter Topology MeasureTheory

/-- Exact `HardySetupV2.mean_square_lower` signature, obtained from the
standalone Hardy-Littlewood asymptotic hypothesis wrapper. -/
theorem hardy_mean_square_lower_for_setup_v2 :
    [Aristotle.HardyMeanSquareAsymptoticLeaf.HardyMeanSquareAsymptoticHyp] →
    ∃ c : ℝ, c > 0 ∧ ∃ T₀ : ℝ, T₀ ≥ 2 ∧ ∀ T : ℝ, T ≥ T₀ →
      c * T * Real.log T ≤ ∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t)^2 := by
  intro _h
  exact Aristotle.HardyMeanSquareAsymptoticLeaf.hardy_mean_square_lower_for_setup_v2

end Aristotle.HardyMeanSquareLowerStandalone
