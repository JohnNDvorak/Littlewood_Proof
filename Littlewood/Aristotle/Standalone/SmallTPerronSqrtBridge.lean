import Littlewood.Aristotle.Standalone.SmallTContourInfra
import Littlewood.Development.HadamardProductZeta

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.SmallTPerronSqrtBridge

open SmallTContourInfra

/-- Focused small-`T` leaf for the Perron contour lane.

On the bounded height range `2 ≤ T ≤ 16`, the standard error shape
`√x * (log T)^2 / √T` is uniformly comparable to `√x`. A direct finite-height
Perron contour proof can therefore be exposed at the simpler `O(√x)` scale and
then lifted to the existing public `SmallTPerronBoundHyp` surface by finite-range
absorption. -/
class SmallTPerronSqrtBoundHyp : Prop where
  bound :
    ∃ M > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Littlewood.Development.ShiftedRemainderInterface.shiftedRemainderRe x T| ≤
        M * Real.sqrt x

/-- Lift the focused bounded-height `O(√x)` Perron leaf to the existing
small-`T` general-formula surface. -/
theorem smallTPerron_general_bound_of_sqrt
    [SmallTPerronSqrtBoundHyp] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Littlewood.Development.ShiftedRemainderInterface.shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  obtain ⟨M, hM, hBound⟩ := SmallTPerronSqrtBoundHyp.bound
  refine ⟨M * 4 / (Real.log 2) ^ 2, by positivity, ?_⟩
  intro x T hx hT_lo hT_hi
  have hx0 : 0 ≤ x := by linarith
  have hLower := logT_sq_div_sqrtT_lower_bound T hT_lo hT_hi
  have hSqrt :
      |Littlewood.Development.ShiftedRemainderInterface.shiftedRemainderRe x T| ≤
        (M * 4 / (Real.log 2) ^ 2) *
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
    exact absorb_into_contour_shape
      (Littlewood.Development.ShiftedRemainderInterface.shiftedRemainderRe x T)
      x T M (hBound x T hx hT_lo hT_hi) hLower hM.le hx0
  have hLog_nonneg : 0 ≤ (Real.log x) ^ 2 := by positivity
  have hConst_nonneg : 0 ≤ M * 4 / (Real.log 2) ^ 2 := by positivity
  calc
    |Littlewood.Development.ShiftedRemainderInterface.shiftedRemainderRe x T|
      ≤ (M * 4 / (Real.log 2) ^ 2) *
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := hSqrt
    _ ≤ (M * 4 / (Real.log 2) ^ 2) *
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hConst_nonneg
        linarith

/-- Compatibility bridge from the focused bounded-height leaf to the legacy
small-`T` Perron contour boundary used throughout the current explicit-formula
and `π-li` stack. -/
instance (priority := 100)
    [SmallTPerronSqrtBoundHyp] :
    Littlewood.Development.HadamardProductZeta.SmallTPerronBoundHyp where
  bound := smallTPerron_general_bound_of_sqrt

end Aristotle.Standalone.SmallTPerronSqrtBridge
