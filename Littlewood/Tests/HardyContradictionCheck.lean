/-
Verify the Hardy contradiction works with correct exponents.

CRITICAL CHECK:
With ε₁ (first moment) and ε₂ (convexity), the contradiction requires:
  1/4 + ε₂ + 1/2 + ε₁ < 1
i.e. ε₁ + ε₂ < 1/4

Standard: ε₁ = ε₂ = 1/10 gives 1/4 + 1/10 + 1/2 + 1/10 = 19/20 < 1 ✓

So the exponent is 19/20, and we need T·log T ≤ C·T^{19/20} to fail.
Since T·log T / T^{19/20} = T^{1/20}·log T → ∞, we get contradiction. ✓
-/

import Mathlib

set_option maxHeartbeats 400000

-- Quick check: for large T, T * log T > C * T^(19/20)
-- Equivalently: T^(1/20) * log T > C
-- This goes to infinity, so yes.
example : ∀ C : ℝ, ∃ T : ℝ, T > 0 ∧ C * T^((19:ℝ)/20) < T * Real.log T := by
  intro C
  -- Pick T = exp(max C 0 + 1). Then log T = max C 0 + 1 > C,
  -- T ≥ e > 1, so T^{19/20} ≤ T, giving C * T^{19/20} < log T * T.
  set T := Real.exp (max C 0 + 1) with hT_def
  use T
  have hT_pos : (0:ℝ) < T := Real.exp_pos _
  have harg_pos : (0:ℝ) < max C 0 + 1 := by linarith [le_max_right C 0]
  have hT_ge1 : (1:ℝ) ≤ T := Real.one_le_exp (le_of_lt harg_pos)
  have hlog : Real.log T = max C 0 + 1 := Real.log_exp _
  have hlog_pos : (0:ℝ) < Real.log T := by rw [hlog]; linarith
  constructor
  · exact hT_pos
  · -- T^{19/20} ≤ T^1 = T since T ≥ 1
    have h_rpow_le : T ^ ((19:ℝ)/20) ≤ T := by
      calc T ^ ((19:ℝ)/20) ≤ T ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hT_ge1 (by norm_num : (19:ℝ)/20 ≤ 1)
        _ = T := Real.rpow_one T
    -- C < log T = max C 0 + 1
    have hC_lt_log : C < Real.log T := by rw [hlog]; linarith [le_max_left C 0]
    -- Case split on sign of C
    by_cases hC : C ≤ 0
    · -- C ≤ 0: C * T^{19/20} ≤ 0 < T * log T
      have : C * T ^ ((19:ℝ)/20) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (by positivity)
      nlinarith [mul_pos hT_pos hlog_pos]
    · -- C > 0: C * T^{19/20} ≤ C * T < log T * T = T * log T
      push_neg at hC
      nlinarith [mul_lt_mul_of_pos_right hC_lt_log hT_pos,
                 mul_le_mul_of_nonneg_left h_rpow_le (le_of_lt hC)]

#check "Hardy contradiction math checks out ✓"
