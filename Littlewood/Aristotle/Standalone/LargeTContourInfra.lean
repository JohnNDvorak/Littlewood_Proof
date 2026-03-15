/-
Infrastructure for the large-T contour bound (T ≥ 16).

The large-T contour integration decomposes into three segments:
1. Vertical: ∫_{1/2}^{c} |ζ'/ζ(σ+iT)·x^σ| dσ ≤ A·√x·(logT)²·T^{-1/2}
2. Horizontal top: ∫_{1/2}^{c} |ζ'/ζ(σ+iT)·x^σ| dσ ≤ B·√x·(logT)²·T^{-1}
3. Horizontal bottom: same as top

The key input is: |ζ'/ζ(s)| ≤ A·(logT)² for s on the contour (Hadamard product).

This file provides:
- Segment bound → contour bound assembly
- (logT)²/T ≤ (logT)²/√T (since √T ≤ T)
- (logT)³/T ≤ (logT)²/√T (since logT ≤ √T for T ≥ 16)
- Three-segment combination

SORRY COUNT: 0

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LargeTContourInfra

open Real

-- ============================================================
-- Part 1: Algebraic domination lemmas
-- ============================================================

/-- √T ≤ T for T ≥ 1. -/
theorem sqrtT_le_T (T : ℝ) (hT : 1 ≤ T) : Real.sqrt T ≤ T := by
  calc Real.sqrt T ≤ Real.sqrt T * Real.sqrt T :=
        le_mul_of_one_le_right (Real.sqrt_nonneg T)
          (by rw [Real.one_le_sqrt]; exact hT)
    _ = T := Real.mul_self_sqrt (by linarith)

/-- (logT)²/T ≤ (logT)²/√T for T ≥ 1: since √T ≤ T. -/
theorem logT_sq_over_T_le_over_sqrtT (T : ℝ) (hT : 1 ≤ T) :
    (Real.log T) ^ 2 / T ≤ (Real.log T) ^ 2 / Real.sqrt T := by
  have hT_pos : 0 < T := by linarith
  have h_sqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos_of_pos hT_pos
  rw [div_le_div_iff₀ hT_pos h_sqrtT_pos]
  exact mul_le_mul_of_nonneg_left (sqrtT_le_T T hT) (sq_nonneg _)

/-- logT ≤ √T for T ≥ 16. -/
theorem logT_le_sqrtT (T : ℝ) (hT : 16 ≤ T) : Real.log T ≤ Real.sqrt T := by
  have hT_pos : 0 < T := by linarith
  rw [← Real.exp_le_exp]
  calc Real.exp (Real.log T) = T := Real.exp_log hT_pos
    _ = (Real.sqrt T) ^ 2 := (Real.sq_sqrt hT_pos.le).symm
    _ ≤ Real.exp (Real.sqrt T) := by
        have h4 : (4 : ℝ) ≤ Real.sqrt T := by
          calc (4 : ℝ) = Real.sqrt 16 := by
                rw [show (16 : ℝ) = 4 ^ 2 from by norm_num,
                    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
            _ ≤ Real.sqrt T := Real.sqrt_le_sqrt (by linarith)
        have hst := Real.sum_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ Real.sqrt T) 4
        simp [Finset.sum_range_succ, Nat.factorial] at hst
        nlinarith [sq_nonneg (Real.sqrt T - 4)]

/-- (logT)³/T ≤ (logT)²/√T for T ≥ 16.
    Since logT ≤ √T: (logT)³/T = (logT)²·logT/T ≤ (logT)²·√T/T = (logT)²/√T. -/
theorem logT_cubed_over_T_le_sq_over_sqrtT (T : ℝ) (hT : 16 ≤ T) :
    (Real.log T) ^ 3 / T ≤ (Real.log T) ^ 2 / Real.sqrt T := by
  have hT_pos : 0 < T := by linarith
  have h_sqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos_of_pos hT_pos
  rw [div_le_div_iff₀ hT_pos h_sqrtT_pos]
  rw [show (Real.log T) ^ 2 * T =
      (Real.log T) ^ 2 * (Real.sqrt T * Real.sqrt T) from by
    rw [Real.mul_self_sqrt hT_pos.le]]
  have h_log_le := logT_le_sqrtT T hT
  have hlog_nn : 0 ≤ Real.log T := le_of_lt (Real.log_pos (by linarith : (1:ℝ) < T))
  nlinarith [mul_le_mul_of_nonneg_left h_log_le
    (mul_nonneg (Real.sqrt_nonneg T) (sq_nonneg (Real.log T)))]

-- ============================================================
-- Part 2: Three-segment assembly
-- ============================================================

/-- √x factor: √x · (logT)²/T ≤ √x · (logT)²/√T for T ≥ 1. -/
theorem sqrt_x_logT_sq_over_T_le (x T : ℝ) (hx : 0 ≤ x) (hT : 1 ≤ T) :
    Real.sqrt x * (Real.log T) ^ 2 / T ≤
    Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T := by
  have hT_pos : 0 < T := by linarith
  have h_sqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos_of_pos hT_pos
  rw [div_le_div_iff₀ hT_pos h_sqrtT_pos]
  exact mul_le_mul_of_nonneg_left (sqrtT_le_T T hT)
    (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _))

/-- √x factor for cubed: √x · (logT)³/T ≤ √x · (logT)²/√T for T ≥ 16. -/
theorem sqrt_x_logT_cubed_over_T_le (x T : ℝ) (_hx : 0 ≤ x) (hT : 16 ≤ T) :
    Real.sqrt x * (Real.log T) ^ 3 / T ≤
    Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T := by
  have hT_pos : 0 < T := by linarith
  have h_sqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos_of_pos hT_pos
  rw [div_le_div_iff₀ hT_pos h_sqrtT_pos]
  rw [show Real.sqrt x * (Real.log T) ^ 2 * T =
      Real.sqrt x * (Real.log T) ^ 2 * (Real.sqrt T * Real.sqrt T) from by
    rw [Real.mul_self_sqrt hT_pos.le]]
  have h_log_le := logT_le_sqrtT T hT
  have hlog_nn : 0 ≤ Real.log T := le_of_lt (Real.log_pos (by linarith : (1:ℝ) < T))
  nlinarith [mul_le_mul_of_nonneg_left h_log_le
    (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg (Real.log T)))]

/-- **Three-segment combination**: if vertical ≤ A·√x·(logT)³/T
    and horizontal ≤ B·√x·(logT)²/T, then total ≤ (A+2B)·√x·(logT)²/√T.
    The factor 2 accounts for top and bottom horizontal segments. -/
theorem three_segment_bound (A B x T : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx : 0 ≤ x) (hT : 16 ≤ T)
    (v_vert h_horiz : ℝ)
    (h_v : |v_vert| ≤ A * (Real.sqrt x * (Real.log T) ^ 3 / T))
    (h_h : |h_horiz| ≤ B * (Real.sqrt x * (Real.log T) ^ 2 / T)) :
    |v_vert + 2 * h_horiz| ≤
      (A + 2 * B) * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
  have h1 := sqrt_x_logT_cubed_over_T_le x T hx hT
  have h2 := sqrt_x_logT_sq_over_T_le x T hx (by linarith : (1:ℝ) ≤ T)
  have h_target_nn : 0 ≤ Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _))
      (Real.sqrt_nonneg T)
  calc |v_vert + 2 * h_horiz|
      ≤ |v_vert| + |2 * h_horiz| := abs_add_le _ _
    _ ≤ |v_vert| + 2 * |h_horiz| := by
        linarith [abs_nonneg h_horiz,
          show |2 * h_horiz| = 2 * |h_horiz| from by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]]
    _ ≤ A * (Real.sqrt x * (Real.log T) ^ 3 / T) +
        2 * (B * (Real.sqrt x * (Real.log T) ^ 2 / T)) :=
      add_le_add h_v (mul_le_mul_of_nonneg_left h_h (by norm_num))
    _ ≤ A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) +
        2 * (B * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left h1 hA
      · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hB) (by norm_num)
    _ = (A + 2 * B) * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by ring

end LargeTContourInfra
