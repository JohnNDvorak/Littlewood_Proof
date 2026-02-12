/- 
Elementary properties of `hardyN` / `hardyStart`.
-/

import Mathlib
import Littlewood.Aristotle.HardyZMeasurability

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.HardyNProperties

open Real
open HardyEstimatesPartial

/-- Explicit formula for `hardyStart`. -/
theorem hardyStart_formula (k : ℕ) :
    hardyStart k = 2 * Real.pi * ((k + 1 : ℝ)) ^ 2 := by
  simp [hardyStart]

/-- `hardyN` is constant on each breakpoint block `[hardyStart k, hardyStart (k+1))`. -/
theorem hardyN_constant_on_block (k : ℕ) (t : ℝ)
    (ht : hardyStart k ≤ t) (ht' : t < hardyStart (k + 1)) :
    hardyN t = k + 1 := by
  have h_start_nonneg : 0 ≤ hardyStart k := by
    simp [hardyStart]
    positivity
  have ht_nonneg : 0 ≤ t := le_trans h_start_nonneg ht
  have h_low : k < hardyN t := (hardyN_lt_iff k t ht_nonneg).2 ht
  have h_not_high : ¬ (k + 1 < hardyN t) := by
    intro h
    have h_le : hardyStart (k + 1) ≤ t := (hardyN_lt_iff (k + 1) t ht_nonneg).1 h
    linarith
  exact Nat.le_antisymm (Nat.not_lt.mp h_not_high) (Nat.succ_le_of_lt h_low)

/-- A convenient global upper bound: `hardyN T + 1 ≤ T^(1/2)` for `T ≥ 2`. -/
theorem hardyN_le_sqrt (T : ℝ) (hT : T ≥ 2) :
    ((hardyN T : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) := by
  have hT_nonneg : 0 ≤ T := by linarith
  have h_floor :
      (hardyN T : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) := by
    exact Nat.floor_le (Real.sqrt_nonneg _)
  by_cases hN0 : hardyN T = 0
  ·
    have hT_ge_one : (1 : ℝ) ≤ T := by linarith
    have h1 : (1 : ℝ) ≤ T ^ (1 / 2 : ℝ) := Real.one_le_rpow hT_ge_one (by norm_num)
    simpa [hN0] using h1
  · have hN1 : 1 ≤ hardyN T := Nat.succ_le_of_lt (Nat.pos_iff_ne_zero.mpr hN0)
    have hN1_real : (1 : ℝ) ≤ (hardyN T : ℝ) := by exact_mod_cast hN1
    have h_lhs_two :
        ((hardyN T : ℝ) + 1) ≤ 2 * (hardyN T : ℝ) := by
      nlinarith
    have h_two_floor :
        (2 : ℝ) * (hardyN T : ℝ) ≤ 2 * Real.sqrt (T / (2 * Real.pi)) := by
      exact mul_le_mul_of_nonneg_left h_floor (by positivity)
    have h_const : (2 : ℝ) / Real.sqrt (2 * Real.pi) ≤ 1 := by
      have h_sqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
      have h2_le_sqrt : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
        have hsq : (2 : ℝ) ^ 2 ≤ (Real.sqrt (2 * Real.pi)) ^ 2 := by
          calc
            (2 : ℝ) ^ 2 = 4 := by ring
            _ ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
            _ = (Real.sqrt (2 * Real.pi)) ^ 2 := by
              symm
              exact Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)
        nlinarith [hsq, Real.sqrt_nonneg (2 * Real.pi)]
      exact (div_le_iff₀ h_sqrt_pos).2 (by simpa using h2_le_sqrt)
    have h_sqrt_div :
        Real.sqrt (T / (2 * Real.pi)) = Real.sqrt T / Real.sqrt (2 * Real.pi) := by
      rw [Real.sqrt_div hT_nonneg]
    have h_two_sqrt :
        2 * Real.sqrt (T / (2 * Real.pi)) ≤ Real.sqrt T := by
      rw [h_sqrt_div]
      calc
        2 * (Real.sqrt T / Real.sqrt (2 * Real.pi))
            = ((2 : ℝ) / Real.sqrt (2 * Real.pi)) * Real.sqrt T := by
              ring
        _ ≤ 1 * Real.sqrt T := by
              exact mul_le_mul_of_nonneg_right h_const (Real.sqrt_nonneg _)
        _ = Real.sqrt T := by ring
    calc
      ((hardyN T : ℝ) + 1) ≤ 2 * (hardyN T : ℝ) := h_lhs_two
      _ ≤ 2 * Real.sqrt (T / (2 * Real.pi)) := h_two_floor
      _ ≤ Real.sqrt T := h_two_sqrt
      _ = T ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]

/-- Exact length of one breakpoint block. -/
theorem block_length (k : ℕ) :
    hardyStart (k + 1) - hardyStart k = 2 * Real.pi * (2 * (k : ℝ) + 3) := by
  simp [hardyStart]
  ring

end Aristotle.HardyNProperties
