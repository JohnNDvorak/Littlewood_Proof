/-
# Arithmetic Assembly Lemmas for the Explicit Formula Remainder Bound

Sorry-free target — all lemmas are pure real analysis / algebra.
AXLE-verified against latest Mathlib. Minor API differences with
project-pinned Mathlib (v4.27.0-rc1) are sorry'd for now.

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Littlewood.ExplicitFormulaAssemblyArithmetic

open Real

/-- log x ≤ x - 1 for x ≥ 1. -/
theorem log_le_sub_one (x : ℝ) (hx : 1 ≤ x) : Real.log x ≤ x - 1 := by
  linarith [Real.add_one_le_exp (Real.log x), Real.exp_log (by linarith : 0 < x)]

/-- log T ≤ 2√T for T ≥ 1. -/
theorem log_le_two_sqrt (T : ℝ) (hT : 1 ≤ T) : Real.log T ≤ 2 * Real.sqrt T := by
  have hT0 : 0 < T := by linarith
  have hsqrt1 : 1 ≤ Real.sqrt T := Real.one_le_sqrt.mpr hT
  calc Real.log T = 2 * (Real.log T / 2) := by ring
    _ = 2 * Real.log (Real.sqrt T) := by rw [← Real.log_sqrt hT0.le]
    _ ≤ 2 * (Real.sqrt T - 1) := by gcongr; exact log_le_sub_one _ hsqrt1
    _ ≤ 2 * Real.sqrt T := by linarith

/-- The target bound shape is non-negative. -/
theorem target_nonneg (x T : ℝ) :
    0 ≤ Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2 :=
  add_nonneg (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (Real.sqrt_nonneg _))
    (sq_nonneg _)

/-- **Three-piece assembly**: given bounds on truncation error, horizontal segments,
    and segment remainder, produce the standard contour bound. AXLE-verified. -/
theorem three_piece_assembly
    (x T R_trunc R_horiz R_seg C₁ C₂ C₃ : ℝ)
    (_hx : 2 ≤ x) (hT : 1 ≤ T)
    (hC1 : 0 ≤ C₁) (hC2 : 0 ≤ C₂) (hC3 : 0 ≤ C₃)
    (h1 : |R_trunc| ≤ C₁ * (Real.log x) ^ 2)
    (h2 : |R_horiz| ≤ C₂ * (Real.sqrt x * (Real.log T) ^ 2 / T))
    (h3 : |R_seg| ≤ C₃ * (Real.sqrt x * (Real.log T) ^ 3 / T)) :
    |R_trunc + R_horiz + R_seg| ≤
      (C₁ + C₂ + 2 * C₃) *
      (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hsqrt_le : Real.sqrt T ≤ T := by
    calc Real.sqrt T = Real.sqrt T * 1 := (mul_one _).symm
      _ ≤ Real.sqrt T * Real.sqrt T := by gcongr; exact Real.one_le_sqrt.mpr hT
      _ = T := Real.mul_self_sqrt hT0.le
  have hlog2sqrt : Real.log T ≤ 2 * Real.sqrt T := log_le_two_sqrt T hT
  -- (logT)²/T ≤ (logT)²/√T
  have h_t2 : Real.sqrt x * (Real.log T) ^ 2 / T ≤
      Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T := by gcongr
  -- (logT)³/T ≤ 2(logT)²/√T  [AXLE-verified; algebra with division]
  have h_t3 : Real.sqrt x * (Real.log T) ^ 3 / T ≤
      2 * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
    have hsqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.2 hT0
    have hne : Real.sqrt T ≠ 0 := hsqrt_pos.ne'
    calc Real.sqrt x * (Real.log T) ^ 3 / T
        ≤ Real.sqrt x * ((Real.log T) ^ 2 * (2 * Real.sqrt T)) / T := by
          apply div_le_div_of_nonneg_right _ hT0.le
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          calc (Real.log T) ^ 3 = (Real.log T) ^ 2 * Real.log T := by ring
            _ ≤ (Real.log T) ^ 2 * (2 * Real.sqrt T) := by gcongr
            _ = (Real.log T) ^ 2 * (2 * Real.sqrt T) := rfl
      _ = 2 * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
          have hT_eq : T = Real.sqrt T * Real.sqrt T := (Real.mul_self_sqrt hT0.le).symm
          field_simp [hne, hT0.ne']
          nlinarith [Real.mul_self_sqrt hT0.le]
  have hshape : 0 ≤ Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T := by positivity
  calc |R_trunc + R_horiz + R_seg|
      ≤ |R_trunc + R_horiz| + |R_seg| := abs_add_le _ _
    _ ≤ (|R_trunc| + |R_horiz|) + |R_seg| := by gcongr; exact abs_add_le R_trunc R_horiz
    _ ≤ C₁ * (Real.log x) ^ 2 + (C₂ * (Real.sqrt x * (Real.log T) ^ 2 / T) +
          C₃ * (Real.sqrt x * (Real.log T) ^ 3 / T)) := by linarith
    _ ≤ C₁ * (Real.log x) ^ 2 + (C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) +
          C₃ * (2 * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T))) := by
        linarith [mul_le_mul_of_nonneg_left h_t2 hC2, mul_le_mul_of_nonneg_left h_t3 hC3]
    _ = C₁ * (Real.log x) ^ 2 + (C₂ + 2 * C₃) * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by ring
    _ ≤ (C₁ + C₂ + 2 * C₃) * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
        nlinarith [sq_nonneg (Real.log x)]

end Littlewood.ExplicitFormulaAssemblyArithmetic
