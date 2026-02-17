import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial

/-
Hardy mean-square leaf reduction.

This file is separate from the main build chain. It proves the exact
`HardySetupV2.mean_square_lower` conclusion from one explicit asymptotic
hypothesis:

  ∫_{1}^{T} Z(t)^2 dt = T log T + O(T),

with `Z = HardyEstimatesPartial.hardyZ`.
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

namespace Aristotle.HardyMeanSquareLeafFromAsymptotic

open Complex Real Set Filter Topology MeasureTheory Asymptotics

/-- If the Hardy-Littlewood asymptotic
`∫_{1}^{T} Z(t)^2 - T log T = O(T)` is available, then the exact
`HardySetupV2.mean_square_lower` field follows. -/
theorem hardy_mean_square_lower_of_asymptotic
    (h_asymp :
      (fun T : ℝ =>
        (∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t)^2) - T * Real.log T)
      =O[atTop] (fun T : ℝ => T)) :
    ∃ c : ℝ, c > 0 ∧ ∃ T₀ : ℝ, T₀ ≥ 2 ∧ ∀ T : ℝ, T ≥ T₀ →
      c * T * Real.log T ≤ ∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t)^2 := by
  obtain ⟨C, hC_nonneg, hC_with⟩ := h_asymp.exists_nonneg
  rw [Asymptotics.IsBigOWith] at hC_with
  rw [Filter.Eventually, Filter.mem_atTop_sets] at hC_with
  obtain ⟨M, hM⟩ := hC_with

  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  refine ⟨max (max M 2) (Real.exp (2 * C + 1)), ?_, ?_⟩
  · exact le_trans (le_max_right M 2) (le_max_left _ _)
  · intro T hT
    set I : ℝ := ∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t)^2

    have hT_ge_M : T ≥ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
    have hT_ge_exp : Real.exp (2 * C + 1) ≤ T :=
      le_trans (le_max_right _ _) hT
    have hT_ge_two : T ≥ 2 := le_trans (le_trans (le_max_right M 2) (le_max_left _ _)) hT
    have hT_nonneg : 0 ≤ T := by linarith

    have h_err := hM T hT_ge_M
    have h_err_abs' : |I - T * Real.log T| ≤ C * |T| := by
      simpa [I, Real.norm_eq_abs] using h_err
    have h_err_abs : |I - T * Real.log T| ≤ C * T := by
      simpa [abs_of_nonneg hT_nonneg] using h_err_abs'

    have hI_lower : T * Real.log T - C * T ≤ I := by
      have hleft := (abs_le.mp h_err_abs).1
      linarith

    have hlog_large : 2 * C + 1 ≤ Real.log T := by
      calc
        2 * C + 1 = Real.log (Real.exp (2 * C + 1)) := by rw [Real.log_exp]
        _ ≤ Real.log T := Real.log_le_log (Real.exp_pos _) hT_ge_exp

    have hCT_le_half : C * T ≤ (1 / 2 : ℝ) * T * Real.log T := by
      have hCle : C ≤ (1 / 2 : ℝ) * Real.log T := by linarith
      nlinarith [mul_le_mul_of_nonneg_right hCle hT_nonneg]

    have h_half_lower : (1 / 2 : ℝ) * T * Real.log T ≤ I := by
      linarith [hI_lower, hCT_le_half]

    simpa [I, mul_assoc, mul_left_comm, mul_comm] using h_half_lower

end Aristotle.HardyMeanSquareLeafFromAsymptotic
