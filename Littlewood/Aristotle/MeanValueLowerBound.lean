import Mathlib
import Littlewood.Aristotle.HardyApproxFunctionalEq

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.MeanValueLowerBound

open Filter Asymptotics MeasureTheory Set
open HardyApproxFunctional

lemma tlog_nonneg_of_one_le {T : ℝ} (hT : 1 ≤ T) : 0 ≤ T * Real.log T :=
  mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hT) (Real.log_nonneg hT)

lemma partial_sum_integral_nonneg {T : ℝ} :
    0 ≤ ∫ t in Set.Ioc 1 T, ‖partial_sum_approx t‖ ^ 2 := by
  exact setIntegral_nonneg measurableSet_Ioc (fun _ _ => sq_nonneg _)

/-- Extract an explicit eventual upper bound from
`HardyApproxFunctional.partial_sum_approx_mean_square_asymp`. -/
theorem partial_sum_approx_eventually_upper :
    ∃ C > 0, ∃ T₀ ≥ (1 : ℝ), ∀ T : ℝ, T ≥ T₀ →
      ∫ t in Set.Ioc 1 T, ‖partial_sum_approx t‖ ^ 2 ≤ C * (T * Real.log T) := by
  obtain ⟨C, hC, hCw⟩ := partial_sum_approx_mean_square_asymp.1.exists_pos
  rw [IsBigOWith] at hCw
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hCw
  refine ⟨C, hC, max T₀ 1, le_max_right _ _, ?_⟩
  intro T hT
  have hT₀' : T ≥ T₀ := le_trans (le_max_left _ _) hT
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  have h := hT₀ T hT₀'
  have hnorm_int :
      ‖∫ t in (1 : ℝ)..T, ‖partial_sum_approx t‖ ^ 2‖ =
        ∫ t in Set.Ioc 1 T, ‖partial_sum_approx t‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hT1, Real.norm_of_nonneg]
    exact partial_sum_integral_nonneg
  have hnorm_tlog : ‖T * Real.log T‖ = T * Real.log T := by
    exact Real.norm_of_nonneg (tlog_nonneg_of_one_le hT1)
  rw [hnorm_int, hnorm_tlog] at h
  exact h

/-- Extract an explicit eventual lower bound from
`HardyApproxFunctional.partial_sum_approx_mean_square_asymp`. -/
theorem partial_sum_approx_eventually_lower :
    ∃ c > 0, ∃ T₀ ≥ (2 : ℝ), ∀ T : ℝ, T ≥ T₀ →
      c * (T * Real.log T) ≤ ∫ t in Set.Ioc 1 T, ‖partial_sum_approx t‖ ^ 2 := by
  obtain ⟨C, hC, hCw⟩ := partial_sum_approx_mean_square_asymp.2.exists_pos
  rw [IsBigOWith] at hCw
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hCw
  refine ⟨C⁻¹, inv_pos.mpr hC, max T₀ 2, le_max_right _ _, ?_⟩
  intro T hT
  have hT₀' : T ≥ T₀ := le_trans (le_max_left _ _) hT
  have hT2 : 2 ≤ T := le_trans (le_max_right _ _) hT
  have hT1 : 1 ≤ T := by linarith
  have h := hT₀ T hT₀'
  have h_tlog_nonneg : 0 ≤ T * Real.log T := tlog_nonneg_of_one_le hT1
  have h_int_nonneg : 0 ≤ ∫ t in Set.Ioc 1 T, ‖partial_sum_approx t‖ ^ 2 :=
    partial_sum_integral_nonneg
  have hnorm_tlog : ‖T * Real.log T‖ = T * Real.log T :=
    Real.norm_of_nonneg h_tlog_nonneg
  have hnorm_int :
      ‖∫ t in (1 : ℝ)..T, ‖partial_sum_approx t‖ ^ 2‖ =
        ∫ t in Set.Ioc 1 T, ‖partial_sum_approx t‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hT1, Real.norm_of_nonneg h_int_nonneg]
  rw [hnorm_tlog, hnorm_int] at h
  have hmul : C⁻¹ * (T * Real.log T) ≤ C⁻¹ *
      (C * ∫ t in Set.Ioc 1 T, ‖partial_sum_approx t‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hC.le)
  have hcancel :
      C⁻¹ * (C * ∫ t in Set.Ioc 1 T, ‖partial_sum_approx t‖ ^ 2) =
        ∫ t in Set.Ioc 1 T, ‖partial_sum_approx t‖ ^ 2 := by
    ring_nf
    field_simp [hC.ne']
  simpa [hcancel] using hmul

end Aristotle.MeanValueLowerBound
