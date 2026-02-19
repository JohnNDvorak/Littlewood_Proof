import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.HardyMeanSquareLowerUnconditional

open Complex Real Set Filter Topology MeasureTheory Asymptotics

/-- Norm-based Hardy `Z` used by `HardyApproxFunctionalEq`. -/
def hardyZ (t : ℝ) : ℝ :=
  ‖riemannZeta (1 / 2 + t * Complex.I)‖

/-- Explicit asymptotic gap needed for the critical-line mean-square lower bound. -/
def zeta_critical_mean_value_lower_gap : Prop :=
  (fun T : ℝ =>
    (∫ t in Set.Ioc 1 T, (hardyZ t)^2) - T * Real.log T)
    =O[atTop] (fun T : ℝ => T)

/-- Explicit extraction: if `∫₁ᵀ |ζ(1/2+it)|² = T log T + O(T)` with witness
constants `(C, M)`, then for all `T ≥ max (max M 2) (exp (2C+1))`:
`∫₁ᵀ |ζ(1/2+it)|² ≥ (1/2) T log T`. -/
theorem zeta_critical_mean_value_lower_explicit
    {C M : ℝ}
    (hM :
      ∀ T : ℝ, T ≥ M →
        ‖(∫ t in Set.Ioc 1 T, (hardyZ t)^2) - T * Real.log T‖ ≤ C * ‖T‖) :
    ∀ T : ℝ, T ≥ max (max M 2) (Real.exp (2 * C + 1)) →
      ∫ t in Set.Ioc 1 T, (hardyZ t)^2 ≥ (1 / 2 : ℝ) * T * Real.log T := by
  intro T hT
  set I : ℝ := ∫ t in Set.Ioc 1 T, (hardyZ t)^2

  have hT_ge_M : T ≥ M :=
    le_trans (le_trans (le_max_left M 2) (le_max_left _ _)) hT
  have hT_ge_exp : Real.exp (2 * C + 1) ≤ T :=
    le_trans (le_max_right _ _) hT
  have hT_ge_two : T ≥ 2 :=
    le_trans (le_trans (le_max_right M 2) (le_max_left _ _)) hT
  have hT_nonneg : 0 ≤ T := by linarith

  have h_err := hM T hT_ge_M
  have h_err_abs : |I - T * Real.log T| ≤ C * T := by
    simpa [I, Real.norm_eq_abs, abs_of_nonneg hT_nonneg] using h_err

  have hI_lower : T * Real.log T - C * T ≤ I := by
    have hleft := (abs_le.mp h_err_abs).1
    linarith

  have hlog_large : 2 * C + 1 ≤ Real.log T := by
    calc
      2 * C + 1 = Real.log (Real.exp (2 * C + 1)) := by rw [Real.log_exp]
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos _) hT_ge_exp

  have hCT_le_half : C * T ≤ (1 / 2 : ℝ) * T * Real.log T := by
    have hCle : C ≤ (1 / 2 : ℝ) * Real.log T := by linarith
    have hCmul : C * T ≤ ((1 / 2 : ℝ) * Real.log T) * T :=
      mul_le_mul_of_nonneg_right hCle hT_nonneg
    nlinarith [hCmul]

  have h_half_lower : (1 / 2 : ℝ) * T * Real.log T ≤ I := by
    linarith [hI_lower, hCT_le_half]

  simpa [I, mul_assoc, mul_left_comm, mul_comm] using h_half_lower

/-- Shape match of `HardyApproxFunctionalEq.zeta_critical_mean_value_lower`,
proved from the single explicit asymptotic gap hypothesis. -/
theorem zeta_critical_mean_value_lower_of_asymptotic
    (hgap : zeta_critical_mean_value_lower_gap) :
    ∃ c > 0, ∃ T₁ ≥ (2 : ℝ), ∀ T : ℝ, T ≥ T₁ →
      ∫ t in Set.Ioc 1 T, (hardyZ t)^2 ≥ c * T * Real.log T := by
  obtain ⟨C, _hC_nonneg, hC_with⟩ := hgap.exists_nonneg
  rw [Asymptotics.IsBigOWith] at hC_with
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hC_with

  refine ⟨(1 / 2 : ℝ), by norm_num,
    max (max M 2) (Real.exp (2 * C + 1)), ?_, ?_⟩
  · exact le_trans (le_max_right M 2) (le_max_left _ _)
  · intro T hT
    have hmain :=
      zeta_critical_mean_value_lower_explicit (C := C) (M := M) hM T hT
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmain

/-- Inline variant of `zeta_critical_mean_value_lower_of_asymptotic`. -/
theorem zeta_critical_mean_value_lower_from_isBigO
    (h_asymp :
      (fun T : ℝ =>
        (∫ t in Set.Ioc 1 T, (hardyZ t)^2) - T * Real.log T)
      =O[atTop] (fun T : ℝ => T)) :
    ∃ c > 0, ∃ T₁ ≥ (2 : ℝ), ∀ T : ℝ, T ≥ T₁ →
      ∫ t in Set.Ioc 1 T, (hardyZ t)^2 ≥ c * T * Real.log T := by
  obtain ⟨C, _hC_nonneg, hC_with⟩ := h_asymp.exists_nonneg
  rw [Asymptotics.IsBigOWith] at hC_with
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hC_with

  refine ⟨(1 / 2 : ℝ), by norm_num,
    max (max M 2) (Real.exp (2 * C + 1)), ?_, ?_⟩
  · exact le_trans (le_max_right M 2) (le_max_left _ _)
  · intro T hT
    have hmain :=
      zeta_critical_mean_value_lower_explicit (C := C) (M := M) hM T hT
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmain

end Aristotle.Standalone.HardyMeanSquareLowerUnconditional
