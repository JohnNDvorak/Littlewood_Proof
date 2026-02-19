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

namespace Aristotle.HardyMeanValueLowerStrict

open Complex Real Set Filter Topology MeasureTheory Asymptotics

/-- Norm-based Hardy `Z` used in `HardyApproxFunctionalEq`. -/
def hardyZ (t : ℝ) : ℝ :=
  ‖riemannZeta (1 / 2 + t * Complex.I)‖

/-- Generic strict lower bound extraction from a Hardy-Littlewood type asymptotic.

If
`∫_{1}^{T} f(t)^2 dt = T log T + O(T)`,
then for large `T`, `∫_{1}^{T} f(t)^2 dt ≥ c * T * log T` for some `c > 0`. -/
theorem mean_square_lower_of_asymptotic
    (f : ℝ → ℝ)
    (h_asymp :
      (fun T : ℝ => (∫ t in Ioc 1 T, (f t)^2) - T * Real.log T)
      =O[atTop] (fun T : ℝ => T)) :
    ∃ c > 0, ∃ T₀ ≥ (2 : ℝ), ∀ T : ℝ, T ≥ T₀ →
      ∫ t in Ioc 1 T, (f t)^2 ≥ c * T * Real.log T := by
  obtain ⟨C, _hC_nonneg, hC_with⟩ := h_asymp.exists_nonneg
  rw [Asymptotics.IsBigOWith] at hC_with
  rw [Filter.Eventually, Filter.mem_atTop_sets] at hC_with
  obtain ⟨M, hM⟩ := hC_with

  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  refine ⟨max (max M 2) (Real.exp (2 * C + 1)), ?_, ?_⟩
  · exact le_trans (le_max_right M 2) (le_max_left _ _)
  · intro T hT
    set I : ℝ := ∫ t in Ioc 1 T, (f t)^2

    have hT_ge_M : T ≥ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
    have hT_ge_exp : Real.exp (2 * C + 1) ≤ T := le_trans (le_max_right _ _) hT
    have hT_nonneg : 0 ≤ T := by
      have h_exp_pos : 0 < Real.exp (2 * C + 1) := Real.exp_pos _
      linarith

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
      have hCmul : C * T ≤ ((1 / 2 : ℝ) * Real.log T) * T :=
        mul_le_mul_of_nonneg_right hCle hT_nonneg
      nlinarith [hCmul]

    have h_half_lower : (1 / 2 : ℝ) * T * Real.log T ≤ I := by
      linarith [hI_lower, hCT_le_half]

    have h_target : (1 / 2 : ℝ) * T * Real.log T ≤ ∫ t in Ioc 1 T, (f t)^2 := by
      simpa [I, mul_assoc, mul_left_comm, mul_comm] using h_half_lower

    linarith

/-- Standalone shape match of `HardyApproxFunctionalEq.zeta_critical_mean_value_lower`,
proved from the concrete Hardy-Littlewood asymptotic input. -/
theorem zeta_critical_mean_value_lower_of_asymptotic
    (h_asymp :
      (fun T : ℝ =>
        (∫ t in Set.Ioc 1 T, (hardyZ t)^2) - T * Real.log T)
      =O[atTop] (fun T : ℝ => T)) :
    ∃ c > 0, ∃ T₁ ≥ (2 : ℝ), ∀ T : ℝ, T ≥ T₁ →
      ∫ t in Set.Ioc 1 T, (hardyZ t)^2 ≥ c * T * Real.log T := by
  obtain ⟨c, hc, T₁, hT₁, hmain⟩ :=
    mean_square_lower_of_asymptotic hardyZ h_asymp
  refine ⟨c, hc, T₁, hT₁, ?_⟩
  intro T hT
  exact hmain T hT

/-- Remaining unconditional gap needed to recover
`HardyApproxFunctionalEq.zeta_critical_mean_value_lower` without hypotheses. -/
def zeta_critical_mean_value_lower_gap : Prop :=
  (fun T : ℝ =>
    (∫ t in Set.Ioc 1 T, (hardyZ t)^2) - T * Real.log T)
    =O[atTop] (fun T : ℝ => T)

/-- Exact dependency closure: the gap proposition implies the target-shaped theorem. -/
theorem zeta_critical_mean_value_lower_from_gap
    (hgap : zeta_critical_mean_value_lower_gap) :
    ∃ c > 0, ∃ T₁ ≥ (2 : ℝ), ∀ T : ℝ, T ≥ T₁ →
      ∫ t in Set.Ioc 1 T, (hardyZ t)^2 ≥ c * T * Real.log T := by
  have h_asymp :
      (fun T : ℝ =>
        (∫ t in Set.Ioc 1 T, (hardyZ t)^2) - T * Real.log T)
      =O[atTop] (fun T : ℝ => T) := by
    simpa [zeta_critical_mean_value_lower_gap] using hgap
  obtain ⟨c, hc, T₁, hT₁, hmain⟩ :=
    mean_square_lower_of_asymptotic hardyZ h_asymp
  refine ⟨c, hc, T₁, hT₁, ?_⟩
  intro T hT
  exact hmain T hT

/-- Target-shaped standalone endpoint, reduced to the explicit asymptotic gap. -/
theorem zeta_critical_mean_value_lower
    (hgap : zeta_critical_mean_value_lower_gap) :
    ∃ c > 0, ∃ T₁ ≥ (2 : ℝ), ∀ T : ℝ, T ≥ T₁ →
      ∫ t in Set.Ioc 1 T, (hardyZ t)^2 ≥ c * T * Real.log T := by
  have h_asymp :
      (fun T : ℝ =>
        (∫ t in Set.Ioc 1 T, (hardyZ t)^2) - T * Real.log T)
      =O[atTop] (fun T : ℝ => T) := by
    simpa [zeta_critical_mean_value_lower_gap] using hgap
  obtain ⟨c, hc, T₁, hT₁, hmain⟩ :=
    mean_square_lower_of_asymptotic hardyZ h_asymp
  refine ⟨c, hc, T₁, hT₁, ?_⟩
  intro T hT
  exact hmain T hT

end Aristotle.HardyMeanValueLowerStrict
