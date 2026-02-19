import Mathlib
import Littlewood.Aristotle.ZetaMeanSquare

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.HardyMeanSquareLowerFromHalfBound

open Complex Real Set Filter Topology MeasureTheory Asymptotics

/-- Norm-based Hardy `Z` used in `HardyApproxFunctionalEq`. -/
def hardyZ (t : ℝ) : ℝ :=
  ‖riemannZeta ((2⁻¹ : ℂ) + (t : ℂ) * Complex.I)‖

private def zetaIntegrand (t : ℝ) : ℝ :=
  ‖riemannZeta ((2⁻¹ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2

private lemma zetaIntegrand_eq_hardyZ_sq (t : ℝ) :
    zetaIntegrand t = (hardyZ t) ^ 2 := by
  simp [zetaIntegrand, hardyZ]

private lemma continuous_zetaIntegrand : Continuous zetaIntegrand := by
  let g : ℝ → ℂ := fun t => (2⁻¹ : ℂ) + (t : ℂ) * Complex.I
  have hg : Continuous g := by
    simpa [g] using (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  have hcont_zeta : Continuous fun t : ℝ => riemannZeta (g t) := by
    refine continuous_iff_continuousAt.2 ?_
    intro t
    have hs : g t ≠ 1 := by
      intro h
      have hre : (g t).re = (1 : ℂ).re := congrArg Complex.re h
      simp [g] at hre
    have hz : ContinuousAt (fun z : ℂ => riemannZeta z) (g t) :=
      (differentiableAt_riemannZeta hs).continuousAt
    exact hz.comp hg.continuousAt
  simpa [zetaIntegrand, g] using (hcont_zeta.norm.pow 2)

private lemma intervalIntegrable_zetaIntegrand (a b : ℝ) :
    IntervalIntegrable zetaIntegrand volume a b :=
  continuous_zetaIntegrand.intervalIntegrable a b

private lemma mean_square_zeta_half_eq_integral (T : ℝ) :
    mean_square_zeta (1 / 2) T = ∫ t in (0 : ℝ)..T, zetaIntegrand t := by
  simp [mean_square_zeta, zetaIntegrand, mul_comm]

private lemma integral_Ioc_one_eq_mean_square_sub (T : ℝ) (hT : 1 ≤ T) :
    ∫ t in Set.Ioc 1 T, (hardyZ t)^2 = mean_square_zeta (1 / 2) T - mean_square_zeta (1 / 2) 1 := by
  have h01 : IntervalIntegrable zetaIntegrand volume (0 : ℝ) 1 :=
    intervalIntegrable_zetaIntegrand 0 1
  have h1T : IntervalIntegrable zetaIntegrand volume (1 : ℝ) T :=
    intervalIntegrable_zetaIntegrand 1 T
  have h0T : IntervalIntegrable zetaIntegrand volume (0 : ℝ) T :=
    h01.trans h1T
  have hsub :
      (∫ t in (0 : ℝ)..T, zetaIntegrand t) - ∫ t in (0 : ℝ)..1, zetaIntegrand t =
        ∫ t in (1 : ℝ)..T, zetaIntegrand t :=
    intervalIntegral.integral_interval_sub_left h0T h01
  have hIoc :
      ∫ t in (1 : ℝ)..T, zetaIntegrand t =
        ∫ t in Set.Ioc 1 T, (hardyZ t)^2 := by
    rw [intervalIntegral.integral_of_le hT]
    simp [zetaIntegrand_eq_hardyZ_sq]
  calc
    ∫ t in Set.Ioc 1 T, (hardyZ t)^2
        = ∫ t in (1 : ℝ)..T, zetaIntegrand t := by simpa using hIoc.symm
    _ = ((∫ t in (0 : ℝ)..T, zetaIntegrand t) - ∫ t in (0 : ℝ)..1, zetaIntegrand t) := by
      exact hsub.symm
    _ = mean_square_zeta (1 / 2) T - mean_square_zeta (1 / 2) 1 := by
      rw [mean_square_zeta_half_eq_integral T, mean_square_zeta_half_eq_integral 1]

/--
From the critical-line second-moment asymptotic
`mean_square_zeta (1/2) T = T log T + O(T)`, extract the exact lower-bound shape used at
`HardyApproxFunctionalEq.zeta_critical_mean_value_lower`.
-/
theorem zeta_critical_mean_value_lower_of_asymptotic
    (h_asymp :
      (fun T : ℝ => mean_square_zeta (1 / 2) T - T * Real.log T)
      =O[atTop] (fun T : ℝ => T)) :
    ∃ c > 0, ∃ T₁ ≥ (2 : ℝ), ∀ T : ℝ, T ≥ T₁ →
      ∫ t in Set.Ioc 1 T, (hardyZ t)^2 ≥ c * T * Real.log T := by
  obtain ⟨C, hC_nonneg, hC_with⟩ := h_asymp.exists_nonneg
  rw [Asymptotics.IsBigOWith] at hC_with
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hC_with

  set K : ℝ := mean_square_zeta (1 / 2) 1

  refine ⟨(1 / 2 : ℝ), by norm_num,
    max (max M 2) (max (Real.exp (4 * C + 1)) (4 * |K|)), ?_, ?_⟩
  · exact le_trans (le_max_right M 2) (le_max_left _ _)
  · intro T hT
    have hT_ge_M : T ≥ M :=
      le_trans (le_trans (le_max_left M 2) (le_max_left _ _)) hT
    have hT_ge_two : T ≥ 2 :=
      le_trans (le_trans (le_max_right M 2) (le_max_left _ _)) hT
    have hT_ge_exp : Real.exp (4 * C + 1) ≤ T :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
    have hT_ge_K : 4 * |K| ≤ T :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
    have hT_nonneg : 0 ≤ T := by linarith
    have hT_ge_one : 1 ≤ T := by linarith

    have h_err := hM T hT_ge_M
    have h_err_abs : |mean_square_zeta (1 / 2) T - T * Real.log T| ≤ C * T := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hT_nonneg] using h_err

    have h_ms_lower : T * Real.log T - C * T ≤ mean_square_zeta (1 / 2) T := by
      have hleft := (abs_le.mp h_err_abs).1
      linarith

    have h_shift :
        ∫ t in Set.Ioc 1 T, (hardyZ t)^2 = mean_square_zeta (1 / 2) T - K := by
      simpa [K] using integral_Ioc_one_eq_mean_square_sub T hT_ge_one

    have hI_lower :
        T * Real.log T - C * T - K ≤ ∫ t in Set.Ioc 1 T, (hardyZ t)^2 := by
      linarith [h_ms_lower, h_shift]

    have hlog_large : 4 * C + 1 ≤ Real.log T := by
      calc
        4 * C + 1 = Real.log (Real.exp (4 * C + 1)) := by rw [Real.log_exp]
        _ ≤ Real.log T := Real.log_le_log (Real.exp_pos _) hT_ge_exp

    have hCT_quarter : C * T ≤ (1 / 4 : ℝ) * T * Real.log T := by
      have hCle : C ≤ (1 / 4 : ℝ) * Real.log T := by linarith
      have hCmul : C * T ≤ ((1 / 4 : ℝ) * Real.log T) * T :=
        mul_le_mul_of_nonneg_right hCle hT_nonneg
      nlinarith [hCmul]

    have hTlog_ge_T : T ≤ T * Real.log T := by
      have hlog_ge_one : 1 ≤ Real.log T := by linarith [hlog_large]
      nlinarith

    have hK_quarter : |K| ≤ (1 / 4 : ℝ) * T * Real.log T := by
      have hK_le_T4 : |K| ≤ T / 4 := by nlinarith [hT_ge_K]
      have hT4_le : T / 4 ≤ (1 / 4 : ℝ) * T * Real.log T := by
        nlinarith [hTlog_ge_T]
      exact le_trans hK_le_T4 hT4_le

    have hI_lower_abs :
        T * Real.log T - C * T - |K| ≤ ∫ t in Set.Ioc 1 T, (hardyZ t)^2 := by
      have hK : K ≤ |K| := le_abs_self K
      linarith [hI_lower, hK]

    have hhalf : (1 / 2 : ℝ) * T * Real.log T ≤ ∫ t in Set.Ioc 1 T, (hardyZ t)^2 := by
      linarith [hI_lower_abs, hCT_quarter, hK_quarter]

    linarith [hhalf]

/--
Typeclass-instantiated version using the repo hypothesis
`ZetaMeanSquareHalfBound.bound`.
-/
theorem zeta_critical_mean_value_lower
    [ZetaMeanSquareHalfBound] :
    ∃ c > 0, ∃ T₁ ≥ (2 : ℝ), ∀ T : ℝ, T ≥ T₁ →
      ∫ t in Set.Ioc 1 T, (hardyZ t)^2 ≥ c * T * Real.log T := by
  have h_asymp :
      (fun T : ℝ => mean_square_zeta (1 / 2) T - T * Real.log T)
        =O[atTop] (fun T : ℝ => T) :=
    mean_square_zeta_half_asymp
  obtain ⟨c, hc, T₁, hT₁, hmain⟩ :=
    zeta_critical_mean_value_lower_of_asymptotic h_asymp
  refine ⟨c, hc, T₁, hT₁, ?_⟩
  intro T hT
  exact hmain T hT

end Aristotle.Standalone.HardyMeanSquareLowerFromHalfBound
