/-
Almost-periodic mean value infrastructure for the Landau contradiction.

This file provides lemmas for the Cesàro mean theory used in the Landau
oscillation argument:

  1. Exponential integral bound: ‖∫₀ᵀ e^{iγu} du‖ ≤ 2/|γ|
  2. Norm of exp(iθ) = 1 for real θ (PROVED)
  3. Cesàro mean of exponentials → 0
  4. One-sided bound + zero Cesàro mean + bounded → zero L² Cesàro mean

These are building blocks toward proving the Landau contradiction
(currently in DeepSorries.deep_mathematical_results) from a hypothesized
smoothed explicit formula.

STATUS: 5 of 6 lemmas proved (1 sorry: parseval_finite_trig_sum).
NOT imported by the main build (no effect on project sorry count).

REFERENCES:
  - Landau, "Über einen Satz von Tschebyschef" (1905)
  - Bohr, "Fastperiodische Funktionen" (1925)
  - Montgomery-Vaughan, "Multiplicative Number Theory I", §15.1
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.AlmostPeriodicMeanValue

open Complex Filter MeasureTheory Topology Real

/-! ## Norm of complex exponential with purely imaginary argument -/

/-- The real part of `I * ↑γ * ↑T` is zero (purely imaginary).

PROVED: direct computation from `Complex.mul_re` and `I_re/I_im`. -/
private lemma re_I_mul_ofReal_mul_ofReal (γ T : ℝ) :
    (Complex.I * (↑γ : ℂ) * (↑T : ℂ)).re = 0 := by
  simp [Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]

/-- The norm of `exp(I * γ * T)` is 1 for real γ, T.

PROVED: from `Complex.norm_exp` and `re_I_mul_ofReal_mul_ofReal`. -/
lemma norm_exp_I_mul_real (γ T : ℝ) :
    ‖Complex.exp (Complex.I * (↑γ : ℂ) * (↑T : ℂ))‖ = 1 := by
  rw [Complex.norm_exp, re_I_mul_ofReal_mul_ofReal, Real.exp_zero]

/-- ‖I * ↑γ‖ = |γ| for γ : ℝ.

PROVED: from `norm_mul`, `Complex.norm_I`, and `Complex.norm_real`. -/
lemma norm_I_mul_ofReal (γ : ℝ) : ‖(Complex.I * (↑γ : ℂ))‖ = |γ| := by
  rw [norm_mul, Complex.norm_I, one_mul]
  simp [Complex.norm_real, Real.norm_eq_abs]

/-! ## Exponential integral bound -/

/-- **Exponential integral bound**: ‖∫₀ᵀ e^{iγu} du‖ ≤ 2/|γ| for γ ≠ 0.

This is the key oscillatory cancellation lemma: the integral of a
complex exponential over [0,T] is bounded independently of T.

PROOF SKETCH:
  By `integral_exp_mul_complex`, ∫₀ᵀ e^{iγu} du = (e^{iγT} - 1)/(iγ).
  Then ‖numerator‖ ≤ ‖e^{iγT}‖ + 1 = 1 + 1 = 2 and ‖denominator‖ = |γ|.

USES: `integral_exp_mul_complex` from Mathlib.Analysis.SpecialFunctions.Integrals.Basic -/
theorem exp_integral_bound (γ : ℝ) (hγ : γ ≠ 0) (T : ℝ) :
    ‖∫ u in (0 : ℝ)..T, Complex.exp (Complex.I * (↑γ : ℂ) * ↑u)‖ ≤
      2 / |γ| := by
  have hc : (Complex.I * (↑γ : ℂ)) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hγ)
  rw [integral_exp_mul_complex hc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [norm_div]
  have h_den : ‖(Complex.I * (↑γ : ℂ))‖ = |γ| := by
    rw [norm_mul, Complex.norm_I, one_mul]
    simp [Complex.norm_real, Real.norm_eq_abs]
  rw [h_den]
  have h_num : ‖Complex.exp (Complex.I * ↑γ * ↑T) - 1‖ ≤ 2 := by
    calc ‖Complex.exp (Complex.I * ↑γ * ↑T) - 1‖
        ≤ ‖Complex.exp (Complex.I * ↑γ * ↑T)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_exp_I_mul_real, norm_one]; norm_num
  exact div_le_div_of_nonneg_right h_num (abs_pos.mpr hγ).le

/-! ## Cesàro mean convergence -/

/-- The Cesàro mean of a complex exponential converges to 0.
Specifically, (1/T)·‖∫₀ᵀ e^{iγu} du‖ → 0 as T → ∞ for γ ≠ 0.

PROOF: From `exp_integral_bound`, (1/T)·‖∫‖ ≤ 2/(|γ|·T) → 0. -/
theorem cesaro_exp_norm_tendsto_zero (γ : ℝ) (hγ : γ ≠ 0) :
    Tendsto (fun T : ℝ => (1 / T) * ‖∫ u in (0 : ℝ)..T,
      Complex.exp (Complex.I * (↑γ : ℂ) * ↑u)‖) atTop (nhds 0) := by
  have hγ_pos : (0 : ℝ) < |γ| := abs_pos.mpr hγ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    (show Tendsto (fun T : ℝ => (2 / |γ|) * T⁻¹) atTop (nhds 0) from by
      rw [show (0 : ℝ) = (2 / |γ|) * 0 from by ring]
      exact tendsto_inv_atTop_zero.const_mul _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact mul_nonneg (div_nonneg one_pos.le (by linarith)) (norm_nonneg _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hT_pos : 0 < T := by linarith
    calc (1 / T) * ‖∫ u in (0:ℝ)..T, Complex.exp (I * ↑γ * ↑u)‖
        ≤ (1 / T) * (2 / |γ|) :=
          mul_le_mul_of_nonneg_left (exp_integral_bound γ hγ T)
            (div_nonneg one_pos.le hT_pos.le)
      _ = (2 / |γ|) * T⁻¹ := by rw [one_div]; ring

/-! ## One-sided bound lemma -/

/-- **One-sided zero absolute mean**: If f : ℝ → ℝ satisfies:
  (i)  |f(u)| ≤ B for all u,
  (ii) f(u) ≤ 0 for u ≥ u₀,
  (iii) (1/T)∫₀ᵀ f → 0 as T → ∞,
then (1/T)∫₀ᵀ |f| → 0 as T → ∞.

PROVED: For u ≥ u₀, |f(u)| + f(u) = 0, so ∫₀ᵀ |f| = C - ∫₀ᵀ f where
C = ∫₀^{u₀}(|f|+f) is constant. Both C/T → 0 and (1/T)∫₀ᵀ f → 0. -/
theorem one_sided_zero_abs_mean
    (f : ℝ → ℝ) (B : ℝ) (u₀ : ℝ)
    (_hB : ∀ u, |f u| ≤ B)
    (hf_neg : ∀ u, u ≥ u₀ → f u ≤ 0)
    (hf_int : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hf_mean : Tendsto (fun T => (1 / T) * ∫ u in (0 : ℝ)..T, f u) atTop (nhds 0)) :
    Tendsto (fun T => (1 / T) * ∫ u in (0 : ℝ)..T, |f u|) atTop (nhds 0) := by
  -- |f| is integrable (since ‖·‖ = |·| for reals)
  have hf_abs_int : ∀ a b : ℝ, IntervalIntegrable (fun u => |f u|) volume a b :=
    fun a b => (hf_int a b).norm
  -- |f(u)| + f(u) = 0 for u ≥ u₀
  have h_sum_zero : ∀ u, u ≥ u₀ → |f u| + f u = 0 := by
    intro u hu
    rw [abs_of_nonpos (hf_neg u hu)]
    ring
  -- Define C = ∫₀^{u₀} (|f| + f)
  set C := ∫ u in (0 : ℝ)..u₀, (|f u| + f u) with hC_def
  -- For T ≥ u₀: ∫₀ᵀ (|f| + f) = C
  have h_sum_eq : ∀ T, u₀ ≤ T →
      ∫ u in (0 : ℝ)..T, (|f u| + f u) = C := by
    intro T hT
    have h_zero : ∫ u in u₀..T, (|f u| + f u) = 0 := by
      rw [← intervalIntegral.integral_zero (a := u₀) (b := T)]
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.mem_uIcc] at hu
      apply h_sum_zero
      rcases hu with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · linarith
    have h_split := intervalIntegral.integral_add_adjacent_intervals
          ((hf_abs_int 0 u₀).add (hf_int 0 u₀))
          ((hf_abs_int u₀ T).add (hf_int u₀ T))
    linarith
  -- For T ≥ u₀: ∫₀ᵀ |f| = C - ∫₀ᵀ f
  have h_abs_eq : ∀ T, u₀ ≤ T →
      ∫ u in (0 : ℝ)..T, |f u| = C - ∫ u in (0 : ℝ)..T, f u := by
    intro T hT
    have h_add := intervalIntegral.integral_add (hf_abs_int 0 T) (hf_int 0 T)
    have h_eq := h_sum_eq T hT
    linarith
  -- C·T⁻¹ → 0
  have h_CT : Tendsto (fun T : ℝ => C * T⁻¹) atTop (nhds 0) := by
    rw [show (0 : ℝ) = C * 0 from (mul_zero C).symm]
    exact tendsto_const_nhds.mul tendsto_inv_atTop_zero
  -- C·T⁻¹ - (1/T)∫f → 0 - 0 = 0
  have h_lim : Tendsto (fun T : ℝ =>
      C * T⁻¹ - (1 / T) * ∫ u in (0 : ℝ)..T, f u) atTop (nhds 0) := by
    have := h_CT.sub hf_mean
    rwa [sub_zero] at this
  -- Transfer: rhs → lhs via eventual equality
  refine h_lim.congr' ?_
  filter_upwards [eventually_ge_atTop u₀] with T hT
  rw [h_abs_eq T hT]; ring

/-- **One-sided zero L² mean**: If f : ℝ → ℝ satisfies:
  (i)  |f(u)| ≤ B for all u,
  (ii) f(u) ≤ 0 for u ≥ u₀,
  (iii) (1/T)∫₀ᵀ f → 0 as T → ∞,
then (1/T)∫₀ᵀ f² → 0 as T → ∞.

PROVED: Squeeze between 0 and B·(1/T)∫|f|. The pointwise bound
f² = |f|² ≤ B·|f| (from |f| ≤ B) gives ∫f² ≤ B·∫|f|, and
`one_sided_zero_abs_mean` provides (1/T)∫|f| → 0. -/
theorem one_sided_zero_l2_mean
    (f : ℝ → ℝ) (B : ℝ) (hB_pos : 0 < B) (u₀ : ℝ)
    (hB : ∀ u, |f u| ≤ B)
    (hf_neg : ∀ u, u ≥ u₀ → f u ≤ 0)
    (hf_int : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hf_mean : Tendsto (fun T => (1 / T) * ∫ u in (0 : ℝ)..T, f u) atTop (nhds 0)) :
    Tendsto (fun T => (1 / T) * ∫ u in (0 : ℝ)..T, (f u) ^ 2) atTop (nhds 0) := by
  have h_abs := one_sided_zero_abs_mean f B u₀ hB hf_neg hf_int hf_mean
  have hf_abs_int : ∀ a b : ℝ, IntervalIntegrable (fun u => |f u|) volume a b :=
    fun a b => (hf_int a b).norm
  -- Key pointwise bound: f² ≤ B·|f|
  have h_pw : ∀ u, (f u) ^ 2 ≤ B * |f u| := by
    intro u
    calc (f u) ^ 2 = |f u| ^ 2 := by rw [sq_abs]
      _ = |f u| * |f u| := by ring
      _ ≤ B * |f u| := mul_le_mul_of_nonneg_right (hB u) (abs_nonneg _)
  -- Upper bound: B * (1/T * ∫|f|) → 0
  have h_upper : Tendsto (fun T : ℝ => B * ((1 / T) * ∫ u in (0 : ℝ)..T, |f u|))
      atTop (nhds 0) := by
    have := (tendsto_const_nhds (x := B)).mul h_abs
    rwa [mul_zero] at this
  -- Squeeze: 0 ≤ (1/T)∫f² ≤ B·(1/T)∫|f| → 0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ => (0 : ℝ))
    (h := fun T => B * ((1 / T) * ∫ u in (0 : ℝ)..T, |f u|))
    tendsto_const_nhds h_upper
  · -- 0 ≤ (1/T)∫f²
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    apply mul_nonneg (by positivity)
    exact intervalIntegral.integral_nonneg (by linarith) (fun u _ => sq_nonneg _)
  · -- (1/T)∫f² ≤ B·(1/T)∫|f|
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hT_pos : (0 : ℝ) < T := by linarith
    show 1 / T * ∫ u in (0:ℝ)..T, (f u) ^ 2 ≤ B * (1 / T * ∫ u in (0:ℝ)..T, |f u|)
    calc 1 / T * ∫ u in (0:ℝ)..T, (f u) ^ 2
        ≤ 1 / T * ∫ u in (0:ℝ)..T, B * |f u| := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply intervalIntegral.integral_mono_on (by linarith)
          · apply IntervalIntegrable.mono_fun (intervalIntegrable_const (c := B ^ 2))
            · exact ((intervalIntegrable_iff.mp (hf_int 0 T)).aestronglyMeasurable).pow 2
            · exact ae_of_all _ fun u => by
                show ‖f u ^ 2‖ ≤ |B ^ 2|
                have h1 : f u ^ 2 ≤ B ^ 2 :=
                  sq_le_sq' ((abs_le.mp (hB u)).1) ((abs_le.mp (hB u)).2)
                rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
                exact h1
          · exact (hf_abs_int 0 T).const_mul B
          · intro u _; exact h_pw u
      _ = 1 / T * (B * ∫ u in (0:ℝ)..T, |f u|) := by
          congr 1
          exact intervalIntegral.integral_const_mul B _
      _ = B * (1 / T * ∫ u in (0:ℝ)..T, |f u|) := by ring

/-! ## Parseval identity for finite trigonometric sums -/

/-- Parseval identity for finite sums of complex exponentials:
  M(|∑ₖ cₖ e^{iγₖu}|²) = ∑ₖ |cₖ|²
when the frequencies γₖ are distinct and nonzero.

More precisely: for distinct nonzero reals γ₁,...,γₙ and complex c₁,...,cₙ,
  lim_{T→∞} (1/T)∫₀ᵀ |∑ₖ cₖ e^{iγₖu}|² du = ∑ₖ |cₖ|²

PROOF SKETCH:
  |∑ cₖ e^{iγₖu}|² = ∑_{j,k} cⱼ c̄ₖ e^{i(γⱼ-γₖ)u}.
  Taking Cesàro means, the cross terms (j≠k) vanish by
  `cesaro_exp_norm_tendsto_zero` (since γⱼ-γₖ ≠ 0).
  The diagonal terms (j=k) contribute |cⱼ|². -/
theorem parseval_finite_trig_sum
    {n : ℕ} (γ : Fin n → ℝ) (c : Fin n → ℂ)
    (hγ_distinct : Function.Injective γ)
    (hγ_nonzero : ∀ k, γ k ≠ 0) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ u in (0 : ℝ)..T,
      ‖∑ k : Fin n, c k * Complex.exp (Complex.I * ↑(γ k) * ↑u)‖ ^ 2)
      atTop (nhds (∑ k : Fin n, ‖c k‖ ^ 2)) := by
  sorry

end Aristotle.AlmostPeriodicMeanValue
