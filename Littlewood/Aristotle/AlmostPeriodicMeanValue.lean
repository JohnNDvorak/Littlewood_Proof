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

STATUS: Architecture file. norm_exp_I_mul_real is proved (0 sorry).
Other lemmas have correct types but sorry'd proofs — to be filled.
NOT imported by the main build (no effect on project sorry count).

REFERENCES:
  - Landau, "Über einen Satz von Tschebyschef" (1905)
  - Bohr, "Fastperiodische Funktionen" (1925)
  - Montgomery-Vaughan, "Multiplicative Number Theory I", §15.1
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 400000

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

/-- If f : ℝ → ℝ satisfies:
  (i)  |f(u)| ≤ B for all u,
  (ii) f(u) ≤ 0 for u ≥ u₀,
  (iii) (1/T)∫₀ᵀ f → 0 as T → ∞,
then (1/T)∫₀ᵀ |f| → 0 as T → ∞.

This is the key analysis lemma for Landau's oscillation argument:
one-sided bound + zero mean + boundedness implies zero absolute mean.

PROOF SKETCH:
  For T > u₀:
  (1/T)∫₀ᵀ |f| = (1/T)∫₀^{u₀} |f| + (1/T)∫_{u₀}^T |f|
  First term ≤ B·u₀/T → 0.
  For u ≥ u₀: f(u) ≤ 0, so |f(u)| = -f(u), hence
  (1/T)∫_{u₀}^T |f| = -(1/T)∫_{u₀}^T f = (1/T)∫₀^{u₀} f - (1/T)∫₀ᵀ f
  → 0 - 0 = 0.
  Thus (1/T)∫₀ᵀ |f| → 0. -/
theorem one_sided_zero_abs_mean
    (f : ℝ → ℝ) (B : ℝ) (u₀ : ℝ)
    (hB : ∀ u, |f u| ≤ B)
    (hf_neg : ∀ u, u ≥ u₀ → f u ≤ 0)
    (hf_mean : Tendsto (fun T => (1 / T) * ∫ u in (0 : ℝ)..T, f u) atTop (nhds 0)) :
    Tendsto (fun T => (1 / T) * ∫ u in (0 : ℝ)..T, |f u|) atTop (nhds 0) := by
  sorry

/-- If f : ℝ → ℝ satisfies:
  (i)  |f(u)| ≤ B for all u,
  (ii) f(u) ≤ 0 for u ≥ u₀,
  (iii) (1/T)∫₀ᵀ f → 0 as T → ∞,
then (1/T)∫₀ᵀ f² → 0 as T → ∞.

Corollary of `one_sided_zero_abs_mean`: since f² ≤ B·|f|, zero absolute
mean implies zero L² mean.

PROOF: f² = |f|² ≤ B·|f| (using |f| ≤ B), so
  (1/T)∫ f² ≤ B·(1/T)∫|f| → 0 by `one_sided_zero_abs_mean`. -/
theorem one_sided_zero_l2_mean
    (f : ℝ → ℝ) (B : ℝ) (hB_pos : 0 < B) (u₀ : ℝ)
    (hB : ∀ u, |f u| ≤ B)
    (hf_neg : ∀ u, u ≥ u₀ → f u ≤ 0)
    (hf_mean : Tendsto (fun T => (1 / T) * ∫ u in (0 : ℝ)..T, f u) atTop (nhds 0)) :
    Tendsto (fun T => (1 / T) * ∫ u in (0 : ℝ)..T, (f u) ^ 2) atTop (nhds 0) := by
  sorry

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
