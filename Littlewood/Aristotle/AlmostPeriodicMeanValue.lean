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

STATUS: ALL 7 lemmas proved (0 sorries).
NOT imported by the main build yet — ready for integration.

REFERENCES:
  - Landau, "Über einen Satz von Tschebyschef" (1905)
  - Bohr, "Fastperiodische Funktionen" (1925)
  - Montgomery-Vaughan, "Multiplicative Number Theory I", §15.1
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

namespace Aristotle.AlmostPeriodicMeanValue

open Complex Filter MeasureTheory Topology Real Finset

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

/-- **Cesàro mean of Re(d·exp(iδu)) → 0**: For any d : ℂ and nonzero δ : ℝ,
  (1/T)∫₀ᵀ Re(d·e^{iδu}) du → 0 as T → ∞.

PROOF: Factor out d from the integral, bound |Re(z)| ≤ ‖z‖, then
use `cesaro_exp_norm_tendsto_zero` on the exponential part. -/
theorem cesaro_re_cmul_exp_tendsto_zero (d : ℂ) (δ : ℝ) (hδ : δ ≠ 0) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ u in (0 : ℝ)..T,
      (d * Complex.exp (Complex.I * ↑δ * ↑u)).re) atTop (nhds 0) := by
  have h_bound : Tendsto (fun T : ℝ => ‖d‖ * ((1 / T) *
      ‖∫ u in (0:ℝ)..T, exp (I * ↑δ * ↑u)‖)) atTop (nhds 0) := by
    have := (cesaro_exp_norm_tendsto_zero δ hδ).const_mul ‖d‖
    rwa [mul_zero] at this
  refine squeeze_zero_norm' ?_ h_bound
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hT_pos : (0 : ℝ) < T := by linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/T)]
  have hf_int : IntervalIntegrable (fun u => d * exp (I * ↑δ * ↑u)) volume 0 T :=
    (continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).intervalIntegrable 0 T
  have h_re_comm : ∫ u in (0:ℝ)..T, (d * exp (I * ↑δ * ↑u)).re =
      (∫ u in (0:ℝ)..T, d * exp (I * ↑δ * ↑u)).re := by
    simp only [← Complex.reCLM_apply]
    exact (Complex.reCLM.intervalIntegral_comp_comm hf_int)
  rw [h_re_comm]
  calc (1 / T) * |(∫ u in (0:ℝ)..T, d * exp (I * ↑δ * ↑u)).re|
      ≤ (1 / T) * ‖∫ u in (0:ℝ)..T, d * exp (I * ↑δ * ↑u)‖ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Complex.abs_re_le_norm _
    _ = (1 / T) * ‖d * ∫ u in (0:ℝ)..T, exp (I * ↑δ * ↑u)‖ := by
        congr 1; rw [← intervalIntegral.integral_const_mul]
    _ = (1 / T) * (‖d‖ * ‖∫ u in (0:ℝ)..T, exp (I * ↑δ * ↑u)‖) := by
        rw [norm_mul]
    _ = ‖d‖ * ((1 / T) * ‖∫ u in (0:ℝ)..T, exp (I * ↑δ * ↑u)‖) := by ring

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

private lemma inner_eq_re_conj_mul (z w : ℂ) :
    @inner ℝ ℂ _ z w = (starRingEnd ℂ z * w).re := by
  simp [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

private lemma norm_cmul_cexp (c : ℂ) (γ u : ℝ) :
    ‖c * cexp (I * ↑γ * ↑u)‖ = ‖c‖ := by
  rw [norm_mul, Complex.norm_exp]
  simp [Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Real.exp_zero, mul_one]

private lemma conj_cexp_mul_cexp (γ δ u : ℝ) :
    starRingEnd ℂ (cexp (I * ↑γ * ↑u)) * cexp (I * ↑δ * ↑u) =
    cexp (I * ↑(δ - γ) * ↑u) := by
  have h : starRingEnd ℂ (cexp (I * ↑γ * ↑u)) = cexp (starRingEnd ℂ (I * ↑γ * ↑u)) := by
    rw [← Complex.exp_conj]
  rw [h]; simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma cross_term_eq
    {n : ℕ} (γ' : Fin n → ℝ) (c' : Fin n → ℂ)
    (c_last : ℂ) (γ_last : ℝ) (u : ℝ) :
    @inner ℝ ℂ _ (∑ k : Fin n, c' k * cexp (I * ↑(γ' k) * ↑u))
                  (c_last * cexp (I * ↑γ_last * ↑u)) =
    ∑ k : Fin n, (starRingEnd ℂ (c' k) * c_last *
      cexp (I * ↑(γ_last - γ' k) * ↑u)).re := by
  rw [inner_eq_re_conj_mul]
  have h : starRingEnd ℂ (∑ k : Fin n, c' k * cexp (I * ↑(γ' k) * ↑u)) *
      (c_last * cexp (I * ↑γ_last * ↑u)) =
      ∑ k : Fin n, starRingEnd ℂ (c' k) * c_last *
        cexp (I * ↑(γ_last - γ' k) * ↑u) := by
    rw [map_sum, Finset.sum_mul]
    congr 1; ext k
    simp only [map_mul]
    calc starRingEnd ℂ (c' k) * starRingEnd ℂ (cexp (I * ↑(γ' k) * ↑u)) *
          (c_last * cexp (I * ↑γ_last * ↑u))
        = starRingEnd ℂ (c' k) * c_last *
          (starRingEnd ℂ (cexp (I * ↑(γ' k) * ↑u)) * cexp (I * ↑γ_last * ↑u)) := by ring
      _ = starRingEnd ℂ (c' k) * c_last *
          cexp (I * ↑(γ_last - γ' k) * ↑u) := by rw [conj_cexp_mul_cexp]
  rw [h]
  exact_mod_cast map_sum Complex.reAddGroupHom _ _

private lemma cross_term_cesaro_zero
    {n : ℕ} (γ' : Fin n → ℝ) (c' : Fin n → ℂ)
    (c_last : ℂ) (γ_last : ℝ)
    (h_distinct : ∀ k, γ' k ≠ γ_last) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ u in (0 : ℝ)..T,
      @inner ℝ ℂ _ (∑ k : Fin n, c' k * cexp (I * ↑(γ' k) * ↑u))
                    (c_last * cexp (I * ↑γ_last * ↑u)))
      atTop (nhds 0) := by
  simp_rw [cross_term_eq]
  have h_int : ∀ k : Fin n, ∀ a b : ℝ,
      IntervalIntegrable (fun u => (starRingEnd ℂ (c' k) * c_last *
        cexp (I * ↑(γ_last - γ' k) * ↑u)).re) volume a b := by
    intro k a b; apply Continuous.intervalIntegrable
    exact Complex.continuous_re.comp (continuous_const.mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)))
  have h_swap : ∀ T : ℝ,
      ∫ u in (0:ℝ)..T, ∑ k : Fin n,
        (starRingEnd ℂ (c' k) * c_last * cexp (I * ↑(γ_last - γ' k) * ↑u)).re =
      ∑ k : Fin n, ∫ u in (0:ℝ)..T,
        (starRingEnd ℂ (c' k) * c_last * cexp (I * ↑(γ_last - γ' k) * ↑u)).re :=
    fun T => intervalIntegral.integral_finset_sum (fun k _ => h_int k 0 T)
  simp_rw [h_swap, Finset.mul_sum]
  have h_each : ∀ k : Fin n, Tendsto (fun T : ℝ => 1 / T *
      ∫ u in (0:ℝ)..T, (starRingEnd ℂ (c' k) * c_last *
        cexp (I * ↑(γ_last - γ' k) * ↑u)).re) atTop (nhds 0) :=
    fun k => cesaro_re_cmul_exp_tendsto_zero _ _ (sub_ne_zero.mpr (h_distinct k).symm)
  have := tendsto_finset_sum Finset.univ (fun k _ => h_each k)
  simp only [Finset.sum_const_zero] at this; exact this

private lemma continuous_trig_sum {n : ℕ} (γ : Fin n → ℝ) (c : Fin n → ℂ) :
    Continuous (fun u : ℝ => ∑ k : Fin n, c k * cexp (I * ↑(γ k) * ↑u)) :=
  continuous_finset_sum _ fun _ _ =>
    continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))

/-- Parseval identity for finite sums of complex exponentials:
  M(|∑ₖ cₖ e^{iγₖu}|²) = ∑ₖ |cₖ|²
when the frequencies γₖ are distinct and nonzero.

More precisely: for distinct nonzero reals γ₁,...,γₙ and complex c₁,...,cₙ,
  lim_{T→∞} (1/T)∫₀ᵀ |∑ₖ cₖ e^{iγₖu}|² du = ∑ₖ |cₖ|²

PROOF: Induction on n. Base: n=0 trivial. Step: decompose sum into
first n terms S(u) plus last term b(u). Then ‖S+b‖² = ‖S‖² + 2⟨S,b⟩ + ‖b‖².
The IH handles ‖S‖², cross terms vanish by `cross_term_cesaro_zero`,
and ‖b‖² = ‖c_last‖² is constant. -/
theorem parseval_finite_trig_sum
    {n : ℕ} (γ : Fin n → ℝ) (c : Fin n → ℂ)
    (hγ_distinct : Function.Injective γ)
    (hγ_nonzero : ∀ k, γ k ≠ 0) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ u in (0 : ℝ)..T,
      ‖∑ k : Fin n, c k * Complex.exp (Complex.I * ↑(γ k) * ↑u)‖ ^ 2)
      atTop (nhds (∑ k : Fin n, ‖c k‖ ^ 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    set γ' := γ ∘ Fin.castSucc
    set c' := c ∘ Fin.castSucc
    set c_last := c (Fin.last n)
    set γ_last := γ (Fin.last n)
    set S := fun u : ℝ => ∑ i : Fin n, c' i * cexp (I * ↑(γ' i) * ↑u)
    set bt := fun u : ℝ => c_last * cexp (I * ↑γ_last * ↑u)
    have hγ'_inj : Function.Injective γ' := hγ_distinct.comp (Fin.castSucc_injective n)
    have hγ'_nz : ∀ k, γ' k ≠ 0 := fun k => hγ_nonzero _
    have h_dist : ∀ k : Fin n, γ' k ≠ γ_last :=
      fun k => hγ_distinct.ne (Fin.castSucc_lt_last k).ne
    have h_ih := ih γ' c' hγ'_inj hγ'_nz
    have h_sum_eq : ∀ u : ℝ,
        ∑ i : Fin (n + 1), c i * cexp (I * ↑(γ i) * ↑u) = S u + bt u :=
      fun u => Fin.sum_univ_castSucc _
    rw [show ∑ i : Fin (n + 1), ‖c i‖ ^ 2 =
        (∑ i : Fin n, ‖c' i‖ ^ 2) + ‖c_last‖ ^ 2 from Fin.sum_univ_castSucc _]
    simp_rw [h_sum_eq]
    -- Continuity & integrability
    have hS_cont : Continuous S := continuous_trig_sum γ' c'
    have hbt_cont : Continuous bt := continuous_const.mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
    have hS2_int : ∀ a b : ℝ, IntervalIntegrable (fun u => ‖S u‖ ^ 2) volume a b :=
      fun a b => (hS_cont.norm.pow 2).intervalIntegrable a b
    have hI_int : ∀ a b : ℝ,
        IntervalIntegrable (fun u => @inner ℝ ℂ _ (S u) (bt u)) volume a b :=
      fun a b => (hS_cont.inner hbt_cont).intervalIntegrable a b
    have h_bt_norm : ∀ u : ℝ, ‖bt u‖ = ‖c_last‖ := fun u => norm_cmul_cexp c_last γ_last u
    -- Integral decomposition
    have h_int_decomp : ∀ T : ℝ, 0 < T →
        ∫ u in (0:ℝ)..T, ‖S u + bt u‖ ^ 2 =
        (∫ u in (0:ℝ)..T, ‖S u‖ ^ 2) +
        2 * (∫ u in (0:ℝ)..T, @inner ℝ ℂ _ (S u) (bt u)) +
        T * ‖c_last‖ ^ 2 := by
      intro T _
      have hp : ∀ u, ‖S u + bt u‖ ^ 2 =
          ‖S u‖ ^ 2 + 2 * @inner ℝ ℂ _ (S u) (bt u) + ‖c_last‖ ^ 2 := by
        intro u; rw [norm_add_sq_real, h_bt_norm]
      simp_rw [hp]
      have h1 := intervalIntegral.integral_add
        ((hS2_int 0 T).add ((hI_int 0 T).const_mul 2))
        (intervalIntegrable_const (c := ‖c_last‖ ^ 2))
      have h2 := intervalIntegral.integral_add (hS2_int 0 T) ((hI_int 0 T).const_mul 2)
      have h3 : ∫ u in (0:ℝ)..T, (2 : ℝ) * @inner ℝ ℂ _ (S u) (bt u) =
          (2 : ℝ) * ∫ u in (0:ℝ)..T, @inner ℝ ℂ _ (S u) (bt u) :=
        intervalIntegral.integral_const_mul ..
      have h4 : ∫ _ in (0:ℝ)..T, (‖c_last‖ ^ 2 : ℝ) = T * ‖c_last‖ ^ 2 := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]
      linarith
    -- Eventual equality
    have h_eq : ∀ᶠ T in atTop,
        (1 / T) * ∫ u in (0:ℝ)..T, ‖S u + bt u‖ ^ 2 =
        ((1 / T) * ∫ u in (0:ℝ)..T, ‖S u‖ ^ 2) +
        2 * ((1 / T) * ∫ u in (0:ℝ)..T, @inner ℝ ℂ _ (S u) (bt u)) +
        ‖c_last‖ ^ 2 := by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
      rw [h_int_decomp T hT]; field_simp
    -- Cross terms → 0
    have h_cross := cross_term_cesaro_zero γ' c' c_last γ_last h_dist
    -- Combined limit
    have h2 : Tendsto (fun T =>
        2 * ((1 / T) * ∫ u in (0:ℝ)..T, @inner ℝ ℂ _ (S u) (bt u)))
        atTop (nhds 0) := by
      have := h_cross.const_mul 2; rwa [mul_zero] at this
    have h_combined : Tendsto (fun T =>
        ((1 / T) * ∫ u in (0:ℝ)..T, ‖S u‖ ^ 2) +
        2 * ((1 / T) * ∫ u in (0:ℝ)..T, @inner ℝ ℂ _ (S u) (bt u)) +
        ‖c_last‖ ^ 2)
        atTop (nhds ((∑ i : Fin n, ‖c' i‖ ^ 2) + ‖c_last‖ ^ 2)) := by
      have := (h_ih.add h2).add (tendsto_const_nhds (x := ‖c_last‖ ^ 2))
      simp only [add_zero] at this; exact this
    exact h_combined.congr' (h_eq.mono fun _ h => h.symm)

end Aristotle.AlmostPeriodicMeanValue
