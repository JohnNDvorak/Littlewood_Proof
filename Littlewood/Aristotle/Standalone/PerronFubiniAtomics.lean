/-
# Perron Fubini Atomics

Atomic sub-lemmas for the Perron formula: Sorry 1 (Euler product / Dirichlet
series identity) and Sorry 2 (Fubini sum-integral interchange).

## Sorry 1 atoms
The Dirichlet series identity -ζ'/ζ(s) = Σ Λ(n)/n^s for Re(s) > 1 is
already proved in `StrongPNTLogDerivSeriesCompat`. We provide a wrapper.

## Sorry 2 atoms
Concrete Mathlib computations: re/im extraction, non-vanishing of c+ti,
continuity of x^(c+ti), integrability on compact intervals, norm bounds,
and summability for the Fubini interchange.

SORRY COUNT: 0

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTLogDerivSeriesCompat
import Littlewood.Aristotle.Standalone.PerronKernelAtomics
import Littlewood.Aristotle.Standalone.PerronKernelBound

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

open Complex Real MeasureTheory Set Filter
open scoped BigOperators LSeries.notation

noncomputable section

namespace Aristotle.Standalone.PerronFubiniAtomics

open Aristotle.Standalone.ExternalPort.StrongPNTLogDerivSeriesCompat
  in
private alias sldc := neg_logDeriv_riemannZeta_eq_vonMangoldt_tsum_of_re_gt_one

open Aristotle.Standalone.ExternalPort.DirichletNonvanishingCompat
  in
private alias sldc_summable := summable_LSeries_term_vonMangoldt_port

open Aristotle.Standalone.ExternalPort.StrongPNTLogDerivSeriesCompat
  in
private alias sldc_line := neg_logDeriv_riemannZeta_eq_vonMangoldt_tsum_on_line

/-! ## Sorry 1 atoms: Dirichlet series identity wrapper -/

/-- **Sorry 1.3: Dirichlet series identity.**
For Re(s) > 1, the logarithmic derivative of ζ satisfies
  -ζ'(s)/ζ(s) = Σ_{n} Λ(n)/n^s
as a sum of LSeries terms. This is a direct wrapper around the proved theorem
in `StrongPNTLogDerivSeriesCompat`. -/
theorem dirichlet_series_identity (s : ℂ) (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
    ∑' n, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n :=
  sldc hs

/-- **Sorry 1 summability.**
The von Mangoldt LSeries terms are summable for Re(s) > 1. -/
theorem dirichlet_series_summable (s : ℂ) (hs : 1 < s.re) :
    Summable (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) :=
  sldc_summable hs

/-- **Sorry 1, line-specialized form.**
On the vertical line Re = σ > 1:
  -ζ'(σ+it)/ζ(σ+it) = Σ_{n} Λ(n)/n^{σ+it}. -/
theorem dirichlet_series_on_line {σ t : ℝ} (hσ : 1 < σ) :
    -deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I) =
    ∑' n : ℕ, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (σ + t * I) n :=
  sldc_line hσ

/-! ## Sorry 2 atoms: Concrete Mathlib computations -/

/-- **2.1a: Re(c + t*I) = c.** -/
lemma perron_denom_re_eq (c t : ℝ) : ((c : ℂ) + (t : ℂ) * I).re = c := by
  simp only [add_re, ofReal_re, mul_re, ofReal_re, I_re, mul_zero,
    ofReal_im, I_im, mul_one, sub_zero, add_zero]

/-- **2.1b: Im(c + t*I) = t.** -/
lemma perron_denom_im_eq (c t : ℝ) : ((c : ℂ) + (t : ℂ) * I).im = t := by
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
    mul_one, ofReal_im, mul_zero, add_zero, zero_add]

/-- **2.1c: c + t*I ≠ 0 when c > 0.** -/
lemma perron_denom_ne_zero (c t : ℝ) (hc : 0 < c) :
    (c : ℂ) + (t : ℂ) * I ≠ 0 := by
  intro h
  have := congr_arg re h
  simp only [add_re, ofReal_re, mul_re, ofReal_re, I_re, mul_zero,
    ofReal_im, I_im, mul_one, sub_zero, add_zero, zero_re] at this
  linarith

/-- **2.1d: c + t*I ≠ 0 when c > 0** (Perron line non-vanishing, alternate name). -/
lemma vertical_line_ne_zero' (c : ℝ) (hc : 0 < c) (t : ℝ) :
    (c : ℂ) + (t : ℂ) * I ≠ 0 :=
  perron_denom_ne_zero c t hc

/-- **2.2a: x^(c+t*I) is continuous in t** for x > 0. -/
lemma cpow_continuous_in_t (x c : ℝ) (hx : 0 < x) :
    Continuous (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) := by
  apply Continuous.cpow continuous_const (by continuity)
  intro t
  left
  exact_mod_cast hx

/-- **2.2b: t ↦ (c + t*I)⁻¹ is continuous** for c > 0. -/
lemma inv_perron_continuous (c : ℝ) (hc : 0 < c) :
    Continuous (fun t : ℝ => ((c : ℂ) + (t : ℂ) * I)⁻¹) := by
  apply Continuous.inv₀ (by continuity)
  intro t
  exact perron_denom_ne_zero c t hc

/-- **2.2c: t ↦ x^(c+tI)/(c+tI) is continuous** for x > 0, c > 0. -/
lemma perron_integrand_continuous (x c : ℝ) (hx : 0 < x) (hc : 0 < c) :
    Continuous (fun t : ℝ =>
      (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) := by
  apply Continuous.div
  · exact cpow_continuous_in_t x c hx
  · continuity
  · intro t; exact perron_denom_ne_zero c t hc

/-- **2.3a: Integrability of x^(c+tI)/(c+tI) on [-T, T].**
From continuity on a compact interval. -/
lemma perron_kernel_integrable_on (x c T : ℝ) (hx : 0 < x) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ =>
      (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))
      (Icc (-T) T) := by
  exact (perron_integrand_continuous x c hx hc).continuousOn.integrableOn_compact
    isCompact_Icc

/-- **2.3b: Integrability of vonMangoldt-weighted Perron term on [-T, T].**
The integrand is a product of continuous functions, hence continuous on ℝ,
hence integrable on the compact interval [-T, T]. -/
lemma perron_term_integrable_on (x c T : ℝ) (hx : 0 < x) (hc : 0 < c)
    (_hT : 0 < T) (n : ℕ) :
    IntegrableOn (fun t : ℝ =>
      (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ)^((c : ℂ) + (t : ℂ)*I) *
      ((x : ℂ)^((c : ℂ) + (t : ℂ)*I) / ((c : ℂ) + (t : ℂ)*I)))
      (Icc (-T) T) := by
  -- The integrand is const * (continuous in t), hence continuous, hence integrable
  -- on the compact set Icc (-T) T.
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  -- Strategy: bound by a continuous function. The Λ(n) factor is constant.
  -- For n = 0: Λ(0) = 0, so the whole integrand is 0, which is trivially continuous.
  -- For n ≥ 1: n^s is nonzero (since (n:ℂ) ≠ 0), so we have a product of
  -- continuous functions divided by a nonvanishing denominator.
  by_cases hn : n = 0
  · -- n = 0: Λ(0) = 0 (ArithmeticFunction maps 0 to 0), integrand is 0
    subst hn
    simp only [Nat.cast_zero, ArithmeticFunction.map_zero,
      ofReal_zero, zero_div, zero_mul]
    exact continuousOn_const
  · -- n ≥ 1: product of continuous functions
    apply ContinuousOn.mul
    · have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      apply ContinuousOn.div continuousOn_const
      · apply Continuous.continuousOn
        apply Continuous.cpow continuous_const (by continuity)
        intro _
        left
        simp [Nat.pos_of_ne_zero hn]
      · intro t _
        rw [ne_eq, cpow_eq_zero_iff, not_and_or]
        exact Or.inl hn_ne
    · exact (perron_integrand_continuous x c hx hc).continuousOn

/-- **2.4a: ‖x^(c+ti)‖ = x^c.** Re-export from PerronKernelAtomics. -/
theorem norm_cpow_real_exponent (x c t : ℝ) (hx : 0 < x) :
    ‖(x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ = x ^ c :=
  PerronKernelAtomics.norm_cpow_real_exponent x c t hx

/-- **2.4b: c ≤ ‖c + ti‖.** Re-export from PerronKernelAtomics. -/
theorem norm_perron_denom_ge (c t : ℝ) (hc : 0 < c) :
    c ≤ ‖(c : ℂ) + (t : ℂ) * I‖ := by
  rw [Complex.norm_add_mul_I]
  calc c = Real.sqrt (c ^ 2) := by rw [Real.sqrt_sq (le_of_lt hc)]
    _ ≤ Real.sqrt (c ^ 2 + t ^ 2) := by
        apply Real.sqrt_le_sqrt; linarith [sq_nonneg t]

/-- **2.4c: ‖x^(c+ti)/(c+ti)‖ ≤ x^c / c** for x > 0, c > 0. -/
theorem perron_integrand_norm_bound (x c t : ℝ) (hx : 0 < x) (hc : 0 < c) :
    ‖(x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)‖ ≤
    x ^ c / c := by
  rw [norm_div, norm_cpow_real_exponent x c t hx]
  exact div_le_div_of_nonneg_left (rpow_pos_of_pos hx c).le hc
    (norm_perron_denom_ge c t hc)

/-- **2.5: Norm bound for the Perron vertical integral.**
‖∫_{-T}^{T} x^{c+it}/(c+it) dt‖ ≤ 2T·x^c/c. Re-export from PerronKernelBound. -/
theorem perron_vertical_norm_bound (x c T : ℝ) (hx : 0 < x) (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t in (-T)..T,
      (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)‖ ≤
    2 * T * x ^ c / c :=
  Aristotle.Standalone.PerronKernelBound.perron_vertical_crude_bound hx hc hT

/-- **2.6a: Λ(n) ≥ 0.** Direct from Mathlib. -/
theorem vonMangoldt_nonneg' (n : ℕ) :
    0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
  ArithmeticFunction.vonMangoldt_nonneg

/-- **2.6b: LSeries summability for Re(s) > 1.** -/
theorem vonMangoldt_lseries_summable' {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (↗ArithmeticFunction.vonMangoldt) s :=
  ArithmeticFunction.LSeriesSummable_vonMangoldt hs

/-- **2.6c: Summability of Λ(n)/n^c for c > 1** (real-valued version).
This is the key summability fact for the Fubini domination argument.
Follows the same pattern as `PerronTruncationInfra.vonMangoldt_weighted_summable`. -/
lemma vonMangoldt_div_rpow_summable (c : ℝ) (hc : 1 < c) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)^c) := by
  -- Strategy: show Λ(n)/n^c = ‖LSeries.term (↗Λ) c n‖, then use .norm summability.
  have h_ls := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (c : ℂ)) (by simp [ofReal_re]; exact hc)
  have h_eq : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ c) =
      (fun n : ℕ => ‖LSeries.term (↗ArithmeticFunction.vonMangoldt) (↑c) n‖) := by
    ext n
    by_cases hn : n = 0
    · subst hn; simp [LSeries.term]
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      simp only [LSeries.term, if_neg hn]
      rw [norm_div, norm_natCast_cpow_of_pos hn_pos,
          show ((c : ℂ)).re = c from ofReal_re c]
      congr 1
      simp [Complex.norm_real, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  rw [h_eq]
  exact h_ls.norm

/-- **2.7: Norm summability for integral_tsum (Fubini domination).**
The integrals ∫_{-T}^T ‖ term_n ‖ are summable over n. This is the
domination condition needed for `MeasureTheory.integral_tsum` or
`tsum_integral_eq_integral_tsum`. -/
lemma perron_norm_sum_finite (x c T : ℝ) (hx : 2 ≤ x) (hc : 1 < c)
    (hT : 0 < T) :
    Summable (fun n : ℕ => ∫ t in Icc (-T) T,
      ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ)^((c:ℂ)+(t:ℂ)*I) *
       ((x:ℂ)^((c:ℂ)+(t:ℂ)*I) / ((c:ℂ)+(t:ℂ)*I))‖) := by
  -- Each integral is bounded by 2T * Λ(n) * x^c / (n^c * c),
  -- and Σ Λ(n)/n^c converges for c > 1.
  have hx_pos : (0 : ℝ) < x := by linarith
  have hc_pos : (0 : ℝ) < c := by linarith
  -- Step 1: Pointwise norm bound
  -- ‖Λ(n)/n^s * x^s/(c+ti)‖ ≤ Λ(n)/n^c * x^c/c
  have h_ptwise : ∀ n : ℕ, ∀ t : ℝ,
      ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ)^((c:ℂ)+(t:ℂ)*I) *
       ((x:ℂ)^((c:ℂ)+(t:ℂ)*I) / ((c:ℂ)+(t:ℂ)*I))‖ ≤
      (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)^c * (x^c / c) := by
    intro n t
    by_cases hn : n = 0
    · subst hn; simp [ArithmeticFunction.map_zero]
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      rw [norm_mul, norm_div, norm_div]
      -- ‖Λ(n)‖ = Λ(n) (nonneg real cast)
      have h_vnorm : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ =
          (ArithmeticFunction.vonMangoldt n : ℝ) := by
        simp [Complex.norm_real, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      -- ‖n^s‖ = n^c
      have h_nnorm : ‖(n : ℂ)^((c:ℂ)+(t:ℂ)*I)‖ = (n : ℝ)^c := by
        rw [norm_natCast_cpow_of_pos hn_pos]
        simp [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
      -- ‖x^s‖ = x^c
      have h_xnorm : ‖(x:ℂ)^((c:ℂ)+(t:ℂ)*I)‖ = x^c :=
        norm_cpow_real_exponent x c t hx_pos
      rw [h_vnorm, h_nnorm, h_xnorm]
      -- Goal: Λ(n)/n^c * (x^c / ‖c+ti‖) ≤ Λ(n)/n^c * (x^c / c)
      apply mul_le_mul_of_nonneg_left
      · -- x^c / ‖c+ti‖ ≤ x^c / c
        apply div_le_div_of_nonneg_left (rpow_pos_of_pos hx_pos c).le hc_pos
          (norm_perron_denom_ge c t hc_pos)
      · -- Λ(n)/n^c ≥ 0
        apply div_nonneg
        · exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg
        · exact rpow_nonneg (Nat.cast_nonneg n) c
  -- Step 2: Each integral ≤ (2T * x^c / c) * Λ(n)/n^c
  -- via ∫ ‖term‖ ≤ ∫ (bound) = measure(Icc) * bound
  set K := 2 * T * x ^ c / c with hK_def
  -- Step 3: The dominating series is summable
  have h_dom : Summable (fun n : ℕ => K * ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)^c)) :=
    (vonMangoldt_div_rpow_summable c hc).const_smul K
  -- Step 4: Apply Summable.of_nonneg_of_le
  apply Summable.of_nonneg_of_le
  · -- Each integral is ≥ 0 (integral of nonneg function)
    intro n; exact setIntegral_nonneg measurableSet_Icc (fun t _ => norm_nonneg _)
  · -- Each integral ≤ K * Λ(n)/n^c
    intro n
    have h_intble : IntegrableOn (fun t : ℝ =>
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ)^((c:ℂ)+(t:ℂ)*I) *
         ((x:ℂ)^((c:ℂ)+(t:ℂ)*I) / ((c:ℂ)+(t:ℂ)*I))‖) (Icc (-T) T) :=
      Integrable.norm (perron_term_integrable_on x c T hx_pos hc_pos hT n)
    calc ∫ t in Icc (-T) T,
          ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ)^((c:ℂ)+(t:ℂ)*I) *
           ((x:ℂ)^((c:ℂ)+(t:ℂ)*I) / ((c:ℂ)+(t:ℂ)*I))‖
        ≤ ∫ _ in Icc (-T) T,
          ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)^c * (x^c / c)) := by
          exact setIntegral_mono_on h_intble
            (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne))
            measurableSet_Icc (fun t _ => h_ptwise n t)
      _ = volume.real (Icc (-T) T) •
          ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)^c * (x^c / c)) := by
          rw [setIntegral_const]
      _ = K * ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ)^c) := by
          rw [Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
          simp only [hK_def]; ring
  · exact h_dom

/-! ## Assembly lemmas -/

/-- **Perron integrand continuity at the level of the full product.**
For n ≥ 1, x > 0, c > 0, the function
  t ↦ (-ζ'/ζ)(c+ti) · x^{c+ti} / (c+ti)
is continuous in t on the vertical line Re = c > 1. -/
theorem full_perron_integrand_continuous (x c : ℝ) (hx : 0 < x) (hc : 1 < c) :
    Continuous (fun t : ℝ =>
      (-deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) /
        riemannZeta ((c : ℂ) + (t : ℂ) * I)) *
      ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))) := by
  apply Continuous.mul
  · -- -ζ'/ζ is continuous on Re > 1 (holomorphic, non-vanishing)
    apply Continuous.div
    · apply Continuous.neg
      -- deriv ζ is continuous on Re > 1 (ζ is analytic there, so deriv is analytic)
      -- Build AnalyticOnNhd from DifferentiableOn on open set
      have h_diff_on : DifferentiableOn ℂ riemannZeta {s | 1 < s.re} := fun s hs =>
        (differentiableAt_riemannZeta (by intro h; rw [h] at hs; simp at hs)).differentiableWithinAt
      have h_open : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
      have h_analNhd : AnalyticOnNhd ℂ riemannZeta {s | 1 < s.re} :=
        h_diff_on.analyticOnNhd h_open
      -- The line map t ↦ c + t*I is continuous
      have hline : Continuous (fun t : ℝ => (c : ℂ) + (t : ℂ) * I) :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      -- Composition: (deriv ζ) ∘ (t ↦ c + t*I) is continuous
      -- Use ContinuousOn.comp with the open set {Re > 1}
      have hderiv_contOn : ContinuousOn (deriv riemannZeta) {s | 1 < s.re} :=
        h_analNhd.deriv.continuousOn
      have hrange : ∀ t : ℝ, (c : ℂ) + (t : ℂ) * I ∈ {s : ℂ | 1 < s.re} := by
        intro t; simp [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]; linarith
      exact (hderiv_contOn.comp_continuous hline (fun t => hrange t))
    · -- ζ is continuous on Re > 1 (differentiable implies continuous)
      have hline : Continuous (fun t : ℝ => (c : ℂ) + (t : ℂ) * I) :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      have hzeta_contOn : ContinuousOn riemannZeta {s | 1 < s.re} := by
        intro s hs
        exact (differentiableAt_riemannZeta (by intro h; rw [h] at hs; simp at hs)).continuousAt.continuousWithinAt
      have hrange : ∀ t : ℝ, (c : ℂ) + (t : ℂ) * I ∈ {s : ℂ | 1 < s.re} := by
        intro t; simp [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]; linarith
      exact (hzeta_contOn.comp_continuous hline (fun t => hrange t))
    · -- ζ(c+ti) ≠ 0 for c > 1
      intro t
      exact riemannZeta_ne_zero_of_one_le_re (by
        simp only [add_re, ofReal_re, mul_re, ofReal_re, I_re, mul_zero,
          ofReal_im, I_im, mul_one, sub_zero, add_zero]
        linarith)
  · exact perron_integrand_continuous x c hx (by linarith)

/-- **Full Perron integrand integrability on [-T, T].**
Since the integrand is continuous and [-T, T] is compact. -/
theorem full_perron_integrable (x c T : ℝ) (hx : 0 < x) (hc : 1 < c) :
    IntegrableOn (fun t : ℝ =>
      (-deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) /
        riemannZeta ((c : ℂ) + (t : ℂ) * I)) *
      ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)))
      (Icc (-T) T) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact (full_perron_integrand_continuous x c hx hc).continuousOn

end Aristotle.Standalone.PerronFubiniAtomics
