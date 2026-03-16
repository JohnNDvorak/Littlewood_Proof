/-
Perron Formula: Sum-Integral Interchange for Dirichlet Series

Proves the core analytic fact: for c > 1, T > 0, x > 0,
the truncated contour integral of (-ζ'/ζ)(s)·x^s/s equals
the sum of per-term Perron integrals via dominated convergence.

Key theorem: `perron_sum_integral_interchange`

References: Davenport Ch. 17; Montgomery-Vaughan §5.1.

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

namespace Littlewood.Development.PerronFormulaProof

open Complex Real Set MeasureTheory Filter Topology
open scoped BigOperators LSeries.notation

/-! ## Section 1: Pointwise Tsum Identity -/

/-- Pointwise identity: the full Perron integrand is a tsum of L-series terms
    multiplied by x^s/s. Uses `tsum_mul_right` + `LSeries_vonMangoldt_eq`. -/
theorem pointwise_integrand_tsum (x : ℝ) (c t : ℝ) (hc : 1 < c) :
    (-deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) /
      riemannZeta ((c : ℂ) + (t : ℂ) * I)) *
     ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
      ((c : ℂ) + (t : ℂ) * I)) =
    ∑' n, LSeries.term (↗ArithmeticFunction.vonMangoldt)
      ((c : ℂ) + (t : ℂ) * I) n *
      ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
       ((c : ℂ) + (t : ℂ) * I)) := by
  have hs : 1 < ((c : ℂ) + (t : ℂ) * I).re := by
    simp only [add_re, ofReal_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_zero, add_zero]; linarith
  rw [tsum_mul_right]; congr 1
  exact (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs).symm

/-! ## Section 2: Norm Bounds -/

/-- ‖(n : ℂ)^s‖ = n^(Re s) for n ≥ 1. -/
theorem nat_cpow_norm {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re := by
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) from by push_cast; rfl]
  exact norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) s

/-- ‖LSeries.term(Λ, c+it, n)‖ = ‖LSeries.term(Λ, c, n)‖ — norm is independent of Im(s). -/
theorem lseries_term_norm_indep (n : ℕ) (c t : ℝ) :
    ‖LSeries.term (↗ArithmeticFunction.vonMangoldt) ((c : ℂ) + (t : ℂ) * I) n‖ =
    ‖LSeries.term (↗ArithmeticFunction.vonMangoldt) (c : ℂ) n‖ := by
  by_cases hn : n = 0
  · simp [LSeries.term, hn]
  · simp only [LSeries.term, hn, ↓reduceIte, norm_div]
    congr 1
    rw [nat_cpow_norm hn, nat_cpow_norm hn]
    simp [add_re, mul_re, I_re, I_im, ofReal_re]

/-- The denominator |c + it| ≥ c for c > 0. -/
theorem denom_ge_c {c t : ℝ} (hc : 0 < c) :
    c ≤ ‖(c : ℂ) + (t : ℂ) * I‖ := by
  calc (c : ℝ) = |c| := (abs_of_pos hc).symm
    _ = |((c : ℂ) + (t : ℂ) * I).re| := by congr 1; simp [add_re, mul_re, I_re, I_im]
    _ ≤ ‖(c : ℂ) + (t : ℂ) * I‖ := Complex.abs_re_le_norm _

/-- ‖x^{c+it}/(c+it)‖ ≤ x^c/c for x > 0, c > 0. -/
theorem xpow_div_s_bound {x : ℝ} (hx : 0 < x) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖(x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)‖ ≤ x ^ c / c := by
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos hx]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
    add_zero]
  gcongr; exact denom_ge_c hc

/-- Pointwise bound: ‖term_n(t) * x^s/s‖ ≤ ‖term_n(c)‖ * x^c/c. -/
theorem pointwise_bound {x : ℝ} (hx : 0 < x) {c : ℝ} (hc : 0 < c) (n : ℕ) (t : ℝ) :
    ‖LSeries.term (↗ArithmeticFunction.vonMangoldt) ((c : ℂ) + (t : ℂ) * I) n *
      ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))‖ ≤
    ‖LSeries.term (↗ArithmeticFunction.vonMangoldt) (c : ℂ) n‖ * (x ^ c / c) := by
  rw [norm_mul, lseries_term_norm_indep n c t]
  gcongr; exact xpow_div_s_bound hx hc t

/-! ## Section 3: Integrability -/

/-- c + it ≠ 0 for c > 0. -/
theorem s_ne_zero {c t : ℝ} (hc : 0 < c) : (c : ℂ) + (t : ℂ) * I ≠ 0 := by
  have : ((c : ℂ) + (t : ℂ) * I).re = c := by simp [add_re, mul_re, I_re, I_im]
  exact ne_of_apply_ne re (by rw [this, zero_re]; linarith)

/-- Each term is continuous in t. -/
theorem term_continuous {x : ℝ} (hx : 0 < x) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Continuous (fun t : ℝ =>
      LSeries.term (↗ArithmeticFunction.vonMangoldt) ((c : ℂ) + (t : ℂ) * I) n *
      ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))) := by
  apply Continuous.mul
  · unfold LSeries.term
    by_cases hn : n = 0
    · simp [hn]; exact continuous_const
    · simp [hn]
      apply Continuous.div
      · exact continuous_const
      · exact Continuous.cpow continuous_const (by continuity)
          (fun t => Or.inl (by simp; exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))
      · intro t
        have h_ne : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.cast_ne_zero.mpr hn
        exact cpow_ne_zero_iff.mpr (Or.inl h_ne)
  · apply Continuous.div
    · exact Continuous.cpow continuous_const (by continuity)
        (fun t => Or.inl (by simp; linarith))
    · exact continuous_const.add (continuous_ofReal.mul continuous_const)
    · intro t; exact s_ne_zero hc

/-- Each term is integrable on Ioc(-T, T). -/
theorem term_integrable {x : ℝ} (hx : 0 < x) {c : ℝ} (hc : 0 < c)
    (n : ℕ) (T : ℝ) :
    Integrable (fun t : ℝ =>
      LSeries.term (↗ArithmeticFunction.vonMangoldt) ((c : ℂ) + (t : ℂ) * I) n *
      ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)))
    (volume.restrict (Ioc (-T) T)) := by
  exact ((term_continuous hx hc n).continuousOn.integrableOn_compact isCompact_Icc).mono_set
    Ioc_subset_Icc_self

/-! ## Section 4: Summability of Integral Norms -/

/-- The sum of integral norms converges. This is the key dominated convergence condition.
    Uses: LSeriesSummable_vonMangoldt for absolute convergence of Σ Λ(n)/n^c. -/
theorem integral_norms_summable {x : ℝ} (hx : 0 < x) {c : ℝ} (hc : 1 < c)
    {T : ℝ} (hT : 0 < T) :
    Summable (fun n => ∫ t in Ioc (-T) T,
      ‖LSeries.term (↗ArithmeticFunction.vonMangoldt) ((c : ℂ) + (t : ℂ) * I) n *
       ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))‖) := by
  have hc0 : 0 < c := by linarith
  -- Each integral is bounded by constant * ‖LSeries.term at real c‖
  have hbound : ∀ n, ∫ t in Ioc (-T) T,
      ‖LSeries.term (↗ArithmeticFunction.vonMangoldt) ((c : ℂ) + (t : ℂ) * I) n *
       ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))‖ ≤
      2 * T * (x ^ c / c) *
      ‖LSeries.term (↗ArithmeticFunction.vonMangoldt) (c : ℂ) n‖ := by
    intro n
    calc ∫ t in Ioc (-T) T, ‖_‖
        ≤ ∫ _ in Ioc (-T) T,
            ‖LSeries.term (↗ArithmeticFunction.vonMangoldt) (c : ℂ) n‖ * (x ^ c / c) := by
          apply setIntegral_mono_on
          · exact ((term_continuous hx hc0 n).norm.continuousOn.integrableOn_compact
              isCompact_Icc).mono_set Ioc_subset_Icc_self
          · exact (continuousOn_const.integrableOn_compact isCompact_Icc).mono_set
              Ioc_subset_Icc_self
          · exact measurableSet_Ioc
          · intro t _; exact pointwise_bound hx hc0 n t
      _ ≤ 2 * T * (x ^ c / c) *
            ‖LSeries.term (↗ArithmeticFunction.vonMangoldt) (c : ℂ) n‖ := by
          rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioc,
              ENNReal.toReal_ofReal (by linarith)]
          nlinarith [norm_nonneg (LSeries.term (↗ArithmeticFunction.vonMangoldt) (c : ℂ) n),
                      rpow_nonneg hx.le c]
  exact Summable.of_nonneg_of_le
    (fun n => integral_nonneg_of_ae (ae_of_all _ (fun t => norm_nonneg _)))
    hbound
    ((ArithmeticFunction.LSeriesSummable_vonMangoldt
      (show 1 < (c : ℂ).re by simp; linarith)).norm.mul_left _)

/-! ## Section 5: Main Sum-Integral Interchange -/

/-- **Sum-integral interchange for the Perron integrand**:
    ∫ (-ζ'/ζ)(c+it) · x^{c+it}/(c+it) dt = Σ_n ∫ (Λ(n)/n^{c+it}) · x^{c+it}/(c+it) dt

    Proved via:
    1. `pointwise_integrand_tsum`: pointwise equality of integrand = tsum of terms
    2. `term_integrable`: each term is integrable on [-T,T]
    3. `integral_norms_summable`: dominated convergence condition
    4. `integral_tsum_of_summable_integral_norm`: Mathlib's sum-integral interchange -/
theorem perron_sum_integral_interchange {x : ℝ} (hx : 0 < x)
    {c : ℝ} (hc : 1 < c) {T : ℝ} (hT : 0 < T) :
    ∫ t in Ioc (-T) T,
      (-deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) /
        riemannZeta ((c : ℂ) + (t : ℂ) * I)) *
       ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) =
    ∑' n, ∫ t in Ioc (-T) T,
      LSeries.term (↗ArithmeticFunction.vonMangoldt) ((c : ℂ) + (t : ℂ) * I) n *
      ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) := by
  have h_eq : (fun t : ℝ =>
      (-deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) /
        riemannZeta ((c : ℂ) + (t : ℂ) * I)) *
       ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))) =
    (fun t : ℝ =>
      ∑' n, LSeries.term (↗ArithmeticFunction.vonMangoldt) ((c : ℂ) + (t : ℂ) * I) n *
        ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))) :=
    funext (fun t => pointwise_integrand_tsum x c t hc)
  rw [h_eq]
  exact (integral_tsum_of_summable_integral_norm
    (fun n => term_integrable hx (by linarith : 0 < c) n T)
    (integral_norms_summable hx hc hT)).symm

end Littlewood.Development.PerronFormulaProof
