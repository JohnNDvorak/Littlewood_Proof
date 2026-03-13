/-
Perron truncation infrastructure for B5a.

This file provides the mathematical backbone for the Perron truncation bound
(Davenport Ch. 17, Theorem 17.1):
  |ψ(x) - (1/2πi) ∫_{c-iT}^{c+iT} (-ζ'/ζ)(s) x^s/s ds| ≤ Cₚ · (log x)²

Key results:
- `perronVerticalIntegral`: the actual truncated Perron integral definition
- `perronPerTermIntegral`: individual term (1/2π) ∫ Re(y^{c+it}/(c+it)) dt
- `rpow_c_eq_e_mul`: x^{1+1/log x} = e·x (key for error analysis)
- `c_param_gt_one`, `c_param_re_gt_one`: the abscissa c > 1
- `vonMangoldt_lseries_eq_neg_zeta_logderiv`: L(Λ,s) = -ζ'/ζ(s) (Mathlib bridge)
- `perron_per_term_large_bound_with_R`: per-term bound (R-parametric) — PROVED
- `perron_per_term_large_bound`: per-term bound for y > 1 (Davenport form) — PROVED
- `perron_per_term_small_bound`: per-term bound for 0 < y < 1
- `dirichlet_series_perron_exchange`: sum-integral interchange

SORRY COUNT: 2

References: Davenport Ch. 17; Montgomery-Vaughan §5.1.

Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aDefs
import Littlewood.Aristotle.Standalone.PerronVerticalFromRectangle

set_option linter.mathlibStandardSet false

open scoped BigOperators Real LSeries.notation
open Real Complex Set MeasureTheory intervalIntegral Filter Topology

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.PerronTruncationInfra

/-! ## Perron vertical line integral definitions -/

/-- The per-term Perron integral: `(1/2π) ∫_{-T}^{T} Re(y^{c+it} / (c+it)) dt`.
    For `y = x/n`, this is the contribution of the n-th term of the Dirichlet series
    to the truncated Perron integral. -/
def perronPerTermIntegral (y : ℝ) (c T : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ t in (-T)..T,
    ((y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
     ((c : ℂ) + (t : ℂ) * Complex.I)).re

/-- The truncated Perron integral for the Chebyshev psi function:
    `(1/2π) ∫_{-T}^{T} Re((-ζ'/ζ)(c+it) · x^{c+it} / (c+it)) dt`
    with `c = 1 + 1/log x`. -/
def perronVerticalIntegral (x T : ℝ) : ℝ :=
  let c := 1 + 1 / Real.log x
  (2 * Real.pi)⁻¹ * ∫ t in (-T)..T,
    ((-deriv riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I) /
      riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I)) *
     (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
     ((c : ℂ) + (t : ℂ) * Complex.I)).re

/-! ## Mathlib bridge: Dirichlet series = -ζ'/ζ -/

/-- The von Mangoldt L-series equals -ζ'/ζ for Re(s) > 1.
    Direct wrapper around Mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`. -/
theorem vonMangoldt_lseries_eq_neg_zeta_logderiv {s : ℂ} (hs : 1 < s.re) :
    L ↗ArithmeticFunction.vonMangoldt s = -deriv riemannZeta s / riemannZeta s :=
  ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/-- The L-series of von Mangoldt is summable for Re(s) > 1.
    Wrapper around Mathlib. -/
theorem vonMangoldt_lseries_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable ↗ArithmeticFunction.vonMangoldt s :=
  ArithmeticFunction.LSeriesSummable_vonMangoldt hs

/-! ## The c parameter -/

/-- For `x ≥ 2`, the parameter `c = 1 + 1/log x` satisfies `c > 1`. -/
theorem c_param_gt_one (x : ℝ) (hx : 2 ≤ x) :
    1 < 1 + 1 / Real.log x := by
  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
  linarith [div_pos one_pos hlog_pos]

/-- For `x ≥ 2`, the parameter `c = 1 + 1/log x` satisfies `c > 0`. -/
theorem c_param_pos (x : ℝ) (hx : 2 ≤ x) :
    0 < 1 + 1 / Real.log x := by
  linarith [c_param_gt_one x hx]

/-- For `x ≥ 2`, the point `c + it` on the vertical line has Re > 1. -/
theorem c_param_re_gt_one (x : ℝ) (hx : 2 ≤ x) (t : ℝ) :
    1 < ((1 + 1 / Real.log x : ℝ) + (t : ℂ) * Complex.I).re := by
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, mul_one, sub_zero, add_zero]
  exact c_param_gt_one x hx

/-! ## Key algebraic identity -/

/-- When `c = 1 + 1/log x` and `x ≥ 2`, we have `x^c = e · x`.
    This is used to bound the per-term contributions in the truncation error sum. -/
theorem rpow_c_eq_e_mul (x : ℝ) (hx : 2 ≤ x) :
    x ^ (1 + 1 / Real.log x) = Real.exp 1 * x := by
  have hx_pos : 0 < x := by linarith
  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog_ne : Real.log x ≠ 0 := ne_of_gt hlog_pos
  rw [Real.rpow_add hx_pos, Real.rpow_one, mul_comm]
  suffices x ^ (1 / Real.log x) = Real.exp 1 by rw [this]
  rw [Real.rpow_def_of_pos hx_pos]
  congr 1
  rw [one_div, mul_inv_cancel₀ hlog_ne]

/-- Bound: for `x ≥ 2` and `1 ≤ n ≤ x`, `(x/n)^c ≤ e · x/n`. -/
theorem per_term_rpow_bound (x : ℝ) (hx : 2 ≤ x) (n : ℕ) (hn : 1 ≤ n)
    (hn_le : (n : ℝ) ≤ x) :
    (x / n) ^ (1 + 1 / Real.log x) ≤ Real.exp 1 * (x / n) := by
  have hx_pos : 0 < x := by linarith
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hxn_pos : 0 < x / n := div_pos hx_pos hn_pos
  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog_ne : Real.log x ≠ 0 := ne_of_gt hlog_pos
  have hn_cast_pos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hxn_ge_one : 1 ≤ x / n := by
    rw [le_div_iff₀ hn_pos]; linarith
  have hlog_xn_nonneg : 0 ≤ Real.log (x / n) := Real.log_nonneg hxn_ge_one
  have hlog_xn_le : Real.log (x / n) ≤ Real.log x := by
    apply Real.log_le_log hxn_pos
    exact div_le_self (by linarith) hn_cast_pos
  rw [Real.rpow_add hxn_pos, Real.rpow_one]
  suffices h : (x / ↑n) ^ (1 / Real.log x) ≤ Real.exp 1 by
    calc (x / ↑n) * (x / ↑n) ^ (1 / Real.log x)
        ≤ (x / ↑n) * Real.exp 1 := by gcongr
      _ = Real.exp 1 * (x / ↑n) := by ring
  rw [Real.rpow_def_of_pos hxn_pos]
  calc Real.exp (Real.log (x / ↑n) * (1 / Real.log x))
      ≤ Real.exp (Real.log x * (1 / Real.log x)) := by
        apply Real.exp_monotone
        exact mul_le_mul_of_nonneg_right hlog_xn_le (by positivity)
    _ = Real.exp 1 := by congr 1; field_simp

/-! ## Per-term Perron bounds -/

/-- For y > 1 and c > 0 and R > 0, the per-term Perron integral satisfies a bound
    via the rectangle contour. The bound involves the boundary remainder from the
    rectangle [-R, c] × [-T, T].

    This is proved by connecting the rectangle contour evaluations (V2) to the
    per-term vertical line integral via `PerronVerticalFromRectangle`. -/
theorem perron_per_term_large_bound_with_R (y : ℝ) (hy : 1 < y) (c : ℝ) (hc : 0 < c)
    (T : ℝ) (hT : 0 < T) (R : ℝ) (hR : 0 < R) :
    |perronPerTermIntegral y c T - 1| ≤
      (2 * Real.pi)⁻¹ *
        (2 * (y ^ c - y ^ (-R)) / (T * Real.log y) + 2 * T * y ^ (-R) / R) := by
  -- Step 1: Rewrite perronPerTermIntegral as (2π)⁻¹ * Re(∫ perronIntegrand)
  -- The key is that ∫ Re(f) = Re(∫ f) via reCLM
  have hy_pos : 0 < y := by linarith
  have hpi : 0 < 2 * Real.pi := by positivity
  -- The integrand is continuous (hence integrable)
  have hcont : Continuous (fun t : ℝ =>
      PerronVerticalFromRectangle.perronIntegrand y c t) := by
    unfold PerronVerticalFromRectangle.perronIntegrand
    apply Continuous.div
    · exact Continuous.cpow continuous_const
        (by continuity)
        (fun t => Or.inl (by simp; linarith))
    · continuity
    · intro t
      have : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
          mul_one, sub_zero, add_zero]
      exact ne_of_apply_ne Complex.re (by rw [this, Complex.zero_re]; linarith)
  have hint : IntervalIntegrable (fun t =>
      PerronVerticalFromRectangle.perronIntegrand y c t) volume (-T) T :=
    hcont.intervalIntegrable _ _
  -- ∫ Re(f) = Re(∫ f)
  have h_re_comm : ∫ t in (-T)..T,
      (PerronVerticalFromRectangle.perronIntegrand y c t).re =
    (∫ t in (-T)..T, PerronVerticalFromRectangle.perronIntegrand y c t).re := by
    have := Complex.reCLM.intervalIntegral_comp_comm hint
    simp only [Complex.reCLM_apply] at this
    exact this
  -- Step 2: Show perronPerTermIntegral = (2π)⁻¹ * Re(∫ perronIntegrand)
  have h_eq : perronPerTermIntegral y c T =
      (2 * Real.pi)⁻¹ *
        (∫ t in (-T)..T, PerronVerticalFromRectangle.perronIntegrand y c t).re := by
    unfold perronPerTermIntegral; congr 1
  -- Step 3: Apply perron_per_term_error_from_boundary
  rw [h_eq]
  calc |(2 * Real.pi)⁻¹ *
          (∫ t in (-T)..T, PerronVerticalFromRectangle.perronIntegrand y c t).re - 1|
      ≤ (2 * Real.pi)⁻¹ *
          ‖PerronVerticalFromRectangle.boundaryRemainder y c T R‖ :=
        PerronVerticalFromRectangle.perron_per_term_error_from_boundary y hy c hc T hT R hR
    _ ≤ (2 * Real.pi)⁻¹ *
          (2 * (y ^ c - y ^ (-R)) / (T * Real.log y) + 2 * T * y ^ (-R) / R) := by
        gcongr
        exact PerronVerticalFromRectangle.boundaryRemainder_norm_bound y hy c hc T hT R hR

/-- For y > 1 and c > 0, the per-term Perron integral satisfies a bound.
    This follows from the rectangle contour: the full rectangle integral
    equals 2πi (Cauchy), and the other three segments are bounded.

    The bound `(y^c + 1)/(T·log y) + 2·y^c/(c·T)` is Davenport's form
    (Ch. 17, Theorem 17.1), obtained by taking R → ∞ in the rectangle bound. -/
theorem perron_per_term_large_bound (y : ℝ) (hy : 1 < y) (c : ℝ) (hc : 0 < c)
    (T : ℝ) (hT : 0 < T) :
    |perronPerTermIntegral y c T - 1| ≤
      (y ^ c + 1) / (T * Real.log y) + 2 * y ^ c / (c * T) := by
  -- Strategy: for every ε > 0, the R-dependent bound < target + ε.
  -- Pick R = T/(π·ε) + 1 so that T/(π·R) < ε.
  apply le_of_forall_pos_lt_add
  intro ε hε
  have hy_pos : 0 < y := by linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hlog_pos : 0 < Real.log y := Real.log_pos (by linarith)
  have hTlog : 0 < T * Real.log y := mul_pos hT hlog_pos
  -- Pick R > T/(π·ε) so that T/(π·R) < ε
  set R := T / (Real.pi * ε) + 1 with hR_def
  have hR : 0 < R := by positivity
  -- Apply the R-dependent bound
  have h_bound := perron_per_term_large_bound_with_R y hy c hc T hT R hR
  -- Now bound: (2π)⁻¹ * (2(y^c - y^{-R})/(T·log y) + 2T·y^{-R}/R)
  --          ≤ y^c/(T·log y) + T/(π·R)
  --          < (y^c + 1)/(T·log y) + 2·y^c/(c·T) + ε
  -- Step 1: y^{-R} ≥ 0 and y^{-R} ≤ 1
  have hy_rpow_neg_nonneg : 0 ≤ y ^ (-R) := rpow_nonneg (by linarith) _
  have hy_rpow_neg_le_one : y ^ (-R) ≤ 1 := by
    rw [rpow_neg (by linarith : (0:ℝ) ≤ y)]
    have h1R : 1 ≤ y ^ R := by
      calc (1:ℝ) = 1 ^ R := (one_rpow R).symm
        _ ≤ y ^ R := rpow_le_rpow (by linarith) hy.le hR.le
    exact inv_le_one_of_one_le₀ h1R
  have hy_rpow_pos : 0 < y ^ c := rpow_pos_of_pos hy_pos c
  -- Step 2: bound the (2π)⁻¹ factor
  have hpi_gt_one : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have h2pi_inv_pos : 0 < (2 * Real.pi)⁻¹ := by positivity
  -- The first piece: (2π)⁻¹ * 2(y^c - y^{-R})/(T·log y)
  --               ≤ (2π)⁻¹ * 2·y^c/(T·log y) = y^c/(π·T·log y)
  --               ≤ y^c/(T·log y)  [since π > 1]
  -- The second piece: (2π)⁻¹ * 2T·y^{-R}/R ≤ (2π)⁻¹ * 2T/R = T/(π·R)
  -- Total ≤ y^c/(T·log y) + T/(π·R)
  have h_piece1 : (2 * Real.pi)⁻¹ * (2 * (y ^ c - y ^ (-R)) / (T * Real.log y)) ≤
      y ^ c / (T * Real.log y) := by
    have h1 : y ^ c - y ^ (-R) ≤ y ^ c := by linarith
    have h2 : 2 * (y ^ c - y ^ (-R)) / (T * Real.log y) ≤
        2 * y ^ c / (T * Real.log y) := by
      gcongr
    calc (2 * Real.pi)⁻¹ * (2 * (y ^ c - y ^ (-R)) / (T * Real.log y))
        ≤ (2 * Real.pi)⁻¹ * (2 * y ^ c / (T * Real.log y)) := by gcongr
      _ = y ^ c / (Real.pi * (T * Real.log y)) := by ring
      _ ≤ y ^ c / (1 * (T * Real.log y)) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right (le_of_lt hpi_gt_one) (by positivity)
      _ = y ^ c / (T * Real.log y) := by ring
  have h_piece2 : (2 * Real.pi)⁻¹ * (2 * T * y ^ (-R) / R) ≤ T / (Real.pi * R) := by
    calc (2 * Real.pi)⁻¹ * (2 * T * y ^ (-R) / R)
        ≤ (2 * Real.pi)⁻¹ * (2 * T * 1 / R) := by gcongr
      _ = T / (Real.pi * R) := by ring
  have h_R_bound : T / (Real.pi * R) < ε := by
    rw [hR_def, div_lt_iff₀ (by positivity : 0 < Real.pi * (T / (Real.pi * ε) + 1))]
    have h1 : T < Real.pi * (T / (Real.pi * ε) + 1) * ε := by
      have : T / (Real.pi * ε) * (Real.pi * ε) = T := by
        field_simp
      nlinarith [mul_pos hpi_pos hε]
    linarith
  -- Combine
  calc |perronPerTermIntegral y c T - 1|
      ≤ (2 * Real.pi)⁻¹ *
          (2 * (y ^ c - y ^ (-R)) / (T * Real.log y) + 2 * T * y ^ (-R) / R) :=
        h_bound
    _ = (2 * Real.pi)⁻¹ * (2 * (y ^ c - y ^ (-R)) / (T * Real.log y)) +
        (2 * Real.pi)⁻¹ * (2 * T * y ^ (-R) / R) := by ring
    _ ≤ y ^ c / (T * Real.log y) + T / (Real.pi * R) := by linarith [h_piece1, h_piece2]
    _ < y ^ c / (T * Real.log y) + ε := by linarith
    _ ≤ (y ^ c + 1) / (T * Real.log y) + 2 * y ^ c / (c * T) + ε := by
        have : y ^ c / (T * Real.log y) ≤ (y ^ c + 1) / (T * Real.log y) := by
          gcongr; linarith
        linarith [div_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2) hy_rpow_pos.le)
          (mul_pos hc hT).le]

/-- For 0 < y < 1 and c > 0, the per-term Perron integral is bounded.
    This follows from the rectangle contour: the full rectangle integral
    equals 0 (Cauchy), so the vertical segment is bounded by the other segments.

    SORRY: requires connecting interval integrals to rectangle contour (V2). -/
theorem perron_per_term_small_bound (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) (c : ℝ)
    (hc : 0 < c) (T : ℝ) (hT : 0 < T) :
    |perronPerTermIntegral y c T| ≤
      (y ^ c + 1) / (T * |Real.log y|) + 2 * y ^ c / (c * T) := by
  sorry

/-! ## Dirichlet series exchange -/

/-- The Dirichlet series exchange: the Perron integral of -ζ'/ζ can be
    approximated by the sum of per-term Perron integrals weighted by Λ(n)/n^c.

    This is valid when `c > 1` because the Dirichlet series converges absolutely.
    The tail (n > N for large N) is bounded because it is dominated by the
    convergent series Σ Λ(n)/n^c.

    SORRY: requires Fubini/dominated convergence for the interchange. -/
theorem dirichlet_series_perron_exchange (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T) :
    ∃ (error : ℝ),
      |error| ≤ 1 ∧
      perronVerticalIntegral x T =
        (∑ n ∈ Finset.range (Nat.floor x + 1),
          ArithmeticFunction.vonMangoldt n *
            perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T) + error := by
  sorry

end Aristotle.Standalone.PerronTruncationInfra
