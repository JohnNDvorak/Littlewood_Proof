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
- `perron_per_term_small_bound_with_R`: per-term bound for y < 1, R-parametric — PROVED
- `perron_per_term_small_bound`: per-term bound for 0 < y < 1 (Davenport form) — PROVED
- `dirichlet_series_perron_exchange`: sum-integral interchange

SORRY COUNT: 2 (perron_vertical_eq_tsum: Fubini ∫Σ=Σ∫; perron_tail_bound: tail O(1))
PROVED: perron_fubini_exchange (from sub-lemmas), perron_exchange_error_bound

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

/-- For 0 < y < 1 and c > 0 and R > c, the per-term Perron integral satisfies a
    bound via the rectangle contour to the RIGHT (Re(s) = R).
    The rectangle integral is 0 (no pole inside), so the vertical integral
    is bounded by the other three sides. -/
theorem perron_per_term_small_bound_with_R (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1)
    (c : ℝ) (hc : 0 < c) (T : ℝ) (hT : 0 < T) (R : ℝ) (hR : c < R) :
    |perronPerTermIntegral y c T| ≤
      (2 * Real.pi)⁻¹ *
        (2 * (y ^ c - y ^ R) / (T * |Real.log y|) + 2 * T * y ^ R / R) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hR_pos : 0 < R := by linarith
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
  -- perronPerTermIntegral = (2π)⁻¹ * Re(∫ perronIntegrand)
  have h_eq : perronPerTermIntegral y c T =
      (2 * Real.pi)⁻¹ *
        (∫ t in (-T)..T, PerronVerticalFromRectangle.perronIntegrand y c t).re := by
    unfold perronPerTermIntegral
    congr 1
    have h_re_comm := Complex.reCLM.intervalIntegral_comp_comm hint
    simp only [Complex.reCLM_apply] at h_re_comm
    exact h_re_comm
  rw [h_eq]
  -- Bound: |(2π)⁻¹ * Re(z)| ≤ (2π)⁻¹ * ‖z‖
  have h_re_le : |(2 * Real.pi)⁻¹ *
      (∫ t in (-T)..T, PerronVerticalFromRectangle.perronIntegrand y c t).re| ≤
      (2 * Real.pi)⁻¹ *
        ‖∫ t in (-T)..T, PerronVerticalFromRectangle.perronIntegrand y c t‖ := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hpi)]
    gcongr
    exact Complex.abs_re_le_norm _
  apply le_trans h_re_le
  gcongr
  -- Now bound ‖∫ perronIntegrand‖ using the rectangle = 0 identity.
  -- From integral_boundary_rect_perron_neg: the full rectangle integral = 0.
  -- Rewrite: vert * I = -(top + right*I + bottom)
  -- Step 1: Connect ∫ perronIntegrand to the rectangle's vertical term.
  have h_vert_rewrite : ∀ t : ℝ,
      ((↑y : ℂ) ^ ((↑c : ℂ) + I * (↑t : ℂ)) / ((↑c : ℂ) + I * (↑t : ℂ))) * I =
      PerronVerticalFromRectangle.perronIntegrand y c t * I := by
    intro t; unfold PerronVerticalFromRectangle.perronIntegrand; ring
  have hRect := integral_boundary_rect_perron_neg y hy0 hy1 c hc T hT R hR
  simp_rw [h_vert_rewrite] at hRect
  rw [intervalIntegral.integral_mul_const] at hRect
  -- hRect : (∫ perronIntegrand) * I + top + right*I + bottom = 0
  -- Define the three boundary integrals
  set topI := ∫ x_var in (c : ℝ)..(R : ℝ),
    ((y : ℂ) ^ ((x_var : ℂ) + Complex.I * (T : ℂ)) /
     ((x_var : ℂ) + Complex.I * (T : ℂ)))
  set rightI := ∫ t in (T : ℝ)..((-T : ℝ)),
    ((y : ℂ) ^ ((R : ℂ) + Complex.I * (t : ℂ)) /
     ((R : ℂ) + Complex.I * (t : ℂ))) * Complex.I
  set bottomI := ∫ x_var in (R : ℝ)..(c : ℝ),
    ((y : ℂ) ^ ((x_var : ℂ) - Complex.I * (T : ℂ)) /
     ((x_var : ℂ) - Complex.I * (T : ℂ)))
  -- Extract: vert * I = -(topI + rightI + bottomI)
  have h_vert_eq : (∫ t in (-T)..T,
      PerronVerticalFromRectangle.perronIntegrand y c t) * Complex.I =
      -(topI + rightI + bottomI) := by
    have h_sum : (∫ t in (-T)..T,
        PerronVerticalFromRectangle.perronIntegrand y c t) * Complex.I +
        topI + rightI + bottomI = 0 := hRect
    linear_combination h_sum
  -- ‖vert‖ = ‖vert * I‖ (since ‖I‖ = 1)
  have h_norm_I : ‖(Complex.I : ℂ)‖ = 1 := Complex.norm_I
  have h_vert_norm : ‖∫ t in (-T)..T,
      PerronVerticalFromRectangle.perronIntegrand y c t‖ =
      ‖(∫ t in (-T)..T,
        PerronVerticalFromRectangle.perronIntegrand y c t) * Complex.I‖ := by
    rw [norm_mul, h_norm_I, mul_one]
  rw [h_vert_norm, h_vert_eq, norm_neg]
  -- Triangle inequality
  calc ‖topI + rightI + bottomI‖
      ≤ ‖topI‖ + ‖rightI‖ + ‖bottomI‖ := by
        calc ‖topI + rightI + bottomI‖
            ≤ ‖topI + rightI‖ + ‖bottomI‖ := norm_add_le _ _
          _ ≤ (‖topI‖ + ‖rightI‖) + ‖bottomI‖ := by gcongr; exact norm_add_le _ _
    _ ≤ (y ^ c - y ^ R) / (T * |Real.log y|) +
        2 * T * y ^ R / R +
        (y ^ c - y ^ R) / (T * |Real.log y|) := by
      gcongr
      -- Top horizontal: ∫ c..R ‖y^{x+iT}/(x+iT)‖ ≤ (y^c - y^R)/(T·|log y|)
      · calc ‖topI‖ ≤ ∫ x_var in (c : ℝ)..(R : ℝ),
              ‖((y : ℂ) ^ ((x_var : ℂ) + Complex.I * (T : ℂ)) /
               ((x_var : ℂ) + Complex.I * (T : ℂ)))‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith)
          _ ≤ (y ^ c - y ^ R) / (T * |Real.log y|) :=
            integral_norm_bound_small_y y hy0 hy1 c T hT R hR.le
      -- Right vertical: ‖∫ T..-T y^{R+it}/(R+it) * I‖ ≤ 2T·y^R/R
      · -- Factor out * I
        rw [show rightI = (∫ t in (T : ℝ)..((-T : ℝ)),
            ((y : ℂ) ^ ((R : ℂ) + Complex.I * (t : ℂ)) /
             ((R : ℂ) + Complex.I * (t : ℂ)))) * Complex.I from
          intervalIntegral.integral_mul_const _ _]
        rw [norm_mul, Complex.norm_I, mul_one]
        -- ∫ T..-T = -(∫ -T..T)
        rw [intervalIntegral.integral_symm, norm_neg]
        exact vertical_integral_bound_far_right y hy0 R hR_pos T hT
      -- Bottom horizontal: same bound as top by norm equality
      · show ‖∫ x_var in (R : ℝ)..(c : ℝ),
              ((y : ℂ) ^ ((x_var : ℂ) - Complex.I * (T : ℂ)) /
               ((x_var : ℂ) - Complex.I * (T : ℂ)))‖ ≤ _
        rw [intervalIntegral.integral_symm, norm_neg]
        calc ‖∫ x_var in (c : ℝ)..(R : ℝ),
              ((y : ℂ) ^ ((x_var : ℂ) - Complex.I * (T : ℂ)) /
               ((x_var : ℂ) - Complex.I * (T : ℂ)))‖
            ≤ ∫ x_var in (c : ℝ)..(R : ℝ),
              ‖((y : ℂ) ^ ((x_var : ℂ) - Complex.I * (T : ℂ)) /
               ((x_var : ℂ) - Complex.I * (T : ℂ)))‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by linarith)
          _ = ∫ x_var in (c : ℝ)..(R : ℝ),
              ‖((y : ℂ) ^ ((x_var : ℂ) + Complex.I * (T : ℂ)) /
               ((x_var : ℂ) + Complex.I * (T : ℂ)))‖ := by
            congr 1; ext x_var
            exact PerronVerticalFromRectangle.norm_integrand_conj_eq y hy0 x_var T
          _ ≤ (y ^ c - y ^ R) / (T * |Real.log y|) :=
            integral_norm_bound_small_y y hy0 hy1 c T hT R hR.le
    _ = 2 * (y ^ c - y ^ R) / (T * |Real.log y|) + 2 * T * y ^ R / R := by ring

/-- For 0 < y < 1 and c > 0, the per-term Perron integral is bounded.
    This follows from the rectangle contour: the full rectangle integral
    equals 0 (Cauchy), so the vertical segment is bounded by the other segments.

    The bound `(y^c + 1)/(T·|log y|) + 2·y^c/(c·T)` is Davenport's form
    (Ch. 17), obtained by taking R → ∞ in the rectangle bound. -/
theorem perron_per_term_small_bound (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) (c : ℝ)
    (hc : 0 < c) (T : ℝ) (hT : 0 < T) :
    |perronPerTermIntegral y c T| ≤
      (y ^ c + 1) / (T * |Real.log y|) + 2 * y ^ c / (c * T) := by
  -- Take R → ∞ strategy: for every ε > 0, the R-dependent bound < target + ε
  apply le_of_forall_pos_lt_add
  intro ε hε
  have hlog_neg : Real.log y < 0 := Real.log_neg hy0 hy1
  have habs_log_pos : 0 < |Real.log y| := abs_pos.mpr (ne_of_lt hlog_neg)
  have hTlog : 0 < T * |Real.log y| := mul_pos hT habs_log_pos
  have hy_rpow_pos : 0 < y ^ c := rpow_pos_of_pos hy0 c
  -- Pick R large enough: y^R < min(ε·T·|log y|/4, ε·R/(4T)) — use R = -log(δ)/log(y⁻¹) with δ small
  -- Simpler: pick R so that (2π)⁻¹ * bound < target + ε
  -- The bound with R is: (2π)⁻¹ * (2(y^c - y^R)/(T|log y|) + 2T·y^R/R)
  -- ≤ (2π)⁻¹ * (2·y^c/(T|log y|) + 2T·y^R/R)    [since y^R > 0]
  -- = y^c/(π·T·|log y|) + T·y^R/(π·R)
  -- ≤ y^c/(T·|log y|) + T·y^R/(π·R)    [since π > 1]
  -- For the second term, pick R large enough that y^R/(π·R) < ε·c/(2T)
  -- i.e. T·y^R/(π·R) < ε/2
  -- Since y^R → 0 as R → ∞ (y < 1), we can find such R.
  -- Actually, let's just pick R = c + 1 + enough, and use a cleaner approach:
  -- Since y < 1, y^R ≤ y^(c+1) for R ≥ c + 1.
  -- Pick R = max(c+1, 2T·y^(c+1)/(ε·π) + 1) so T·y^R/(πR) < ε.
  -- But actually we can be simpler: use the limit argument like the large case.
  set R := max (c + 1) (2 * T / (Real.pi * ε) + 1) with hR_def
  have hR_gt_c : c < R := by
    simp only [hR_def, lt_max_iff]; left; linarith
  have hR_pos : 0 < R := by linarith
  -- Apply the R-dependent bound
  have h_bound := perron_per_term_small_bound_with_R y hy0 hy1 c hc T hT R hR_gt_c
  -- Key facts about y^R
  have hy_rpow_R_nonneg : 0 ≤ y ^ R := rpow_nonneg hy0.le R
  have hy_rpow_R_le_yc : y ^ R ≤ y ^ c := by
    apply rpow_le_rpow_of_exponent_ge hy0 hy1.le
    exact hR_gt_c.le
  have hy_rpow_c_sub_R : 0 ≤ y ^ c - y ^ R := by linarith
  have hpi_gt_one : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have h2pi_inv_pos : 0 < (2 * Real.pi)⁻¹ := by positivity
  -- Bound piece 1: (2π)⁻¹ * 2(y^c - y^R)/(T|log y|) ≤ y^c/(T|log y|)
  have h_piece1 : (2 * Real.pi)⁻¹ * (2 * (y ^ c - y ^ R) / (T * |Real.log y|)) ≤
      y ^ c / (T * |Real.log y|) := by
    have h1 : y ^ c - y ^ R ≤ y ^ c := by linarith
    calc (2 * Real.pi)⁻¹ * (2 * (y ^ c - y ^ R) / (T * |Real.log y|))
        ≤ (2 * Real.pi)⁻¹ * (2 * y ^ c / (T * |Real.log y|)) := by
          gcongr
      _ = y ^ c / (Real.pi * (T * |Real.log y|)) := by ring
      _ ≤ y ^ c / (1 * (T * |Real.log y|)) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hpi_gt_one.le (by positivity)
      _ = y ^ c / (T * |Real.log y|) := by ring
  -- Bound piece 2: (2π)⁻¹ * 2T·y^R/R ≤ T/(πR)
  have h_piece2 : (2 * Real.pi)⁻¹ * (2 * T * y ^ R / R) ≤ T / (Real.pi * R) := by
    calc (2 * Real.pi)⁻¹ * (2 * T * y ^ R / R)
        ≤ (2 * Real.pi)⁻¹ * (2 * T * 1 / R) := by
          gcongr
          calc y ^ R ≤ y ^ c := hy_rpow_R_le_yc
            _ ≤ y ^ (0 : ℝ) := rpow_le_rpow_of_exponent_ge hy0 hy1.le hc.le
            _ = 1 := rpow_zero y
      _ = T / (Real.pi * R) := by ring
  -- Bound T/(πR): since R ≥ 2T/(πε) + 1 > 2T/(πε), we have T/(πR) < ε/2
  have h_R_bound : T / (Real.pi * R) < ε := by
    have hR_ge : R ≥ 2 * T / (Real.pi * ε) + 1 := le_max_right _ _
    rw [div_lt_iff₀ (by positivity : 0 < Real.pi * R)]
    have h1 : T < Real.pi * (2 * T / (Real.pi * ε) + 1) * ε := by
      have : 2 * T / (Real.pi * ε) * (Real.pi * ε) = 2 * T := by field_simp
      nlinarith [mul_pos Real.pi_pos hε]
    have h2 : Real.pi * (2 * T / (Real.pi * ε) + 1) ≤ Real.pi * R := by
      exact mul_le_mul_of_nonneg_left hR_ge Real.pi_pos.le
    nlinarith
  -- Combine
  calc |perronPerTermIntegral y c T|
      ≤ (2 * Real.pi)⁻¹ *
          (2 * (y ^ c - y ^ R) / (T * |Real.log y|) + 2 * T * y ^ R / R) :=
        h_bound
    _ = (2 * Real.pi)⁻¹ * (2 * (y ^ c - y ^ R) / (T * |Real.log y|)) +
        (2 * Real.pi)⁻¹ * (2 * T * y ^ R / R) := by ring
    _ ≤ y ^ c / (T * |Real.log y|) + T / (Real.pi * R) := by
        linarith [h_piece1, h_piece2]
    _ < y ^ c / (T * |Real.log y|) + ε := by linarith
    _ ≤ (y ^ c + 1) / (T * |Real.log y|) + 2 * y ^ c / (c * T) + ε := by
        have : y ^ c / (T * |Real.log y|) ≤ (y ^ c + 1) / (T * |Real.log y|) := by
          gcongr; linarith
        linarith [div_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2) hy_rpow_pos.le)
          (mul_pos hc hT).le]

/-! ## Per-term Perron integral infrastructure for sum-integral interchange

These lemmas establish the pointwise and integral bounds needed for the
Dirichlet series Perron exchange (Fubini / dominated convergence).

Key results:
- `vertical_line_ne_zero`: c + it ≠ 0 for c > 0
- `vertical_line_norm_ge`: ‖c + it‖ ≥ c for c > 0
- `perron_integrand_pointwise_norm_bound`: ‖y^{c+it}/(c+it)‖ ≤ y^c/c
- `perron_integrand_cont`: y^{c+it}/(c+it) is continuous in t
- `perron_integrand_iIntegrable`: interval-integrable on [-T, T]
- `perron_integral_norm_le`: ‖∫_{-T}^{T} y^{c+it}/(c+it)‖ ≤ 2T·y^c/c
- `perron_per_term_re_integral_abs_bound`: |(2π)⁻¹ ∫ Re(...)| ≤ T·y^c/(πc)
-/

/-- For c > 0, the point c + it on the vertical line is nonzero. -/
theorem vertical_line_ne_zero (c : ℝ) (hc : 0 < c) (t : ℝ) :
    (c : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
  intro h
  have hre := congr_arg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero,
    add_zero, Complex.zero_re] at hre
  linarith

/-- For c > 0, ‖c + it‖ ≥ c. The real part dominates. -/
theorem vertical_line_norm_ge (c : ℝ) (hc : 0 < c) (t : ℝ) :
    c ≤ ‖(c : ℂ) + (t : ℂ) * Complex.I‖ := by
  have h1 : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  calc c = |((c : ℂ) + (t : ℂ) * Complex.I).re| := by rw [h1, abs_of_pos hc]
    _ ≤ ‖(c : ℂ) + (t : ℂ) * Complex.I‖ := Complex.abs_re_le_norm _

/-- For y > 0 and c > 0, ‖y^{c+it}/(c+it)‖ ≤ y^c/c.
    The modulus of the numerator is y^c (imaginary exponent has unit modulus),
    and the modulus of the denominator is ≥ c. -/
theorem perron_integrand_pointwise_norm_bound (y : ℝ) (hy : 0 < y) (c : ℝ) (hc : 0 < c)
    (t : ℝ) :
    ‖(y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
      ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ y ^ c / c := by
  rw [norm_div]
  have hnum : ‖(y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)‖ = y ^ c := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    congr 1
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have hden : c ≤ ‖(c : ℂ) + (t : ℂ) * Complex.I‖ :=
    vertical_line_norm_ge c hc t
  rw [hnum]
  exact div_le_div_of_nonneg_left (rpow_pos_of_pos hy c).le hc hden

/-- The Perron integrand y^{c+it}/(c+it) is continuous in t for c > 0, y > 0. -/
theorem perron_integrand_cont (y : ℝ) (hy : 0 < y) (c : ℝ) (hc : 0 < c) :
    Continuous (fun t : ℝ =>
      (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
        ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  apply Continuous.div
  · exact Continuous.cpow continuous_const
      (by continuity)
      (fun t => Or.inl (by simp; linarith))
  · continuity
  · intro t
    exact vertical_line_ne_zero c hc t

/-- The per-term Perron integrand is interval-integrable on [-T, T]. -/
theorem perron_integrand_iIntegrable (y : ℝ) (hy : 0 < y) (c : ℝ) (hc : 0 < c) (T : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
        ((c : ℂ) + (t : ℂ) * Complex.I))
      MeasureTheory.MeasureSpace.volume (-T) T :=
  (perron_integrand_cont y hy c hc).continuousOn.intervalIntegrable

/-- Integral norm bound: ‖∫_{-T}^{T} y^{c+it}/(c+it) dt‖ ≤ 2T·y^c/c. -/
theorem perron_integral_norm_le (y : ℝ) (hy : 0 < y) (c : ℝ) (hc : 0 < c) (T : ℝ)
    (hT : 0 < T) :
    ‖∫ t in (-T)..T,
      (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
        ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      2 * T * y ^ c / c := by
  calc ‖∫ t in (-T)..T,
          (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
            ((c : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (y ^ c / c) * |T - (-T)| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t _
        exact perron_integrand_pointwise_norm_bound y hy c hc t
    _ = 2 * T * y ^ c / c := by
        rw [show T - (-T) = 2 * T from by ring, abs_of_pos (by positivity)]
        ring

/-- The Re part of the per-term Perron integral satisfies the bound
    |(2π)⁻¹ ∫_{-T}^{T} Re(y^{c+it}/(c+it)) dt| ≤ T·y^c/(π·c).

    This is the key bound for the sum-integral interchange: each term
    of the Dirichlet series contributes at most T·(x/n)^c/(π·c) to the
    per-term Perron integral. Combined with Σ Λ(n)/n^c convergent for c > 1,
    this gives dominated convergence. -/
theorem perron_per_term_re_integral_abs_bound (y : ℝ) (hy : 0 < y) (c : ℝ) (hc : 0 < c)
    (T : ℝ) (hT : 0 < T) :
    |(2 * Real.pi)⁻¹ * ∫ t in (-T)..T,
      ((y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
        ((c : ℂ) + (t : ℂ) * Complex.I)).re| ≤
      T * y ^ c / (Real.pi * c) := by
  -- ∫ Re(f) = Re(∫ f) via reCLM
  have hint := perron_integrand_iIntegrable y hy c hc T
  have h_re_comm : ∫ t in (-T)..T,
      ((y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
        ((c : ℂ) + (t : ℂ) * Complex.I)).re =
    (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
        ((c : ℂ) + (t : ℂ) * Complex.I)).re := by
    have := Complex.reCLM.intervalIntegral_comp_comm hint
    simp only [Complex.reCLM_apply] at this
    exact this
  rw [h_re_comm, abs_mul, abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹)]
  calc (2 * Real.pi)⁻¹ *
          |(∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
            ((c : ℂ) + (t : ℂ) * Complex.I)).re|
      ≤ (2 * Real.pi)⁻¹ *
          ‖∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
            ((c : ℂ) + (t : ℂ) * Complex.I)‖ := by
        gcongr; exact Complex.abs_re_le_norm _
    _ ≤ (2 * Real.pi)⁻¹ * (2 * T * y ^ c / c) := by
        gcongr; exact perron_integral_norm_le y hy c hc T hT
    _ = T * y ^ c / (Real.pi * c) := by ring

/-! ## Dirichlet series exchange -/

/-! The Dirichlet series exchange: the Perron integral of -ζ'/ζ can be
    approximated by the sum of per-term Perron integrals weighted by Λ(n)/n^c.

    This is valid when `c > 1` because the Dirichlet series converges absolutely.
    The tail (n > N for large N) is bounded because it is dominated by the
    convergent series Σ Λ(n)/n^c.

    Architecture: decomposed into two atomic sub-lemmas:
    1. `perron_fubini_atomic`: Fubini interchange ∫ Σ = Σ ∫ on compact [-T,T]
    2. `perron_tail_bound`: tail Σ_{n > ⌊x⌋} is bounded by 1

    References: Davenport Ch. 17; Montgomery-Vaughan §5.1. -/

/-! ### Per-term Perron integral bounds for the tail -/

/-- For n ≥ 1, the per-term Perron integral is bounded by T·(x/n)^c/(π·c).
    This is the key domination bound for the Fubini interchange. -/
theorem perron_per_term_abs_bound_general (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T)
    (n : ℕ) (hn : 1 ≤ n) :
    |perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T| ≤
      T * (x / n) ^ (1 + 1 / Real.log x) / (Real.pi * (1 + 1 / Real.log x)) := by
  have hx_pos : (0 : ℝ) < x := by linarith
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hxn_pos : (0 : ℝ) < x / n := div_pos hx_pos hn_pos
  have hc_pos := c_param_pos x hx
  set c := 1 + 1 / Real.log x
  -- Use perron_per_term_re_integral_abs_bound
  exact perron_per_term_re_integral_abs_bound (x / n) hxn_pos c hc_pos T hT

/-- Λ(n) ≤ log n for all n ≥ 1. This follows from von Mangoldt being supported
    on prime powers with value log(minFac n) ≤ log n. -/
theorem vonMangoldt_le_log (n : ℕ) (hn : 1 ≤ n) :
    ArithmeticFunction.vonMangoldt n ≤ Real.log n := by
  simp only [ArithmeticFunction.vonMangoldt_apply]
  split_ifs with h
  · -- IsPrimePow n: vonMangoldt n = log(minFac n) ≤ log n
    have h_mf_pos : (0 : ℝ) < (n.minFac : ℝ) := Nat.cast_pos.mpr (Nat.minFac_pos n)
    have h_mf_le_n : n.minFac ≤ n := Nat.minFac_le hn
    exact Real.log_le_log h_mf_pos (by exact_mod_cast h_mf_le_n)
  · -- Not a prime power: vonMangoldt n = 0 ≤ log n
    exact Real.log_nonneg (by exact_mod_cast hn)

/-- **Fubini sub-lemma 1**: The Perron vertical integral equals the infinite
    Dirichlet series of per-term Perron integrals weighted by Λ(n).

    Mathematical proof:
    1. `-ζ'/ζ(c+it) = L(Λ, c+it) = Σ_n Λ(n)/n^{c+it}` (Mathlib: `vonMangoldt_lseries_eq_neg_zeta_logderiv`)
    2. Therefore the integrand `(-ζ'/ζ)(c+it) · x^{c+it}/(c+it)` equals `Σ_n Λ(n) · (x/n)^{c+it}/(c+it)`
    3. Each term is bounded: `|Λ(n) · (x/n)^{c+it}/(c+it)| ≤ Λ(n) · (x/n)^c/c`
    4. The domination `Σ_n Λ(n)·(x/n)^c/c = x^c/c · Σ_n Λ(n)/n^c < ∞` (summable for c > 1)
    5. By dominated convergence / Fubini on the compact interval [-T, T],
       `∫ Σ = Σ ∫`, i.e., `perronVerticalIntegral x T = Σ_n Λ(n) · perronPerTermIntegral(x/n, c, T)`

    Reference: Davenport Ch. 17; Montgomery-Vaughan §5.1. -/
private theorem perron_vertical_eq_tsum (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T) :
    perronVerticalIntegral x T =
      ∑' (n : ℕ), ArithmeticFunction.vonMangoldt n *
        perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T := by
  sorry

/-- **Fubini sub-lemma 2**: The tail of the Dirichlet series
    `Σ_{n > ⌊x⌋} Λ(n) · perronPerTermIntegral(x/n, c, T)` is bounded by 1.

    Mathematical proof: For n > ⌊x⌋, we have x/n < 1, so
    `perron_per_term_small_bound` gives
    `|perronPerTermIntegral(x/n, c, T)| ≤ (y^c + 1)/(T·|log y|) + 2y^c/(cT)`
    where y = x/n < 1. Since Λ(n) ≤ log n, and the sum converges
    (L-series summable), the total tail is bounded by 1. -/
private theorem perron_tail_bound (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T) :
    |∑' (n : ℕ), ArithmeticFunction.vonMangoldt n *
      perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T -
      ∑ n ∈ Finset.range (Nat.floor x + 1),
        ArithmeticFunction.vonMangoldt n *
          perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T| ≤ 1 := by
  sorry

/-- **Perron Fubini exchange** (Davenport Ch. 17, Theorem 17.1).

    The Perron vertical integral decomposes as a finite Dirichlet sum
    plus a bounded tail error:
      perronVerticalIntegral x T = Σ_{n ≤ ⌊x⌋} Λ(n)·perronPerTermIntegral(x/n, c, T) + O(1)

    Mathematical content (two sub-obligations):
    1. **Fubini interchange**: On [-T, T] with c > 1, the L-series
       -ζ'/ζ(s) = Σ Λ(n)/n^s converges absolutely and uniformly. Combined
       with `perron_per_term_abs_bound_general`, each term is dominated by
       T·(x/n)^c/(π·c), and `vonMangoldt_lseries_summable` gives
       Σ Λ(n)/n^c < ∞. Apply MeasureTheory.integral_tsum for ∫ Σ = Σ ∫.

    2. **Tail bound**: For n > ⌊x⌋, x/n < 1, so `perron_per_term_small_bound`
       gives exponentially decaying per-term bounds. Combined with
       `vonMangoldt_le_log` (Λ(n) ≤ log n), the tail is O(1).

    Sub-infrastructure proved in this file:
    - `perron_per_term_abs_bound_general` (domination bound)
    - `vonMangoldt_le_log` (Λ ≤ log)
    - `vonMangoldt_lseries_summable` (L-series summability)
    - `perron_per_term_small_bound` (small-y bound)

    Reference: Davenport Ch. 17; Montgomery-Vaughan §5.1. -/
private theorem perron_fubini_exchange (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T) :
    ∃ (tail_error : ℝ),
      perronVerticalIntegral x T =
        (∑ n ∈ Finset.range (Nat.floor x + 1),
          ArithmeticFunction.vonMangoldt n *
            perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T)
        + tail_error ∧
      |tail_error| ≤ 1 := by
  -- Define tail_error as the difference between perronVerticalIntegral
  -- and the finite sum, using the tsum decomposition
  set c := 1 + 1 / Real.log x with hc_def
  set N := Nat.floor x + 1 with hN_def
  set finiteSum := ∑ n ∈ Finset.range N,
    ArithmeticFunction.vonMangoldt n * perronPerTermIntegral (x / n) c T with hFS_def
  set tail_error := perronVerticalIntegral x T - finiteSum with hTE_def
  refine ⟨tail_error, by ring, ?_⟩
  -- Now show |tail_error| ≤ 1
  -- Step 1: perronVerticalIntegral x T = tsum (via perron_vertical_eq_tsum)
  have h_tsum := perron_vertical_eq_tsum x hx T hT
  -- Step 2: tail_error = tsum - finiteSum
  rw [hTE_def, h_tsum]
  -- Step 3: Apply perron_tail_bound
  exact perron_tail_bound x hx T hT

/-- The error in the Dirichlet series Perron exchange is bounded by 1.

    This follows from `perron_fubini_exchange` which provides the decomposition
    into finite sum + bounded tail.

    Mathematical content:
    1. `-ζ'/ζ(s) = L(Λ, s)` for `Re(s) > 1` (Mathlib: `vonMangoldt_lseries_eq_neg_zeta_logderiv`)
    2. The L-series converges absolutely for `c = 1 + 1/log x > 1`
    3. On the compact segment `[-T, T]`, Fubini gives `∫ Σ = Σ ∫`
    4. The tail `Σ_{n > ⌊x⌋} Λ(n) · perronPerTermIntegral(x/n, c, T)` is bounded:
       each `|perronPerTermIntegral(x/n, c, T)|` is bounded by per-term small bounds,
       and `Λ(n)/n^c` is summable.

    PROVED from `perron_fubini_exchange`.
    Sub-sorry count: 0 (local); 1 (in perron_fubini_exchange) -/
theorem perron_exchange_error_bound (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T) :
    |perronVerticalIntegral x T -
      ∑ n ∈ Finset.range (Nat.floor x + 1),
        ArithmeticFunction.vonMangoldt n *
          perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T| ≤ 1 := by
  obtain ⟨tail_error, h_eq, h_bound⟩ := perron_fubini_exchange x hx T hT
  have : perronVerticalIntegral x T -
      ∑ n ∈ Finset.range (Nat.floor x + 1),
        ArithmeticFunction.vonMangoldt n *
          perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T = tail_error := by
    linarith [h_eq]
  rw [this]
  exact h_bound

theorem dirichlet_series_perron_exchange (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T) :
    ∃ (error : ℝ),
      |error| ≤ 1 ∧
      perronVerticalIntegral x T =
        (∑ n ∈ Finset.range (Nat.floor x + 1),
          ArithmeticFunction.vonMangoldt n *
            perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T) + error := by
  refine ⟨perronVerticalIntegral x T -
    ∑ n ∈ Finset.range (Nat.floor x + 1),
      ArithmeticFunction.vonMangoldt n *
        perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T, ?_, by ring⟩
  exact perron_exchange_error_bound x hx T hT

end Aristotle.Standalone.PerronTruncationInfra
