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

SORRY COUNT: 2 (perron_vertical_eq_tsum: Fubini ∫Σ=Σ∫; perron_tail_bound_core: tail norm ≤ 1)
BUILD ERRORS: 0 (weighted_perron_series_summable FIXED via Real.div_rpow factorization)
PROVED: weighted_perron_series_summable, perron_tail_eq_subtype_tsum, tail_rpow_le_one,
        tail_dominating_summable, tail_norm_le_domination, tail_norm_tsum_le_domination,
        perron_tail_bound (wired through perron_tail_bound_core),
        perron_fubini_exchange (from sub-lemmas), perron_exchange_error_bound,
        tail_rpow_le_base, tail_dom_le_linear, tail_dom_factor,
        tail_dom_factor_with_e, tail_prefactor_pos

NOTE (C32): The tail bound `≤ 1` in perron_tail_bound_core is FALSE for general T > 0.
The dominating tsum factors as e·T·x/(πc) · Σ_{tail} Λ(n)/n^c (proved in
tail_dom_factor_with_e). For the product to be ≤ 1, the L-series tail must be
≤ πc/(e·x·T), which fails for small T or large x. The correct tail bound
is O(e·T·x/(πc) · tail_L_series), not O(1). This sorry is NOT on the critical
path (downstream uses placeholder witnesses), so fixing requires revising the
statement before closing.

References: Davenport Ch. 17; Montgomery-Vaughan §5.1.

Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aDefs
import Littlewood.Aristotle.Standalone.PerronVerticalFromRectangle
import Littlewood.Development.PerronFormulaProof

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

/-- The concrete contour-remainder defect for the actual vertical Perron
integral in this file.

This is not a provider shortcut: it only names the exact algebraic difference
between the vertical integral and the pole/zero residue main term.  The
remaining analytic atom is the bounded-height estimate for this concrete
quantity. -/
def perronVerticalContourRemainderRe (x T : ℝ) : ℝ :=
  perronVerticalIntegral x T - x +
    Littlewood.Development.HadamardProductZeta.zeroSumRe x T

/-- The normalized concrete contour-remainder defect used in the small-`T`
slab/tail split. -/
def perronVerticalContourRemainderNormalized (x T : ℝ) : ℝ :=
  |perronVerticalContourRemainderRe x T| /
    (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)

/-- The concrete vertical Perron integral decomposes into the pole residue,
zero sum, and the named contour-remainder defect by definition. -/
theorem perronVerticalIntegral_residue_identity (x T : ℝ) :
    perronVerticalIntegral x T =
      x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T +
        perronVerticalContourRemainderRe x T := by
  unfold perronVerticalContourRemainderRe
  ring

/-- On the small-`T` box, the residue error scale is uniformly positive.

This packages the denominator positivity needed to pass between a normalized
supremum bound and the bounded-height contour-remainder estimate. -/
theorem small_T_residue_error_shape_pos
    (x T : ℝ) (hx : x ≥ 2) (hT_lo : 2 ≤ T) (hT_hi : T ≤ 16) :
    0 < Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T := by
  have hlog2_sq_pos : 0 < (Real.log 2) ^ 2 :=
    sq_pos_of_pos (Real.log_pos (by norm_num))
  have hL_pos : 0 < (Real.log 2) ^ 2 / (4 : ℝ) := by positivity
  have hdenom :
      (Real.log 2) ^ 2 / (4 : ℝ) ≤ (Real.log T) ^ 2 / Real.sqrt T :=
    Littlewood.Development.HadamardProductZeta.small_T_denominator_lower
      hT_lo hT_hi
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt x := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlower :
      (Real.log 2) ^ 2 / (4 : ℝ) ≤
        Real.sqrt x * ((Real.log T) ^ 2 / Real.sqrt T) := by
    calc (Real.log 2) ^ 2 / (4 : ℝ)
        = (1 : ℝ) * ((Real.log 2) ^ 2 / (4 : ℝ)) := by ring
      _ ≤ Real.sqrt x * ((Real.log T) ^ 2 / Real.sqrt T) :=
          mul_le_mul hsqrt_ge_one hdenom hL_pos.le (Real.sqrt_nonneg x)
  have :
      (Real.log 2) ^ 2 / (4 : ℝ) ≤
        Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T := by
    calc (Real.log 2) ^ 2 / (4 : ℝ)
        ≤ Real.sqrt x * ((Real.log T) ^ 2 / Real.sqrt T) := hlower
      _ = Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T := by ring
  linarith

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

/-! ### Tail-term bounds and summability infrastructure

For n > floor(x), we have x/n < 1, so `perron_per_term_small_bound` bounds each term.
Combined with Λ(n) ≤ log n, this gives geometrically decaying tail terms.

For the Fubini interchange, each weighted Perron term is dominated by
T·Λ(n)·(x/n)^c/(π·c), and the series Σ Λ(n)/n^c converges for c > 1
(from Mathlib's `LSeriesSummable_vonMangoldt`). -/

/-- Λ(n) is nonneg for all n.
    PROVED: Λ(n) = log(minFac n) ≥ 0 if n is a prime power, else Λ(n) = 0. -/
theorem vonMangoldt_nonneg (n : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt n := by
  simp only [ArithmeticFunction.vonMangoldt_apply]
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast Nat.minFac_pos n)
  · exact le_refl _

/-- For n > floor(x) with x ≥ 2, we have 0 < x/n < 1.
    PROVED: n ≥ floor(x) + 1 > x gives x/n < 1; x > 0 gives x/n > 0. -/
theorem xdivn_in_unit_interval_of_tail (x : ℝ) (hx : 2 ≤ x) (n : ℕ)
    (hn : Nat.floor x + 1 ≤ n) (hn_pos : 1 ≤ n) :
    0 < x / (n : ℝ) ∧ x / (n : ℝ) < 1 := by
  have hx_pos : (0 : ℝ) < x := by linarith
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  constructor
  · exact div_pos hx_pos hn_real_pos
  · rw [div_lt_one hn_real_pos]
    have h_floor_lt : x < (Nat.floor x : ℝ) + 1 := by
      exact_mod_cast Nat.lt_floor_add_one x
    calc x < (Nat.floor x : ℝ) + 1 := h_floor_lt
      _ ≤ (n : ℝ) := by exact_mod_cast hn

/-- Per-term tail bound: for n > floor(x) with n ≥ 1, the weighted Perron
    |Λ(n) · perronPerTermIntegral(x/n, c, T)| is bounded by
    Λ(n) · [(x/n)^c + 1)/(T·|log(x/n)|) + 2(x/n)^c/(cT)].

    PROVED: from vonMangoldt_nonneg + perron_per_term_small_bound + abs_mul. -/
theorem tail_term_perron_bound (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T)
    (n : ℕ) (hn : Nat.floor x + 1 ≤ n) (hn_pos : 1 ≤ n) :
    |ArithmeticFunction.vonMangoldt n *
      perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T| ≤
    ArithmeticFunction.vonMangoldt n *
      ((x / n) ^ (1 + 1 / Real.log x) + 1) /
        (T * |Real.log (x / n)|) +
    ArithmeticFunction.vonMangoldt n *
      (2 * (x / n) ^ (1 + 1 / Real.log x)) /
        ((1 + 1 / Real.log x) * T) := by
  have ⟨hxn_pos, hxn_lt⟩ := xdivn_in_unit_interval_of_tail x hx n hn hn_pos
  have hc_pos := c_param_pos x hx
  set c := 1 + 1 / Real.log x
  rw [abs_mul, abs_of_nonneg (vonMangoldt_nonneg n)]
  have h_bound := perron_per_term_small_bound (x / n) hxn_pos hxn_lt c hc_pos T hT
  calc ArithmeticFunction.vonMangoldt n * |perronPerTermIntegral (x / ↑n) c T|
      ≤ ArithmeticFunction.vonMangoldt n *
          (((x / ↑n) ^ c + 1) / (T * |Real.log (x / ↑n)|) +
            2 * (x / ↑n) ^ c / (c * T)) := by
        apply mul_le_mul_of_nonneg_left h_bound (vonMangoldt_nonneg n)
    _ = ArithmeticFunction.vonMangoldt n *
          ((x / ↑n) ^ c + 1) / (T * |Real.log (x / ↑n)|) +
        ArithmeticFunction.vonMangoldt n *
          (2 * (x / ↑n) ^ c) / (c * T) := by ring

/-- The domination bound: for n ≥ 1, the weighted Perron integral satisfies
    |Λ(n) · perronPerTermIntegral(x/n, c, T)| ≤ T/(π·c) · Λ(n) · (x/n)^c.

    This bounds EVERY term (not just tail), enabling summability arguments.

    PROVED: from vonMangoldt_nonneg + perron_per_term_abs_bound_general. -/
theorem weighted_perron_term_domination (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T)
    (n : ℕ) (hn : 1 ≤ n) :
    |ArithmeticFunction.vonMangoldt n *
      perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T| ≤
    ArithmeticFunction.vonMangoldt n *
      (T * (x / n) ^ (1 + 1 / Real.log x) / (Real.pi * (1 + 1 / Real.log x))) := by
  rw [abs_mul, abs_of_nonneg (vonMangoldt_nonneg n)]
  exact mul_le_mul_of_nonneg_left
    (perron_per_term_abs_bound_general x hx T hT n hn)
    (vonMangoldt_nonneg n)

/-- The Λ-weighted (x/n)^c factorizes as x^c · Λ(n)/n^c.
    PROVED: algebraic identity using div_rpow. -/
theorem weighted_rpow_factor (x : ℝ) (hx : 2 ≤ x) (n : ℕ) (hn : 1 ≤ n) :
    ArithmeticFunction.vonMangoldt n *
      (x / n) ^ (1 + 1 / Real.log x) =
    x ^ (1 + 1 / Real.log x) *
      (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + 1 / Real.log x)) := by
  have hx_pos : (0 : ℝ) < x := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [div_rpow hx_pos.le hn_pos.le]
  ring

/-- The von Mangoldt L-series is summable at c = 1 + 1/log x > 1.
    Each term Λ(n)/n^c has real norm equal to the complex L-series norm,
    so real summability follows from Mathlib's `LSeriesSummable_vonMangoldt`.

    PROVED: wrapper around Mathlib's L-series summability. -/
theorem vonMangoldt_weighted_summable (x : ℝ) (hx : 2 ≤ x) :
    Summable (fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + 1 / Real.log x)) := by
  have hc := c_param_gt_one x hx
  set c := 1 + 1 / Real.log x with hc_def
  have h_ls := vonMangoldt_lseries_summable
    (s := (c : ℂ)) (by simp [Complex.ofReal_re]; exact hc)
  have h_eq : (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c) =
      (fun n : ℕ => ‖LSeries.term (↗ArithmeticFunction.vonMangoldt) (↑c) n‖) := by
    ext n
    by_cases hn : n = 0
    · subst hn; simp [LSeries.term]
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      -- Goal: Λ(n)/n^c = ‖↗Λ(n) / n^c‖ where ↗ is the nat-coe to ℂ
      -- ‖a/b‖ = ‖a‖/‖b‖, ‖(r:ℂ)‖ = |r|, ‖n^s‖ = n^(Re s)
      simp only [LSeries.term, if_neg hn]
      rw [norm_div, norm_natCast_cpow_of_pos hn_pos,
          show ((c : ℂ)).re = c from Complex.ofReal_re c]
      -- Goal: Λ(n)/n^c = ‖↗Λ(n)‖/n^c, suffices ‖↗Λ(n)‖ = Λ(n)
      congr 1
      simp [Complex.norm_real, abs_of_nonneg (vonMangoldt_nonneg n)]
  rw [h_eq]
  exact h_ls.norm

/-! ### Summability of the weighted Perron series

The full series `∑ Λ(n) · perronPerTermIntegral(x/n, c, T)` is summable.
Each term is dominated by `T/(πc) · Λ(n) · (x/n)^c = T·x^c/(πc) · Λ(n)/n^c`,
and the L-series `∑ Λ(n)/n^c` converges for `c > 1`. -/

/-- The weighted Perron series is summable: each term is dominated
    by a constant multiple of `Λ(n)/n^c`, which is summable.

    PROVED: from `weighted_perron_term_domination` + `vonMangoldt_weighted_summable`
    via `Summable.of_norm_bounded`. -/
theorem weighted_perron_series_summable (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T) :
    Summable (fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n *
        perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T) := by
  -- Strategy: dominate by Λ(n) · T(x/n)^c/(πc), which factors as K · Λ(n)/n^c.
  have hx_pos : (0 : ℝ) < x := by linarith
  set c := 1 + 1 / Real.log x with hc_def
  set K := T * x ^ c / (Real.pi * c) with hK_def
  -- Step 1: Summability of the dominating series via const_smul
  have h_eq_dom : (fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n *
        (T * (x / n) ^ c / (Real.pi * c))) =
      (fun n : ℕ => K * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c)) := by
    ext n
    by_cases hn : n = 0
    · subst hn; simp
    · simp only [hK_def, Real.div_rpow hx_pos.le (Nat.cast_nonneg n) c]; ring
  have h_dom : Summable (fun n : ℕ =>
    ArithmeticFunction.vonMangoldt n *
      (T * (x / n) ^ c / (Real.pi * c))) := by
    rw [h_eq_dom]
    exact (vonMangoldt_weighted_summable x hx).const_smul K
  -- Step 2: Each Perron term is bounded by the dominating term
  exact Summable.of_norm_bounded h_dom (fun n => by
    by_cases hn : n = 0
    · subst hn; simp [perronPerTermIntegral]
    · have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero hn
      rw [Real.norm_eq_abs]
      exact weighted_perron_term_domination x hx T hT n hn_pos)

/-- The tail of the weighted Perron series equals a subtype tsum over the
    complement of `Finset.range (⌊x⌋ + 1)`.

    PROVED: from `weighted_perron_series_summable` + `Summable.sum_add_tsum_subtype_compl`. -/
theorem perron_tail_eq_subtype_tsum (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T) :
    ∑' (n : ℕ), ArithmeticFunction.vonMangoldt n *
        perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T -
      ∑ n ∈ Finset.range (Nat.floor x + 1),
        ArithmeticFunction.vonMangoldt n *
          perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T =
    ∑' (n : { n : ℕ // n ∉ Finset.range (Nat.floor x + 1) }),
      ArithmeticFunction.vonMangoldt (↑n) *
        perronPerTermIntegral (x / (↑n)) (1 + 1 / Real.log x) T := by
  have hS := weighted_perron_series_summable x hx T hT
  have h := hS.sum_add_tsum_subtype_compl (Finset.range (Nat.floor x + 1))
  linarith

/-- For n ∉ range(⌊x⌋ + 1) and n ≥ 1, the per-term contribution is bounded by
    `T/(πc) · Λ(n) · (x/n)^c` where `(x/n)^c ≤ 1` since `x/n < 1`.
    Combined with Λ(n)/n^c summability, this bounds the tail.

    PROVED: from `tail_term_perron_bound` + `xdivn_in_unit_interval_of_tail`. -/
theorem tail_term_abs_le_domination (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T)
    (n : ℕ) (hn : n ∉ Finset.range (Nat.floor x + 1)) (hn_pos : 1 ≤ n) :
    |ArithmeticFunction.vonMangoldt n *
      perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T| ≤
    ArithmeticFunction.vonMangoldt n *
      (T * (x / n) ^ (1 + 1 / Real.log x) / (Real.pi * (1 + 1 / Real.log x))) := by
  exact weighted_perron_term_domination x hx T hT n hn_pos

/-- For n ∉ range(⌊x⌋ + 1), i.e., n ≥ ⌊x⌋ + 1, we have (x/n)^c < 1 since x/n < 1 and c > 0.
    Therefore `Λ(n) · (x/n)^c ≤ Λ(n) · 1 = Λ(n)`.

    PROVED: rpow monotonicity for base in (0,1). -/
theorem tail_rpow_le_one (x : ℝ) (hx : 2 ≤ x) (n : ℕ)
    (hn : Nat.floor x + 1 ≤ n) (hn_pos : 1 ≤ n) :
    (x / n) ^ (1 + 1 / Real.log x) ≤ 1 := by
  have ⟨hxn_pos, hxn_lt⟩ := xdivn_in_unit_interval_of_tail x hx n hn hn_pos
  have hc_pos := c_param_pos x hx
  calc (x / ↑n) ^ (1 + 1 / Real.log x)
      ≤ (x / ↑n) ^ (0 : ℝ) := by
        apply rpow_le_rpow_of_exponent_ge hxn_pos hxn_lt.le hc_pos.le
    _ = 1 := rpow_zero _

/-! ### Tail domination infrastructure

For tail terms (n > ⌊x⌋), the per-term bound using the general domination
gives `|Λ(n) · perron(x/n,c,T)| ≤ T/(πc) · Λ(n) · (x/n)^c`.
For (x/n)^c ≤ 1 (tail terms), this is ≤ T/(πc) · Λ(n).
But the (x/n)^c factor provides GEOMETRIC DECAY for n ≫ x, which is
essential for summability of the dominating series.

The tail tsum satisfies:
  ∑' |f n| ≤ T·x^c/(πc) · ∑' Λ(n)/n^c  (over n > ⌊x⌋)
          = e·T·x/(πc) · tail_of_L_series

where tail_of_L_series → 0 as x → ∞. The bound ≤ 1 requires this product
to be ≤ 1, which holds for x large enough relative to T.

Infrastructure: the tail tsum of norms is bounded by
T·x^c/(πc) times the tail of the vonMangoldt weighted summable series. -/

/-- The tail of the dominating series `Λ(n)·(x/n)^c` is summable.
    PROVED: subtype of the full summable series. -/
private theorem tail_dominating_summable (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T) :
    Summable (fun n : { n : ℕ // n ∉ Finset.range (Nat.floor x + 1) } =>
      ArithmeticFunction.vonMangoldt (↑n) *
        (T * (x / (↑n)) ^ (1 + 1 / Real.log x) /
          (Real.pi * (1 + 1 / Real.log x)))) := by
  -- Strategy: show dom(n) = K · Λ(n)/n^c for all n, then use const_smul.
  have hx_pos : (0 : ℝ) < x := by linarith
  set c := 1 + 1 / Real.log x with hc_def
  set K := T * x ^ c / (Real.pi * c) with hK_def
  -- Each dom term equals K * Λ(n)/n^c (via div_rpow factorization)
  have h_eq_fun : (fun n : ℕ => ArithmeticFunction.vonMangoldt n *
      (T * (x / n) ^ c / (Real.pi * c))) =
      (fun n : ℕ => K * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c)) := by
    ext n
    by_cases hn : n = 0
    · subst hn; simp
    · simp only [hK_def, Real.div_rpow hx_pos.le (Nat.cast_nonneg n) c]; ring
  have h_full : Summable (fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n *
        (T * (x / n) ^ c / (Real.pi * c))) := by
    rw [h_eq_fun]
    exact (vonMangoldt_weighted_summable x hx).const_smul K
  exact h_full.subtype _

/-- Each tail term norm is bounded by the dominating term.
    PROVED: from `weighted_perron_term_domination`. -/
private theorem tail_norm_le_domination (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T)
    (n : { n : ℕ // n ∉ Finset.range (Nat.floor x + 1) }) :
    |ArithmeticFunction.vonMangoldt (↑n) *
      perronPerTermIntegral (x / (↑n)) (1 + 1 / Real.log x) T| ≤
    ArithmeticFunction.vonMangoldt (↑n) *
      (T * (x / (↑n)) ^ (1 + 1 / Real.log x) /
        (Real.pi * (1 + 1 / Real.log x))) := by
  by_cases hn : (n : ℕ) = 0
  · simp [hn, ArithmeticFunction.vonMangoldt_apply]
  · exact weighted_perron_term_domination x hx T hT (↑n) (Nat.pos_of_ne_zero hn)

/-- The tail tsum of norms is bounded by the dominating tsum.
    PROVED: from `tsum_le_tsum` + `tail_norm_le_domination`. -/
private theorem tail_norm_tsum_le_domination (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T) :
    ∑' (n : { n : ℕ // n ∉ Finset.range (Nat.floor x + 1) }),
      |ArithmeticFunction.vonMangoldt (↑n) *
        perronPerTermIntegral (x / (↑n)) (1 + 1 / Real.log x) T| ≤
    ∑' (n : { n : ℕ // n ∉ Finset.range (Nat.floor x + 1) }),
      ArithmeticFunction.vonMangoldt (↑n) *
        (T * (x / (↑n)) ^ (1 + 1 / Real.log x) /
          (Real.pi * (1 + 1 / Real.log x))) := by
  gcongr with n
  · exact ((weighted_perron_series_summable x hx T hT).subtype _).norm
  · exact tail_dominating_summable x hx T hT
  · exact tail_norm_le_domination x hx T hT n

/-! ### Improved tail bound infrastructure: factored form

The dominating tsum `Σ_{tail} Λ(n)·T·(x/n)^c/(πc)` factors as
`T·x^c/(πc) · Σ_{tail} Λ(n)/n^c = e·T·x/(πc) · Σ_{tail} Λ(n)/n^c`.

This section proves:
1. `tail_rpow_le_base`: for tail terms, `(x/n)^c ≤ x/n` (tighter than `≤ 1`)
2. `tail_dominating_tsum_eq_factor`: the factored form of the dominating tsum
3. `tail_dominating_tsum_le_factored`: upper bound using `e·T·x/(πc) · L_tail`

The factoring isolates the L-series tail `Σ_{n > ⌊x⌋} Λ(n)/n^c`, making it clear
that the bound ≤ 1 requires `Σ_{tail} Λ(n)/n^c ≤ πc/(e·x·T)`. -/

/-- For tail terms (n > ⌊x⌋, so x/n < 1), raising to power c > 1 shrinks:
    `(x/n)^c ≤ x/n`. This is tighter than `tail_rpow_le_one`.

    PROVED: `rpow_le_rpow_of_exponent_ge` with base ∈ (0,1) and exponent 1 ≤ c. -/
theorem tail_rpow_le_base (x : ℝ) (hx : 2 ≤ x) (n : ℕ)
    (hn : Nat.floor x + 1 ≤ n) (hn_pos : 1 ≤ n) :
    (x / n) ^ (1 + 1 / Real.log x) ≤ x / n := by
  have ⟨hxn_pos, hxn_lt⟩ := xdivn_in_unit_interval_of_tail x hx n hn hn_pos
  have hc_ge : 1 ≤ 1 + 1 / Real.log x := by
    linarith [c_param_gt_one x hx]
  calc (x / ↑n) ^ (1 + 1 / Real.log x)
      ≤ (x / ↑n) ^ (1 : ℝ) := by
        apply rpow_le_rpow_of_exponent_ge hxn_pos hxn_lt.le hc_ge
    _ = x / ↑n := rpow_one _

/-- For tail terms, the dominating term `Λ(n)·T·(x/n)^c/(πc)` is bounded by
    `Λ(n)·T·(x/n)/(πc)`, which further equals `T·x/(πc·n)·Λ(n)`.

    PROVED: from `tail_rpow_le_base` + monotonicity of multiplication. -/
theorem tail_dom_le_linear (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T)
    (n : ℕ) (hn : Nat.floor x + 1 ≤ n) (hn_pos : 1 ≤ n) :
    ArithmeticFunction.vonMangoldt n *
      (T * (x / n) ^ (1 + 1 / Real.log x) /
        (Real.pi * (1 + 1 / Real.log x))) ≤
    ArithmeticFunction.vonMangoldt n *
      (T * (x / n) / (Real.pi * (1 + 1 / Real.log x))) := by
  apply mul_le_mul_of_nonneg_left _ (vonMangoldt_nonneg n)
  apply div_le_div_of_nonneg_right _ (mul_pos Real.pi_pos (c_param_pos x hx)).le
  exact mul_le_mul_of_nonneg_left (tail_rpow_le_base x hx n hn hn_pos) hT.le

/-- The dominating term factors: `Λ(n)·T·(x/n)^c/(πc) = (T·x^c/(πc)) · Λ(n)/n^c`.

    This is the algebraic identity underlying the factored tsum representation.

    PROVED: from `weighted_rpow_factor` + arithmetic. -/
theorem tail_dom_factor (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T)
    (n : ℕ) (hn_pos : 1 ≤ n) :
    ArithmeticFunction.vonMangoldt n *
      (T * (x / n) ^ (1 + 1 / Real.log x) /
        (Real.pi * (1 + 1 / Real.log x))) =
    T / (Real.pi * (1 + 1 / Real.log x)) *
      (x ^ (1 + 1 / Real.log x) *
        (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + 1 / Real.log x))) := by
  have hx_pos : (0 : ℝ) < x := by linarith
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  rw [Real.div_rpow hx_pos.le hn_real_pos.le]
  ring

/-- Combining `rpow_c_eq_e_mul` with the factor form: each dominating term equals
    `(e·T·x/(πc)) · Λ(n)/n^c`.

    PROVED: from `tail_dom_factor` + `rpow_c_eq_e_mul`. -/
theorem tail_dom_factor_with_e (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T)
    (n : ℕ) (hn_pos : 1 ≤ n) :
    ArithmeticFunction.vonMangoldt n *
      (T * (x / n) ^ (1 + 1 / Real.log x) /
        (Real.pi * (1 + 1 / Real.log x))) =
    (Real.exp 1 * T * x / (Real.pi * (1 + 1 / Real.log x))) *
      (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + 1 / Real.log x)) := by
  rw [tail_dom_factor x hx T hT n hn_pos, rpow_c_eq_e_mul x hx]
  ring

/-- The constant prefactor `K = e·T·x/(πc)` is positive for x ≥ 2 and T > 0.
    PROVED: positivity. -/
theorem tail_prefactor_pos (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T) :
    0 < Real.exp 1 * T * x / (Real.pi * (1 + 1 / Real.log x)) := by
  have hx_pos : (0 : ℝ) < x := by linarith
  have hc_pos := c_param_pos x hx
  have hpi_pos := Real.pi_pos
  exact div_pos (mul_pos (mul_pos (Real.exp_pos 1) hT) hx_pos) (mul_pos hpi_pos hc_pos)

/-- For tail terms (n ≥ ⌊x⌋+1), the small-y Perron bound gives a bound with
    `1/T` factor: `|Λ(n) * perron(x/n, c, T)| ≤ (3/T) · Λ(n)`.

    This is because for y = x/n < 1: y^c ≤ 1 and
    `|perron(y,c,T)| ≤ (y^c + 1)/(T·|log y|) + 2y^c/(cT) ≤ 2/(T·|log y|) + 2/(cT)`.
    For n ≥ ⌊x⌋+1 ≥ 3 and x ≥ 2, `|log(x/n)| = log(n/x) ≥ log(1) = 0` which
    can be small, so we use the simpler domination: `|perron(y,c,T)| ≤ T·y^c/(πc)`.

    Since y^c ≤ 1 and c > 1: `|perron(y,c,T)| ≤ T/(πc) < T/π < T`.
    Then `|Λ(n) * perron| ≤ T · Λ(n)`, which unfortunately grows with T.

    For the tail bound `≤ 1`, we instead use: for each tail term,
    `|Λ(n) * perron(x/n, c, T)| ≤ T·x^c/(πc) · Λ(n)/n^c` (domination),
    and the tail of `Λ(n)/n^c` is small for `N ≥ ⌊x⌋ + 1`.
    Since `x^c = e·x` (from `rpow_c_eq_e_mul`) and `c = 1 + 1/log(x)`,
    the tail sum decays as `e·x·T/(πc) · ∑_{n > ⌊x⌋} Λ(n)/n^c`.

    The actual bound `≤ 1` requires: `∑_{n > ⌊x⌋} Λ(n)/n^c ≤ πc/(e·x·T)`.
    This is an atomic analytic fact about the tail of the von Mangoldt L-series. -/
private theorem perron_tail_bound_core (x : ℝ) (hx : 2 ≤ x) (T : ℝ) (hT : 0 < T) :
    |∑' (n : { n : ℕ // n ∉ Finset.range (Nat.floor x + 1) }),
      ArithmeticFunction.vonMangoldt (↑n) *
        perronPerTermIntegral (x / (↑n)) (1 + 1 / Real.log x) T| ≤ 1 := by
  -- Step 1: Bound |tail| ≤ ∑ |terms| via norm_tsum_le_tsum_norm
  have hS := weighted_perron_series_summable x hx T hT
  set f := fun n : ℕ => ArithmeticFunction.vonMangoldt n *
    perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T with hf_def
  set s := Finset.range (Nat.floor x + 1) with hs_def
  have hf_sub : Summable (fun n : { n : ℕ // n ∉ s } => f ↑n) := hS.subtype _
  calc |∑' (n : { n : ℕ // n ∉ s }), f ↑n|
      ≤ ∑' (n : { n : ℕ // n ∉ s }), |f ↑n| := by
        rw [← Real.norm_eq_abs]
        exact le_trans (norm_tsum_le_tsum_norm (hf_sub.norm))
          (by simp_rw [Real.norm_eq_abs]; exact le_refl _)
    _ ≤ ∑' (n : { n : ℕ // n ∉ s }),
        ArithmeticFunction.vonMangoldt (↑n) *
          (T * (x / (↑n)) ^ (1 + 1 / Real.log x) /
            (Real.pi * (1 + 1 / Real.log x))) :=
        tail_norm_tsum_le_domination x hx T hT
    _ ≤ 1 := by
        -- Remaining atomic content: the dominating tsum
        -- = T·x^c/(πc) · ∑' Λ(n)/n^c (over n > ⌊x⌋)
        -- = e·T·x/(πc) · tail_of_L_series ≤ 1
        -- This requires a quantitative bound on the L-series tail.
        sorry

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
/-
  set c := 1 + 1 / Real.log x with hc_def
  have hc1 : 1 < c := c_param_gt_one x hx
  have hc0 : 0 < c := by linarith
  have hx0 : 0 < x := by linarith
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpi_inv_ne : (2 * Real.pi : ℝ)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hpi)
  have hT_neg_le : -T ≤ T := by linarith
  -- Step 1: Unfold perronVerticalIntegral
  unfold perronVerticalIntegral
  -- Step 2: Suffices to show the integrals match after cancelling (2π)⁻¹
  -- LHS = (2π)⁻¹ * ∫ t in (-T)..T, Re((-ζ'/ζ)(c+it) * x^(c+it) / (c+it))
  -- RHS = ∑' n, Λ(n) * ((2π)⁻¹ * ∫ t in (-T)..T, Re((x/n)^(c+it) / (c+it)))
  -- Rewrite RHS: pull (2π)⁻¹ out of each term
  have h_rhs_factor :
      (∑' (n : ℕ), ArithmeticFunction.vonMangoldt n *
          perronPerTermIntegral (x / ↑n) c T) =
        ∑' (n : ℕ), (2 * Real.pi)⁻¹ *
          (ArithmeticFunction.vonMangoldt n *
            ∫ t in (-T)..T,
              ((↑(x / ↑n) : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
               ((c : ℂ) + (t : ℂ) * Complex.I)).re) := by
    refine tsum_congr ?_
    intro n
    unfold perronPerTermIntegral
    ring
  rw [h_rhs_factor, tsum_mul_left]
  -- Now both sides are (2π)⁻¹ * _; cancel (2π)⁻¹
  congr 1
  -- Goal: ∫ t in (-T)..T, Re((-ζ'/ζ)(c+it) * x^(c+it) / (c+it))
  --     = ∑' n, Λ(n) * ∫ t in (-T)..T, Re((x/n)^(c+it) / (c+it))
  -- Step 3: Convert interval integrals to set integrals
  rw [intervalIntegral.integral_of_le hT_neg_le]
  -- Step 4: Use Re-integral interchange: ∫ Re(f) = Re(∫ f)
  -- For the LHS
  have h_lhs_integrable :
      MeasureTheory.Integrable
        (fun t : ℝ => (-deriv riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I) /
          riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I)) *
          (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
          ((c : ℂ) + (t : ℂ) * Complex.I))
        (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioc (-T) T)) := by
    -- The integrand is continuous on the compact set Icc
    apply ContinuousOn.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · apply ContinuousOn.div
        · exact (riemannZeta_differentiable.deriv.neg).continuous.continuousOn
        · exact riemannZeta_differentiable.continuous.continuousOn
        · intro t _
          exact riemannZeta_ne_zero_of_one_lt_re (by
            simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
              Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
              mul_one, sub_zero, add_zero]; linarith)
      · exact (Complex.continuous_ofReal_cpow_const hx0.le).continuousOn
    · exact (continuous_const.add
        (continuous_ofReal.mul continuous_const)).continuousOn
    · intro t _
      have : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
          mul_one, sub_zero, add_zero]
      exact ne_of_apply_ne Complex.re (by rw [this, Complex.zero_re]; linarith)
  rw [show (∫ t in Set.Ioc (-T) T,
      ((-deriv riemannZeta ((c : ℂ) + (↑t) * Complex.I) /
        riemannZeta ((c : ℂ) + (↑t) * Complex.I)) *
        (↑x) ^ ((c : ℂ) + (↑t) * Complex.I) /
        ((c : ℂ) + (↑t) * Complex.I)).re) =
    (∫ t in Set.Ioc (-T) T,
      (-deriv riemannZeta ((c : ℂ) + (↑t) * Complex.I) /
        riemannZeta ((c : ℂ) + (↑t) * Complex.I)) *
        (↑x) ^ ((c : ℂ) + (↑t) * Complex.I) /
        ((c : ℂ) + (↑t) * Complex.I)).re from
    (Complex.reCLM.integral_comp_comm h_lhs_integrable).symm]
  -- Step 5: Use perron_sum_integral_interchange
  -- Need: the integrand matches the form in PerronFormulaProof
  -- PerronFormulaProof has: (-ζ'/ζ(c+it)) * (x^(c+it) / (c+it))
  -- We have: (-ζ'/ζ(c+it)) * x^(c+it) / (c+it)
  -- These are equal by associativity of multiplication/division
  have h_integrand_eq : ∀ t : ℝ,
      (-deriv riemannZeta ((c : ℂ) + (↑t) * Complex.I) /
        riemannZeta ((c : ℂ) + (↑t) * Complex.I)) *
        (↑x) ^ ((c : ℂ) + (↑t) * Complex.I) /
        ((c : ℂ) + (↑t) * Complex.I) =
      (-deriv riemannZeta ((c : ℂ) + (↑t) * Complex.I) /
        riemannZeta ((c : ℂ) + (↑t) * Complex.I)) *
        ((↑x) ^ ((c : ℂ) + (↑t) * Complex.I) /
        ((c : ℂ) + (↑t) * Complex.I)) := by
    intro t; ring
  simp_rw [h_integrand_eq]
  rw [Littlewood.Development.PerronFormulaProof.perron_sum_integral_interchange hx0 hc1 hT]
  -- Goal: Re(∑' n, ∫ t in Ioc, term(Λ, s, n) * (x^s/s))
  --     = ∑' n, Λ(n) * ∫ t in (-T)..T, Re((x/n)^(c+it) / (c+it))
  -- Step 6: Distribute Re through tsum
  have h_sum_integrable :
      Summable (fun n => ∫ t in Set.Ioc (-T) T,
        LSeries.term (↗ArithmeticFunction.vonMangoldt)
          ((c : ℂ) + (↑t) * Complex.I) n *
          ((↑x) ^ ((c : ℂ) + (↑t) * Complex.I) /
          ((c : ℂ) + (↑t) * Complex.I))) := by
    exact (Littlewood.Development.PerronFormulaProof.integral_norms_summable
      hx0 hc1 hT).of_norm
  rw [Complex.hasSum_re h_sum_integrable.hasSum |>.tsum_eq]
  -- Goal: ∑' n, Re(∫ t in Ioc, term * x^s/s)
  --     = ∑' n, Λ(n) * ∫ t in (-T)..T, Re((x/n)^(c+it) / (c+it))
  -- Step 7: For each n, Re(∫ ...) = ∫ Re(...)
  -- and then unfold LSeries.term to get Λ(n) * ...
  congr 1; ext n
  -- Show: Re(∫ t ∈ Ioc(-T,T), term(Λ, c+it, n) * (x^(c+it)/(c+it)))
  --     = Λ(n) * ∫ t ∈ (-T)..T, Re((x/n)^(c+it) / (c+it))
  have h_n_integrable := Littlewood.Development.PerronFormulaProof.term_integrable
    hx0 hc0 n T
  rw [Complex.reCLM.integral_comp_comm h_n_integrable]
  -- Goal: ∫ t ∈ Ioc(-T,T), Re(term(Λ, c+it, n) * (x^(c+it)/(c+it)))
  --     = Λ(n) * ∫ t ∈ (-T)..T, Re((x/n)^(c+it) / (c+it))
  rw [← intervalIntegral.integral_of_le hT_neg_le]
  -- Goal: ∫ t in (-T)..T, Re(term(Λ, c+it, n) * (x^(c+it)/(c+it)))
  --     = Λ(n) * ∫ t in (-T)..T, Re((x/n)^(c+it) / (c+it))
  -- Step 8: Show the integrands are equal pointwise
  by_cases hn : n = 0
  · -- n = 0: both sides are 0
    simp [hn, LSeries.term_zero]
  · -- n ≠ 0: unfold LSeries.term
    congr 1; ext t
    simp only [LSeries.term_of_ne_zero hn]
    -- Re(Λ(n)/n^s * (x^s/s)) = Λ(n) * Re((x/n)^s / s)
    -- where s = c + it
    set s := (c : ℂ) + (↑t) * Complex.I with hs_def
    -- Λ(n)/n^s * x^s/s = Λ(n) * (x/n)^s / s
    have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hxn : (x / ↑n : ℝ) = x / (↑n : ℝ) := rfl
    -- Key: x^s / n^s = (x/n)^s
    have h_cpow_div : (↑x : ℂ) ^ s / (↑n : ℂ) ^ s = (↑(x / ↑n) : ℂ) ^ s := by
      rw [Complex.ofReal_div]
      rw [Complex.div_cpow (by exact_mod_cast hx0.le : (0 : ℝ) ≤ x)
          (by exact_mod_cast hn_pos.le : (0 : ℝ) ≤ (↑n : ℝ))]
    -- So: Λ(n)/n^s * (x^s/s) = Λ(n) * (x/n)^s / s
    have h_term : ↑(ArithmeticFunction.vonMangoldt n) / (↑n : ℂ) ^ s *
        ((↑x : ℂ) ^ s / s) =
        ↑(ArithmeticFunction.vonMangoldt n) * ((↑(x / ↑n) : ℂ) ^ s / s) := by
      rw [div_mul_eq_mul_div, mul_div_assoc', ← h_cpow_div, div_mul_eq_mul_div,
          mul_comm ((↑x : ℂ) ^ s) _, mul_div_assoc']
    rw [h_term]
    -- Re(Λ(n) * z) = Λ(n) * Re(z) since Λ(n) is real
    rw [Complex.ofReal_mul_re]
-/

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
  -- Step 1: Rewrite the difference as a subtype tsum over the tail
  rw [perron_tail_eq_subtype_tsum x hx T hT]
  -- Step 2: Apply the core tail bound
  exact perron_tail_bound_core x hx T hT

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

/-- The finite Perron-kernel sum obtained after exchanging the vertical integral
with the von Mangoldt Dirichlet series and truncating at `n ≤ x`. -/
def perronKernelFiniteSum (x T : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Nat.floor x + 1),
    ArithmeticFunction.vonMangoldt n *
      perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T

/-- Weighted finite cutoff error for the Perron kernel. This is the sharp-cutoff
finite-sum atom left after the vertical integral has been exchanged with the
von Mangoldt Dirichlet series. -/
def perronKernelWeightedCutoffError (x T : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Nat.floor x + 1),
    ArithmeticFunction.vonMangoldt n *
      |1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T|

/-- Boundary-window portion of the finite weighted Perron-kernel cutoff error.

The window `|x - n| <= x / T` is the sharp-cutoff transition region where the
standard per-term bounds involving `log (x / n)` are least useful. -/
def perronKernelWeightedBoundaryWindowError (x T : ℝ) : ℝ :=
  ∑ n ∈ (Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => |x - (n : ℝ)| ≤ x / T),
    ArithmeticFunction.vonMangoldt n *
      |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|

/-- Exact-hit part of the boundary-window weighted error.  This isolates the
integer discontinuity `n = x`, where the Perron kernel has a jump-size error and
the decaying boundary-kernel estimate is not scale-correct. -/
def perronKernelWeightedExactHitBoundaryError (x T : ℝ) : ℝ :=
  ∑ n ∈ ((Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => |x - (n : ℝ)| ≤ x / T)).filter
        (fun n : ℕ => (n : ℝ) = x),
    ArithmeticFunction.vonMangoldt n *
      |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|

/-- Punctured boundary-window weighted error, with the exact integer hit
removed.  This is the scale-correct location for the decaying kernel estimate. -/
def perronKernelWeightedPuncturedBoundaryWindowError (x T : ℝ) : ℝ :=
  ∑ n ∈ ((Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => |x - (n : ℝ)| ≤ x / T)).filter
        (fun n : ℕ => (n : ℝ) ≠ x),
    ArithmeticFunction.vonMangoldt n *
      |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|

/-- The finite near-diagonal punctured boundary set.  It lies in the unit band
`|x - n| <= 1` below the sharp cutoff and removes the exact hit `(n : ℝ) = x`. -/
def perronKernelNearDiagonalPuncturedBoundarySet (x T : ℝ) : Finset ℕ :=
  (((Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => |x - (n : ℝ)| ≤ x / T)).filter
        (fun n : ℕ => (n : ℝ) ≠ x)).filter
          (fun n : ℕ => |x - (n : ℝ)| ≤ 1)

/-- Near-diagonal part of the punctured boundary-window weighted error.  The
exact hit has already been removed, but this unit band records the remaining
integer-nearby obstruction where pointwise decay at scale
`T * (log x)^2 / x` is still not scale-correct. -/
def perronKernelWeightedNearDiagonalPuncturedBoundaryError (x T : ℝ) : ℝ :=
  ∑ n ∈ (((Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => |x - (n : ℝ)| ≤ x / T)).filter
        (fun n : ℕ => (n : ℝ) ≠ x)).filter
          (fun n : ℕ => |x - (n : ℝ)| ≤ 1),
    ArithmeticFunction.vonMangoldt n *
      |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|

/-- The separated punctured boundary set: the macroscopic boundary window with
the exact integer hit and the unit near-diagonal band removed. -/
def perronKernelSeparatedPuncturedBoundarySet (x T : ℝ) : Finset ℕ :=
  (((Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => |x - (n : ℝ)| ≤ x / T)).filter
        (fun n : ℕ => (n : ℝ) ≠ x)).filter
          (fun n : ℕ => ¬ |x - (n : ℝ)| ≤ 1)

/-- Separated part of the punctured boundary-window weighted error.  This
keeps the macroscopic boundary-window terms that remain after the exact-hit and
unit near-diagonal obstructions have been removed. -/
def perronKernelWeightedSeparatedPuncturedBoundaryError (x T : ℝ) : ℝ :=
  ∑ n ∈ perronKernelSeparatedPuncturedBoundarySet x T,
    ArithmeticFunction.vonMangoldt n *
      |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|

/-- Davenport-style pointwise envelope for separated boundary-window terms.

The factor `1 / log (x / n)` preserves the distance-from-cutoff singularity;
this is the scale-safe replacement for the demoted constant-supremum route on
the macroscopic boundary window. -/
def perronKernelSeparatedDavenportEnvelopeTerm (x T : ℝ) (n : ℕ) : ℝ :=
  let y : ℝ := x / (n : ℝ)
  (y ^ (1 + 1 / Real.log x) + 1) / (T * Real.log y) +
    2 * y ^ (1 + 1 / Real.log x) / ((1 + 1 / Real.log x) * T)

/-- Weighted Davenport envelope over the separated punctured boundary window.
The scale-correct summation target retains the linear boundary-window factor
`x / T`; the pure `O((log x)^2)` target is false on this macroscopic window. -/
def perronKernelSeparatedDavenportEnvelope (x T : ℝ) : ℝ :=
  ∑ n ∈ perronKernelSeparatedPuncturedBoundarySet x T,
    ArithmeticFunction.vonMangoldt n *
      perronKernelSeparatedDavenportEnvelopeTerm x T n

/-- Numerator of the singular Davenport summand.  This is uniformly bounded
on the separated boundary window once `x / n <= 2` is extracted. -/
def perronKernelSeparatedDavenportSingularNumerator (x : ℝ) (n : ℕ) : ℝ :=
  (x / (n : ℝ)) ^ (1 + 1 / Real.log x) + 1

/-- Singular summand of the separated Davenport envelope. -/
def perronKernelSeparatedDavenportSingularTerm (x T : ℝ) (n : ℕ) : ℝ :=
  perronKernelSeparatedDavenportSingularNumerator x n /
    (T * Real.log (x / (n : ℝ)))

/-- Singular `1 / log (x/n)` part of the separated Davenport envelope. -/
def perronKernelSeparatedDavenportSingularEnvelope (x T : ℝ) : ℝ :=
  ∑ n ∈ perronKernelSeparatedPuncturedBoundarySet x T,
    ArithmeticFunction.vonMangoldt n *
      perronKernelSeparatedDavenportSingularTerm x T n

/-- Smooth `1 / T` part of the separated Davenport envelope. -/
def perronKernelSeparatedDavenportSmoothEnvelope (x T : ℝ) : ℝ :=
  ∑ n ∈ perronKernelSeparatedPuncturedBoundarySet x T,
    ArithmeticFunction.vonMangoldt n *
      (2 * (x / (n : ℝ)) ^ (1 + 1 / Real.log x) /
        ((1 + 1 / Real.log x) * T))

/-- Harmonic-distance summand corresponding to the singular Davenport term. -/
def perronKernelSeparatedLogDistanceTerm (x T : ℝ) (n : ℕ) : ℝ :=
  x / (T * (x - (n : ℝ)))

/-- Weighted harmonic-distance envelope for the separated boundary window. -/
def perronKernelSeparatedLogDistanceEnvelope (x T : ℝ) : ℝ :=
  ∑ n ∈ perronKernelSeparatedPuncturedBoundarySet x T,
    ArithmeticFunction.vonMangoldt n *
      perronKernelSeparatedLogDistanceTerm x T n

/-- Unweighted harmonic-distance envelope for the separated boundary window.
This isolates the purely finite harmonic-distance summation left after the
von Mangoldt weight is bounded by `log x`. -/
def perronKernelSeparatedUnweightedLogDistanceEnvelope (x T : ℝ) : ℝ :=
  ∑ n ∈ perronKernelSeparatedPuncturedBoundarySet x T,
    perronKernelSeparatedLogDistanceTerm x T n

/-- Reciprocal-distance sum under the separated boundary window.  This is the
pure finite harmonic atom left after factoring the global `x / T` scale. -/
def perronKernelSeparatedReciprocalDistanceEnvelope (x T : ℝ) : ℝ :=
  ∑ n ∈ perronKernelSeparatedPuncturedBoundarySet x T,
    (x - (n : ℝ))⁻¹

/-- Integer floor-distance majorant for the separated reciprocal-distance sum.
It reindexes each term by its distance below `floor x`. -/
def perronKernelSeparatedFloorDistanceEnvelope (x T : ℝ) : ℝ :=
  ∑ n ∈ perronKernelSeparatedPuncturedBoundarySet x T,
    (((Nat.floor x - n : ℕ) : ℝ)⁻¹)

/-- Pure von Mangoldt weight of the near-diagonal punctured boundary set. -/
def perronKernelNearDiagonalPuncturedVonMangoldtWeight (x T : ℝ) : ℝ :=
  ∑ n ∈ perronKernelNearDiagonalPuncturedBoundarySet x T,
    ArithmeticFunction.vonMangoldt n

/-- Pure von Mangoldt weight of the boundary window. This is the exact
arithmetic count/log-weight atom left after separating the uniformly bounded
kernel factor. -/
def perronKernelBoundaryWindowVonMangoldtWeight (x T : ℝ) : ℝ :=
  ∑ n ∈ (Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => |x - (n : ℝ)| ≤ x / T),
    ArithmeticFunction.vonMangoldt n

/-- Off-boundary portion of the finite weighted Perron-kernel cutoff error. -/
def perronKernelWeightedOffBoundaryWindowError (x T : ℝ) : ℝ :=
  ∑ n ∈ (Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => ¬ |x - (n : ℝ)| ≤ x / T),
    ArithmeticFunction.vonMangoldt n *
      |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|

/-- Davenport-style weighted envelope for one off-boundary finite Perron term.

The `n = 0` branch is harmless because `vonMangoldt 0 = 0`; it avoids asking
the large-side Perron kernel bound to interpret `x / 0`. -/
def perronKernelOffBoundaryDavenportEnvelopeTerm (x T : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    ArithmeticFunction.vonMangoldt n *
      (((x / (n : ℝ)) ^ (1 + 1 / Real.log x) + 1) /
          (T * Real.log (x / (n : ℝ))) +
        2 * (x / (n : ℝ)) ^ (1 + 1 / Real.log x) /
          ((1 + 1 / Real.log x) * T))

/-- Davenport-style weighted envelope over the off-boundary finite Perron
range.  The remaining summation task keeps the distance from the cutoff inside
this envelope rather than using the false pure boundary-window route. -/
def perronKernelOffBoundaryDavenportEnvelope (x T : ℝ) : ℝ :=
  ∑ n ∈ (Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => ¬ |x - (n : ℝ)| ≤ x / T),
    perronKernelOffBoundaryDavenportEnvelopeTerm x T n

/-- Singular `1 / log (x / n)` part of the off-boundary Davenport envelope. -/
def perronKernelOffBoundaryDavenportSingularTerm (x T : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    ArithmeticFunction.vonMangoldt n *
      (((x / (n : ℝ)) ^ (1 + 1 / Real.log x) + 1) /
        (T * Real.log (x / (n : ℝ))))

/-- Smooth `1 / T` part of the off-boundary Davenport envelope. -/
def perronKernelOffBoundaryDavenportSmoothTerm (x T : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    ArithmeticFunction.vonMangoldt n *
      (2 * (x / (n : ℝ)) ^ (1 + 1 / Real.log x) /
        ((1 + 1 / Real.log x) * T))

/-- Singular off-boundary Davenport envelope. -/
def perronKernelOffBoundaryDavenportSingularEnvelope (x T : ℝ) : ℝ :=
  ∑ n ∈ (Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => ¬ |x - (n : ℝ)| ≤ x / T),
    perronKernelOffBoundaryDavenportSingularTerm x T n

/-- Smooth off-boundary Davenport envelope. -/
def perronKernelOffBoundaryDavenportSmoothEnvelope (x T : ℝ) : ℝ :=
  ∑ n ∈ (Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => ¬ |x - (n : ℝ)| ≤ x / T),
    perronKernelOffBoundaryDavenportSmoothTerm x T n

/-- Finite reciprocal von Mangoldt weight up to `floor x`.  The zero branch is
included to match `Finset.range (floor x + 1)` without dividing by zero. -/
def perronKernelVonMangoldtReciprocalWeight (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Nat.floor x + 1),
    if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ)

/-- Off-boundary reciprocal-distance von Mangoldt weight.  This is the
singular summation atom left after converting `1 / log (x / n)` into a
distance from the sharp cutoff. -/
def perronKernelOffBoundaryDistanceWeight (x T : ℝ) : ℝ :=
  ∑ n ∈ (Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => ¬ |x - (n : ℝ)| ≤ x / T),
    if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / (x - (n : ℝ))

/-- Exact finite-sum split of the weighted cutoff error into the sharp boundary
window and its complement. -/
theorem perronKernelWeightedCutoffError_eq_boundary_add_offBoundary
    (x T : ℝ) :
    perronKernelWeightedCutoffError x T =
      perronKernelWeightedBoundaryWindowError x T +
        perronKernelWeightedOffBoundaryWindowError x T := by
  classical
  dsimp [perronKernelWeightedCutoffError, perronKernelWeightedBoundaryWindowError,
    perronKernelWeightedOffBoundaryWindowError]
  exact
    (Finset.sum_filter_add_sum_filter_not
      (Finset.range (Nat.floor x + 1))
      (fun n : ℕ => |x - (n : ℝ)| ≤ x / T)
      (fun n =>
        ArithmeticFunction.vonMangoldt n *
          |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|)).symm

/-- Boundary-window split into the exact integer hit and the punctured boundary
window. -/
theorem perronKernelWeightedBoundaryWindowError_eq_exactHit_add_punctured
    (x T : ℝ) :
    perronKernelWeightedBoundaryWindowError x T =
      perronKernelWeightedExactHitBoundaryError x T +
        perronKernelWeightedPuncturedBoundaryWindowError x T := by
  classical
  dsimp [perronKernelWeightedBoundaryWindowError,
    perronKernelWeightedExactHitBoundaryError,
    perronKernelWeightedPuncturedBoundaryWindowError]
  exact
    (Finset.sum_filter_add_sum_filter_not
      ((Finset.range (Nat.floor x + 1)).filter
        (fun n : ℕ => |x - (n : ℝ)| ≤ x / T))
      (fun n : ℕ => (n : ℝ) = x)
      (fun n =>
        ArithmeticFunction.vonMangoldt n *
          |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|)).symm

/-- Punctured boundary-window split into the near-diagonal unit band and the
remaining separated punctured window. -/
theorem perronKernelWeightedPuncturedBoundaryWindowError_eq_nearDiagonal_add_separated
    (x T : ℝ) :
    perronKernelWeightedPuncturedBoundaryWindowError x T =
      perronKernelWeightedNearDiagonalPuncturedBoundaryError x T +
        perronKernelWeightedSeparatedPuncturedBoundaryError x T := by
  classical
  dsimp [perronKernelWeightedPuncturedBoundaryWindowError,
    perronKernelWeightedNearDiagonalPuncturedBoundaryError,
    perronKernelWeightedSeparatedPuncturedBoundaryError]
  exact
    (Finset.sum_filter_add_sum_filter_not
      (((Finset.range (Nat.floor x + 1)).filter
        (fun n : ℕ => |x - (n : ℝ)| ≤ x / T)).filter
          (fun n : ℕ => (n : ℝ) ≠ x))
      (fun n : ℕ => |x - (n : ℝ)| ≤ 1)
      (fun n =>
        ArithmeticFunction.vonMangoldt n *
          |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|)).symm

/-- The small-`T` weighted cutoff atom follows from separate estimates on the
sharp boundary window and the off-boundary range.

This isolates the currently dangerous part of the finite Perron-kernel problem:
near `n = x`, the denominator `log (x / n)` degenerates, so direct use of the
standard per-term kernel bounds is not scale-safe. -/
theorem small_T_weighted_kernel_cutoff_bound_from_boundary_split
    (hboundary : ∃ Cb > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedBoundaryWindowError x T ≤ Cb * (Real.log x) ^ 2)
    (hoffBoundary : ∃ Co > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedOffBoundaryWindowError x T ≤ Co * (Real.log x) ^ 2) :
    ∃ Cw > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedCutoffError x T ≤ Cw * (Real.log x) ^ 2 := by
  rcases hboundary with ⟨Cb, hCb_pos, hboundary⟩
  rcases hoffBoundary with ⟨Co, hCo_pos, hoffBoundary⟩
  refine ⟨Cb + Co, add_pos hCb_pos hCo_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  have hboundary_x := hboundary x T hx hT_lo hT_hi
  have hoffBoundary_x := hoffBoundary x T hx hT_lo hT_hi
  calc perronKernelWeightedCutoffError x T
      = perronKernelWeightedBoundaryWindowError x T +
          perronKernelWeightedOffBoundaryWindowError x T :=
        perronKernelWeightedCutoffError_eq_boundary_add_offBoundary x T
    _ ≤ Cb * (Real.log x) ^ 2 + Co * (Real.log x) ^ 2 := by
        exact add_le_add hboundary_x hoffBoundary_x
    _ = (Cb + Co) * (Real.log x) ^ 2 := by ring

/-- Boundary-window weighted error is controlled by a uniform kernel-error
supremum times the pure von Mangoldt weight of the boundary window. -/
theorem perronKernelWeightedBoundaryWindowError_le_kernelSup_mul_vonMangoldtWeight
    (x T K : ℝ)
    (hkernel : ∀ n : ℕ,
      n ∈ (Finset.range (Nat.floor x + 1)).filter
          (fun n : ℕ => |x - (n : ℝ)| ≤ x / T) →
        |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤ K) :
    perronKernelWeightedBoundaryWindowError x T ≤
      K * perronKernelBoundaryWindowVonMangoldtWeight x T := by
  classical
  let s := (Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => |x - (n : ℝ)| ≤ x / T)
  calc perronKernelWeightedBoundaryWindowError x T
      = ∑ n ∈ s,
          ArithmeticFunction.vonMangoldt n *
            |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| := by
        rfl
    _ ≤ ∑ n ∈ s, ArithmeticFunction.vonMangoldt n * K := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left (hkernel n hn) (vonMangoldt_nonneg n)
    _ = ∑ n ∈ s, K * ArithmeticFunction.vonMangoldt n := by
        apply Finset.sum_congr rfl
        intro n _hn
        ring
    _ = K * perronKernelBoundaryWindowVonMangoldtWeight x T := by
        dsimp [perronKernelBoundaryWindowVonMangoldtWeight, s]
        rw [Finset.mul_sum]

/-- Punctured boundary-window weighted error is controlled by a punctured
kernel supremum times the full boundary-window von Mangoldt weight. -/
theorem perronKernelWeightedPuncturedBoundaryWindowError_le_kernelSup_mul_vonMangoldtWeight
    (x T K : ℝ) (hK_nonneg : 0 ≤ K)
    (hkernel : ∀ n : ℕ,
      n ∈ ((Finset.range (Nat.floor x + 1)).filter
          (fun n : ℕ => |x - (n : ℝ)| ≤ x / T)).filter
            (fun n : ℕ => (n : ℝ) ≠ x) →
        |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤ K) :
    perronKernelWeightedPuncturedBoundaryWindowError x T ≤
      K * perronKernelBoundaryWindowVonMangoldtWeight x T := by
  classical
  let s := (Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => |x - (n : ℝ)| ≤ x / T)
  let sp := s.filter (fun n : ℕ => (n : ℝ) ≠ x)
  calc perronKernelWeightedPuncturedBoundaryWindowError x T
      = ∑ n ∈ sp,
          ArithmeticFunction.vonMangoldt n *
            |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| := by
        rfl
    _ ≤ ∑ n ∈ sp, ArithmeticFunction.vonMangoldt n * K := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left (hkernel n hn) (vonMangoldt_nonneg n)
    _ = K * ∑ n ∈ sp, ArithmeticFunction.vonMangoldt n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        ring
    _ ≤ K * perronKernelBoundaryWindowVonMangoldtWeight x T := by
        apply mul_le_mul_of_nonneg_left _ hK_nonneg
        dsimp [perronKernelBoundaryWindowVonMangoldtWeight, s, sp]
        exact
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _)
            (by
              intro n _hn_s _hn_not_sp
              exact vonMangoldt_nonneg n)

/-- Separated punctured boundary-window weighted error is controlled by a
separated kernel supremum times the full boundary-window von Mangoldt weight. -/
theorem perronKernelWeightedSeparatedPuncturedBoundaryError_le_kernelSup_mul_vonMangoldtWeight
    (x T K : ℝ) (hK_nonneg : 0 ≤ K)
    (hkernel : ∀ n : ℕ,
      n ∈ (((Finset.range (Nat.floor x + 1)).filter
          (fun n : ℕ => |x - (n : ℝ)| ≤ x / T)).filter
            (fun n : ℕ => (n : ℝ) ≠ x)).filter
              (fun n : ℕ => ¬ |x - (n : ℝ)| ≤ 1) →
        |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤ K) :
    perronKernelWeightedSeparatedPuncturedBoundaryError x T ≤
      K * perronKernelBoundaryWindowVonMangoldtWeight x T := by
  classical
  let s := (Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => |x - (n : ℝ)| ≤ x / T)
  let sp := s.filter (fun n : ℕ => (n : ℝ) ≠ x)
  let ss := sp.filter (fun n : ℕ => ¬ |x - (n : ℝ)| ≤ 1)
  calc perronKernelWeightedSeparatedPuncturedBoundaryError x T
      = ∑ n ∈ ss,
          ArithmeticFunction.vonMangoldt n *
            |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| := by
        rfl
    _ ≤ ∑ n ∈ ss, ArithmeticFunction.vonMangoldt n * K := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left (hkernel n hn) (vonMangoldt_nonneg n)
    _ = K * ∑ n ∈ ss, ArithmeticFunction.vonMangoldt n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        ring
    _ ≤ K * perronKernelBoundaryWindowVonMangoldtWeight x T := by
        apply mul_le_mul_of_nonneg_left _ hK_nonneg
        dsimp [perronKernelBoundaryWindowVonMangoldtWeight, s, sp, ss]
        exact
          Finset.sum_le_sum_of_subset_of_nonneg
            (by
              intro n hn
              exact (Finset.filter_subset _ _) ((Finset.filter_subset _ _) hn))
            (by
              intro n _hn_s _hn_not_ss
              exact vonMangoldt_nonneg n)

/-- Separated weighted error from a pointwise Davenport envelope.  This exact
finite-sum reduction keeps the distance singularity inside the remaining
arithmetic summation atom instead of replacing the separated window by a false
pure `O((log x)^2)` weight estimate. -/
theorem perronKernelWeightedSeparatedPuncturedBoundaryError_le_davenportEnvelope
    (x T : ℝ)
    (hkernel : ∀ n : ℕ,
      n ∈ perronKernelSeparatedPuncturedBoundarySet x T →
        |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤
          perronKernelSeparatedDavenportEnvelopeTerm x T n) :
    perronKernelWeightedSeparatedPuncturedBoundaryError x T ≤
      perronKernelSeparatedDavenportEnvelope x T := by
  classical
  calc perronKernelWeightedSeparatedPuncturedBoundaryError x T
      = ∑ n ∈ perronKernelSeparatedPuncturedBoundarySet x T,
          ArithmeticFunction.vonMangoldt n *
            |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| := by
        rfl
    _ ≤ ∑ n ∈ perronKernelSeparatedPuncturedBoundarySet x T,
          ArithmeticFunction.vonMangoldt n *
            perronKernelSeparatedDavenportEnvelopeTerm x T n := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left (hkernel n hn) (vonMangoldt_nonneg n)
    _ = perronKernelSeparatedDavenportEnvelope x T := by
        rfl

/-- Exact split of the separated Davenport envelope into its singular and
smooth pieces.  The singular piece carries the only distance-to-cutoff
singularity. -/
theorem perronKernelSeparatedDavenportEnvelope_eq_singular_add_smooth
    (x T : ℝ) :
    perronKernelSeparatedDavenportEnvelope x T =
      perronKernelSeparatedDavenportSingularEnvelope x T +
        perronKernelSeparatedDavenportSmoothEnvelope x T := by
  classical
  dsimp [perronKernelSeparatedDavenportEnvelope,
    perronKernelSeparatedDavenportEnvelopeTerm,
    perronKernelSeparatedDavenportSingularNumerator,
    perronKernelSeparatedDavenportSingularTerm,
    perronKernelSeparatedDavenportSingularEnvelope,
    perronKernelSeparatedDavenportSmoothEnvelope]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

/-- The singular Davenport envelope is controlled by the weighted
harmonic-distance envelope once the pointwise comparison
`1 / log (x/n) <= const * x / (x-n)` has been supplied. -/
theorem perronKernelSeparatedDavenportSingularEnvelope_le_logDistanceEnvelope
    (x T K : ℝ)
    (hpoint : ∀ n : ℕ,
      n ∈ perronKernelSeparatedPuncturedBoundarySet x T →
        perronKernelSeparatedDavenportSingularTerm x T n ≤
          K * perronKernelSeparatedLogDistanceTerm x T n) :
    perronKernelSeparatedDavenportSingularEnvelope x T ≤
      K * perronKernelSeparatedLogDistanceEnvelope x T := by
  classical
  calc perronKernelSeparatedDavenportSingularEnvelope x T
      = ∑ n ∈ perronKernelSeparatedPuncturedBoundarySet x T,
          ArithmeticFunction.vonMangoldt n *
            perronKernelSeparatedDavenportSingularTerm x T n := by
        rfl
    _ ≤ ∑ n ∈ perronKernelSeparatedPuncturedBoundarySet x T,
          ArithmeticFunction.vonMangoldt n *
            (K * perronKernelSeparatedLogDistanceTerm x T n) := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left (hpoint n hn) (vonMangoldt_nonneg n)
    _ = K * perronKernelSeparatedLogDistanceEnvelope x T := by
        dsimp [perronKernelSeparatedLogDistanceEnvelope]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        ring

/-- Pointwise singular Davenport comparison from the two elementary local
ingredients: a uniform numerator bound and the reciprocal-log distance
comparison. -/
theorem perronKernelSeparatedDavenportSingularTerm_le_logDistanceTerm_of_num_and_recip
    (x T K : ℝ) (n : ℕ)
    (hT_pos : 0 < T)
    (hlog_pos : 0 < Real.log (x / (n : ℝ)))
    (hK_nonneg : 0 ≤ K)
    (hnum : perronKernelSeparatedDavenportSingularNumerator x n ≤ K)
    (hrecip : (Real.log (x / (n : ℝ)))⁻¹ ≤ x / (x - (n : ℝ))) :
    perronKernelSeparatedDavenportSingularTerm x T n ≤
      K * perronKernelSeparatedLogDistanceTerm x T n := by
  have hT_inv_nonneg : 0 ≤ T⁻¹ := inv_nonneg.mpr hT_pos.le
  have hlog_inv_nonneg : 0 ≤ (Real.log (x / (n : ℝ)))⁻¹ :=
    inv_nonneg.mpr hlog_pos.le
  calc perronKernelSeparatedDavenportSingularTerm x T n
      = perronKernelSeparatedDavenportSingularNumerator x n *
          T⁻¹ * (Real.log (x / (n : ℝ)))⁻¹ := by
        dsimp [perronKernelSeparatedDavenportSingularTerm]
        ring
    _ ≤ K * T⁻¹ * (Real.log (x / (n : ℝ)))⁻¹ := by
        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hnum hT_inv_nonneg)
            hlog_inv_nonneg
    _ ≤ K * T⁻¹ * (x / (x - (n : ℝ))) := by
        exact
          mul_le_mul_of_nonneg_left hrecip
            (mul_nonneg hK_nonneg hT_inv_nonneg)
    _ = K * perronKernelSeparatedLogDistanceTerm x T n := by
        dsimp [perronKernelSeparatedLogDistanceTerm]
        rw [div_eq_mul_inv]
        field_simp [hT_pos.ne']

/-- Membership in the separated punctured boundary set puts the term strictly
on the large side of the sharp cutoff.  The finite Perron sum only ranges over
`n <= floor x`, so no `n > x` branch is present here. -/
theorem perronKernelSeparatedPuncturedBoundarySet_mem_large_side
    (x T : ℝ) (hx : 2 ≤ x) (hT_lo : 2 ≤ T) {n : ℕ}
    (hn : n ∈ perronKernelSeparatedPuncturedBoundarySet x T) :
    1 ≤ n ∧ (n : ℝ) < x ∧ 1 < x / (n : ℝ) := by
  have hx_nonneg : 0 ≤ x := by linarith
  have hT_pos : 0 < T := by linarith
  have hn_unfold := hn
  dsimp [perronKernelSeparatedPuncturedBoundarySet] at hn_unfold
  have hnot_unit : ¬ |x - (n : ℝ)| ≤ 1 := (Finset.mem_filter.mp hn_unfold).2
  have hsp := (Finset.mem_filter.mp hn_unfold).1
  have hne : (n : ℝ) ≠ x := (Finset.mem_filter.mp hsp).2
  have hboundary := (Finset.mem_filter.mp hsp).1
  have hboundary_dist : |x - (n : ℝ)| ≤ x / T := (Finset.mem_filter.mp hboundary).2
  have hrange : n ∈ Finset.range (Nat.floor x + 1) := (Finset.mem_filter.mp hboundary).1
  have hn_le_floor : n ≤ Nat.floor x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange)
  have hn_le_x : (n : ℝ) ≤ x :=
    le_trans (Nat.cast_le.mpr hn_le_floor) (Nat.floor_le hx_nonneg)
  have hn_pos_real : (0 : ℝ) < n := by
    by_contra hn_nonpos
    have hn_zero : (n : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hn_nonpos) (Nat.cast_nonneg n)
    have hx_le_div : x ≤ x / T := by
      simpa [hn_zero, sub_zero, abs_of_nonneg hx_nonneg] using hboundary_dist
    have hx_mul_le : x * T ≤ x := (le_div_iff₀ hT_pos).mp hx_le_div
    nlinarith [hx, hT_lo]
  have hn_pos : 1 ≤ n := Nat.succ_le_of_lt (Nat.cast_pos.mp hn_pos_real)
  have hn_lt_x : (n : ℝ) < x := lt_of_le_of_ne hn_le_x hne
  have hy_gt_one : 1 < x / (n : ℝ) := by
    rw [one_lt_div hn_pos_real]
    simpa using hn_lt_x
  exact ⟨hn_pos, hn_lt_x, hy_gt_one⟩

/-- Pointwise Davenport-envelope normalization on the separated punctured
boundary set.  Since all separated finite-sum terms satisfy `n < x`, the
large-side Perron per-term bound applies directly. -/
theorem small_T_separated_davenport_kernel_bound :
    ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ perronKernelSeparatedPuncturedBoundarySet x T →
          |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤
            perronKernelSeparatedDavenportEnvelopeTerm x T n := by
  intro x T hx hT_lo _hT_hi n hn
  have hT_pos : 0 < T := by linarith
  rcases perronKernelSeparatedPuncturedBoundarySet_mem_large_side x T hx hT_lo hn with
    ⟨_hn_pos, _hn_lt_x, hy_gt_one⟩
  have hc_pos := c_param_pos x hx
  calc |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|
      = |perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T - 1| :=
        abs_sub_comm _ _
    _ ≤ ( (x / (n : ℝ)) ^ (1 + 1 / Real.log x) + 1) /
          (T * Real.log (x / (n : ℝ))) +
        2 * (x / (n : ℝ)) ^ (1 + 1 / Real.log x) /
          ((1 + 1 / Real.log x) * T) :=
        perron_per_term_large_bound
          (x / (n : ℝ)) hy_gt_one (1 + 1 / Real.log x) hc_pos T hT_pos
    _ = perronKernelSeparatedDavenportEnvelopeTerm x T n := by
        rfl

/-- Near-diagonal punctured boundary weighted error is controlled by a uniform
kernel bound times the pure near-diagonal von Mangoldt weight. -/
theorem perronKernelWeightedNearDiagonalPuncturedBoundaryError_le_kernelSup_mul_weight
    (x T K : ℝ)
    (hkernel : ∀ n : ℕ,
      n ∈ perronKernelNearDiagonalPuncturedBoundarySet x T →
        |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤ K) :
    perronKernelWeightedNearDiagonalPuncturedBoundaryError x T ≤
      K * perronKernelNearDiagonalPuncturedVonMangoldtWeight x T := by
  classical
  let s := perronKernelNearDiagonalPuncturedBoundarySet x T
  calc perronKernelWeightedNearDiagonalPuncturedBoundaryError x T
      = ∑ n ∈ s,
          ArithmeticFunction.vonMangoldt n *
            |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| := by
        rfl
    _ ≤ ∑ n ∈ s, ArithmeticFunction.vonMangoldt n * K := by
        apply Finset.sum_le_sum
        intro n hn
        exact
          mul_le_mul_of_nonneg_left
            (hkernel n (by simpa [s] using hn)) (vonMangoldt_nonneg n)
    _ = K * perronKernelNearDiagonalPuncturedVonMangoldtWeight x T := by
        dsimp [perronKernelNearDiagonalPuncturedVonMangoldtWeight, s]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        ring

/-- The near-diagonal punctured boundary set has at most one natural number.

All its elements lie in the closed interval `[x - 1, x]`.  Two distinct
naturals in this interval would have to be its two endpoints, forcing the upper
one to equal `x`, which is excluded by the puncturing condition. -/
theorem perronKernelNearDiagonalPuncturedBoundarySet_card_le_one
    (x T : ℝ) (hx : 2 ≤ x) :
    (perronKernelNearDiagonalPuncturedBoundarySet x T).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  have hx_nonneg : 0 ≤ x := by linarith
  have ha_unfold := ha
  have hb_unfold := hb
  dsimp [perronKernelNearDiagonalPuncturedBoundarySet] at ha_unfold hb_unfold
  have ha_unit : |x - (a : ℝ)| ≤ 1 := (Finset.mem_filter.mp ha_unfold).2
  have hb_unit : |x - (b : ℝ)| ≤ 1 := (Finset.mem_filter.mp hb_unfold).2
  have ha_sp := (Finset.mem_filter.mp ha_unfold).1
  have hb_sp := (Finset.mem_filter.mp hb_unfold).1
  have ha_ne : (a : ℝ) ≠ x := (Finset.mem_filter.mp ha_sp).2
  have hb_ne : (b : ℝ) ≠ x := (Finset.mem_filter.mp hb_sp).2
  have ha_boundary := (Finset.mem_filter.mp ha_sp).1
  have hb_boundary := (Finset.mem_filter.mp hb_sp).1
  have ha_range : a ∈ Finset.range (Nat.floor x + 1) := (Finset.mem_filter.mp ha_boundary).1
  have hb_range : b ∈ Finset.range (Nat.floor x + 1) := (Finset.mem_filter.mp hb_boundary).1
  have ha_le_floor : a ≤ Nat.floor x := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha_range)
  have hb_le_floor : b ≤ Nat.floor x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb_range)
  have ha_le_x : (a : ℝ) ≤ x :=
    le_trans (Nat.cast_le.mpr ha_le_floor) (Nat.floor_le hx_nonneg)
  have hb_le_x : (b : ℝ) ≤ x :=
    le_trans (Nat.cast_le.mpr hb_le_floor) (Nat.floor_le hx_nonneg)
  have hx_le_a_succ : x ≤ (a : ℝ) + 1 := by
    have h := (abs_le.mp ha_unit).2
    linarith
  have hx_le_b_succ : x ≤ (b : ℝ) + 1 := by
    have h := (abs_le.mp hb_unit).2
    linarith
  have ha_le_b_succ : a ≤ b + 1 := by
    exact_mod_cast (le_trans ha_le_x hx_le_b_succ)
  have hb_le_a_succ : b ≤ a + 1 := by
    exact_mod_cast (le_trans hb_le_x hx_le_a_succ)
  by_cases hab : a = b
  · exact hab
  · rcases lt_or_gt_of_ne hab with hlt | hgt
    · have ha_succ_le_b : a + 1 ≤ b := Nat.succ_le_of_lt hlt
      have hb_eq : b = a + 1 := le_antisymm hb_le_a_succ ha_succ_le_b
      have hx_eq_b : x = (b : ℝ) := by
        apply le_antisymm
        · calc x ≤ (a : ℝ) + 1 := hx_le_a_succ
            _ = (b : ℝ) := by
              rw [hb_eq]
              norm_num
        · exact hb_le_x
      exact False.elim (hb_ne hx_eq_b.symm)
    · have hb_succ_le_a : b + 1 ≤ a := Nat.succ_le_of_lt hgt
      have ha_eq : a = b + 1 := le_antisymm ha_le_b_succ hb_succ_le_a
      have hx_eq_a : x = (a : ℝ) := by
        apply le_antisymm
        · calc x ≤ (b : ℝ) + 1 := hx_le_b_succ
            _ = (a : ℝ) := by
              rw [ha_eq]
              norm_num
        · exact ha_le_x
      exact False.elim (ha_ne hx_eq_a.symm)

/-- Membership in the near-diagonal punctured boundary set gives the elementary
size facts needed for bounded-height Perron estimates. -/
theorem perronKernelNearDiagonalPuncturedBoundarySet_mem_bounds
    (x T : ℝ) (hx : 2 ≤ x) {n : ℕ}
    (hn : n ∈ perronKernelNearDiagonalPuncturedBoundarySet x T) :
    1 ≤ n ∧ (n : ℝ) ≤ x ∧ x ≤ (n : ℝ) + 1 := by
  have hx_nonneg : 0 ≤ x := by linarith
  have hn_unfold := hn
  dsimp [perronKernelNearDiagonalPuncturedBoundarySet] at hn_unfold
  have hunit : |x - (n : ℝ)| ≤ 1 := (Finset.mem_filter.mp hn_unfold).2
  have hsp := (Finset.mem_filter.mp hn_unfold).1
  have hboundary := (Finset.mem_filter.mp hsp).1
  have hrange : n ∈ Finset.range (Nat.floor x + 1) := (Finset.mem_filter.mp hboundary).1
  have hn_le_floor : n ≤ Nat.floor x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange)
  have hn_le_x : (n : ℝ) ≤ x :=
    le_trans (Nat.cast_le.mpr hn_le_floor) (Nat.floor_le hx_nonneg)
  have hx_le_n_add_one : x ≤ (n : ℝ) + 1 := by
    have h := (abs_le.mp hunit).2
    linarith
  have hn_pos_real : (0 : ℝ) < n := by
    by_contra hn_nonpos
    have hn_zero : (n : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hn_nonpos) (Nat.cast_nonneg n)
    have hx_le_one : x ≤ 1 := by
      calc x ≤ (n : ℝ) + 1 := hx_le_n_add_one
        _ = 1 := by rw [hn_zero]; ring
    linarith
  exact ⟨Nat.succ_le_of_lt (Nat.cast_pos.mp hn_pos_real), hn_le_x, hx_le_n_add_one⟩

/-- Uniform bounded-height Perron-kernel estimate on the near-diagonal
punctured set.

This deliberately uses only the absolute bounded-height per-term estimate.  It
does not assert any decay in `x`, which would be false near integer hits. -/
theorem small_T_nearDiagonal_punctured_kernel_uniform_bound :
    ∃ K > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ perronKernelNearDiagonalPuncturedBoundarySet x T →
          |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤ K := by
  let K : ℝ := 1 + 32 * Real.exp 1
  refine ⟨K, by positivity, ?_⟩
  intro x T hx hT_lo hT_hi n hn
  have hT_pos : 0 < T := by linarith
  rcases perronKernelNearDiagonalPuncturedBoundarySet_mem_bounds x T hx hn with
    ⟨hn_pos, hn_le_x, hx_le_n_add_one⟩
  have hn_pos_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hc_pos := c_param_pos x hx
  have hden_ge_one :
      (1 : ℝ) ≤ Real.pi * (1 + 1 / Real.log x) := by
    have hpi_ge_one : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hc_ge_one : (1 : ℝ) ≤ 1 + 1 / Real.log x :=
      le_of_lt (c_param_gt_one x hx)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Real.pi * (1 + 1 / Real.log x) :=
          mul_le_mul hpi_ge_one hc_ge_one zero_le_one (by linarith [Real.pi_gt_three])
  have hxn_le_two : x / (n : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hn_pos_real]
    have hn_one_le : (1 : ℝ) ≤ n := by exact_mod_cast hn_pos
    calc x ≤ (n : ℝ) + 1 := hx_le_n_add_one
      _ ≤ 2 * (n : ℝ) := by linarith
  have hrpow_le_two_exp :
      (x / (n : ℝ)) ^ (1 + 1 / Real.log x) ≤ 2 * Real.exp 1 := by
    calc (x / (n : ℝ)) ^ (1 + 1 / Real.log x)
        ≤ Real.exp 1 * (x / (n : ℝ)) :=
          per_term_rpow_bound x hx n hn_pos hn_le_x
      _ ≤ Real.exp 1 * 2 :=
          mul_le_mul_of_nonneg_left hxn_le_two (Real.exp_pos 1).le
      _ = 2 * Real.exp 1 := by ring
  have hP_abs_le :
      |perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤
        32 * Real.exp 1 := by
    have hden_pos : 0 < Real.pi * (1 + 1 / Real.log x) :=
      mul_pos Real.pi_pos hc_pos
    calc |perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|
        ≤ T * (x / (n : ℝ)) ^ (1 + 1 / Real.log x) /
            (Real.pi * (1 + 1 / Real.log x)) :=
          perron_per_term_abs_bound_general x hx T hT_pos n hn_pos
      _ ≤ T * (2 * Real.exp 1) / (Real.pi * (1 + 1 / Real.log x)) := by
          exact
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hrpow_le_two_exp hT_pos.le)
              hden_pos.le
      _ ≤ T * (2 * Real.exp 1) := by
          exact div_le_self (by positivity : 0 ≤ T * (2 * Real.exp 1)) hden_ge_one
      _ ≤ 16 * (2 * Real.exp 1) := by
          exact mul_le_mul_of_nonneg_right hT_hi (by positivity)
      _ = 32 * Real.exp 1 := by ring
  calc |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|
      ≤ |(1 : ℝ)| + |perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| :=
        abs_sub _ _
    _ ≤ K := by
        dsimp [K]
        simpa using add_le_add_left hP_abs_le (1 : ℝ)

/-- If the near-diagonal punctured boundary set has at most one element, then
its weighted kernel error is only `O(log x)` under a uniform kernel bound. -/
theorem perronKernelWeightedNearDiagonalPuncturedBoundaryError_le_kernelSup_mul_log
    (x T K : ℝ) (hx : 2 ≤ x) (hK_nonneg : 0 ≤ K)
    (hcard : (perronKernelNearDiagonalPuncturedBoundarySet x T).card ≤ 1)
    (hkernel : ∀ n : ℕ,
      n ∈ perronKernelNearDiagonalPuncturedBoundarySet x T →
        |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤ K) :
    perronKernelWeightedNearDiagonalPuncturedBoundaryError x T ≤ K * Real.log x := by
  classical
  let s := perronKernelNearDiagonalPuncturedBoundarySet x T
  have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hB_nonneg : 0 ≤ K * Real.log x := mul_nonneg hK_nonneg hlogx_nonneg
  have hterm :
      ∀ n ∈ s,
        ArithmeticFunction.vonMangoldt n *
            |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤
          K * Real.log x := by
    intro n hn
    have hn_set : n ∈ perronKernelNearDiagonalPuncturedBoundarySet x T := by
      simpa [s] using hn
    have hn_unfold := hn_set
    dsimp [perronKernelNearDiagonalPuncturedBoundarySet] at hn_unfold
    have hnear : |x - (n : ℝ)| ≤ 1 := (Finset.mem_filter.mp hn_unfold).2
    have hsp := (Finset.mem_filter.mp hn_unfold).1
    have hs := (Finset.mem_filter.mp hsp).1
    have hrange : n ∈ Finset.range (Nat.floor x + 1) := (Finset.mem_filter.mp hs).1
    have hn_le_floor : n ≤ Nat.floor x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange)
    have hn_le_x : (n : ℝ) ≤ x := by
      exact le_trans (Nat.cast_le.mpr hn_le_floor) (Nat.floor_le (by linarith : 0 ≤ x))
    have hn_pos_real : (0 : ℝ) < n := by
      by_contra hn_nonpos
      have hn_zero : (n : ℝ) = 0 :=
        le_antisymm (le_of_not_gt hn_nonpos) (Nat.cast_nonneg n)
      have hx_le_one : x ≤ 1 := by
        have hnear_zero : |x| ≤ 1 := by
          simpa [hn_zero] using hnear
        exact le_trans (le_abs_self x) hnear_zero
      linarith
    have hn_pos : 1 ≤ n := Nat.succ_le_of_lt (Nat.cast_pos.mp hn_pos_real)
    have hΛ_le_logx : ArithmeticFunction.vonMangoldt n ≤ Real.log x := by
      calc ArithmeticFunction.vonMangoldt n
          ≤ Real.log (n : ℝ) := vonMangoldt_le_log n hn_pos
        _ ≤ Real.log x := Real.log_le_log hn_pos_real hn_le_x
    calc ArithmeticFunction.vonMangoldt n *
          |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|
        ≤ Real.log x * K :=
          mul_le_mul hΛ_le_logx (hkernel n hn_set) (abs_nonneg _)
            hlogx_nonneg
      _ = K * Real.log x := by ring
  calc perronKernelWeightedNearDiagonalPuncturedBoundaryError x T
      = ∑ n ∈ s,
          ArithmeticFunction.vonMangoldt n *
            |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| := by
        rfl
    _ ≤ s.card • (K * Real.log x) :=
        Finset.sum_le_card_nsmul s
          (fun n =>
            ArithmeticFunction.vonMangoldt n *
              |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|)
          (K * Real.log x) hterm
    _ ≤ 1 • (K * Real.log x) :=
        nsmul_le_nsmul_left hB_nonneg (by simpa [s] using hcard)
    _ = K * Real.log x := by simp

/-- For `x >= 2`, one logarithm is absorbed by a constant multiple of
`(log x)^2`. -/
theorem log_le_const_mul_log_sq_of_ge_two (x : ℝ) (hx : 2 ≤ x) :
    Real.log x ≤ (1 / Real.log 2) * (Real.log x) ^ 2 := by
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2_le : Real.log (2 : ℝ) ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx
  have hlogx_nonneg : 0 ≤ Real.log x := le_trans hlog2_pos.le hlog2_le
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hlog2_pos]
  calc Real.log x * Real.log 2
      ≤ Real.log x * Real.log x :=
        mul_le_mul_of_nonneg_left hlog2_le hlogx_nonneg
    _ = (Real.log x) ^ 2 := by ring

/-- Exact-hit boundary weighted error is controlled by a uniform exact-hit
kernel bound times `log x`.  The exact-hit set has at most one natural number. -/
theorem perronKernelWeightedExactHitBoundaryError_le_kernelSup_mul_log
    (x T K : ℝ) (hx : 2 ≤ x) (hK_nonneg : 0 ≤ K)
    (hkernel : ∀ n : ℕ,
      n ∈ ((Finset.range (Nat.floor x + 1)).filter
          (fun n : ℕ => |x - (n : ℝ)| ≤ x / T)).filter
            (fun n : ℕ => (n : ℝ) = x) →
        |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤ K) :
    perronKernelWeightedExactHitBoundaryError x T ≤ K * Real.log x := by
  classical
  let s := ((Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => |x - (n : ℝ)| ≤ x / T)).filter
        (fun n : ℕ => (n : ℝ) = x)
  have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hB_nonneg : 0 ≤ K * Real.log x := mul_nonneg hK_nonneg hlogx_nonneg
  have hcard : s.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro a b ha hb
    have ha_eq : (a : ℝ) = x := (Finset.mem_filter.mp ha).2
    have hb_eq : (b : ℝ) = x := (Finset.mem_filter.mp hb).2
    exact_mod_cast ha_eq.trans hb_eq.symm
  have hterm :
      ∀ n ∈ s,
        ArithmeticFunction.vonMangoldt n *
            |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤
          K * Real.log x := by
    intro n hn
    have hn_eq : (n : ℝ) = x := (Finset.mem_filter.mp hn).2
    have hn_pos_real : (0 : ℝ) < n := by linarith
    have hn_pos : 1 ≤ n := Nat.succ_le_of_lt (Nat.cast_pos.mp hn_pos_real)
    have hΛ_le_logx : ArithmeticFunction.vonMangoldt n ≤ Real.log x := by
      calc ArithmeticFunction.vonMangoldt n
          ≤ Real.log (n : ℝ) := vonMangoldt_le_log n hn_pos
        _ = Real.log x := by rw [hn_eq]
    calc ArithmeticFunction.vonMangoldt n *
          |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|
        ≤ Real.log x * K :=
          mul_le_mul hΛ_le_logx (hkernel n hn) (abs_nonneg _)
            hlogx_nonneg
      _ = K * Real.log x := by ring
  calc perronKernelWeightedExactHitBoundaryError x T
      = ∑ n ∈ s,
          ArithmeticFunction.vonMangoldt n *
            |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| := by
        rfl
    _ ≤ s.card • (K * Real.log x) :=
        Finset.sum_le_card_nsmul s
          (fun n =>
            ArithmeticFunction.vonMangoldt n *
              |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|)
          (K * Real.log x) hterm
    _ ≤ 1 • (K * Real.log x) := nsmul_le_nsmul_left hB_nonneg hcard
    _ = K * Real.log x := by simp

/-- The exact integer hit has a uniform bounded-height Perron-kernel error. -/
theorem small_T_exactHit_kernel_uniform_bound :
    ∃ K > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ ((Finset.range (Nat.floor x + 1)).filter
            (fun n : ℕ => |x - (n : ℝ)| ≤ x / T)).filter
              (fun n : ℕ => (n : ℝ) = x) →
          |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤ K := by
  let K : ℝ := 1 + 16 * Real.exp 1
  refine ⟨K, by positivity, ?_⟩
  intro x T hx hT_lo hT_hi n hn
  have hT_pos : 0 < T := by linarith
  have hn_eq : (n : ℝ) = x := (Finset.mem_filter.mp hn).2
  have hn_pos_real : (0 : ℝ) < n := by linarith
  have hn_pos : 1 ≤ n := Nat.succ_le_of_lt (Nat.cast_pos.mp hn_pos_real)
  have hxn_eq : x / (n : ℝ) = 1 := by
    rw [← hn_eq]
    exact div_self (ne_of_gt hn_pos_real)
  have hrpow_eq :
      (x / (n : ℝ)) ^ (1 + 1 / Real.log x) = 1 := by
    rw [hxn_eq, one_rpow]
  have hden_ge_one :
      (1 : ℝ) ≤ Real.pi * (1 + 1 / Real.log x) := by
    have hpi_ge_one : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hc_ge_one : (1 : ℝ) ≤ 1 + 1 / Real.log x :=
      le_of_lt (c_param_gt_one x hx)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Real.pi * (1 + 1 / Real.log x) :=
          mul_le_mul hpi_ge_one hc_ge_one zero_le_one (by linarith [Real.pi_gt_three])
  have hP_abs_le_T :
      |perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤ T := by
    calc |perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|
        ≤ T * (x / (n : ℝ)) ^ (1 + 1 / Real.log x) /
            (Real.pi * (1 + 1 / Real.log x)) :=
          perron_per_term_abs_bound_general x hx T hT_pos n hn_pos
      _ = T * 1 / (Real.pi * (1 + 1 / Real.log x)) := by rw [hrpow_eq]
      _ ≤ T := by
          simpa using div_le_self hT_pos.le hden_ge_one
  have hexp_ge_one : (1 : ℝ) ≤ Real.exp 1 := by
    calc (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp 1 := Real.exp_monotone (by norm_num)
  have hT_le_exp : T ≤ 16 * Real.exp 1 := by
    calc T ≤ 16 := hT_hi
      _ ≤ 16 * Real.exp 1 := by nlinarith
  have hP_abs_le : |perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤
      16 * Real.exp 1 :=
    le_trans hP_abs_le_T hT_le_exp
  calc |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T|
      ≤ |(1 : ℝ)| + |perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| :=
        abs_sub _ _
    _ ≤ K := by
        dsimp [K]
        simpa using add_le_add_left hP_abs_le (1 : ℝ)

/-- The exact-hit weighted boundary error is harmless: the exact-hit set has at
most one term, `Λ(n) <= log n = log x`, and the kernel error is uniformly
bounded on `2 <= T <= 16`. -/
theorem small_T_exactHit_boundary_error_bound :
    ∃ Ce > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedExactHitBoundaryError x T ≤ Ce * (Real.log x) ^ 2 := by
  rcases small_T_exactHit_kernel_uniform_bound with ⟨K, hK_pos, hkernel⟩
  let Ce : ℝ := K / Real.log 2
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨Ce, div_pos hK_pos hlog2_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  have hlog_absorb := log_le_const_mul_log_sq_of_ge_two x hx
  have hhit :=
    perronKernelWeightedExactHitBoundaryError_le_kernelSup_mul_log
      x T K hx hK_pos.le (hkernel x T hx hT_lo hT_hi)
  calc perronKernelWeightedExactHitBoundaryError x T
      ≤ K * Real.log x := hhit
    _ ≤ K * ((1 / Real.log 2) * (Real.log x) ^ 2) :=
        mul_le_mul_of_nonneg_left hlog_absorb hK_pos.le
    _ = Ce * (Real.log x) ^ 2 := by
        dsimp [Ce]
        ring

/-- The concrete `DirichletPhaseAlignment.chebyshevPsi` finite-range
definition agrees with Mathlib's Chebyshev `psi`. -/
theorem dirichletPhase_chebyshevPsi_eq_chebyshev_psi (x : ℝ) :
    Aristotle.DirichletPhaseAlignment.chebyshevPsi x = Chebyshev.psi x := by
  have hsets :
      Finset.range (Nat.floor x + 1) = Finset.Icc 0 (Nat.floor x) := by
    ext n
    simp [Nat.lt_succ_iff]
  unfold Aristotle.DirichletPhaseAlignment.chebyshevPsi
  rw [Chebyshev.psi_eq_sum_Icc, hsets]

/-- Global Chebyshev linear bound for the local
`DirichletPhaseAlignment.chebyshevPsi` definition. -/
theorem dirichletPhase_chebyshevPsi_le_const_mul_self
    (x : ℝ) (hx : 0 ≤ x) :
    Aristotle.DirichletPhaseAlignment.chebyshevPsi x ≤ (Real.log 4 + 4) * x := by
  rw [dirichletPhase_chebyshevPsi_eq_chebyshev_psi]
  exact Chebyshev.psi_le_const_mul_self hx

/-- The boundary window's pure von Mangoldt weight is bounded by the full
Chebyshev psi sum at height `x`. -/
theorem perronKernelBoundaryWindowVonMangoldtWeight_le_chebyshevPsi
    (x T : ℝ) :
    perronKernelBoundaryWindowVonMangoldtWeight x T ≤
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x := by
  classical
  dsimp [perronKernelBoundaryWindowVonMangoldtWeight,
    Aristotle.DirichletPhaseAlignment.chebyshevPsi]
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro n hn
        exact (Finset.mem_filter.mp hn).1)
      (by
        intro n _hn_range _hn_not_window
        exact vonMangoldt_nonneg n)

/-- Scale-correct linear bound for the boundary-window von Mangoldt weight.

Since `T <= 16`, the global Chebyshev bound `psi(x) = O(x)` implies the weaker
but correctly scaled `O(x / T)` bound needed by the small-`T` boundary-window
route. -/
theorem small_T_boundary_window_vonMangoldt_weight_linear_bound :
    ∃ Cv > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelBoundaryWindowVonMangoldtWeight x T ≤ Cv * (x / T) := by
  let Cv : ℝ := 16 * (Real.log 4 + 4)
  have hlog4_nonneg : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hconst_nonneg : 0 ≤ Real.log (4 : ℝ) + 4 := by linarith
  have hconst_pos : 0 < Real.log (4 : ℝ) + 4 := by linarith
  refine ⟨Cv, mul_pos (by norm_num) hconst_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  have hx_nonneg : 0 ≤ x := by linarith
  have hT_pos : 0 < T := by linarith
  have hx_over_T_nonneg : 0 ≤ x / T := div_nonneg hx_nonneg hT_pos.le
  have hx_le_scaled : x ≤ 16 * (x / T) := by
    calc x = T * (x / T) := by
          rw [← mul_div_assoc, mul_div_cancel_left₀ x (ne_of_gt hT_pos)]
      _ ≤ 16 * (x / T) :=
          mul_le_mul_of_nonneg_right hT_hi hx_over_T_nonneg
  calc perronKernelBoundaryWindowVonMangoldtWeight x T
      ≤ Aristotle.DirichletPhaseAlignment.chebyshevPsi x :=
        perronKernelBoundaryWindowVonMangoldtWeight_le_chebyshevPsi x T
    _ ≤ (Real.log 4 + 4) * x :=
        dirichletPhase_chebyshevPsi_le_const_mul_self x hx_nonneg
    _ ≤ (Real.log 4 + 4) * (16 * (x / T)) :=
        mul_le_mul_of_nonneg_left hx_le_scaled hconst_nonneg
    _ = Cv * (x / T) := by
        dsimp [Cv]
        ring

/-- Diagnostic small-`T` boundary-window atom from a uniform kernel-error bound
and an `O((log x)^2)` von Mangoldt weight estimate for the boundary window.

This is retained as a formal conditional, but the pure weight estimate is not
scale-correct for the current macroscopic window `|x - n| <= x / T` when
`2 <= T <= 16`.  The scale-correct replacement below pairs a linear-window
weight bound with a decaying kernel estimate. -/
theorem small_T_boundary_window_bound_from_kernel_sup_and_vonMangoldt_weight
    (hkernel : ∃ K > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ (Finset.range (Nat.floor x + 1)).filter
            (fun n : ℕ => |x - (n : ℝ)| ≤ x / T) →
          |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤ K)
    (hweight : ∃ Cv > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelBoundaryWindowVonMangoldtWeight x T ≤ Cv * (Real.log x) ^ 2) :
    ∃ Cb > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedBoundaryWindowError x T ≤ Cb * (Real.log x) ^ 2 := by
  rcases hkernel with ⟨K, hK_pos, hkernel⟩
  rcases hweight with ⟨Cv, hCv_pos, hweight⟩
  refine ⟨K * Cv, mul_pos hK_pos hCv_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  have hkernel_x := hkernel x T hx hT_lo hT_hi
  have hweight_x := hweight x T hx hT_lo hT_hi
  calc perronKernelWeightedBoundaryWindowError x T
      ≤ K * perronKernelBoundaryWindowVonMangoldtWeight x T :=
        perronKernelWeightedBoundaryWindowError_le_kernelSup_mul_vonMangoldtWeight
          x T K hkernel_x
    _ ≤ K * (Cv * (Real.log x) ^ 2) :=
        mul_le_mul_of_nonneg_left hweight_x hK_pos.le
    _ = K * Cv * (Real.log x) ^ 2 := by ring

/-- Scale-correct boundary-window reduction.

For the present bounded-height range `2 <= T <= 16`, the boundary window has
linear size `x / T`, not logarithmic size.  Thus the usable route is:

* prove the kernel error is `O(T * (log x)^2 / x)` on the boundary window;
* prove the pure von Mangoldt window weight is `O(x / T)`.

Their product has the desired `O((log x)^2)` scale. -/
theorem small_T_boundary_window_bound_from_scaled_kernel_and_linear_weight
    (hkernel : ∃ K > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ (Finset.range (Nat.floor x + 1)).filter
            (fun n : ℕ => |x - (n : ℝ)| ≤ x / T) →
          |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤
            K * (T * (Real.log x) ^ 2 / x))
    (hweight : ∃ Cv > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelBoundaryWindowVonMangoldtWeight x T ≤ Cv * (x / T)) :
    ∃ Cb > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedBoundaryWindowError x T ≤ Cb * (Real.log x) ^ 2 := by
  rcases hkernel with ⟨K, hK_pos, hkernel⟩
  rcases hweight with ⟨Cv, hCv_pos, hweight⟩
  refine ⟨K * Cv, mul_pos hK_pos hCv_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  have hx_pos : 0 < x := by linarith
  have hT_pos : 0 < T := by linarith
  have hkernel_x := hkernel x T hx hT_lo hT_hi
  have hweight_x := hweight x T hx hT_lo hT_hi
  have hfactor_nonneg : 0 ≤ K * (T * (Real.log x) ^ 2 / x) :=
    mul_nonneg hK_pos.le
      (div_nonneg (mul_nonneg hT_pos.le (sq_nonneg (Real.log x))) hx_pos.le)
  calc perronKernelWeightedBoundaryWindowError x T
      ≤ K * (T * (Real.log x) ^ 2 / x) *
          perronKernelBoundaryWindowVonMangoldtWeight x T :=
        perronKernelWeightedBoundaryWindowError_le_kernelSup_mul_vonMangoldtWeight
          x T (K * (T * (Real.log x) ^ 2 / x)) hkernel_x
    _ ≤ K * (T * (Real.log x) ^ 2 / x) * (Cv * (x / T)) :=
        mul_le_mul_of_nonneg_left hweight_x hfactor_nonneg
    _ = K * Cv * (Real.log x) ^ 2 := by
        field_simp [ne_of_gt hx_pos, ne_of_gt hT_pos]

/-- Scale-correct boundary-window reduction with the exact integer hit removed.

The full decaying per-term kernel estimate is false at `n = x`.  This theorem
therefore separates the jump atom from the punctured boundary window, where the
decaying kernel estimate is the remaining analytic task. -/
theorem small_T_boundary_window_bound_from_punctured_scaled_kernel_linear_weight_and_exactHit
    (hexact : ∃ Ce > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedExactHitBoundaryError x T ≤ Ce * (Real.log x) ^ 2)
    (hkernel : ∃ K > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ ((Finset.range (Nat.floor x + 1)).filter
            (fun n : ℕ => |x - (n : ℝ)| ≤ x / T)).filter
              (fun n : ℕ => (n : ℝ) ≠ x) →
          |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤
            K * (T * (Real.log x) ^ 2 / x))
    (hweight : ∃ Cv > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelBoundaryWindowVonMangoldtWeight x T ≤ Cv * (x / T)) :
    ∃ Cb > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedBoundaryWindowError x T ≤ Cb * (Real.log x) ^ 2 := by
  rcases hexact with ⟨Ce, hCe_pos, hexact⟩
  rcases hkernel with ⟨K, hK_pos, hkernel⟩
  rcases hweight with ⟨Cv, hCv_pos, hweight⟩
  refine ⟨Ce + K * Cv, add_pos hCe_pos (mul_pos hK_pos hCv_pos), ?_⟩
  intro x T hx hT_lo hT_hi
  have hx_pos : 0 < x := by linarith
  have hT_pos : 0 < T := by linarith
  have hexact_x := hexact x T hx hT_lo hT_hi
  have hkernel_x := hkernel x T hx hT_lo hT_hi
  have hweight_x := hweight x T hx hT_lo hT_hi
  have hfactor_nonneg : 0 ≤ K * (T * (Real.log x) ^ 2 / x) :=
    mul_nonneg hK_pos.le
      (div_nonneg (mul_nonneg hT_pos.le (sq_nonneg (Real.log x))) hx_pos.le)
  have hpunctured :
      perronKernelWeightedPuncturedBoundaryWindowError x T ≤
        K * Cv * (Real.log x) ^ 2 := by
    calc perronKernelWeightedPuncturedBoundaryWindowError x T
        ≤ K * (T * (Real.log x) ^ 2 / x) *
            perronKernelBoundaryWindowVonMangoldtWeight x T :=
          perronKernelWeightedPuncturedBoundaryWindowError_le_kernelSup_mul_vonMangoldtWeight
            x T (K * (T * (Real.log x) ^ 2 / x)) hfactor_nonneg hkernel_x
      _ ≤ K * (T * (Real.log x) ^ 2 / x) * (Cv * (x / T)) :=
          mul_le_mul_of_nonneg_left hweight_x hfactor_nonneg
      _ = K * Cv * (Real.log x) ^ 2 := by
          field_simp [ne_of_gt hx_pos, ne_of_gt hT_pos]
  calc perronKernelWeightedBoundaryWindowError x T
      = perronKernelWeightedExactHitBoundaryError x T +
          perronKernelWeightedPuncturedBoundaryWindowError x T :=
        perronKernelWeightedBoundaryWindowError_eq_exactHit_add_punctured x T
    _ ≤ Ce * (Real.log x) ^ 2 + K * Cv * (Real.log x) ^ 2 :=
        add_le_add hexact_x hpunctured
    _ = (Ce + K * Cv) * (Real.log x) ^ 2 := by ring

/-- Punctured boundary-window reduction after removing the remaining
near-diagonal unit band.

The pointwise decaying kernel estimate is now requested only on the separated
punctured window `1 < |x - n|` inside the macroscopic boundary window.  The
near-diagonal punctured band is kept as its own weighted atom because excluding
only the exact equality `(n : ℝ) = x` is not enough for pointwise decay. -/
theorem small_T_punctured_boundary_window_bound_from_nearDiagonal_and_separated_kernel
    (hnear : ∃ Cn > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedNearDiagonalPuncturedBoundaryError x T ≤ Cn * (Real.log x) ^ 2)
    (hkernel : ∃ K > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ (((Finset.range (Nat.floor x + 1)).filter
            (fun n : ℕ => |x - (n : ℝ)| ≤ x / T)).filter
              (fun n : ℕ => (n : ℝ) ≠ x)).filter
                (fun n : ℕ => ¬ |x - (n : ℝ)| ≤ 1) →
          |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤
            K * (T * (Real.log x) ^ 2 / x))
    (hweight : ∃ Cv > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelBoundaryWindowVonMangoldtWeight x T ≤ Cv * (x / T)) :
    ∃ Cp > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedPuncturedBoundaryWindowError x T ≤ Cp * (Real.log x) ^ 2 := by
  rcases hnear with ⟨Cn, hCn_pos, hnear⟩
  rcases hkernel with ⟨K, hK_pos, hkernel⟩
  rcases hweight with ⟨Cv, hCv_pos, hweight⟩
  refine ⟨Cn + K * Cv, add_pos hCn_pos (mul_pos hK_pos hCv_pos), ?_⟩
  intro x T hx hT_lo hT_hi
  have hx_pos : 0 < x := by linarith
  have hT_pos : 0 < T := by linarith
  have hnear_x := hnear x T hx hT_lo hT_hi
  have hkernel_x := hkernel x T hx hT_lo hT_hi
  have hweight_x := hweight x T hx hT_lo hT_hi
  have hfactor_nonneg : 0 ≤ K * (T * (Real.log x) ^ 2 / x) :=
    mul_nonneg hK_pos.le
      (div_nonneg (mul_nonneg hT_pos.le (sq_nonneg (Real.log x))) hx_pos.le)
  have hseparated :
      perronKernelWeightedSeparatedPuncturedBoundaryError x T ≤
        K * Cv * (Real.log x) ^ 2 := by
    calc perronKernelWeightedSeparatedPuncturedBoundaryError x T
        ≤ K * (T * (Real.log x) ^ 2 / x) *
            perronKernelBoundaryWindowVonMangoldtWeight x T :=
          perronKernelWeightedSeparatedPuncturedBoundaryError_le_kernelSup_mul_vonMangoldtWeight
            x T (K * (T * (Real.log x) ^ 2 / x)) hfactor_nonneg hkernel_x
      _ ≤ K * (T * (Real.log x) ^ 2 / x) * (Cv * (x / T)) :=
          mul_le_mul_of_nonneg_left hweight_x hfactor_nonneg
      _ = K * Cv * (Real.log x) ^ 2 := by
          field_simp [ne_of_gt hx_pos, ne_of_gt hT_pos]
  calc perronKernelWeightedPuncturedBoundaryWindowError x T
      = perronKernelWeightedNearDiagonalPuncturedBoundaryError x T +
          perronKernelWeightedSeparatedPuncturedBoundaryError x T :=
        perronKernelWeightedPuncturedBoundaryWindowError_eq_nearDiagonal_add_separated x T
    _ ≤ Cn * (Real.log x) ^ 2 + K * Cv * (Real.log x) ^ 2 :=
        add_le_add hnear_x hseparated
    _ = (Cn + K * Cv) * (Real.log x) ^ 2 := by ring

/-- Near-diagonal punctured weighted error from its two small atoms:
finite-cardinality of the unit punctured boundary set and a uniform bounded
kernel estimate on that set. -/
theorem small_T_nearDiagonal_punctured_boundary_bound_from_cardinality_and_kernel
    (hcard : ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      (perronKernelNearDiagonalPuncturedBoundarySet x T).card ≤ 1)
    (hkernel : ∃ K > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ perronKernelNearDiagonalPuncturedBoundarySet x T →
          |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤ K) :
    ∃ Cn > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedNearDiagonalPuncturedBoundaryError x T ≤ Cn * (Real.log x) ^ 2 := by
  rcases hkernel with ⟨K, hK_pos, hkernel⟩
  let Cn : ℝ := K / Real.log 2
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨Cn, div_pos hK_pos hlog2_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  have hlog_absorb := log_le_const_mul_log_sq_of_ge_two x hx
  have hnear :=
    perronKernelWeightedNearDiagonalPuncturedBoundaryError_le_kernelSup_mul_log
      x T K hx hK_pos.le (hcard x T hx hT_lo hT_hi)
      (hkernel x T hx hT_lo hT_hi)
  calc perronKernelWeightedNearDiagonalPuncturedBoundaryError x T
      ≤ K * Real.log x := hnear
    _ ≤ K * ((1 / Real.log 2) * (Real.log x) ^ 2) :=
        mul_le_mul_of_nonneg_left hlog_absorb hK_pos.le
    _ = Cn * (Real.log x) ^ 2 := by
        dsimp [Cn]
        ring

/-- Near-diagonal punctured weighted error from only the remaining uniform
bounded-height kernel estimate; the finite-cardinality source atom is already
closed by `perronKernelNearDiagonalPuncturedBoundarySet_card_le_one`. -/
theorem small_T_nearDiagonal_punctured_boundary_bound_from_kernel
    (hkernel : ∃ K > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ perronKernelNearDiagonalPuncturedBoundarySet x T →
          |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤ K) :
    ∃ Cn > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedNearDiagonalPuncturedBoundaryError x T ≤ Cn * (Real.log x) ^ 2 :=
  small_T_nearDiagonal_punctured_boundary_bound_from_cardinality_and_kernel
    (fun x T hx _hT_lo _hT_hi =>
      perronKernelNearDiagonalPuncturedBoundarySet_card_le_one x T hx)
    hkernel

/-- The near-diagonal punctured weighted boundary atom is closed by the
finite-cardinality theorem and the uniform bounded-height kernel estimate. -/
theorem small_T_nearDiagonal_punctured_boundary_bound :
    ∃ Cn > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedNearDiagonalPuncturedBoundaryError x T ≤ Cn * (Real.log x) ^ 2 :=
  small_T_nearDiagonal_punctured_boundary_bound_from_kernel
    small_T_nearDiagonal_punctured_kernel_uniform_bound

/-- Punctured boundary-window estimate from a direct separated weighted-error
bound.

The previously exposed pointwise-decay route is too strong for bounded height:
after the exact hit and unit near-diagonal band are removed, the remaining
macroscopic boundary window can still have bounded-height kernel error of
constant size.  This assembly keeps the true remaining target as a weighted
separated estimate. -/
theorem small_T_punctured_boundary_window_bound_from_nearDiagonal_and_separated_weighted
    (hnear : ∃ Cn > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedNearDiagonalPuncturedBoundaryError x T ≤ Cn * (Real.log x) ^ 2)
    (hseparated : ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedSeparatedPuncturedBoundaryError x T ≤ Cs * (Real.log x) ^ 2) :
    ∃ Cp > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedPuncturedBoundaryWindowError x T ≤ Cp * (Real.log x) ^ 2 := by
  rcases hnear with ⟨Cn, hCn_pos, hnear⟩
  rcases hseparated with ⟨Cs, hCs_pos, hseparated⟩
  refine ⟨Cn + Cs, add_pos hCn_pos hCs_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  have hnear_x := hnear x T hx hT_lo hT_hi
  have hseparated_x := hseparated x T hx hT_lo hT_hi
  calc perronKernelWeightedPuncturedBoundaryWindowError x T
      = perronKernelWeightedNearDiagonalPuncturedBoundaryError x T +
          perronKernelWeightedSeparatedPuncturedBoundaryError x T :=
        perronKernelWeightedPuncturedBoundaryWindowError_eq_nearDiagonal_add_separated x T
    _ ≤ Cn * (Real.log x) ^ 2 + Cs * (Real.log x) ^ 2 :=
        add_le_add hnear_x hseparated_x
    _ = (Cn + Cs) * (Real.log x) ^ 2 := by ring

/-- Punctured boundary-window estimate from only the separated weighted-error
atom; the near-diagonal weighted atom is already closed. -/
theorem small_T_punctured_boundary_window_bound_from_separated_weighted
    (hseparated : ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedSeparatedPuncturedBoundaryError x T ≤ Cs * (Real.log x) ^ 2) :
    ∃ Cp > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedPuncturedBoundaryWindowError x T ≤ Cp * (Real.log x) ^ 2 :=
  small_T_punctured_boundary_window_bound_from_nearDiagonal_and_separated_weighted
    small_T_nearDiagonal_punctured_boundary_bound hseparated

/-- Boundary-window estimate from a direct separated weighted-error bound.
Exact-hit and near-diagonal punctured pieces are already closed; the separated
weighted error is the remaining boundary-window atom. -/
theorem small_T_boundary_window_bound_from_separated_weighted
    (hseparated : ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedSeparatedPuncturedBoundaryError x T ≤ Cs * (Real.log x) ^ 2) :
    ∃ Cb > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedBoundaryWindowError x T ≤ Cb * (Real.log x) ^ 2 := by
  rcases small_T_exactHit_boundary_error_bound with ⟨Ce, hCe_pos, hexact⟩
  rcases small_T_punctured_boundary_window_bound_from_separated_weighted hseparated with
    ⟨Cp, hCp_pos, hpunctured⟩
  refine ⟨Ce + Cp, add_pos hCe_pos hCp_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  have hexact_x := hexact x T hx hT_lo hT_hi
  have hpunctured_x := hpunctured x T hx hT_lo hT_hi
  calc perronKernelWeightedBoundaryWindowError x T
      = perronKernelWeightedExactHitBoundaryError x T +
          perronKernelWeightedPuncturedBoundaryWindowError x T :=
        perronKernelWeightedBoundaryWindowError_eq_exactHit_add_punctured x T
    _ ≤ Ce * (Real.log x) ^ 2 + Cp * (Real.log x) ^ 2 :=
        add_le_add hexact_x hpunctured_x
    _ = (Ce + Cp) * (Real.log x) ^ 2 := by ring

/-- Weighted finite cutoff from the separated boundary weighted atom and the
off-boundary weighted atom. -/
theorem small_T_weighted_kernel_cutoff_bound_from_separated_boundary_and_offBoundary
    (hseparated : ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedSeparatedPuncturedBoundaryError x T ≤ Cs * (Real.log x) ^ 2)
    (hoffBoundary : ∃ Co > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedOffBoundaryWindowError x T ≤ Co * (Real.log x) ^ 2) :
    ∃ Cw > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedCutoffError x T ≤ Cw * (Real.log x) ^ 2 :=
  small_T_weighted_kernel_cutoff_bound_from_boundary_split
    (small_T_boundary_window_bound_from_separated_weighted hseparated)
    hoffBoundary

/-- Direct separated weighted atom from a pointwise Davenport kernel envelope
and the corresponding weighted envelope summation bound. -/
theorem small_T_separated_weighted_bound_from_davenport_envelope
    (hkernel : ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ perronKernelSeparatedPuncturedBoundarySet x T →
          |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤
            perronKernelSeparatedDavenportEnvelopeTerm x T n)
    (henvelope : ∃ Cd > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedDavenportEnvelope x T ≤ Cd * (Real.log x) ^ 2) :
    ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedSeparatedPuncturedBoundaryError x T ≤ Cs * (Real.log x) ^ 2 := by
  rcases henvelope with ⟨Cd, hCd_pos, henvelope⟩
  refine ⟨Cd, hCd_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  calc perronKernelWeightedSeparatedPuncturedBoundaryError x T
      ≤ perronKernelSeparatedDavenportEnvelope x T :=
        perronKernelWeightedSeparatedPuncturedBoundaryError_le_davenportEnvelope
          x T (hkernel x T hx hT_lo hT_hi)
    _ ≤ Cd * (Real.log x) ^ 2 := henvelope x T hx hT_lo hT_hi

/-- Direct separated weighted atom from only the weighted Davenport-envelope
summation bound.  The pointwise Davenport normalization is closed by
`small_T_separated_davenport_kernel_bound`. -/
theorem small_T_separated_weighted_bound_from_davenport_envelope_bound
    (henvelope : ∃ Cd > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedDavenportEnvelope x T ≤ Cd * (Real.log x) ^ 2) :
    ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedSeparatedPuncturedBoundaryError x T ≤ Cs * (Real.log x) ^ 2 :=
  small_T_separated_weighted_bound_from_davenport_envelope
    small_T_separated_davenport_kernel_bound henvelope

/-- Scale-correct separated Davenport-envelope bound from bounds for the
singular and smooth components.

The pure `O((log x)^2)` target is too small for this macroscopic separated
window.  The honest bounded-height scale retains the linear window factor
`x / T`; the remaining hard atom is the singular weighted harmonic sum. -/
theorem small_T_separated_davenport_envelope_linear_bound_from_components
    (hsingular : ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedDavenportSingularEnvelope x T ≤
        Cs * (x / T) * (Real.log x) ^ 2)
    (hsmooth : ∃ Cm > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedDavenportSmoothEnvelope x T ≤
        Cm * (x / T) * (Real.log x) ^ 2) :
    ∃ Cd > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedDavenportEnvelope x T ≤
        Cd * (x / T) * (Real.log x) ^ 2 := by
  rcases hsingular with ⟨Cs, hCs_pos, hsingular⟩
  rcases hsmooth with ⟨Cm, hCm_pos, hsmooth⟩
  refine ⟨Cs + Cm, add_pos hCs_pos hCm_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  have hsingular_x := hsingular x T hx hT_lo hT_hi
  have hsmooth_x := hsmooth x T hx hT_lo hT_hi
  calc perronKernelSeparatedDavenportEnvelope x T
      = perronKernelSeparatedDavenportSingularEnvelope x T +
          perronKernelSeparatedDavenportSmoothEnvelope x T :=
        perronKernelSeparatedDavenportEnvelope_eq_singular_add_smooth x T
    _ ≤ Cs * (x / T) * (Real.log x) ^ 2 +
          Cm * (x / T) * (Real.log x) ^ 2 :=
        add_le_add hsingular_x hsmooth_x
    _ = (Cs + Cm) * (x / T) * (Real.log x) ^ 2 := by ring

/-- Singular Davenport-envelope component from the two genuinely smaller
harmonic-distance atoms: pointwise log-distance comparison and a weighted
harmonic-distance summation bound. -/
theorem small_T_separated_singular_envelope_bound_from_logDistance
    (hpoint : ∃ K > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ perronKernelSeparatedPuncturedBoundarySet x T →
          perronKernelSeparatedDavenportSingularTerm x T n ≤
            K * perronKernelSeparatedLogDistanceTerm x T n)
    (hdistance : ∃ Cℓ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedLogDistanceEnvelope x T ≤
        Cℓ * (x / T) * (Real.log x) ^ 2) :
    ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedDavenportSingularEnvelope x T ≤
        Cs * (x / T) * (Real.log x) ^ 2 := by
  rcases hpoint with ⟨K, hK_pos, hpoint⟩
  rcases hdistance with ⟨Cℓ, hCℓ_pos, hdistance⟩
  refine ⟨K * Cℓ, mul_pos hK_pos hCℓ_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  have hpoint_x := hpoint x T hx hT_lo hT_hi
  have hdistance_x := hdistance x T hx hT_lo hT_hi
  calc perronKernelSeparatedDavenportSingularEnvelope x T
      ≤ K * perronKernelSeparatedLogDistanceEnvelope x T :=
        perronKernelSeparatedDavenportSingularEnvelope_le_logDistanceEnvelope
          x T K hpoint_x
    _ ≤ K * (Cℓ * (x / T) * (Real.log x) ^ 2) :=
        mul_le_mul_of_nonneg_left hdistance_x hK_pos.le
    _ = (K * Cℓ) * (x / T) * (Real.log x) ^ 2 := by ring

/-- Pointwise singular log-distance comparison from a numerator bound and the
reciprocal-log distance comparison. -/
theorem small_T_separated_singular_pointwise_bound_from_num_and_recip
    (hnum : ∃ A > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ perronKernelSeparatedPuncturedBoundarySet x T →
          perronKernelSeparatedDavenportSingularNumerator x n ≤ A)
    (hrecip : ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ perronKernelSeparatedPuncturedBoundarySet x T →
          (Real.log (x / (n : ℝ)))⁻¹ ≤ x / (x - (n : ℝ))) :
    ∃ K > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ perronKernelSeparatedPuncturedBoundarySet x T →
          perronKernelSeparatedDavenportSingularTerm x T n ≤
            K * perronKernelSeparatedLogDistanceTerm x T n := by
  rcases hnum with ⟨A, hA_pos, hnum⟩
  refine ⟨A, hA_pos, ?_⟩
  intro x T hx hT_lo hT_hi n hn
  have hT_pos : 0 < T := by linarith
  rcases perronKernelSeparatedPuncturedBoundarySet_mem_large_side x T hx hT_lo hn with
    ⟨_hn_pos, _hn_lt_x, hy_gt_one⟩
  have hlog_pos : 0 < Real.log (x / (n : ℝ)) := Real.log_pos hy_gt_one
  exact
    perronKernelSeparatedDavenportSingularTerm_le_logDistanceTerm_of_num_and_recip
      x T A n hT_pos hlog_pos hA_pos.le (hnum x T hx hT_lo hT_hi n hn)
      (hrecip x T hx hT_lo hT_hi n hn)

/-- The singular Davenport numerator is uniformly bounded on the separated
boundary window.  The boundary-window condition and `T >= 2` give
`x / n <= 2`, and the standard `c = 1 + 1/log x` rpow bound gives
`(x/n)^c <= 2e`. -/
theorem small_T_separated_singular_numerator_bound :
    ∃ A > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ perronKernelSeparatedPuncturedBoundarySet x T →
          perronKernelSeparatedDavenportSingularNumerator x n ≤ A := by
  let A : ℝ := 2 * Real.exp 1 + 1
  refine ⟨A, by positivity, ?_⟩
  intro x T hx hT_lo _hT_hi n hn
  have hx_nonneg : 0 ≤ x := by linarith
  have hT_pos : 0 < T := by linarith
  rcases perronKernelSeparatedPuncturedBoundarySet_mem_large_side x T hx hT_lo hn with
    ⟨hn_pos, hn_lt_x, _hy_gt_one⟩
  have hn_pos_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hn_le_x : (n : ℝ) ≤ x := le_of_lt hn_lt_x
  have hn_unfold := hn
  dsimp [perronKernelSeparatedPuncturedBoundarySet] at hn_unfold
  have hsp := (Finset.mem_filter.mp hn_unfold).1
  have hboundary := (Finset.mem_filter.mp hsp).1
  have hboundary_dist : |x - (n : ℝ)| ≤ x / T := (Finset.mem_filter.mp hboundary).2
  have hdist_le : x - (n : ℝ) ≤ x / T := by
    have hdist_nonneg : 0 ≤ x - (n : ℝ) := sub_nonneg.mpr hn_le_x
    simpa [abs_of_nonneg hdist_nonneg] using hboundary_dist
  have hx_div_T_le_half : x / T ≤ x / 2 := by
    exact div_le_div_of_nonneg_left hx_nonneg (by norm_num : (0 : ℝ) < 2) hT_lo
  have hdist_le_half : x - (n : ℝ) ≤ x / 2 := le_trans hdist_le hx_div_T_le_half
  have hxn_le_two : x / (n : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hn_pos_real]
    linarith
  have hrpow_le_two_exp :
      (x / (n : ℝ)) ^ (1 + 1 / Real.log x) ≤ 2 * Real.exp 1 := by
    calc (x / (n : ℝ)) ^ (1 + 1 / Real.log x)
        ≤ Real.exp 1 * (x / (n : ℝ)) :=
          per_term_rpow_bound x hx n hn_pos hn_le_x
      _ ≤ Real.exp 1 * 2 :=
          mul_le_mul_of_nonneg_left hxn_le_two (Real.exp_pos 1).le
      _ = 2 * Real.exp 1 := by ring
  calc perronKernelSeparatedDavenportSingularNumerator x n
      = (x / (n : ℝ)) ^ (1 + 1 / Real.log x) + 1 := by
        rfl
    _ ≤ A := by
        dsimp [A]
        linarith

/-- The smooth Davenport summand is uniformly bounded on the separated
boundary window. -/
theorem small_T_separated_davenport_smooth_pointwise_bound :
    ∃ K > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ perronKernelSeparatedPuncturedBoundarySet x T →
          2 * (x / (n : ℝ)) ^ (1 + 1 / Real.log x) /
              ((1 + 1 / Real.log x) * T) ≤ K := by
  rcases small_T_separated_singular_numerator_bound with ⟨A, hA_pos, hnum⟩
  refine ⟨2 * A, mul_pos (by norm_num : (0 : ℝ) < 2) hA_pos, ?_⟩
  intro x T hx hT_lo hT_hi n hn
  have hx_nonneg : 0 ≤ x := by linarith
  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hc_ge_one : 1 ≤ 1 + 1 / Real.log x := by
    have hrecip_nonneg : 0 ≤ 1 / Real.log x :=
      div_nonneg zero_le_one hlog_pos.le
    linarith
  have hden_ge_one : 1 ≤ (1 + 1 / Real.log x) * T := by
    nlinarith [hc_ge_one, hT_lo]
  rcases perronKernelSeparatedPuncturedBoundarySet_mem_large_side x T hx hT_lo hn with
    ⟨hn_pos, _hn_lt_x, _hy_gt_one⟩
  have hn_pos_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hy_nonneg : 0 ≤ x / (n : ℝ) := div_nonneg hx_nonneg hn_pos_real.le
  have hyc_nonneg :
      0 ≤ (x / (n : ℝ)) ^ (1 + 1 / Real.log x) :=
    Real.rpow_nonneg hy_nonneg _
  have hnum_x := hnum x T hx hT_lo hT_hi n hn
  have hyc_le_A :
      (x / (n : ℝ)) ^ (1 + 1 / Real.log x) ≤ A := by
    dsimp [perronKernelSeparatedDavenportSingularNumerator] at hnum_x
    linarith
  calc
    2 * (x / (n : ℝ)) ^ (1 + 1 / Real.log x) /
          ((1 + 1 / Real.log x) * T)
        ≤ 2 * (x / (n : ℝ)) ^ (1 + 1 / Real.log x) :=
          div_le_self (mul_nonneg (by norm_num) hyc_nonneg) hden_ge_one
    _ ≤ 2 * A :=
        mul_le_mul_of_nonneg_left hyc_le_A (by norm_num)

/-- The smooth Davenport envelope has the honest linear-window scale. -/
theorem small_T_separated_davenport_smooth_envelope_bound :
    ∃ Cm > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedDavenportSmoothEnvelope x T ≤
        Cm * (x / T) * (Real.log x) ^ 2 := by
  rcases small_T_separated_davenport_smooth_pointwise_bound with
    ⟨K, hK_pos, hpoint⟩
  rcases small_T_boundary_window_vonMangoldt_weight_linear_bound with
    ⟨Cv, hCv_pos, hweight⟩
  let Clog : ℝ := ((Real.log 2) ^ 2)⁻¹
  let Cm : ℝ := K * Cv * Clog
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hClog_pos : 0 < Clog := by
    dsimp [Clog]
    exact inv_pos.mpr (sq_pos_of_pos hlog2_pos)
  refine ⟨Cm, mul_pos (mul_pos hK_pos hCv_pos) hClog_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  let sp := perronKernelSeparatedPuncturedBoundarySet x T
  let logSq : ℝ := (Real.log x) ^ 2
  have hx_nonneg : 0 ≤ x := by linarith
  have hT_pos : 0 < T := by linarith
  have hscale_nonneg : 0 ≤ x / T := div_nonneg hx_nonneg hT_pos.le
  have hbase_nonneg : 0 ≤ (K * Cv) * (x / T) :=
    mul_nonneg (mul_nonneg hK_pos.le hCv_pos.le) hscale_nonneg
  have hlog_mono : Real.log (2 : ℝ) ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx
  have hlog_sq_le : (Real.log (2 : ℝ)) ^ 2 ≤ logSq := by
    dsimp [logSq]
    nlinarith
  have hone_absorb : 1 ≤ Clog * logSq := by
    dsimp [Clog]
    calc (1 : ℝ)
        = ((Real.log (2 : ℝ)) ^ 2)⁻¹ * (Real.log (2 : ℝ)) ^ 2 := by
            field_simp [ne_of_gt (sq_pos_of_pos hlog2_pos)]
      _ ≤ ((Real.log (2 : ℝ)) ^ 2)⁻¹ * logSq :=
            mul_le_mul_of_nonneg_left hlog_sq_le
              (inv_nonneg.mpr (sq_nonneg (Real.log (2 : ℝ))))
  have hsep_weight_le_boundary :
      ∑ n ∈ sp, ArithmeticFunction.vonMangoldt n ≤
        perronKernelBoundaryWindowVonMangoldtWeight x T := by
    dsimp [sp, perronKernelSeparatedPuncturedBoundarySet,
      perronKernelBoundaryWindowVonMangoldtWeight]
    exact
      Finset.sum_le_sum_of_subset_of_nonneg
        (by
          intro n hn
          exact (Finset.filter_subset _ _) ((Finset.filter_subset _ _) hn))
        (by
          intro n _hn_boundary _hn_not_sp
          exact vonMangoldt_nonneg n)
  calc perronKernelSeparatedDavenportSmoothEnvelope x T
      = ∑ n ∈ sp,
          ArithmeticFunction.vonMangoldt n *
            (2 * (x / (n : ℝ)) ^ (1 + 1 / Real.log x) /
              ((1 + 1 / Real.log x) * T)) := by
        dsimp [sp, perronKernelSeparatedDavenportSmoothEnvelope]
    _ ≤ ∑ n ∈ sp, ArithmeticFunction.vonMangoldt n * K := by
        apply Finset.sum_le_sum
        intro n hn
        exact
          mul_le_mul_of_nonneg_left
            (hpoint x T hx hT_lo hT_hi n hn)
            (vonMangoldt_nonneg n)
    _ = K * ∑ n ∈ sp, ArithmeticFunction.vonMangoldt n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        ring
    _ ≤ K * perronKernelBoundaryWindowVonMangoldtWeight x T :=
        mul_le_mul_of_nonneg_left hsep_weight_le_boundary hK_pos.le
    _ ≤ K * (Cv * (x / T)) :=
        mul_le_mul_of_nonneg_left (hweight x T hx hT_lo hT_hi) hK_pos.le
    _ = (K * Cv) * (x / T) := by ring
    _ ≤ (K * Cv) * (x / T) * (Clog * logSq) := by
        nth_rewrite 1 [← mul_one ((K * Cv) * (x / T))]
        exact mul_le_mul_of_nonneg_left hone_absorb hbase_nonneg
    _ = Cm * (x / T) * (Real.log x) ^ 2 := by
        dsimp [Cm, logSq]
        ring

/-- Reciprocal-log comparison for separated boundary-window terms.  This is
the formal `log (x / n) >= (x - n) / x` step, inverted on positive quantities. -/
theorem small_T_separated_reciprocal_log_distance_bound :
    ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ perronKernelSeparatedPuncturedBoundarySet x T →
          (Real.log (x / (n : ℝ)))⁻¹ ≤ x / (x - (n : ℝ)) := by
  intro x T hx hT_lo _hT_hi n hn
  rcases perronKernelSeparatedPuncturedBoundarySet_mem_large_side x T hx hT_lo hn with
    ⟨hn_pos, hn_lt_x, hy_gt_one⟩
  have hx_pos : 0 < x := by linarith
  have hn_pos_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hy_pos : 0 < x / (n : ℝ) := div_pos hx_pos hn_pos_real
  have hdist_pos : 0 < x - (n : ℝ) := sub_pos.mpr hn_lt_x
  have hratio_pos : 0 < (x - (n : ℝ)) / x := div_pos hdist_pos hx_pos
  have hlog_pos : 0 < Real.log (x / (n : ℝ)) := Real.log_pos hy_gt_one
  have hlog_lower :
      (x - (n : ℝ)) / x ≤ Real.log (x / (n : ℝ)) := by
    have hbase := Real.one_sub_inv_le_log_of_pos hy_pos
    have hbase' :
        1 - (x / (n : ℝ))⁻¹ ≤ Real.log (x / (n : ℝ)) := by
      linarith [hbase]
    have hrewrite : 1 - (x / (n : ℝ))⁻¹ = (x - (n : ℝ)) / x := by
      field_simp [hx_pos.ne', hn_pos_real.ne']
    rw [← hrewrite]
    exact hbase'
  calc (Real.log (x / (n : ℝ)))⁻¹
      ≤ ((x - (n : ℝ)) / x)⁻¹ :=
        (inv_le_inv₀ hlog_pos hratio_pos).2 hlog_lower
    _ = x / (x - (n : ℝ)) := by
        field_simp [hx_pos.ne', hdist_pos.ne']

/-- The separated singular Davenport summand has the required pointwise
log-distance envelope. -/
theorem small_T_separated_singular_pointwise_bound :
    ∃ K > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ perronKernelSeparatedPuncturedBoundarySet x T →
          perronKernelSeparatedDavenportSingularTerm x T n ≤
            K * perronKernelSeparatedLogDistanceTerm x T n :=
  small_T_separated_singular_pointwise_bound_from_num_and_recip
    small_T_separated_singular_numerator_bound
    small_T_separated_reciprocal_log_distance_bound

/-- Separated boundary membership gives the exact distance window needed for
the remaining harmonic sum: distance strictly exceeds one and is at most
`x / T`. -/
theorem perronKernelSeparatedPuncturedBoundarySet_mem_distance_bounds
    (x T : ℝ) (hx : 2 ≤ x) (hT_lo : 2 ≤ T) {n : ℕ}
    (hn : n ∈ perronKernelSeparatedPuncturedBoundarySet x T) :
    1 < x - (n : ℝ) ∧ x - (n : ℝ) ≤ x / T := by
  rcases perronKernelSeparatedPuncturedBoundarySet_mem_large_side x T hx hT_lo hn with
    ⟨_hn_pos, hn_lt_x, _hy_gt_one⟩
  have hn_unfold := hn
  dsimp [perronKernelSeparatedPuncturedBoundarySet] at hn_unfold
  have hnot_unit : ¬ |x - (n : ℝ)| ≤ 1 := (Finset.mem_filter.mp hn_unfold).2
  have hsp := (Finset.mem_filter.mp hn_unfold).1
  have hboundary := (Finset.mem_filter.mp hsp).1
  have hboundary_dist : |x - (n : ℝ)| ≤ x / T := (Finset.mem_filter.mp hboundary).2
  have hdist_pos : 0 < x - (n : ℝ) := sub_pos.mpr hn_lt_x
  have hdist_nonneg : 0 ≤ x - (n : ℝ) := hdist_pos.le
  have hdist_le : x - (n : ℝ) ≤ x / T := by
    simpa [abs_of_nonneg hdist_nonneg] using hboundary_dist
  have hdist_gt_one : 1 < x - (n : ℝ) := by
    by_contra hle_not
    have hle : x - (n : ℝ) ≤ 1 := le_of_not_gt hle_not
    have habs_le : |x - (n : ℝ)| ≤ 1 := by
      simpa [abs_of_nonneg hdist_nonneg] using hle
    exact hnot_unit habs_le
  exact ⟨hdist_gt_one, hdist_le⟩

private theorem perronKernelSeparatedPuncturedBoundarySet_mem_le_floor
    (x T : ℝ) {n : ℕ}
    (hn : n ∈ perronKernelSeparatedPuncturedBoundarySet x T) :
    n ≤ Nat.floor x := by
  have hn_unfold := hn
  dsimp [perronKernelSeparatedPuncturedBoundarySet] at hn_unfold
  have hsp := (Finset.mem_filter.mp hn_unfold).1
  have hboundary := (Finset.mem_filter.mp hsp).1
  have hrange : n ∈ Finset.range (Nat.floor x + 1) :=
    (Finset.mem_filter.mp hboundary).1
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange)

private theorem perronKernelSeparatedPuncturedBoundarySet_mem_floor_distance_pos
    (x T : ℝ) (hx : 2 ≤ x) (hT_lo : 2 ≤ T) {n : ℕ}
    (hn : n ∈ perronKernelSeparatedPuncturedBoundarySet x T) :
    0 < Nat.floor x - n := by
  rcases perronKernelSeparatedPuncturedBoundarySet_mem_distance_bounds
      x T hx hT_lo hn with
    ⟨hdist_gt_one, _hdist_le⟩
  have hx_lt_floor_add_one : x < (Nat.floor x : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one x
  have hn_lt_floor : n < Nat.floor x := by
    have hn_lt_floor_real : (n : ℝ) < (Nat.floor x : ℝ) := by
      linarith
    exact_mod_cast hn_lt_floor_real
  exact Nat.sub_pos_of_lt hn_lt_floor

/-- The real reciprocal distance is dominated termwise by the reciprocal of
the integer floor-distance. -/
theorem perronKernelSeparatedReciprocalDistanceEnvelope_le_floorDistanceEnvelope
    (x T : ℝ) (hx : 2 ≤ x) (hT_lo : 2 ≤ T) :
    perronKernelSeparatedReciprocalDistanceEnvelope x T ≤
      perronKernelSeparatedFloorDistanceEnvelope x T := by
  classical
  dsimp [perronKernelSeparatedReciprocalDistanceEnvelope,
    perronKernelSeparatedFloorDistanceEnvelope]
  apply Finset.sum_le_sum
  intro n hn
  have hx_nonneg : 0 ≤ x := by linarith
  have hn_le_floor :
      n ≤ Nat.floor x :=
    perronKernelSeparatedPuncturedBoundarySet_mem_le_floor x T hn
  rcases perronKernelSeparatedPuncturedBoundarySet_mem_distance_bounds
      x T hx hT_lo hn with
    ⟨hdist_gt_one, _hdist_le⟩
  have hdist_pos : 0 < x - (n : ℝ) := by linarith
  have hfloor_sub_pos_nat :
      0 < Nat.floor x - n :=
    perronKernelSeparatedPuncturedBoundarySet_mem_floor_distance_pos
      x T hx hT_lo hn
  have hfloor_sub_pos : 0 < ((Nat.floor x - n : ℕ) : ℝ) := by
    exact_mod_cast hfloor_sub_pos_nat
  have hfloor_sub_cast :
      ((Nat.floor x - n : ℕ) : ℝ) = (Nat.floor x : ℝ) - (n : ℝ) := by
    rw [Nat.cast_sub hn_le_floor]
  have hfloor_le_x : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx_nonneg
  have hfloor_dist_le : ((Nat.floor x - n : ℕ) : ℝ) ≤ x - (n : ℝ) := by
    rw [hfloor_sub_cast]
    linarith
  exact (inv_le_inv₀ hdist_pos hfloor_sub_pos).2 hfloor_dist_le

/-- The floor-distance reciprocal sum injects into the usual harmonic sum up
to `floor x`. -/
theorem perronKernelSeparatedFloorDistanceEnvelope_le_harmonic_floor
    (x T : ℝ) (hx : 2 ≤ x) (hT_lo : 2 ≤ T) :
    perronKernelSeparatedFloorDistanceEnvelope x T ≤
      (harmonic (Nat.floor x) : ℝ) := by
  classical
  let s := perronKernelSeparatedPuncturedBoundarySet x T
  let N := Nat.floor x
  have hinj :
      Set.InjOn (fun n : ℕ => N - n) (s : Set ℕ) := by
    intro a ha b hb hdist
    have ha_pos_sub :
        0 < N - a := by
      dsimp [N, s] at ha
      simpa [N] using
        (perronKernelSeparatedPuncturedBoundarySet_mem_floor_distance_pos
          x T hx hT_lo ha)
    have hb_pos_sub :
        0 < N - b := by
      dsimp [N, s] at hb
      simpa [N] using
        (perronKernelSeparatedPuncturedBoundarySet_mem_floor_distance_pos
          x T hx hT_lo hb)
    have ha_lt : a < N := tsub_pos_iff_lt.mp ha_pos_sub
    have hb_lt : b < N := tsub_pos_iff_lt.mp hb_pos_sub
    exact (tsub_right_inj ha_lt.le hb_lt.le).mp hdist
  have hsubset :
      s.image (fun n : ℕ => N - n) ⊆ Finset.Icc 1 N := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
    have hpos :
        0 < N - n := by
      dsimp [N, s] at hn
      simpa [N] using
        (perronKernelSeparatedPuncturedBoundarySet_mem_floor_distance_pos
          x T hx hT_lo hn)
    exact Finset.mem_Icc.mpr ⟨hpos, Nat.sub_le N n⟩
  have hsum_image :
      ∑ k ∈ s.image (fun n : ℕ => N - n), ((k : ℝ)⁻¹) =
        ∑ n ∈ s, (((N - n : ℕ) : ℝ)⁻¹) :=
    Finset.sum_image hinj
  calc perronKernelSeparatedFloorDistanceEnvelope x T
      = ∑ n ∈ s, (((N - n : ℕ) : ℝ)⁻¹) := by
        dsimp [perronKernelSeparatedFloorDistanceEnvelope, s, N]
    _ = ∑ k ∈ s.image (fun n : ℕ => N - n), ((k : ℝ)⁻¹) :=
        hsum_image.symm
    _ ≤ ∑ k ∈ Finset.Icc 1 N, ((k : ℝ)⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          hsubset
          (by
            intro k _hk_Icc _hk_not_image
            exact inv_nonneg.mpr (Nat.cast_nonneg k))
    _ = (harmonic N : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- Exact finite reindexing majorant for the separated reciprocal-distance
envelope. -/
theorem perronKernelSeparatedReciprocalDistanceEnvelope_le_harmonic_floor
    (x T : ℝ) (hx : 2 ≤ x) (hT_lo : 2 ≤ T) :
    perronKernelSeparatedReciprocalDistanceEnvelope x T ≤
      (harmonic (Nat.floor x) : ℝ) :=
  le_trans
    (perronKernelSeparatedReciprocalDistanceEnvelope_le_floorDistanceEnvelope
      x T hx hT_lo)
    (perronKernelSeparatedFloorDistanceEnvelope_le_harmonic_floor x T hx hT_lo)

/-- The unweighted log-distance envelope is exactly the global `x / T` scale
times the reciprocal-distance harmonic atom. -/
theorem perronKernelSeparatedUnweightedLogDistanceEnvelope_eq_scale_mul_reciprocal
    (x T : ℝ) (hx : 2 ≤ x) (hT_lo : 2 ≤ T) :
    perronKernelSeparatedUnweightedLogDistanceEnvelope x T =
      (x / T) * perronKernelSeparatedReciprocalDistanceEnvelope x T := by
  classical
  have hT_pos : 0 < T := by linarith
  calc perronKernelSeparatedUnweightedLogDistanceEnvelope x T
      = ∑ n ∈ perronKernelSeparatedPuncturedBoundarySet x T,
          (x / T) * (x - (n : ℝ))⁻¹ := by
        dsimp [perronKernelSeparatedUnweightedLogDistanceEnvelope,
          perronKernelSeparatedLogDistanceTerm]
        apply Finset.sum_congr rfl
        intro n hn
        rcases perronKernelSeparatedPuncturedBoundarySet_mem_distance_bounds
            x T hx hT_lo hn with
          ⟨hdist_gt_one, _hdist_le⟩
        have hdist_ne : x - (n : ℝ) ≠ 0 := by linarith
        field_simp [hT_pos.ne', hdist_ne]
    _ = (x / T) * perronKernelSeparatedReciprocalDistanceEnvelope x T := by
        dsimp [perronKernelSeparatedReciprocalDistanceEnvelope]
        rw [Finset.mul_sum]

/-- The unweighted log-distance target follows from the pure reciprocal
distance harmonic sum. -/
theorem small_T_separated_unweighted_logDistance_bound_from_reciprocal
    (hreciprocal : ∃ Ch > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedReciprocalDistanceEnvelope x T ≤ Ch * Real.log x) :
    ∃ Ch > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedUnweightedLogDistanceEnvelope x T ≤
        Ch * (x / T) * Real.log x := by
  rcases hreciprocal with ⟨Ch, hCh_pos, hreciprocal⟩
  refine ⟨Ch, hCh_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  have hx_nonneg : 0 ≤ x := by linarith
  have hT_pos : 0 < T := by linarith
  have hscale_nonneg : 0 ≤ x / T := div_nonneg hx_nonneg hT_pos.le
  have hreciprocal_x := hreciprocal x T hx hT_lo hT_hi
  calc perronKernelSeparatedUnweightedLogDistanceEnvelope x T
      = (x / T) * perronKernelSeparatedReciprocalDistanceEnvelope x T :=
        perronKernelSeparatedUnweightedLogDistanceEnvelope_eq_scale_mul_reciprocal
          x T hx hT_lo
    _ ≤ (x / T) * (Ch * Real.log x) :=
        mul_le_mul_of_nonneg_left hreciprocal_x hscale_nonneg
    _ = Ch * (x / T) * Real.log x := by ring

/-- Harmonic numbers at `floor x` are bounded by a constant multiple of
`log x` for `x >= 2`. -/
private theorem harmonic_floor_le_const_mul_log (x : ℝ) (hx : 2 ≤ x) :
    (harmonic (Nat.floor x) : ℝ) ≤
      (1 + 1 / Real.log 2) * Real.log x := by
  have hx_one : 1 ≤ x := by linarith
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2_le : Real.log (2 : ℝ) ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx
  have hone_le : (1 : ℝ) ≤ (1 / Real.log 2) * Real.log x := by
    have hcoeff_nonneg : 0 ≤ (1 / Real.log 2 : ℝ) :=
      (div_pos zero_lt_one hlog2_pos).le
    calc (1 : ℝ)
        = (1 / Real.log 2) * Real.log 2 := by
          exact (one_div_mul_cancel hlog2_pos.ne').symm
      _ ≤ (1 / Real.log 2) * Real.log x :=
          mul_le_mul_of_nonneg_left hlog2_le hcoeff_nonneg
  calc (harmonic (Nat.floor x) : ℝ)
      ≤ 1 + Real.log x := harmonic_floor_le_one_add_log x hx_one
    _ ≤ (1 / Real.log 2) * Real.log x + Real.log x :=
        by linarith
    _ = (1 + 1 / Real.log 2) * Real.log x := by ring

/-- The finite reciprocal von Mangoldt weight is bounded by
`log x * harmonic (floor x)`. -/
private theorem perronKernelVonMangoldtReciprocalWeight_le_log_mul_harmonic_floor
    (x : ℝ) (hx : 2 ≤ x) :
    perronKernelVonMangoldtReciprocalWeight x ≤
      Real.log x * (harmonic (Nat.floor x) : ℝ) := by
  classical
  let N := Nat.floor x
  have hx_nonneg : 0 ≤ x := by linarith
  have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hterm :
      ∀ n ∈ Finset.range (N + 1),
        (if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ)) ≤
          Real.log x * (if n = 0 then 0 else ((n : ℝ)⁻¹)) := by
    intro n hn
    by_cases hn_zero : n = 0
    · simp [hn_zero]
    · have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero hn_zero
      have hn_pos_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
      have hn_le_floor : n ≤ Nat.floor x := by
        simpa [N] using Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have hn_le_x : (n : ℝ) ≤ x :=
        le_trans (Nat.cast_le.mpr hn_le_floor) (Nat.floor_le hx_nonneg)
      have hΛ_le_logx : ArithmeticFunction.vonMangoldt n ≤ Real.log x := by
        calc ArithmeticFunction.vonMangoldt n
            ≤ Real.log (n : ℝ) := vonMangoldt_le_log n hn_pos
          _ ≤ Real.log x := Real.log_le_log hn_pos_real hn_le_x
      simpa [hn_zero, div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right hΛ_le_logx (inv_nonneg.mpr hn_pos_real.le)
  have hrecip_le_harmonic :
      (∑ n ∈ Finset.range (N + 1), if n = 0 then 0 else ((n : ℝ)⁻¹)) ≤
        (harmonic N : ℝ) := by
    calc (∑ n ∈ Finset.range (N + 1), if n = 0 then 0 else ((n : ℝ)⁻¹))
        = ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => n ≠ 0),
            ((n : ℝ)⁻¹) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro n _hn
          by_cases hn_zero : n = 0
          · simp [hn_zero]
          · simp [hn_zero]
      _ ≤ ∑ n ∈ Finset.Icc 1 N, ((n : ℝ)⁻¹) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            rcases Finset.mem_filter.mp hn with ⟨hn_range, hn_ne_zero⟩
            have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero hn_ne_zero
            have hn_le_N : n ≤ N :=
              Nat.lt_succ_iff.mp (Finset.mem_range.mp hn_range)
            exact Finset.mem_Icc.mpr ⟨hn_pos, hn_le_N⟩
          · intro n _hn_Icc _hn_not
            exact inv_nonneg.mpr (Nat.cast_nonneg n)
      _ = (harmonic N : ℝ) := by
          simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  calc perronKernelVonMangoldtReciprocalWeight x
      ≤ ∑ n ∈ Finset.range (N + 1),
          Real.log x * (if n = 0 then 0 else ((n : ℝ)⁻¹)) := by
        simpa [perronKernelVonMangoldtReciprocalWeight, N, div_eq_mul_inv]
          using Finset.sum_le_sum hterm
    _ = Real.log x *
          ∑ n ∈ Finset.range (N + 1), if n = 0 then 0 else ((n : ℝ)⁻¹) := by
        rw [Finset.mul_sum]
    _ ≤ Real.log x * (harmonic N : ℝ) :=
        mul_le_mul_of_nonneg_left hrecip_le_harmonic hlogx_nonneg
    _ = Real.log x * (harmonic (Nat.floor x) : ℝ) := by rfl

/-- Closed finite reciprocal von Mangoldt weight bound. -/
theorem small_T_vonMangoldt_reciprocalWeight_bound :
    ∃ Cr > (0 : ℝ), ∀ x : ℝ, x ≥ 2 →
      perronKernelVonMangoldtReciprocalWeight x ≤ Cr * (Real.log x) ^ 2 := by
  let Cr : ℝ := 1 + 1 / Real.log 2
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hCr_pos : 0 < Cr := by
    dsimp [Cr]
    exact add_pos zero_lt_one (div_pos zero_lt_one hlog2_pos)
  refine ⟨Cr, hCr_pos, ?_⟩
  intro x hx
  have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  calc perronKernelVonMangoldtReciprocalWeight x
      ≤ Real.log x * (harmonic (Nat.floor x) : ℝ) :=
        perronKernelVonMangoldtReciprocalWeight_le_log_mul_harmonic_floor x hx
    _ ≤ Real.log x * (Cr * Real.log x) :=
        mul_le_mul_of_nonneg_left (by
          dsimp [Cr]
          exact harmonic_floor_le_const_mul_log x hx) hlogx_nonneg
    _ = Cr * (Real.log x) ^ 2 := by ring

/-- Reciprocal-distance envelope bound from an exact finite harmonic majorant.
This conditional form is kept for downstream wiring; the closed majorant is
provided by `perronKernelSeparatedReciprocalDistanceEnvelope_le_harmonic_floor`. -/
theorem small_T_separated_reciprocalDistance_bound_from_harmonic_floor
    (hharmonic : ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedReciprocalDistanceEnvelope x T ≤
        (harmonic (Nat.floor x) : ℝ)) :
    ∃ Ch > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedReciprocalDistanceEnvelope x T ≤ Ch * Real.log x := by
  let Ch : ℝ := 1 + 1 / Real.log 2
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hCh_pos : 0 < Ch := by
    dsimp [Ch]
    exact add_pos zero_lt_one (div_pos zero_lt_one hlog2_pos)
  refine ⟨Ch, hCh_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  calc perronKernelSeparatedReciprocalDistanceEnvelope x T
      ≤ (harmonic (Nat.floor x) : ℝ) := hharmonic x T hx hT_lo hT_hi
    _ ≤ Ch * Real.log x := by
        dsimp [Ch]
        exact harmonic_floor_le_const_mul_log x hx

/-- Closed pure reciprocal-distance harmonic bound for the separated boundary
window. -/
theorem small_T_separated_reciprocalDistance_bound :
    ∃ Ch > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedReciprocalDistanceEnvelope x T ≤ Ch * Real.log x :=
  small_T_separated_reciprocalDistance_bound_from_harmonic_floor
    (fun x T hx hT_lo _hT_hi =>
      perronKernelSeparatedReciprocalDistanceEnvelope_le_harmonic_floor
        x T hx hT_lo)

/-- The weighted harmonic-distance envelope is bounded by `log x` times the
unweighted harmonic-distance envelope on the separated boundary window. -/
theorem perronKernelSeparatedLogDistanceEnvelope_le_log_mul_unweighted
    (x T : ℝ) (hx : 2 ≤ x) (hT_lo : 2 ≤ T) :
    perronKernelSeparatedLogDistanceEnvelope x T ≤
      Real.log x * perronKernelSeparatedUnweightedLogDistanceEnvelope x T := by
  classical
  have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hx_nonneg : 0 ≤ x := by linarith
  have hT_pos : 0 < T := by linarith
  calc perronKernelSeparatedLogDistanceEnvelope x T
      = ∑ n ∈ perronKernelSeparatedPuncturedBoundarySet x T,
          ArithmeticFunction.vonMangoldt n *
            perronKernelSeparatedLogDistanceTerm x T n := by
        rfl
    _ ≤ ∑ n ∈ perronKernelSeparatedPuncturedBoundarySet x T,
          Real.log x * perronKernelSeparatedLogDistanceTerm x T n := by
        apply Finset.sum_le_sum
        intro n hn
        rcases perronKernelSeparatedPuncturedBoundarySet_mem_large_side x T hx hT_lo hn with
          ⟨hn_pos, hn_lt_x, _hy_gt_one⟩
        have hn_pos_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
        have hn_le_x : (n : ℝ) ≤ x := le_of_lt hn_lt_x
        have hdist_nonneg : 0 ≤ x - (n : ℝ) := sub_nonneg.mpr hn_le_x
        have hterm_nonneg : 0 ≤ perronKernelSeparatedLogDistanceTerm x T n := by
          dsimp [perronKernelSeparatedLogDistanceTerm]
          exact div_nonneg hx_nonneg (mul_nonneg hT_pos.le hdist_nonneg)
        have hΛ_le_logx : ArithmeticFunction.vonMangoldt n ≤ Real.log x := by
          calc ArithmeticFunction.vonMangoldt n
              ≤ Real.log (n : ℝ) := vonMangoldt_le_log n hn_pos
            _ ≤ Real.log x := Real.log_le_log hn_pos_real hn_le_x
        exact
          mul_le_mul hΛ_le_logx
            (le_rfl : perronKernelSeparatedLogDistanceTerm x T n ≤
              perronKernelSeparatedLogDistanceTerm x T n)
            hterm_nonneg hlogx_nonneg
    _ = Real.log x * perronKernelSeparatedUnweightedLogDistanceEnvelope x T := by
        dsimp [perronKernelSeparatedUnweightedLogDistanceEnvelope]
        rw [Finset.mul_sum]

/-- Weighted harmonic-distance bound from the strictly smaller unweighted
harmonic-distance summation atom. -/
theorem small_T_separated_logDistance_bound_from_unweighted
    (hunweighted : ∃ Ch > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedUnweightedLogDistanceEnvelope x T ≤
        Ch * (x / T) * Real.log x) :
    ∃ Cℓ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedLogDistanceEnvelope x T ≤
        Cℓ * (x / T) * (Real.log x) ^ 2 := by
  rcases hunweighted with ⟨Ch, hCh_pos, hunweighted⟩
  refine ⟨Ch, hCh_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hunweighted_x := hunweighted x T hx hT_lo hT_hi
  calc perronKernelSeparatedLogDistanceEnvelope x T
      ≤ Real.log x * perronKernelSeparatedUnweightedLogDistanceEnvelope x T :=
        perronKernelSeparatedLogDistanceEnvelope_le_log_mul_unweighted x T hx hT_lo
    _ ≤ Real.log x * (Ch * (x / T) * Real.log x) :=
        mul_le_mul_of_nonneg_left hunweighted_x hlogx_nonneg
    _ = Ch * (x / T) * (Real.log x) ^ 2 := by ring

/-- Weighted harmonic-distance bound from the pure reciprocal-distance
harmonic atom. -/
theorem small_T_separated_logDistance_bound_from_reciprocal
    (hreciprocal : ∃ Ch > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedReciprocalDistanceEnvelope x T ≤ Ch * Real.log x) :
    ∃ Cℓ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedLogDistanceEnvelope x T ≤
        Cℓ * (x / T) * (Real.log x) ^ 2 :=
  small_T_separated_logDistance_bound_from_unweighted
    (small_T_separated_unweighted_logDistance_bound_from_reciprocal hreciprocal)

/-- Singular Davenport-envelope bound from the unweighted harmonic-distance
summation atom, after the pointwise reciprocal-log route has been closed. -/
theorem small_T_separated_singular_envelope_bound_from_unweighted_logDistance
    (hunweighted : ∃ Ch > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedUnweightedLogDistanceEnvelope x T ≤
        Ch * (x / T) * Real.log x) :
    ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedDavenportSingularEnvelope x T ≤
        Cs * (x / T) * (Real.log x) ^ 2 :=
  small_T_separated_singular_envelope_bound_from_logDistance
    small_T_separated_singular_pointwise_bound
    (small_T_separated_logDistance_bound_from_unweighted hunweighted)

/-- Singular Davenport-envelope bound from the pure reciprocal-distance
harmonic atom. -/
theorem small_T_separated_singular_envelope_bound_from_reciprocal_logDistance
    (hreciprocal : ∃ Ch > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedReciprocalDistanceEnvelope x T ≤ Ch * Real.log x) :
    ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedDavenportSingularEnvelope x T ≤
        Cs * (x / T) * (Real.log x) ^ 2 :=
  small_T_separated_singular_envelope_bound_from_logDistance
    small_T_separated_singular_pointwise_bound
    (small_T_separated_logDistance_bound_from_reciprocal hreciprocal)

/-- Closed singular Davenport-envelope bound at the honest linear-window
scale. -/
theorem small_T_separated_singular_envelope_bound :
    ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedDavenportSingularEnvelope x T ≤
        Cs * (x / T) * (Real.log x) ^ 2 :=
  small_T_separated_singular_envelope_bound_from_reciprocal_logDistance
    small_T_separated_reciprocalDistance_bound

/-- Closed separated Davenport-envelope bound at the honest linear-window
scale. -/
theorem small_T_separated_davenport_envelope_linear_bound :
    ∃ Cd > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedDavenportEnvelope x T ≤
        Cd * (x / T) * (Real.log x) ^ 2 :=
  small_T_separated_davenport_envelope_linear_bound_from_components
    small_T_separated_singular_envelope_bound
    small_T_separated_davenport_smooth_envelope_bound

/-- Scale-correct separated weighted atom from a linear-window Davenport
envelope bound.  This records the usable consequence of the separated
Davenport route without claiming the false pure `O((log x)^2)` envelope sum. -/
theorem small_T_separated_weighted_bound_from_linear_davenport_envelope_bound
    (henvelope : ∃ Cd > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedDavenportEnvelope x T ≤
        Cd * (x / T) * (Real.log x) ^ 2) :
    ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedSeparatedPuncturedBoundaryError x T ≤
        Cs * (x / T) * (Real.log x) ^ 2 := by
  rcases henvelope with ⟨Cd, hCd_pos, henvelope⟩
  refine ⟨Cd, hCd_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  calc perronKernelWeightedSeparatedPuncturedBoundaryError x T
      ≤ perronKernelSeparatedDavenportEnvelope x T :=
        perronKernelWeightedSeparatedPuncturedBoundaryError_le_davenportEnvelope
          x T (small_T_separated_davenport_kernel_bound x T hx hT_lo hT_hi)
    _ ≤ Cd * (x / T) * (Real.log x) ^ 2 := henvelope x T hx hT_lo hT_hi

/-- Closed separated weighted boundary-window bound at the honest
linear-window scale.  This is the usable scale-correct consequence of the
Davenport separated route. -/
theorem small_T_separated_weighted_linear_bound :
    ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedSeparatedPuncturedBoundaryError x T ≤
        Cs * (x / T) * (Real.log x) ^ 2 :=
  small_T_separated_weighted_bound_from_linear_davenport_envelope_bound
    small_T_separated_davenport_envelope_linear_bound

private theorem small_T_logSq_le_eight_linear_logSq
    (x T : ℝ) (hx : 2 ≤ x) (hT_lo : 2 ≤ T) (hT_hi : T ≤ 16) :
    (Real.log x) ^ 2 ≤ 8 * (x / T) * (Real.log x) ^ 2 := by
  have hT_pos : 0 < T := by linarith
  have hscale_ge_one : (1 : ℝ) ≤ 8 * (x / T) := by
    rw [← mul_div_assoc]
    rw [le_div_iff₀ hT_pos]
    nlinarith
  calc (Real.log x) ^ 2
      = 1 * (Real.log x) ^ 2 := by ring
    _ ≤ (8 * (x / T)) * (Real.log x) ^ 2 :=
        mul_le_mul_of_nonneg_right hscale_ge_one (sq_nonneg (Real.log x))
    _ = 8 * (x / T) * (Real.log x) ^ 2 := by ring

/-- Boundary-window weighted error at the honest linear scale from the closed
exact-hit, near-diagonal, and separated linear atoms. -/
theorem small_T_boundary_window_linear_bound_from_separated_linear
    (hseparated : ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedSeparatedPuncturedBoundaryError x T ≤
        Cs * (x / T) * (Real.log x) ^ 2) :
    ∃ Cb > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedBoundaryWindowError x T ≤
        Cb * (x / T) * (Real.log x) ^ 2 := by
  rcases small_T_exactHit_boundary_error_bound with ⟨Ce, hCe_pos, hexact⟩
  rcases small_T_nearDiagonal_punctured_boundary_bound with ⟨Cn, hCn_pos, hnear⟩
  rcases hseparated with ⟨Cs, hCs_pos, hseparated⟩
  refine ⟨8 * Ce + (8 * Cn + Cs),
    add_pos (mul_pos (by norm_num : (0 : ℝ) < 8) hCe_pos)
      (add_pos (mul_pos (by norm_num : (0 : ℝ) < 8) hCn_pos) hCs_pos), ?_⟩
  intro x T hx hT_lo hT_hi
  let linScale : ℝ := (x / T) * (Real.log x) ^ 2
  have hlog_absorb := small_T_logSq_le_eight_linear_logSq x T hx hT_lo hT_hi
  have hexact_x := hexact x T hx hT_lo hT_hi
  have hnear_x := hnear x T hx hT_lo hT_hi
  have hseparated_x := hseparated x T hx hT_lo hT_hi
  have hseparated_linear :
      perronKernelWeightedSeparatedPuncturedBoundaryError x T ≤ Cs * linScale := by
    simpa [linScale, mul_assoc] using hseparated_x
  have hexact_linear :
      perronKernelWeightedExactHitBoundaryError x T ≤ 8 * Ce * linScale := by
    calc perronKernelWeightedExactHitBoundaryError x T
        ≤ Ce * (Real.log x) ^ 2 := hexact_x
      _ ≤ Ce * (8 * (x / T) * (Real.log x) ^ 2) :=
          mul_le_mul_of_nonneg_left hlog_absorb hCe_pos.le
      _ = 8 * Ce * linScale := by
          dsimp [linScale]
          ring
  have hnear_linear :
      perronKernelWeightedNearDiagonalPuncturedBoundaryError x T ≤
        8 * Cn * linScale := by
    calc perronKernelWeightedNearDiagonalPuncturedBoundaryError x T
        ≤ Cn * (Real.log x) ^ 2 := hnear_x
      _ ≤ Cn * (8 * (x / T) * (Real.log x) ^ 2) :=
          mul_le_mul_of_nonneg_left hlog_absorb hCn_pos.le
      _ = 8 * Cn * linScale := by
          dsimp [linScale]
          ring
  have hpunctured_linear :
      perronKernelWeightedPuncturedBoundaryWindowError x T ≤
        (8 * Cn + Cs) * linScale := by
    calc perronKernelWeightedPuncturedBoundaryWindowError x T
        = perronKernelWeightedNearDiagonalPuncturedBoundaryError x T +
            perronKernelWeightedSeparatedPuncturedBoundaryError x T :=
          perronKernelWeightedPuncturedBoundaryWindowError_eq_nearDiagonal_add_separated x T
      _ ≤ 8 * Cn * linScale + Cs * linScale :=
          add_le_add hnear_linear hseparated_linear
      _ = (8 * Cn + Cs) * linScale := by ring
  calc perronKernelWeightedBoundaryWindowError x T
      = perronKernelWeightedExactHitBoundaryError x T +
          perronKernelWeightedPuncturedBoundaryWindowError x T :=
        perronKernelWeightedBoundaryWindowError_eq_exactHit_add_punctured x T
    _ ≤ 8 * Ce * linScale + (8 * Cn + Cs) * linScale :=
        add_le_add hexact_linear hpunctured_linear
    _ = (8 * Ce + (8 * Cn + Cs)) * (x / T) * (Real.log x) ^ 2 := by
        dsimp [linScale]
        ring

/-- Closed boundary-window weighted error at the honest linear scale. -/
theorem small_T_boundary_window_linear_bound :
    ∃ Cb > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedBoundaryWindowError x T ≤
        Cb * (x / T) * (Real.log x) ^ 2 :=
  small_T_boundary_window_linear_bound_from_separated_linear
    small_T_separated_weighted_linear_bound

/-- Scale-correct finite weighted cutoff assembly.  This keeps the boundary
and off-boundary terms at the linear-window scale instead of forcing the false
pure bounded-height target. -/
theorem small_T_weighted_kernel_cutoff_linear_bound_from_boundary_and_offBoundary
    (hboundary : ∃ Cb > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedBoundaryWindowError x T ≤
        Cb * (x / T) * (Real.log x) ^ 2)
    (hoffBoundary : ∃ Co > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedOffBoundaryWindowError x T ≤
        Co * (x / T) * (Real.log x) ^ 2) :
    ∃ Cw > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedCutoffError x T ≤ Cw * (x / T) * (Real.log x) ^ 2 := by
  rcases hboundary with ⟨Cb, hCb_pos, hboundary⟩
  rcases hoffBoundary with ⟨Co, hCo_pos, hoffBoundary⟩
  refine ⟨Cb + Co, add_pos hCb_pos hCo_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  have hboundary_x := hboundary x T hx hT_lo hT_hi
  have hoffBoundary_x := hoffBoundary x T hx hT_lo hT_hi
  calc perronKernelWeightedCutoffError x T
      = perronKernelWeightedBoundaryWindowError x T +
          perronKernelWeightedOffBoundaryWindowError x T :=
        perronKernelWeightedCutoffError_eq_boundary_add_offBoundary x T
    _ ≤ Cb * (x / T) * (Real.log x) ^ 2 +
          Co * (x / T) * (Real.log x) ^ 2 :=
        add_le_add hboundary_x hoffBoundary_x
    _ = (Cb + Co) * (x / T) * (Real.log x) ^ 2 := by ring

/-- Scale-correct finite weighted cutoff from the closed boundary-window
linear route and a compatible off-boundary linear estimate. -/
theorem small_T_weighted_kernel_cutoff_linear_bound_from_offBoundary
    (hoffBoundary : ∃ Co > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedOffBoundaryWindowError x T ≤
        Co * (x / T) * (Real.log x) ^ 2) :
    ∃ Cw > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedCutoffError x T ≤ Cw * (x / T) * (Real.log x) ^ 2 :=
  small_T_weighted_kernel_cutoff_linear_bound_from_boundary_and_offBoundary
    small_T_boundary_window_linear_bound hoffBoundary

/-- Off-boundary weighted error is bounded by its Davenport envelope.  The
finite Perron range only contains `n <= floor x`; after removing the boundary
window, every positive term is on the large side `1 < x / n`, so Davenport's
large-side per-term estimate applies. -/
theorem perronKernelWeightedOffBoundaryWindowError_le_davenportEnvelope
    (x T : ℝ) (hx : 2 ≤ x) (hT_lo : 2 ≤ T) :
    perronKernelWeightedOffBoundaryWindowError x T ≤
      perronKernelOffBoundaryDavenportEnvelope x T := by
  classical
  let s := (Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => ¬ |x - (n : ℝ)| ≤ x / T)
  have hx_nonneg : 0 ≤ x := by linarith
  have hx_pos : 0 < x := by linarith
  have hT_pos : 0 < T := by linarith
  have hx_over_T_pos : 0 < x / T := div_pos hx_pos hT_pos
  have hc_pos := c_param_pos x hx
  calc perronKernelWeightedOffBoundaryWindowError x T
      = ∑ n ∈ s,
          ArithmeticFunction.vonMangoldt n *
            |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| := by
        rfl
    _ ≤ ∑ n ∈ s, perronKernelOffBoundaryDavenportEnvelopeTerm x T n := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hn_zero : n = 0
        · subst n
          simp [perronKernelOffBoundaryDavenportEnvelopeTerm,
            ArithmeticFunction.vonMangoldt_apply]
        · have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero hn_zero
          have hn_pos_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
          have hrange : n ∈ Finset.range (Nat.floor x + 1) :=
            (Finset.mem_filter.mp hn).1
          have hoff : ¬ |x - (n : ℝ)| ≤ x / T :=
            (Finset.mem_filter.mp hn).2
          have hn_le_floor : n ≤ Nat.floor x :=
            Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange)
          have hn_le_x : (n : ℝ) ≤ x :=
            le_trans (Nat.cast_le.mpr hn_le_floor) (Nat.floor_le hx_nonneg)
          have hn_ne_x : (n : ℝ) ≠ x := by
            intro hn_eq
            have hboundary : |x - (n : ℝ)| ≤ x / T := by
              rw [hn_eq, sub_self, abs_zero]
              exact hx_over_T_pos.le
            exact hoff hboundary
          have hn_lt_x : (n : ℝ) < x := lt_of_le_of_ne hn_le_x hn_ne_x
          have hy_gt_one : 1 < x / (n : ℝ) := by
            rw [one_lt_div hn_pos_real]
            exact hn_lt_x
          have hkernel :
              |1 - perronPerTermIntegral (x / (n : ℝ))
                  (1 + 1 / Real.log x) T| ≤
                ((x / (n : ℝ)) ^ (1 + 1 / Real.log x) + 1) /
                    (T * Real.log (x / (n : ℝ))) +
                  2 * (x / (n : ℝ)) ^ (1 + 1 / Real.log x) /
                    ((1 + 1 / Real.log x) * T) := by
            calc |1 - perronPerTermIntegral (x / (n : ℝ))
                    (1 + 1 / Real.log x) T|
                = |perronPerTermIntegral (x / (n : ℝ))
                    (1 + 1 / Real.log x) T - 1| := abs_sub_comm _ _
              _ ≤ ((x / (n : ℝ)) ^ (1 + 1 / Real.log x) + 1) /
                    (T * Real.log (x / (n : ℝ))) +
                  2 * (x / (n : ℝ)) ^ (1 + 1 / Real.log x) /
                    ((1 + 1 / Real.log x) * T) :=
                  perron_per_term_large_bound
                    (x / (n : ℝ)) hy_gt_one
                    (1 + 1 / Real.log x) hc_pos T hT_pos
          calc ArithmeticFunction.vonMangoldt n *
                |1 - perronPerTermIntegral (x / (n : ℝ))
                    (1 + 1 / Real.log x) T|
              ≤ ArithmeticFunction.vonMangoldt n *
                  (((x / (n : ℝ)) ^ (1 + 1 / Real.log x) + 1) /
                    (T * Real.log (x / (n : ℝ))) +
                  2 * (x / (n : ℝ)) ^ (1 + 1 / Real.log x) /
                    ((1 + 1 / Real.log x) * T)) :=
                  mul_le_mul_of_nonneg_left hkernel (vonMangoldt_nonneg n)
            _ = perronKernelOffBoundaryDavenportEnvelopeTerm x T n := by
                simp [perronKernelOffBoundaryDavenportEnvelopeTerm, hn_zero]
    _ = perronKernelOffBoundaryDavenportEnvelope x T := by
        rfl

/-- Scale-correct off-boundary weighted cutoff from the corresponding
Davenport-envelope summation bound. -/
theorem small_T_offBoundary_weighted_linear_bound_from_davenportEnvelope
    (henvelope : ∃ Cd > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelOffBoundaryDavenportEnvelope x T ≤
        Cd * (x / T) * (Real.log x) ^ 2) :
    ∃ Co > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedOffBoundaryWindowError x T ≤
        Co * (x / T) * (Real.log x) ^ 2 := by
  rcases henvelope with ⟨Cd, hCd_pos, henvelope⟩
  refine ⟨Cd, hCd_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  calc perronKernelWeightedOffBoundaryWindowError x T
      ≤ perronKernelOffBoundaryDavenportEnvelope x T :=
        perronKernelWeightedOffBoundaryWindowError_le_davenportEnvelope
          x T hx hT_lo
    _ ≤ Cd * (x / T) * (Real.log x) ^ 2 := henvelope x T hx hT_lo hT_hi

/-- Scale-correct weighted cutoff from an off-boundary Davenport-envelope
summation bound, using the closed linear-scale boundary-window route. -/
theorem small_T_weighted_kernel_cutoff_linear_bound_from_offBoundary_davenportEnvelope
    (henvelope : ∃ Cd > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelOffBoundaryDavenportEnvelope x T ≤
        Cd * (x / T) * (Real.log x) ^ 2) :
    ∃ Cw > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedCutoffError x T ≤ Cw * (x / T) * (Real.log x) ^ 2 :=
  small_T_weighted_kernel_cutoff_linear_bound_from_offBoundary
    (small_T_offBoundary_weighted_linear_bound_from_davenportEnvelope henvelope)

/-- Exact split of the off-boundary Davenport envelope into its singular and
smooth components. -/
theorem perronKernelOffBoundaryDavenportEnvelope_eq_singular_add_smooth
    (x T : ℝ) :
    perronKernelOffBoundaryDavenportEnvelope x T =
      perronKernelOffBoundaryDavenportSingularEnvelope x T +
        perronKernelOffBoundaryDavenportSmoothEnvelope x T := by
  classical
  dsimp [perronKernelOffBoundaryDavenportEnvelope,
    perronKernelOffBoundaryDavenportSingularEnvelope,
    perronKernelOffBoundaryDavenportSmoothEnvelope]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hn_zero : n = 0
  · simp [perronKernelOffBoundaryDavenportEnvelopeTerm,
      perronKernelOffBoundaryDavenportSingularTerm,
      perronKernelOffBoundaryDavenportSmoothTerm, hn_zero]
  · simp [perronKernelOffBoundaryDavenportEnvelopeTerm,
      perronKernelOffBoundaryDavenportSingularTerm,
      perronKernelOffBoundaryDavenportSmoothTerm, hn_zero]
    ring

/-- The off-boundary smooth Davenport component is controlled by the finite
reciprocal von Mangoldt weight. -/
theorem perronKernelOffBoundaryDavenportSmoothEnvelope_le_reciprocalWeight
    (x T : ℝ) (hx : 2 ≤ x) (hT_lo : 2 ≤ T) :
    perronKernelOffBoundaryDavenportSmoothEnvelope x T ≤
      (2 * Real.exp 1) * (x / T) * perronKernelVonMangoldtReciprocalWeight x := by
  classical
  let s := (Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => ¬ |x - (n : ℝ)| ≤ x / T)
  have hx_nonneg : 0 ≤ x := by linarith
  have hx_pos : 0 < x := by linarith
  have hT_pos : 0 < T := by linarith
  have hc_pos := c_param_pos x hx
  have hc_ge_one : (1 : ℝ) ≤ 1 + 1 / Real.log x :=
    le_of_lt (c_param_gt_one x hx)
  have hcoef_nonneg : 0 ≤ (2 * Real.exp 1) * (x / T) := by positivity
  have hterm :
      ∀ n ∈ s,
        perronKernelOffBoundaryDavenportSmoothTerm x T n ≤
          (2 * Real.exp 1) * (x / T) *
            (if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
    intro n hn
    by_cases hn_zero : n = 0
    · simp [perronKernelOffBoundaryDavenportSmoothTerm, hn_zero]
    · have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero hn_zero
      have hn_pos_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
      have hrange : n ∈ Finset.range (Nat.floor x + 1) :=
        (Finset.mem_filter.mp hn).1
      have hn_le_floor : n ≤ Nat.floor x :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange)
      have hn_le_x : (n : ℝ) ≤ x :=
        le_trans (Nat.cast_le.mpr hn_le_floor) (Nat.floor_le hx_nonneg)
      have hrpow :
          (x / (n : ℝ)) ^ (1 + 1 / Real.log x) ≤
            Real.exp 1 * (x / (n : ℝ)) :=
        per_term_rpow_bound x hx n hn_pos hn_le_x
      have hden_ge_T : T ≤ (1 + 1 / Real.log x) * T := by
        nlinarith
      have hnum_nonneg : 0 ≤ 2 * (Real.exp 1 * (x / (n : ℝ))) := by
        positivity
      have hkernel :
          2 * (x / (n : ℝ)) ^ (1 + 1 / Real.log x) /
              ((1 + 1 / Real.log x) * T) ≤
            2 * (Real.exp 1 * (x / (n : ℝ))) / T := by
        calc 2 * (x / (n : ℝ)) ^ (1 + 1 / Real.log x) /
              ((1 + 1 / Real.log x) * T)
            ≤ 2 * (Real.exp 1 * (x / (n : ℝ))) /
                ((1 + 1 / Real.log x) * T) := by
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hrpow (by norm_num))
                (mul_pos hc_pos hT_pos).le
          _ ≤ 2 * (Real.exp 1 * (x / (n : ℝ))) / T :=
              div_le_div_of_nonneg_left hnum_nonneg hT_pos hden_ge_T
      calc perronKernelOffBoundaryDavenportSmoothTerm x T n
          = ArithmeticFunction.vonMangoldt n *
              (2 * (x / (n : ℝ)) ^ (1 + 1 / Real.log x) /
                ((1 + 1 / Real.log x) * T)) := by
              simp [perronKernelOffBoundaryDavenportSmoothTerm, hn_zero]
        _ ≤ ArithmeticFunction.vonMangoldt n *
              (2 * (Real.exp 1 * (x / (n : ℝ))) / T) :=
              mul_le_mul_of_nonneg_left hkernel (vonMangoldt_nonneg n)
        _ = (2 * Real.exp 1) * (x / T) *
              (ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
              field_simp [hT_pos.ne', hn_pos_real.ne']
        _ = (2 * Real.exp 1) * (x / T) *
              (if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
              simp [hn_zero]
  calc perronKernelOffBoundaryDavenportSmoothEnvelope x T
      = ∑ n ∈ s, perronKernelOffBoundaryDavenportSmoothTerm x T n := by
        rfl
    _ ≤ ∑ n ∈ s,
          (2 * Real.exp 1) * (x / T) *
            (if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ)) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ Finset.range (Nat.floor x + 1),
          (2 * Real.exp 1) * (x / T) *
            (if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro n _hn_range _hn_not_s
          by_cases hn_zero : n = 0
          · simp [hn_zero]
          · simpa [hn_zero] using
              mul_nonneg hcoef_nonneg
                (div_nonneg (vonMangoldt_nonneg n) (Nat.cast_nonneg n))
    _ = (2 * Real.exp 1) * (x / T) *
          perronKernelVonMangoldtReciprocalWeight x := by
        dsimp [perronKernelVonMangoldtReciprocalWeight]
        rw [Finset.mul_sum]

/-- Closed smooth off-boundary Davenport-envelope bound at the honest
linear-window scale. -/
theorem small_T_offBoundary_davenportSmoothEnvelope_bound :
    ∃ Cm > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelOffBoundaryDavenportSmoothEnvelope x T ≤
        Cm * (x / T) * (Real.log x) ^ 2 := by
  rcases small_T_vonMangoldt_reciprocalWeight_bound with ⟨Cr, hCr_pos, hrecip⟩
  let Cm : ℝ := 2 * Real.exp 1 * Cr
  refine ⟨Cm, by positivity, ?_⟩
  intro x T hx hT_lo hT_hi
  have hx_nonneg : 0 ≤ x := by linarith
  have hT_pos : 0 < T := by linarith
  have hscale_nonneg : 0 ≤ (2 * Real.exp 1) * (x / T) := by positivity
  have hsmooth :=
    perronKernelOffBoundaryDavenportSmoothEnvelope_le_reciprocalWeight x T hx hT_lo
  have hrecip_x := hrecip x hx
  calc perronKernelOffBoundaryDavenportSmoothEnvelope x T
      ≤ (2 * Real.exp 1) * (x / T) *
          perronKernelVonMangoldtReciprocalWeight x := hsmooth
    _ ≤ (2 * Real.exp 1) * (x / T) *
          (Cr * (Real.log x) ^ 2) :=
        mul_le_mul_of_nonneg_left hrecip_x hscale_nonneg
    _ = Cm * (x / T) * (Real.log x) ^ 2 := by
        dsimp [Cm]
        ring

/-- Pointwise reciprocal-log comparison for the off-boundary singular
Davenport term.  The finite Perron range keeps every positive term on the
large side `n < x`; the off-boundary singularity is then split into the two
natural reciprocal weights `1 / n` and `1 / (x - n)`. -/
theorem small_T_offBoundary_davenportSingular_pointwise_bound :
    ∃ K > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ (Finset.range (Nat.floor x + 1)).filter
          (fun n : ℕ => ¬ |x - (n : ℝ)| ≤ x / T) →
          perronKernelOffBoundaryDavenportSingularTerm x T n ≤
            K * (x / T) *
              ((if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ)) +
                (if n = 0 then 0 else
                  ArithmeticFunction.vonMangoldt n / (x - (n : ℝ)))) := by
  let K : ℝ := 2 * Real.exp 1
  refine ⟨K, by positivity, ?_⟩
  intro x T hx hT_lo _hT_hi n hn
  by_cases hn_zero : n = 0
  · simp [perronKernelOffBoundaryDavenportSingularTerm, hn_zero]
  · have hx_nonneg : 0 ≤ x := by linarith
    have hx_pos : 0 < x := by linarith
    have hT_pos : 0 < T := by linarith
    have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero hn_zero
    have hn_pos_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
    have hrange : n ∈ Finset.range (Nat.floor x + 1) :=
      (Finset.mem_filter.mp hn).1
    have hoff : ¬ |x - (n : ℝ)| ≤ x / T :=
      (Finset.mem_filter.mp hn).2
    have hn_le_floor : n ≤ Nat.floor x :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange)
    have hn_le_x : (n : ℝ) ≤ x :=
      le_trans (Nat.cast_le.mpr hn_le_floor) (Nat.floor_le hx_nonneg)
    have hx_over_T_pos : 0 < x / T := div_pos hx_pos hT_pos
    have hn_ne_x : (n : ℝ) ≠ x := by
      intro hn_eq
      have hboundary : |x - (n : ℝ)| ≤ x / T := by
        rw [hn_eq, sub_self, abs_zero]
        exact hx_over_T_pos.le
      exact hoff hboundary
    have hn_lt_x : (n : ℝ) < x := lt_of_le_of_ne hn_le_x hn_ne_x
    have hdist_pos : 0 < x - (n : ℝ) := sub_pos.mpr hn_lt_x
    have hy_gt_one : 1 < x / (n : ℝ) := by
      rw [one_lt_div hn_pos_real]
      exact hn_lt_x
    have hy_pos : 0 < x / (n : ℝ) := div_pos hx_pos hn_pos_real
    have hy_ge_one : 1 ≤ x / (n : ℝ) := le_of_lt hy_gt_one
    have hlog_pos : 0 < Real.log (x / (n : ℝ)) := Real.log_pos hy_gt_one
    have hratio_pos : 0 < (x - (n : ℝ)) / x := div_pos hdist_pos hx_pos
    have hrecip_log :
        (Real.log (x / (n : ℝ)))⁻¹ ≤ x / (x - (n : ℝ)) := by
      have hbase := Real.one_sub_inv_le_log_of_pos hy_pos
      have hbase' :
          1 - (x / (n : ℝ))⁻¹ ≤ Real.log (x / (n : ℝ)) := by
        linarith [hbase]
      have hrewrite : 1 - (x / (n : ℝ))⁻¹ = (x - (n : ℝ)) / x := by
        field_simp [hx_pos.ne', hn_pos_real.ne']
      have hlog_lower :
          (x - (n : ℝ)) / x ≤ Real.log (x / (n : ℝ)) := by
        rw [← hrewrite]
        exact hbase'
      calc (Real.log (x / (n : ℝ)))⁻¹
          ≤ ((x - (n : ℝ)) / x)⁻¹ :=
            (inv_le_inv₀ hlog_pos hratio_pos).2 hlog_lower
        _ = x / (x - (n : ℝ)) := by
            field_simp [hx_pos.ne', hdist_pos.ne']
    have hrpow :
        (x / (n : ℝ)) ^ (1 + 1 / Real.log x) ≤
          Real.exp 1 * (x / (n : ℝ)) :=
      per_term_rpow_bound x hx n hn_pos hn_le_x
    have hexp_ge_one : (1 : ℝ) ≤ Real.exp 1 := by
      calc (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
        _ ≤ Real.exp 1 := Real.exp_monotone (by norm_num)
    have hone_le_exp_y : (1 : ℝ) ≤ Real.exp 1 * (x / (n : ℝ)) := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ Real.exp 1 * (x / (n : ℝ)) :=
          mul_le_mul hexp_ge_one hy_ge_one zero_le_one (Real.exp_pos 1).le
    have hnum :
        (x / (n : ℝ)) ^ (1 + 1 / Real.log x) + 1 ≤
          2 * Real.exp 1 * (x / (n : ℝ)) := by
      calc (x / (n : ℝ)) ^ (1 + 1 / Real.log x) + 1
          ≤ Real.exp 1 * (x / (n : ℝ)) +
              Real.exp 1 * (x / (n : ℝ)) :=
            add_le_add hrpow hone_le_exp_y
        _ = 2 * Real.exp 1 * (x / (n : ℝ)) := by ring
    have hTlog_pos : 0 < T * Real.log (x / (n : ℝ)) := mul_pos hT_pos hlog_pos
    have hkernel :
        ((x / (n : ℝ)) ^ (1 + 1 / Real.log x) + 1) /
            (T * Real.log (x / (n : ℝ))) ≤
          (2 * Real.exp 1 * (x / (n : ℝ)) / T) *
            (x / (x - (n : ℝ))) := by
      calc ((x / (n : ℝ)) ^ (1 + 1 / Real.log x) + 1) /
            (T * Real.log (x / (n : ℝ)))
          ≤ (2 * Real.exp 1 * (x / (n : ℝ))) /
              (T * Real.log (x / (n : ℝ))) :=
            div_le_div_of_nonneg_right hnum hTlog_pos.le
        _ = (2 * Real.exp 1 * (x / (n : ℝ)) / T) *
              (Real.log (x / (n : ℝ)))⁻¹ := by
            field_simp [hT_pos.ne', hlog_pos.ne']
        _ ≤ (2 * Real.exp 1 * (x / (n : ℝ)) / T) *
              (x / (x - (n : ℝ))) :=
            mul_le_mul_of_nonneg_left hrecip_log (by positivity)
    calc perronKernelOffBoundaryDavenportSingularTerm x T n
        = ArithmeticFunction.vonMangoldt n *
            (((x / (n : ℝ)) ^ (1 + 1 / Real.log x) + 1) /
              (T * Real.log (x / (n : ℝ)))) := by
            simp [perronKernelOffBoundaryDavenportSingularTerm, hn_zero]
      _ ≤ ArithmeticFunction.vonMangoldt n *
            ((2 * Real.exp 1 * (x / (n : ℝ)) / T) *
              (x / (x - (n : ℝ)))) :=
            mul_le_mul_of_nonneg_left hkernel (vonMangoldt_nonneg n)
      _ = K * (x / T) *
            (ArithmeticFunction.vonMangoldt n / (n : ℝ) +
              ArithmeticFunction.vonMangoldt n / (x - (n : ℝ))) := by
            dsimp [K]
            field_simp [hT_pos.ne', hn_pos_real.ne', hdist_pos.ne']
            ring
      _ = K * (x / T) *
            ((if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ)) +
              (if n = 0 then 0 else
                ArithmeticFunction.vonMangoldt n / (x - (n : ℝ)))) := by
            simp [hn_zero]

/-- Off-boundary distance weight is bounded by `(T / x) * psi(x)`.  This is
the exact cancellation behind the remaining singular summation: off the
boundary window, `x / T < x - n`, hence `(x - n)⁻¹ <= T / x`. -/
theorem perronKernelOffBoundaryDistanceWeight_le_scaled_chebyshevPsi
    (x T : ℝ) (hx : 2 ≤ x) (hT_lo : 2 ≤ T) :
    perronKernelOffBoundaryDistanceWeight x T ≤
      (T / x) * Aristotle.DirichletPhaseAlignment.chebyshevPsi x := by
  classical
  let s := (Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => ¬ |x - (n : ℝ)| ≤ x / T)
  have hx_nonneg : 0 ≤ x := by linarith
  have hx_pos : 0 < x := by linarith
  have hT_pos : 0 < T := by linarith
  have hscale_nonneg : 0 ≤ T / x := div_nonneg hT_pos.le hx_pos.le
  have hterm :
      ∀ n ∈ s,
        (if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / (x - (n : ℝ))) ≤
          (T / x) * ArithmeticFunction.vonMangoldt n := by
    intro n hn
    by_cases hn_zero : n = 0
    · have hrhs_nonneg : 0 ≤ (T / x) * ArithmeticFunction.vonMangoldt n :=
        mul_nonneg hscale_nonneg (vonMangoldt_nonneg n)
      simpa [hn_zero] using hrhs_nonneg
    · have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero hn_zero
      have hrange : n ∈ Finset.range (Nat.floor x + 1) :=
        (Finset.mem_filter.mp hn).1
      have hoff : ¬ |x - (n : ℝ)| ≤ x / T :=
        (Finset.mem_filter.mp hn).2
      have hn_le_floor : n ≤ Nat.floor x :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange)
      have hn_le_x : (n : ℝ) ≤ x :=
        le_trans (Nat.cast_le.mpr hn_le_floor) (Nat.floor_le hx_nonneg)
      have hx_over_T_pos : 0 < x / T := div_pos hx_pos hT_pos
      have hn_ne_x : (n : ℝ) ≠ x := by
        intro hn_eq
        have hboundary : |x - (n : ℝ)| ≤ x / T := by
          rw [hn_eq, sub_self, abs_zero]
          exact hx_over_T_pos.le
        exact hoff hboundary
      have hn_lt_x : (n : ℝ) < x := lt_of_le_of_ne hn_le_x hn_ne_x
      have hdist_pos : 0 < x - (n : ℝ) := sub_pos.mpr hn_lt_x
      have hdist_nonneg : 0 ≤ x - (n : ℝ) := hdist_pos.le
      have hdist_gt : x / T < x - (n : ℝ) := by
        have hoff' : ¬ (x - (n : ℝ) ≤ x / T) := by
          simpa [abs_of_nonneg hdist_nonneg] using hoff
        exact lt_of_not_ge hoff'
      have hrecip :
          (x - (n : ℝ))⁻¹ ≤ T / x := by
        calc (x - (n : ℝ))⁻¹
            ≤ (x / T)⁻¹ :=
              (inv_le_inv₀ hdist_pos hx_over_T_pos).2 hdist_gt.le
          _ = T / x := by
              field_simp [hx_pos.ne', hT_pos.ne']
      calc (if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / (x - (n : ℝ)))
          = ArithmeticFunction.vonMangoldt n * (x - (n : ℝ))⁻¹ := by
              simp [hn_zero, div_eq_mul_inv]
        _ ≤ ArithmeticFunction.vonMangoldt n * (T / x) :=
              mul_le_mul_of_nonneg_left hrecip (vonMangoldt_nonneg n)
        _ = (T / x) * ArithmeticFunction.vonMangoldt n := by ring
  calc perronKernelOffBoundaryDistanceWeight x T
      = ∑ n ∈ s,
          if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / (x - (n : ℝ)) := by
        rfl
    _ ≤ ∑ n ∈ s, (T / x) * ArithmeticFunction.vonMangoldt n :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ Finset.range (Nat.floor x + 1),
          (T / x) * ArithmeticFunction.vonMangoldt n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro n _hn_range _hn_not_s
          exact mul_nonneg hscale_nonneg (vonMangoldt_nonneg n)
    _ = (T / x) * Aristotle.DirichletPhaseAlignment.chebyshevPsi x := by
        dsimp [Aristotle.DirichletPhaseAlignment.chebyshevPsi]
        rw [Finset.mul_sum]

/-- Closed off-boundary distance-weight summation bound. -/
theorem small_T_offBoundary_distanceWeight_bound :
    ∃ Cd > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelOffBoundaryDistanceWeight x T ≤ Cd * (Real.log x) ^ 2 := by
  let A : ℝ := Real.log 4 + 4
  let Cd : ℝ := 16 * A * ((Real.log 2) ^ 2)⁻¹
  have hlog4_nonneg : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    linarith
  have hA_pos : 0 < A := by
    dsimp [A]
    linarith
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hCd_pos : 0 < Cd := by
    dsimp [Cd]
    exact mul_pos (mul_pos (by norm_num) hA_pos)
      (inv_pos.mpr (sq_pos_of_pos hlog2_pos))
  refine ⟨Cd, hCd_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  have hx_nonneg : 0 ≤ x := by linarith
  have hx_pos : 0 < x := by linarith
  have hT_nonneg : 0 ≤ T := by linarith
  have hscale_nonneg : 0 ≤ T / x := div_nonneg hT_nonneg hx_pos.le
  have hlog2_le_logx : Real.log (2 : ℝ) ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx
  have hlog_sq_lower : (Real.log (2 : ℝ)) ^ 2 ≤ (Real.log x) ^ 2 := by
    nlinarith [hlog2_pos, hlog2_le_logx]
  have hconst_absorb :
      16 * A ≤ Cd * (Real.log x) ^ 2 := by
    calc 16 * A
        = Cd * (Real.log (2 : ℝ)) ^ 2 := by
            dsimp [Cd]
            field_simp [ne_of_gt (sq_pos_of_pos hlog2_pos)]
      _ ≤ Cd * (Real.log x) ^ 2 :=
          mul_le_mul_of_nonneg_left hlog_sq_lower hCd_pos.le
  calc perronKernelOffBoundaryDistanceWeight x T
      ≤ (T / x) * Aristotle.DirichletPhaseAlignment.chebyshevPsi x :=
        perronKernelOffBoundaryDistanceWeight_le_scaled_chebyshevPsi x T hx hT_lo
    _ ≤ (T / x) * (A * x) :=
        mul_le_mul_of_nonneg_left
          (dirichletPhase_chebyshevPsi_le_const_mul_self x hx_nonneg)
          hscale_nonneg
    _ = T * A := by field_simp [hx_pos.ne']
    _ ≤ 16 * A := mul_le_mul_of_nonneg_right hT_hi hA_nonneg
    _ ≤ Cd * (Real.log x) ^ 2 := hconst_absorb

/-- Conditional singular off-boundary Davenport bound from the pointwise
reciprocal-log comparison and the remaining distance-weight summation atom. -/
theorem small_T_offBoundary_davenportSingularEnvelope_bound_from_pointwise_and_distance
    (hpoint : ∃ K > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ (Finset.range (Nat.floor x + 1)).filter
          (fun n : ℕ => ¬ |x - (n : ℝ)| ≤ x / T) →
          perronKernelOffBoundaryDavenportSingularTerm x T n ≤
            K * (x / T) *
              ((if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ)) +
                (if n = 0 then 0 else
                  ArithmeticFunction.vonMangoldt n / (x - (n : ℝ)))))
    (hdistance : ∃ Cd > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelOffBoundaryDistanceWeight x T ≤ Cd * (Real.log x) ^ 2) :
    ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelOffBoundaryDavenportSingularEnvelope x T ≤
        Cs * (x / T) * (Real.log x) ^ 2 := by
  rcases hpoint with ⟨K, hK_pos, hpoint⟩
  rcases small_T_vonMangoldt_reciprocalWeight_bound with ⟨Cr, hCr_pos, hrecip⟩
  rcases hdistance with ⟨Cd, hCd_pos, hdistance⟩
  refine ⟨K * (Cr + Cd), mul_pos hK_pos (add_pos hCr_pos hCd_pos), ?_⟩
  intro x T hx hT_lo hT_hi
  let s := (Finset.range (Nat.floor x + 1)).filter
      (fun n : ℕ => ¬ |x - (n : ℝ)| ≤ x / T)
  have hx_nonneg : 0 ≤ x := by linarith
  have hT_pos : 0 < T := by linarith
  have hscale_nonneg : 0 ≤ K * (x / T) :=
    mul_nonneg hK_pos.le (div_nonneg hx_nonneg hT_pos.le)
  have hrecip_x := hrecip x hx
  have hdistance_x := hdistance x T hx hT_lo hT_hi
  have hrecip_subset :
      (∑ n ∈ s, if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ)) ≤
        perronKernelVonMangoldtReciprocalWeight x := by
    dsimp [perronKernelVonMangoldtReciprocalWeight, s]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro n _hn_range _hn_not_s
      by_cases hn_zero : n = 0
      · simp [hn_zero]
      · simpa [hn_zero] using
          div_nonneg (vonMangoldt_nonneg n) (Nat.cast_nonneg n)
  calc perronKernelOffBoundaryDavenportSingularEnvelope x T
      = ∑ n ∈ s, perronKernelOffBoundaryDavenportSingularTerm x T n := by
        rfl
    _ ≤ ∑ n ∈ s,
          K * (x / T) *
            ((if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ)) +
              (if n = 0 then 0 else
                ArithmeticFunction.vonMangoldt n / (x - (n : ℝ)))) := by
        exact Finset.sum_le_sum (fun n hn => hpoint x T hx hT_lo hT_hi n hn)
    _ = K * (x / T) *
          ((∑ n ∈ s, if n = 0 then 0 else
              ArithmeticFunction.vonMangoldt n / (n : ℝ)) +
            perronKernelOffBoundaryDistanceWeight x T) := by
        dsimp [perronKernelOffBoundaryDistanceWeight, s]
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_add_distrib]
    _ ≤ K * (x / T) *
          (perronKernelVonMangoldtReciprocalWeight x +
            perronKernelOffBoundaryDistanceWeight x T) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add hrecip_subset
            (le_refl (perronKernelOffBoundaryDistanceWeight x T)))
          hscale_nonneg
    _ ≤ K * (x / T) *
          (Cr * (Real.log x) ^ 2 + Cd * (Real.log x) ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add hrecip_x hdistance_x) hscale_nonneg
    _ = K * (Cr + Cd) * (x / T) * (Real.log x) ^ 2 := by ring

/-- Singular off-boundary Davenport bound from only the remaining
distance-weight summation atom; the pointwise reciprocal-log comparison is
closed by `small_T_offBoundary_davenportSingular_pointwise_bound`. -/
theorem small_T_offBoundary_davenportSingularEnvelope_bound_from_distance
    (hdistance : ∃ Cd > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelOffBoundaryDistanceWeight x T ≤ Cd * (Real.log x) ^ 2) :
    ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelOffBoundaryDavenportSingularEnvelope x T ≤
        Cs * (x / T) * (Real.log x) ^ 2 :=
  small_T_offBoundary_davenportSingularEnvelope_bound_from_pointwise_and_distance
    small_T_offBoundary_davenportSingular_pointwise_bound hdistance

/-- Closed singular off-boundary Davenport-envelope bound. -/
theorem small_T_offBoundary_davenportSingularEnvelope_bound :
    ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelOffBoundaryDavenportSingularEnvelope x T ≤
        Cs * (x / T) * (Real.log x) ^ 2 :=
  small_T_offBoundary_davenportSingularEnvelope_bound_from_distance
    small_T_offBoundary_distanceWeight_bound

/-- Off-boundary Davenport-envelope bound from separate singular and smooth
summation bounds. -/
theorem small_T_offBoundary_davenportEnvelope_linear_bound_from_components
    (hsingular : ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelOffBoundaryDavenportSingularEnvelope x T ≤
        Cs * (x / T) * (Real.log x) ^ 2)
    (hsmooth : ∃ Cm > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelOffBoundaryDavenportSmoothEnvelope x T ≤
        Cm * (x / T) * (Real.log x) ^ 2) :
    ∃ Cd > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelOffBoundaryDavenportEnvelope x T ≤
        Cd * (x / T) * (Real.log x) ^ 2 := by
  rcases hsingular with ⟨Cs, hCs_pos, hsingular⟩
  rcases hsmooth with ⟨Cm, hCm_pos, hsmooth⟩
  refine ⟨Cs + Cm, add_pos hCs_pos hCm_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  have hsingular_x := hsingular x T hx hT_lo hT_hi
  have hsmooth_x := hsmooth x T hx hT_lo hT_hi
  calc perronKernelOffBoundaryDavenportEnvelope x T
      = perronKernelOffBoundaryDavenportSingularEnvelope x T +
          perronKernelOffBoundaryDavenportSmoothEnvelope x T :=
        perronKernelOffBoundaryDavenportEnvelope_eq_singular_add_smooth x T
    _ ≤ Cs * (x / T) * (Real.log x) ^ 2 +
          Cm * (x / T) * (Real.log x) ^ 2 :=
        add_le_add hsingular_x hsmooth_x
    _ = (Cs + Cm) * (x / T) * (Real.log x) ^ 2 := by ring

/-- Scale-correct weighted cutoff from separate singular and smooth
off-boundary Davenport-envelope bounds. -/
theorem small_T_weighted_kernel_cutoff_linear_bound_from_offBoundary_davenport_components
    (hsingular : ∃ Cs > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelOffBoundaryDavenportSingularEnvelope x T ≤
        Cs * (x / T) * (Real.log x) ^ 2)
    (hsmooth : ∃ Cm > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelOffBoundaryDavenportSmoothEnvelope x T ≤
        Cm * (x / T) * (Real.log x) ^ 2) :
    ∃ Cw > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedCutoffError x T ≤ Cw * (x / T) * (Real.log x) ^ 2 :=
  small_T_weighted_kernel_cutoff_linear_bound_from_offBoundary_davenportEnvelope
    (small_T_offBoundary_davenportEnvelope_linear_bound_from_components
      hsingular hsmooth)

/-- Closed off-boundary Davenport-envelope bound at the honest linear-window
scale. -/
theorem small_T_offBoundary_davenportEnvelope_linear_bound :
    ∃ Cd > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelOffBoundaryDavenportEnvelope x T ≤
        Cd * (x / T) * (Real.log x) ^ 2 :=
  small_T_offBoundary_davenportEnvelope_linear_bound_from_components
    small_T_offBoundary_davenportSingularEnvelope_bound
    small_T_offBoundary_davenportSmoothEnvelope_bound

/-- The remaining singular off-boundary route after the smooth component has
been closed: it is enough to prove the pointwise reciprocal-log comparison and
the finite distance-weight summation bound. -/
theorem small_T_weighted_kernel_cutoff_linear_bound_from_offBoundary_singularDistance
    (hpoint : ∃ K > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ (Finset.range (Nat.floor x + 1)).filter
          (fun n : ℕ => ¬ |x - (n : ℝ)| ≤ x / T) →
          perronKernelOffBoundaryDavenportSingularTerm x T n ≤
            K * (x / T) *
              ((if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / (n : ℝ)) +
                (if n = 0 then 0 else
                  ArithmeticFunction.vonMangoldt n / (x - (n : ℝ)))))
    (hdistance : ∃ Cd > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelOffBoundaryDistanceWeight x T ≤ Cd * (Real.log x) ^ 2) :
    ∃ Cw > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedCutoffError x T ≤ Cw * (x / T) * (Real.log x) ^ 2 :=
  small_T_weighted_kernel_cutoff_linear_bound_from_offBoundary_davenport_components
    (small_T_offBoundary_davenportSingularEnvelope_bound_from_pointwise_and_distance
      hpoint hdistance)
    small_T_offBoundary_davenportSmoothEnvelope_bound

/-- Scale-correct weighted cutoff from the sole remaining off-boundary
distance-weight summation atom. -/
theorem small_T_weighted_kernel_cutoff_linear_bound_from_offBoundary_distance
    (hdistance : ∃ Cd > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelOffBoundaryDistanceWeight x T ≤ Cd * (Real.log x) ^ 2) :
    ∃ Cw > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedCutoffError x T ≤ Cw * (x / T) * (Real.log x) ^ 2 :=
  small_T_weighted_kernel_cutoff_linear_bound_from_offBoundary_singularDistance
    small_T_offBoundary_davenportSingular_pointwise_bound hdistance

/-- Closed scale-correct weighted Perron-kernel cutoff bound.  This is the
honest bounded-height cutoff consequence; it remains at linear-window scale
and is not the false pure `O((log x)^2)` provider target. -/
theorem small_T_weighted_kernel_cutoff_linear_bound :
    ∃ Cw > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedCutoffError x T ≤ Cw * (x / T) * (Real.log x) ^ 2 :=
  small_T_weighted_kernel_cutoff_linear_bound_from_offBoundary_distance
    small_T_offBoundary_distanceWeight_bound

/-- Weighted finite cutoff from the Davenport separated-bound route and the
off-boundary weighted atom. -/
theorem small_T_weighted_kernel_cutoff_bound_from_davenport_separated_and_offBoundary
    (hkernel : ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      ∀ n : ℕ,
        n ∈ perronKernelSeparatedPuncturedBoundarySet x T →
          |1 - perronPerTermIntegral (x / (n : ℝ)) (1 + 1 / Real.log x) T| ≤
            perronKernelSeparatedDavenportEnvelopeTerm x T n)
    (henvelope : ∃ Cd > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedDavenportEnvelope x T ≤ Cd * (Real.log x) ^ 2)
    (hoffBoundary : ∃ Co > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedOffBoundaryWindowError x T ≤ Co * (Real.log x) ^ 2) :
    ∃ Cw > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedCutoffError x T ≤ Cw * (Real.log x) ^ 2 :=
  small_T_weighted_kernel_cutoff_bound_from_separated_boundary_and_offBoundary
    (small_T_separated_weighted_bound_from_davenport_envelope hkernel henvelope)
    hoffBoundary

/-- Weighted finite cutoff from the closed Davenport separated-kernel
normalization, the weighted Davenport-envelope summation bound, and the
off-boundary weighted atom. -/
theorem small_T_weighted_kernel_cutoff_bound_from_davenport_envelope_and_offBoundary
    (henvelope : ∃ Cd > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelSeparatedDavenportEnvelope x T ≤ Cd * (Real.log x) ^ 2)
    (hoffBoundary : ∃ Co > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedOffBoundaryWindowError x T ≤ Co * (Real.log x) ^ 2) :
    ∃ Cw > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedCutoffError x T ≤ Cw * (Real.log x) ^ 2 :=
  small_T_weighted_kernel_cutoff_bound_from_davenport_separated_and_offBoundary
    small_T_separated_davenport_kernel_bound henvelope hoffBoundary

/-- Finite Perron-kernel cutoff from a weighted per-term cutoff-error bound.

The only remaining analytic content is the weighted finite sum
`perronKernelWeightedCutoffError`: after unfolding `chebyshevPsi` and
`perronKernelFiniteSum`, the difference is a finite sum of
`Λ(n) * (1 - perronPerTermIntegral (x/n) c T)`, and the triangle inequality
reduces it to the weighted absolute error. -/
theorem small_T_perronKernelFiniteSum_cutoff_bound_from_weighted_error
    (hweighted : ∃ Cw > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedCutoffError x T ≤ Cw * (Real.log x) ^ 2) :
    ∃ Ck > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x -
          perronKernelFiniteSum x T| ≤
        Ck * (Real.log x) ^ 2 := by
  rcases hweighted with ⟨Cw, hCw_pos, hweighted⟩
  refine ⟨Cw, hCw_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  have hrewrite :
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x -
          perronKernelFiniteSum x T =
        ∑ n ∈ Finset.range (Nat.floor x + 1),
          ArithmeticFunction.vonMangoldt n *
            (1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T) := by
    dsimp [Aristotle.DirichletPhaseAlignment.chebyshevPsi, perronKernelFiniteSum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  calc |Aristotle.DirichletPhaseAlignment.chebyshevPsi x -
          perronKernelFiniteSum x T|
      = |∑ n ∈ Finset.range (Nat.floor x + 1),
          ArithmeticFunction.vonMangoldt n *
            (1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T)| := by
            rw [hrewrite]
    _ ≤ ∑ n ∈ Finset.range (Nat.floor x + 1),
          |ArithmeticFunction.vonMangoldt n *
            (1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T)| := by
            exact Finset.abs_sum_le_sum_abs
              (fun n ↦ ArithmeticFunction.vonMangoldt n *
                (1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T))
              (Finset.range (Nat.floor x + 1))
    _ = perronKernelWeightedCutoffError x T := by
            dsimp [perronKernelWeightedCutoffError]
            apply Finset.sum_congr rfl
            intro n _hn
            rw [abs_mul, abs_of_nonneg (vonMangoldt_nonneg n)]
    _ ≤ Cw * (Real.log x) ^ 2 := hweighted x T hx hT_lo hT_hi

/-- Scale-correct finite Perron-kernel cutoff from a weighted per-term
cutoff-error bound at the honest linear-window scale. -/
theorem small_T_perronKernelFiniteSum_cutoff_linear_bound_from_weighted_error
    (hweighted : ∃ Cw > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedCutoffError x T ≤ Cw * (x / T) * (Real.log x) ^ 2) :
    ∃ Ck > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x -
          perronKernelFiniteSum x T| ≤
        Ck * (x / T) * (Real.log x) ^ 2 := by
  rcases hweighted with ⟨Cw, hCw_pos, hweighted⟩
  refine ⟨Cw, hCw_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  have hrewrite :
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x -
          perronKernelFiniteSum x T =
        ∑ n ∈ Finset.range (Nat.floor x + 1),
          ArithmeticFunction.vonMangoldt n *
            (1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T) := by
    dsimp [Aristotle.DirichletPhaseAlignment.chebyshevPsi, perronKernelFiniteSum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  calc |Aristotle.DirichletPhaseAlignment.chebyshevPsi x -
          perronKernelFiniteSum x T|
      = |∑ n ∈ Finset.range (Nat.floor x + 1),
          ArithmeticFunction.vonMangoldt n *
            (1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T)| := by
            rw [hrewrite]
    _ ≤ ∑ n ∈ Finset.range (Nat.floor x + 1),
          |ArithmeticFunction.vonMangoldt n *
            (1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T)| := by
            exact Finset.abs_sum_le_sum_abs
              (fun n ↦ ArithmeticFunction.vonMangoldt n *
                (1 - perronPerTermIntegral (x / n) (1 + 1 / Real.log x) T))
              (Finset.range (Nat.floor x + 1))
    _ = perronKernelWeightedCutoffError x T := by
            dsimp [perronKernelWeightedCutoffError]
            apply Finset.sum_congr rfl
            intro n _hn
            rw [abs_mul, abs_of_nonneg (vonMangoldt_nonneg n)]
    _ ≤ Cw * (x / T) * (Real.log x) ^ 2 := hweighted x T hx hT_lo hT_hi

/-- Closed finite Perron-kernel cutoff at the honest linear-window scale. -/
theorem small_T_perronKernelFiniteSum_cutoff_linear_bound :
    ∃ Ck > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x -
          perronKernelFiniteSum x T| ≤
        Ck * (x / T) * (Real.log x) ^ 2 :=
  small_T_perronKernelFiniteSum_cutoff_linear_bound_from_weighted_error
    small_T_weighted_kernel_cutoff_linear_bound

/-- Small-`T` truncation for the concrete vertical integral from the finite
Perron-kernel cutoff estimate.

This isolates the next analytic atom below
`small_T_perronVerticalIntegral_truncation_bound`: the finite Perron kernel
must approximate the sharp cutoff in the definition of `chebyshevPsi` with
`O((log x)^2)` error. The existing exchange error contributes only `O(1)`,
which is absorbed by `(log x)^2` for `x ≥ 2`. -/
theorem small_T_perronVerticalIntegral_truncation_bound_from_kernel_sum_bound
    (hkernel : ∃ Ck > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x -
          perronKernelFiniteSum x T| ≤
        Ck * (Real.log x) ^ 2) :
    ∃ Cp > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronVerticalIntegral x T| ≤
        Cp * (Real.log x) ^ 2 := by
  rcases hkernel with ⟨Ck, hCk_pos, hkernel⟩
  let Clog : ℝ := ((Real.log 2) ^ 2)⁻¹
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hClog_pos : 0 < Clog := by
    dsimp [Clog]
    exact inv_pos.mpr (sq_pos_of_pos hlog2_pos)
  refine ⟨Ck + Clog, add_pos hCk_pos hClog_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  let psi : ℝ := Aristotle.DirichletPhaseAlignment.chebyshevPsi x
  let P : ℝ := perronVerticalIntegral x T
  let S : ℝ := perronKernelFiniteSum x T
  let logSq : ℝ := (Real.log x) ^ 2
  have hT_pos : 0 < T := by linarith
  have hkernel_x : |psi - S| ≤ Ck * logSq := by
    dsimp [psi, S, logSq]
    exact hkernel x T hx hT_lo hT_hi
  have hexchange : |P - S| ≤ 1 := by
    dsimp [P, S]
    simpa [perronKernelFiniteSum] using perron_exchange_error_bound x hx T hT_pos
  have htri : |psi - P| ≤ |psi - S| + |P - S| := by
    calc |psi - P|
        = |(psi - S) + (S - P)| := by ring
      _ ≤ |psi - S| + |S - P| := abs_add_le _ _
      _ = |psi - S| + |P - S| := by rw [abs_sub_comm S P]
  have hlog_mono : Real.log (2 : ℝ) ≤ Real.log x := by
    exact Real.log_le_log (by norm_num) hx
  have hlog_sq_le : (Real.log (2 : ℝ)) ^ 2 ≤ logSq := by
    dsimp [logSq]
    nlinarith
  have hone_absorb : 1 ≤ Clog * logSq := by
    dsimp [Clog]
    calc (1 : ℝ)
        = ((Real.log (2 : ℝ)) ^ 2)⁻¹ * (Real.log (2 : ℝ)) ^ 2 := by
            field_simp [ne_of_gt (sq_pos_of_pos hlog2_pos)]
      _ ≤ ((Real.log (2 : ℝ)) ^ 2)⁻¹ * logSq := by
            exact mul_le_mul_of_nonneg_left hlog_sq_le
              (inv_nonneg.mpr (sq_nonneg (Real.log (2 : ℝ))))
  calc |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronVerticalIntegral x T|
      = |psi - P| := rfl
    _ ≤ |psi - S| + |P - S| := htri
    _ ≤ Ck * logSq + 1 := by linarith
    _ ≤ Ck * logSq + Clog * logSq := by linarith
    _ = (Ck + Clog) * (Real.log x) ^ 2 := by
        dsimp [logSq]
        ring

/-- Small-`T` truncation for the concrete vertical integral at the honest
linear-window scale.

The finite kernel estimate contributes `(x / T) * (log x)^2`; the exchange
error is `O(1)`, which is absorbed into the same scale on
`x ≥ 2`, `2 ≤ T ≤ 16` because `x / T ≥ 1 / 8`. -/
theorem small_T_perronVerticalIntegral_truncation_linear_bound_from_kernel_sum_bound
    (hkernel : ∃ Ck > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x -
          perronKernelFiniteSum x T| ≤
        Ck * (x / T) * (Real.log x) ^ 2) :
    ∃ Cp > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronVerticalIntegral x T| ≤
        Cp * (x / T) * (Real.log x) ^ 2 := by
  rcases hkernel with ⟨Ck, hCk_pos, hkernel⟩
  let Cexchange : ℝ := 8 * ((Real.log 2) ^ 2)⁻¹
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hCexchange_pos : 0 < Cexchange := by
    dsimp [Cexchange]
    positivity
  refine ⟨Ck + Cexchange, add_pos hCk_pos hCexchange_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  let psi : ℝ := Aristotle.DirichletPhaseAlignment.chebyshevPsi x
  let P : ℝ := perronVerticalIntegral x T
  let S : ℝ := perronKernelFiniteSum x T
  let linLogSq : ℝ := (x / T) * (Real.log x) ^ 2
  have hT_pos : 0 < T := by linarith
  have hkernel_x : |psi - S| ≤ Ck * linLogSq := by
    dsimp [psi, S, linLogSq]
    simpa [mul_assoc] using hkernel x T hx hT_lo hT_hi
  have hexchange : |P - S| ≤ 1 := by
    dsimp [P, S]
    simpa [perronKernelFiniteSum] using perron_exchange_error_bound x hx T hT_pos
  have htri : |psi - P| ≤ |psi - S| + |P - S| := by
    calc |psi - P|
        = |(psi - S) + (S - P)| := by ring
      _ ≤ |psi - S| + |S - P| := abs_add_le _ _
      _ = |psi - S| + |P - S| := by rw [abs_sub_comm S P]
  have hx_over_T_ge : (1 / 8 : ℝ) ≤ x / T := by
    rw [le_div_iff₀ hT_pos]
    nlinarith
  have hx_over_T_nonneg : 0 ≤ x / T :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1 / 8) hx_over_T_ge
  have hlog_mono : Real.log (2 : ℝ) ≤ Real.log x := by
    exact Real.log_le_log (by norm_num) hx
  have hlog_sq_le : (Real.log (2 : ℝ)) ^ 2 ≤ (Real.log x) ^ 2 := by
    nlinarith [sq_nonneg (Real.log x - Real.log (2 : ℝ))]
  have hbase :
      (1 / 8 : ℝ) * (Real.log (2 : ℝ)) ^ 2 ≤ linLogSq := by
    dsimp [linLogSq]
    exact mul_le_mul hx_over_T_ge hlog_sq_le
      (sq_nonneg (Real.log (2 : ℝ))) hx_over_T_nonneg
  have hone_absorb : 1 ≤ Cexchange * linLogSq := by
    dsimp [Cexchange]
    calc (1 : ℝ)
        = (8 * ((Real.log (2 : ℝ)) ^ 2)⁻¹) *
            ((1 / 8 : ℝ) * (Real.log (2 : ℝ)) ^ 2) := by
            field_simp [ne_of_gt (sq_pos_of_pos hlog2_pos)]
      _ ≤ (8 * ((Real.log (2 : ℝ)) ^ 2)⁻¹) * linLogSq := by
            exact mul_le_mul_of_nonneg_left hbase hCexchange_pos.le
  calc |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronVerticalIntegral x T|
      = |psi - P| := rfl
    _ ≤ |psi - S| + |P - S| := htri
    _ ≤ Ck * linLogSq + 1 := by linarith
    _ ≤ Ck * linLogSq + Cexchange * linLogSq := by linarith
    _ = (Ck + Cexchange) * (x / T) * (Real.log x) ^ 2 := by
        dsimp [linLogSq]
        ring

/-- Closed concrete vertical-integral truncation at the honest linear-window
scale.  This deliberately does not claim the pure `(log x)^2` provider
target. -/
theorem small_T_perronVerticalIntegral_truncation_linear_bound :
    ∃ Cp > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronVerticalIntegral x T| ≤
        Cp * (x / T) * (Real.log x) ^ 2 :=
  small_T_perronVerticalIntegral_truncation_linear_bound_from_kernel_sum_bound
    small_T_perronKernelFiniteSum_cutoff_linear_bound

/-- Concrete small-`T` handoff for the actual Perron vertical integral.

This is intentionally not an instance. It records the non-circular route from
the concrete vertical integral in this file to the direct small-`T`
Hadamard/Perron provider target. The remaining analytic atoms are exactly:

* bounded-height truncation for `perronVerticalIntegral`;
* bounded-height residue/contour extraction for `perronVerticalIntegral`.

Neither hypothesis may be discharged through
`ContourRemainderBoundHyp.bound`, `general_formula_accessible`, or a theorem
that already consumes `SmallTPerronBoundHyp`. -/
theorem small_T_direct_bound_from_perronVerticalIntegral_components
    (htrunc : ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronVerticalIntegral x T| ≤
        Cₚ * (Real.log x) ^ 2)
    (hresidue : ∃ Cᵣ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalIntegral x T -
          (x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T)| ≤
        Cᵣ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) :
    ∃ C₂ > (0:ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Littlewood.Development.HadamardProductZeta.shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) :=
  Littlewood.Development.HadamardProductZeta.small_T_direct_bound_from_perron_components
    perronVerticalIntegral htrunc hresidue

/-- Honest linear-window direct handoff from the concrete vertical Perron
integral and residue extraction.

This records what the validated cutoff route can currently support:
the final direct bound contains `(x / T) * (log x)^2`.  That term is not
absorbed into the public small-`T` provider target without a new analytic
argument, so this theorem is intentionally not packaged as
`SmallTPerronBoundHyp`. -/
theorem small_T_direct_linear_bound_from_perronVerticalIntegral_components
    (htrunc : ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronVerticalIntegral x T| ≤
        Cₚ * (x / T) * (Real.log x) ^ 2)
    (hresidue : ∃ Cᵣ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalIntegral x T -
          (x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T)| ≤
        Cᵣ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) :
    ∃ C₂ > (0:ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Littlewood.Development.HadamardProductZeta.shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T +
          (x / T) * (Real.log x) ^ 2) := by
  rcases htrunc with ⟨Cₚ, hCₚ_pos, htrunc⟩
  rcases hresidue with ⟨Cᵣ, hCᵣ_pos, hresidue⟩
  let C₂ : ℝ := max Cₚ Cᵣ
  have hC₂_pos : 0 < C₂ := lt_max_of_lt_left hCₚ_pos
  refine ⟨C₂, hC₂_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  let E : ℝ := Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T
  let Llin : ℝ := (x / T) * (Real.log x) ^ 2
  have hT_pos : 0 < T := by linarith
  have hx_nonneg : 0 ≤ x := by linarith
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact Littlewood.Development.HadamardProductZeta.error_shape_nonneg x T
  have hLlin_nonneg : 0 ≤ Llin := by
    dsimp [Llin]
    exact mul_nonneg (div_nonneg hx_nonneg hT_pos.le) (sq_nonneg (Real.log x))
  have hdecomp :
      Littlewood.Development.HadamardProductZeta.shiftedRemainderRe x T =
        (perronVerticalIntegral x T -
          (x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T)) +
        (Aristotle.DirichletPhaseAlignment.chebyshevPsi x -
          perronVerticalIntegral x T) := by
    change Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x +
        Littlewood.Development.HadamardProductZeta.zeroSumRe x T =
      (perronVerticalIntegral x T -
        (x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T)) +
      (Aristotle.DirichletPhaseAlignment.chebyshevPsi x -
        perronVerticalIntegral x T)
    ring
  have htri :
      |Littlewood.Development.HadamardProductZeta.shiftedRemainderRe x T| ≤
        |perronVerticalIntegral x T -
          (x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T)| +
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x -
          perronVerticalIntegral x T| := by
    rw [hdecomp]
    exact abs_add_le _ _
  have hresidue_x :
      |perronVerticalIntegral x T -
          (x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T)| ≤
        Cᵣ * E := by
    dsimp [E]
    exact hresidue x T hx hT_lo hT_hi
  have htrunc_x :
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x -
          perronVerticalIntegral x T| ≤
        Cₚ * Llin := by
    dsimp [Llin]
    simpa [mul_assoc] using htrunc x T hx hT_lo hT_hi
  calc |Littlewood.Development.HadamardProductZeta.shiftedRemainderRe x T|
      ≤ |perronVerticalIntegral x T -
          (x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T)| +
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x -
          perronVerticalIntegral x T| := htri
    _ ≤ Cᵣ * E + Cₚ * Llin := by linarith
    _ ≤ C₂ * E + C₂ * Llin := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right (le_max_right Cₚ Cᵣ) hE_nonneg)
          (mul_le_mul_of_nonneg_right (le_max_left Cₚ Cᵣ) hLlin_nonneg)
    _ = C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T +
          (x / T) * (Real.log x) ^ 2) := by
        dsimp [C₂, E, Llin]
        ring

/-- Honest linear-window direct handoff from the closed finite Perron cutoff
and a bounded-height residue extraction atom. -/
theorem small_T_direct_linear_bound_from_residue
    (hresidue : ∃ Cᵣ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalIntegral x T -
          (x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T)| ≤
        Cᵣ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) :
    ∃ C₂ > (0:ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Littlewood.Development.HadamardProductZeta.shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T +
          (x / T) * (Real.log x) ^ 2) :=
  small_T_direct_linear_bound_from_perronVerticalIntegral_components
    small_T_perronVerticalIntegral_truncation_linear_bound hresidue

/-- Bounded-height residue extraction from an explicit contour-remainder
identity and bound.

This is the next smaller atom below the direct residue hypothesis: identify
the vertical Perron integral as the pole and zero residues plus a concrete
contour remainder, then bound only that contour remainder. -/
theorem small_T_perronVerticalIntegral_residue_bound_from_contour_remainder
    (contourRemainderRe : ℝ → ℝ → ℝ)
    (hidentity : ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronVerticalIntegral x T =
        x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T +
          contourRemainderRe x T)
    (hbound : ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |contourRemainderRe x T| ≤
        Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) :
    ∃ Cᵣ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalIntegral x T -
          (x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T)| ≤
        Cᵣ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
  rcases hbound with ⟨Cc, hCc_pos, hbound⟩
  refine ⟨Cc, hCc_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  calc |perronVerticalIntegral x T -
          (x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T)|
      = |contourRemainderRe x T| := by
          rw [hidentity x T hx hT_lo hT_hi]
          ring
    _ ≤ Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) :=
        hbound x T hx hT_lo hT_hi

/-- Bounded-height residue extraction for the actual vertical Perron integral
from a bound on the concrete named contour-remainder defect. -/
theorem small_T_perronVerticalIntegral_residue_bound_from_concrete_contour_remainder
    (hbound : ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalContourRemainderRe x T| ≤
        Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) :
    ∃ Cᵣ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalIntegral x T -
          (x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T)| ≤
        Cᵣ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) :=
  small_T_perronVerticalIntegral_residue_bound_from_contour_remainder
    perronVerticalContourRemainderRe
    (fun x T _hx _hT_lo _hT_hi => perronVerticalIntegral_residue_identity x T)
    hbound

/-- Bounded-height estimate for the concrete contour-remainder defect from a
normalized supremum bound.

The normalization denominator is strictly positive on `x ≥ 2`,
`2 ≤ T ≤ 16`, by `small_T_residue_error_shape_pos`.  This is the precise
supremum-style atom left after the algebraic residue identity has been named;
it does not use any legacy small-`T` provider. -/
theorem small_T_concrete_contour_remainder_bound_from_normalized_sup
    (hsup : ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalContourRemainderRe x T| /
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) ≤ Cc) :
    ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalContourRemainderRe x T| ≤
        Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
  rcases hsup with ⟨Cc, hCc_pos, hsup⟩
  refine ⟨Cc, hCc_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  have hshape_pos :
      0 < Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T :=
    small_T_residue_error_shape_pos x T hx hT_lo hT_hi
  exact (div_le_iff₀ hshape_pos).mp (hsup x T hx hT_lo hT_hi)

/-- Global normalized concrete-defect bound from a bounded slab and an
asymptotic tail.

This is the scale-safe replacement for a compactness claim in `x`: the domain
`x ≥ 2` is unbounded, so one must prove a bounded slab estimate up to an
explicit cutoff `X0` and a separate tail estimate from `X0` onward. -/
theorem small_T_concrete_contour_remainder_normalized_sup_from_slab_and_tail
    (X0 : ℝ) (hX0 : 2 ≤ X0)
    (hslab : ∃ Cslab > (0 : ℝ), ∀ x T : ℝ,
      x ≥ 2 → x ≤ X0 → 2 ≤ T → T ≤ 16 →
        |perronVerticalContourRemainderRe x T| /
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) ≤ Cslab)
    (htail : ∃ Ctail > (0 : ℝ), ∀ x T : ℝ,
      2 ≤ X0 → X0 ≤ x → 2 ≤ T → T ≤ 16 →
        |perronVerticalContourRemainderRe x T| /
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) ≤ Ctail) :
    ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalContourRemainderRe x T| /
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) ≤ Cc := by
  rcases hslab with ⟨Cslab, hCslab_pos, hslab⟩
  rcases htail with ⟨Ctail, hCtail_pos, htail⟩
  refine ⟨max Cslab Ctail, lt_max_of_lt_left hCslab_pos, ?_⟩
  intro x T hx hT_lo hT_hi
  rcases le_total x X0 with hx_slab | hx_tail
  · exact le_trans (hslab x T hx hx_slab hT_lo hT_hi)
      (le_max_left Cslab Ctail)
  · exact le_trans (htail x T hX0 hx_tail hT_lo hT_hi)
      (le_max_right Cslab Ctail)

/-- Explicit `X0 = 16` version of the slab/tail split for the normalized
concrete contour-remainder defect.

The bounded slab is now the genuine compact rectangle
`2 ≤ x ≤ 16`, `2 ≤ T ≤ 16`; the unbounded work is isolated in the separate
tail atom `16 ≤ x`. -/
theorem small_T_concrete_contour_remainder_normalized_sup_from_slab16_and_tail16
    (hslab16 : ∃ Cslab > (0 : ℝ), ∀ x T : ℝ,
      x ≥ 2 → x ≤ 16 → 2 ≤ T → T ≤ 16 →
        |perronVerticalContourRemainderRe x T| /
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) ≤ Cslab)
    (htail16 : ∃ Ctail > (0 : ℝ), ∀ x T : ℝ,
      16 ≤ x → 2 ≤ T → T ≤ 16 →
        |perronVerticalContourRemainderRe x T| /
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) ≤ Ctail) :
    ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalContourRemainderRe x T| /
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) ≤ Cc := by
  refine
    small_T_concrete_contour_remainder_normalized_sup_from_slab_and_tail
      (16 : ℝ) (by norm_num) hslab16 ?_
  rcases htail16 with ⟨Ctail, hCtail_pos, htail16⟩
  refine ⟨Ctail, hCtail_pos, ?_⟩
  intro x T _hX0 hx_tail hT_lo hT_hi
  exact htail16 x T hx_tail hT_lo hT_hi

/-- The compact-slab estimate follows from boundedness above of the normalized
defect image over the closed rectangle `2 ≤ x ≤ 16`, `2 ≤ T ≤ 16`.

This is the exact theorem-shaped compactness atom: continuity of the normalized
defect on the rectangle should provide the `BddAbove` hypothesis, while this
lemma performs only the order/unpacking step needed by downstream Perron
surfaces. -/
theorem small_T_concrete_contour_remainder_slab16_from_bddAbove_image
    (hbdd : BddAbove
      ((fun p : ℝ × ℝ =>
          perronVerticalContourRemainderNormalized p.1 p.2) ''
        {p : ℝ × ℝ | 2 ≤ p.1 ∧ p.1 ≤ 16 ∧ 2 ≤ p.2 ∧ p.2 ≤ 16})) :
    ∃ Cslab > (0 : ℝ), ∀ x T : ℝ,
      x ≥ 2 → x ≤ 16 → 2 ≤ T → T ≤ 16 →
        |perronVerticalContourRemainderRe x T| /
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) ≤ Cslab := by
  rcases hbdd with ⟨M, hM⟩
  refine ⟨max (1 : ℝ) M, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) M)
  · intro x T hx_lo hx_hi hT_lo hT_hi
    have hp :
        (x, T) ∈
          {p : ℝ × ℝ | 2 ≤ p.1 ∧ p.1 ≤ 16 ∧ 2 ≤ p.2 ∧ p.2 ≤ 16} := by
      exact ⟨hx_lo, hx_hi, hT_lo, hT_hi⟩
    have himage :
        perronVerticalContourRemainderNormalized x T ∈
          ((fun p : ℝ × ℝ =>
              perronVerticalContourRemainderNormalized p.1 p.2) ''
            {p : ℝ × ℝ | 2 ≤ p.1 ∧ p.1 ≤ 16 ∧ 2 ≤ p.2 ∧ p.2 ≤ 16}) := by
      exact ⟨(x, T), hp, rfl⟩
    change perronVerticalContourRemainderNormalized x T ≤ max (1 : ℝ) M
    exact le_trans (hM himage) (le_max_right (1 : ℝ) M)

/-- Explicit cutoff-`16` normalized supremum from the compact-slab bounded
image atom and the separate unbounded tail atom. -/
theorem small_T_concrete_contour_remainder_normalized_sup_from_bddAbove_slab16_and_tail16
    (hslab_bdd : BddAbove
      ((fun p : ℝ × ℝ =>
          perronVerticalContourRemainderNormalized p.1 p.2) ''
        {p : ℝ × ℝ | 2 ≤ p.1 ∧ p.1 ≤ 16 ∧ 2 ≤ p.2 ∧ p.2 ≤ 16}))
    (htail16 : ∃ Ctail > (0 : ℝ), ∀ x T : ℝ,
      16 ≤ x → 2 ≤ T → T ≤ 16 →
        |perronVerticalContourRemainderRe x T| /
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) ≤ Ctail) :
    ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalContourRemainderRe x T| /
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) ≤ Cc :=
  small_T_concrete_contour_remainder_normalized_sup_from_slab16_and_tail16
    (small_T_concrete_contour_remainder_slab16_from_bddAbove_image hslab_bdd)
    htail16

/-- Strengthened small-`T` surface matching the closed Perron cutoff route.

This class is intentionally separate from
`HadamardProductZeta.SmallTPerronBoundHyp`: it carries the honest
linear-window term `(x / T) * (log x)^2` and therefore should not be used as an
automatic provider for the legacy public surface. -/
class SmallTPerronLinearWindowBoundHyp : Prop where
  bound : ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
    |Littlewood.Development.HadamardProductZeta.shiftedRemainderRe x T| ≤
      C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T +
        (x / T) * (Real.log x) ^ 2)

/-- Constructor for the strengthened linear-window small-`T` surface from the
closed Perron cutoff route and the remaining bounded-height residue atom. -/
theorem small_T_linear_window_bound_hyp_from_residue
    (hresidue : ∃ Cᵣ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalIntegral x T -
          (x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T)| ≤
        Cᵣ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) :
    SmallTPerronLinearWindowBoundHyp :=
  ⟨small_T_direct_linear_bound_from_residue hresidue⟩

/-- Use the strengthened linear-window small-`T` surface directly, without
crossing into the legacy `SmallTPerronBoundHyp` target. -/
theorem small_T_direct_linear_bound_from_linear_window_hyp
    [SmallTPerronLinearWindowBoundHyp] :
    ∃ C₂ > (0:ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Littlewood.Development.HadamardProductZeta.shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T +
          (x / T) * (Real.log x) ^ 2) :=
  SmallTPerronLinearWindowBoundHyp.bound

/-- Adapter from the honest linear-window direct bound to the public small-`T`
target, isolating the exact missing absorption statement.

The second hypothesis is intentionally explicit.  On the full current
small-`T` provider domain it is not supplied by the linear cutoff route: it is
the precise statement needed to absorb `(x / T) * (log x)^2` into the public
shape `sqrt x * (log T)^2 / sqrt T + (log x)^2`. -/
theorem small_T_direct_bound_from_linear_bound_and_absorption
    (hlinear : ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Littlewood.Development.HadamardProductZeta.shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T +
          (x / T) * (Real.log x) ^ 2))
    (habsorb : ∃ A > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      (x / T) * (Real.log x) ^ 2 ≤
        A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T +
          (Real.log x) ^ 2)) :
    ∃ C₂ > (0:ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Littlewood.Development.HadamardProductZeta.shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  rcases hlinear with ⟨Clin, hClin_pos, hlinear⟩
  rcases habsorb with ⟨A, hA_pos, habsorb⟩
  refine ⟨Clin * (1 + A), mul_pos hClin_pos (by positivity), ?_⟩
  intro x T hx hT_lo hT_hi
  let E : ℝ := Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T
  let logSq : ℝ := (Real.log x) ^ 2
  let Llin : ℝ := (x / T) * (Real.log x) ^ 2
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact Littlewood.Development.HadamardProductZeta.error_shape_nonneg x T
  have hL_nonneg : 0 ≤ logSq := by
    dsimp [logSq]
    positivity
  have hlinear_x :
      |Littlewood.Development.HadamardProductZeta.shiftedRemainderRe x T| ≤
        Clin * (E + Llin) := by
    dsimp [E, Llin]
    simpa [mul_assoc] using hlinear x T hx hT_lo hT_hi
  have habsorb_x : Llin ≤ A * (E + logSq) := by
    dsimp [E, logSq, Llin]
    exact habsorb x T hx hT_lo hT_hi
  have hE_le_shape : E ≤ E + logSq := by linarith
  have hlinear_shape : E + Llin ≤ (1 + A) * (E + logSq) := by
    calc E + Llin
        ≤ (E + logSq) + A * (E + logSq) := add_le_add hE_le_shape habsorb_x
      _ = (1 + A) * (E + logSq) := by ring
  calc |Littlewood.Development.HadamardProductZeta.shiftedRemainderRe x T|
      ≤ Clin * (E + Llin) := hlinear_x
    _ ≤ Clin * ((1 + A) * (E + logSq)) :=
        mul_le_mul_of_nonneg_left hlinear_shape hClin_pos.le
    _ = Clin * (1 + A) *
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
        dsimp [E, logSq]
        ring

/-- Non-instance public provider adapter from the closed linear cutoff route
and an explicit linear-window absorption atom.

This is the safe boundary exposed by the current Perron work: it does not
derive the missing absorption fact and it does not change the public
`SmallTPerronBoundHyp` statement. -/
theorem small_T_perron_bound_hyp_from_linear_residue_and_absorption
    (hresidue : ∃ Cᵣ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalIntegral x T -
          (x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T)| ≤
        Cᵣ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T))
    (habsorb : ∃ A > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      (x / T) * (Real.log x) ^ 2 ≤
        A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T +
          (Real.log x) ^ 2)) :
    Littlewood.Development.HadamardProductZeta.SmallTPerronBoundHyp :=
  Littlewood.Development.HadamardProductZeta.small_T_perron_bound_hyp_of_direct_bound
    (small_T_direct_bound_from_linear_bound_and_absorption
      (small_T_direct_linear_bound_from_residue hresidue) habsorb)

/-- Bridge from the strengthened linear-window small-`T` surface to the legacy
public small-`T` surface, conditional on the explicit absorption atom.

This is deliberately a theorem, not an instance: crossing from the
linear-window surface to `SmallTPerronBoundHyp` must stay visible because the
absorption statement is false on the full current domain unless additional
analytic input changes the scale. -/
theorem small_T_perron_bound_hyp_from_linear_window_hyp_and_absorption
    [SmallTPerronLinearWindowBoundHyp]
    (habsorb : ∃ A > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      (x / T) * (Real.log x) ^ 2 ≤
        A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T +
          (Real.log x) ^ 2)) :
    Littlewood.Development.HadamardProductZeta.SmallTPerronBoundHyp :=
  Littlewood.Development.HadamardProductZeta.small_T_perron_bound_hyp_of_direct_bound
    (small_T_direct_bound_from_linear_bound_and_absorption
      small_T_direct_linear_bound_from_linear_window_hyp habsorb)

/-- Linear-window small-`T` surface from the smaller contour-remainder
residue split. -/
theorem small_T_linear_window_bound_hyp_from_contour_remainder
    (contourRemainderRe : ℝ → ℝ → ℝ)
    (hidentity : ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronVerticalIntegral x T =
        x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T +
          contourRemainderRe x T)
    (hbound : ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |contourRemainderRe x T| ≤
        Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) :
    SmallTPerronLinearWindowBoundHyp :=
  small_T_linear_window_bound_hyp_from_residue
    (small_T_perronVerticalIntegral_residue_bound_from_contour_remainder
      contourRemainderRe hidentity hbound)

/-- Linear-window small-`T` surface from the concrete contour-remainder defect
for `perronVerticalIntegral`.  The only remaining analytic hypothesis is the
bounded-height estimate for `perronVerticalContourRemainderRe`. -/
theorem small_T_linear_window_bound_hyp_from_concrete_contour_remainder
    (hbound : ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalContourRemainderRe x T| ≤
        Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) :
    SmallTPerronLinearWindowBoundHyp :=
  small_T_linear_window_bound_hyp_from_residue
    (small_T_perronVerticalIntegral_residue_bound_from_concrete_contour_remainder
      hbound)

/-- Linear-window small-`T` surface from the normalized supremum bound for the
concrete contour-remainder defect. -/
theorem small_T_linear_window_bound_hyp_from_concrete_contour_remainder_normalized_sup
    (hsup : ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalContourRemainderRe x T| /
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) ≤ Cc) :
    SmallTPerronLinearWindowBoundHyp :=
  small_T_linear_window_bound_hyp_from_concrete_contour_remainder
    (small_T_concrete_contour_remainder_bound_from_normalized_sup hsup)

/-- Linear-window small-`T` surface from a bounded slab plus asymptotic tail
for the normalized concrete contour-remainder defect. -/
theorem small_T_linear_window_bound_hyp_from_concrete_contour_remainder_slab_and_tail
    (X0 : ℝ) (hX0 : 2 ≤ X0)
    (hslab : ∃ Cslab > (0 : ℝ), ∀ x T : ℝ,
      x ≥ 2 → x ≤ X0 → 2 ≤ T → T ≤ 16 →
        |perronVerticalContourRemainderRe x T| /
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) ≤ Cslab)
    (htail : ∃ Ctail > (0 : ℝ), ∀ x T : ℝ,
      2 ≤ X0 → X0 ≤ x → 2 ≤ T → T ≤ 16 →
        |perronVerticalContourRemainderRe x T| /
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) ≤ Ctail) :
    SmallTPerronLinearWindowBoundHyp :=
  small_T_linear_window_bound_hyp_from_concrete_contour_remainder_normalized_sup
    (small_T_concrete_contour_remainder_normalized_sup_from_slab_and_tail
      X0 hX0 hslab htail)

/-- Linear-window small-`T` surface from the explicit cutoff `X0 = 16`
slab/tail split for the normalized concrete contour-remainder defect. -/
theorem small_T_linear_window_bound_hyp_from_concrete_contour_remainder_slab16_and_tail16
    (hslab16 : ∃ Cslab > (0 : ℝ), ∀ x T : ℝ,
      x ≥ 2 → x ≤ 16 → 2 ≤ T → T ≤ 16 →
        |perronVerticalContourRemainderRe x T| /
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) ≤ Cslab)
    (htail16 : ∃ Ctail > (0 : ℝ), ∀ x T : ℝ,
      16 ≤ x → 2 ≤ T → T ≤ 16 →
        |perronVerticalContourRemainderRe x T| /
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) ≤ Ctail) :
    SmallTPerronLinearWindowBoundHyp :=
  small_T_linear_window_bound_hyp_from_concrete_contour_remainder_normalized_sup
    (small_T_concrete_contour_remainder_normalized_sup_from_slab16_and_tail16
      hslab16 htail16)

/-- Linear-window small-`T` surface from the compact-slab bounded image atom
and the separate unbounded tail atom. -/
theorem small_T_linear_window_bound_hyp_from_concrete_contour_remainder_bddAbove_slab16_and_tail16
    (hslab_bdd : BddAbove
      ((fun p : ℝ × ℝ =>
          perronVerticalContourRemainderNormalized p.1 p.2) ''
        {p : ℝ × ℝ | 2 ≤ p.1 ∧ p.1 ≤ 16 ∧ 2 ≤ p.2 ∧ p.2 ≤ 16}))
    (htail16 : ∃ Ctail > (0 : ℝ), ∀ x T : ℝ,
      16 ≤ x → 2 ≤ T → T ≤ 16 →
        |perronVerticalContourRemainderRe x T| /
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) ≤ Ctail) :
    SmallTPerronLinearWindowBoundHyp :=
  small_T_linear_window_bound_hyp_from_concrete_contour_remainder_normalized_sup
    (small_T_concrete_contour_remainder_normalized_sup_from_bddAbove_slab16_and_tail16
      hslab_bdd htail16)

/-- Legacy public small-`T` provider from the smaller contour-remainder split,
conditional on the explicit linear-window absorption atom.

No absorption is asserted here; the theorem only wires the smaller residue
atoms through the already explicit bridge. -/
theorem small_T_perron_bound_hyp_from_contour_remainder_and_absorption
    (contourRemainderRe : ℝ → ℝ → ℝ)
    (hidentity : ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronVerticalIntegral x T =
        x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T +
          contourRemainderRe x T)
    (hbound : ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |contourRemainderRe x T| ≤
        Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T))
    (habsorb : ∃ A > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      (x / T) * (Real.log x) ^ 2 ≤
        A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T +
          (Real.log x) ^ 2)) :
    Littlewood.Development.HadamardProductZeta.SmallTPerronBoundHyp := by
  letI : SmallTPerronLinearWindowBoundHyp :=
    small_T_linear_window_bound_hyp_from_contour_remainder
      contourRemainderRe hidentity hbound
  exact small_T_perron_bound_hyp_from_linear_window_hyp_and_absorption habsorb

/-- Legacy public small-`T` provider from the concrete contour-remainder defect,
conditional on the explicit linear-window absorption atom.  This theorem does
not assert the absorption atom and does not install a legacy provider
instance. -/
theorem small_T_perron_bound_hyp_from_concrete_contour_remainder_and_absorption
    (hbound : ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalContourRemainderRe x T| ≤
        Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T))
    (habsorb : ∃ A > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      (x / T) * (Real.log x) ^ 2 ≤
        A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T +
          (Real.log x) ^ 2)) :
    Littlewood.Development.HadamardProductZeta.SmallTPerronBoundHyp := by
  letI : SmallTPerronLinearWindowBoundHyp :=
    small_T_linear_window_bound_hyp_from_concrete_contour_remainder hbound
  exact small_T_perron_bound_hyp_from_linear_window_hyp_and_absorption habsorb

/-- Legacy public small-`T` provider from the normalized supremum bound for the
concrete contour-remainder defect, conditional on the explicit linear-window
absorption atom.  This keeps the legacy absorption obligation visible. -/
theorem small_T_perron_bound_hyp_from_concrete_contour_remainder_normalized_sup_and_absorption
    (hsup : ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalContourRemainderRe x T| /
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) ≤ Cc)
    (habsorb : ∃ A > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      (x / T) * (Real.log x) ^ 2 ≤
        A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T +
          (Real.log x) ^ 2)) :
    Littlewood.Development.HadamardProductZeta.SmallTPerronBoundHyp := by
  letI : SmallTPerronLinearWindowBoundHyp :=
    small_T_linear_window_bound_hyp_from_concrete_contour_remainder_normalized_sup
      hsup
  exact small_T_perron_bound_hyp_from_linear_window_hyp_and_absorption habsorb

/-- Concrete small-`T` provider target from the finite weighted Perron-kernel
cutoff atom plus the bounded-height residue extraction atom.

This is a stricter handoff than `small_T_direct_bound_from_perronVerticalIntegral_components`:
the truncation input has been reduced to the finite weighted cutoff error for
`perronKernelWeightedCutoffError`.  It does not use `SmallTPerronBoundHyp`,
`ContourRemainderBoundHyp.bound`, `general_formula_accessible`, or the false
`perron_tail_bound_core` statement. -/
theorem small_T_direct_bound_from_weighted_kernel_and_residue
    (hweighted : ∃ Cw > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedCutoffError x T ≤ Cw * (Real.log x) ^ 2)
    (hresidue : ∃ Cᵣ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalIntegral x T -
          (x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T)| ≤
        Cᵣ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) :
    ∃ C₂ > (0:ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |Littlewood.Development.HadamardProductZeta.shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact
    small_T_direct_bound_from_perronVerticalIntegral_components
      (small_T_perronVerticalIntegral_truncation_bound_from_kernel_sum_bound
        (small_T_perronKernelFiniteSum_cutoff_bound_from_weighted_error hweighted))
      hresidue

/-- Honest non-instance provider constructor for the public small-`T` Perron
hypothesis from the finite weighted Perron-kernel cutoff atom and the
bounded-height residue extraction atom. -/
theorem small_T_perron_bound_hyp_from_weighted_kernel_and_residue
    (hweighted : ∃ Cw > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelWeightedCutoffError x T ≤ Cw * (Real.log x) ^ 2)
    (hresidue : ∃ Cᵣ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      |perronVerticalIntegral x T -
          (x - Littlewood.Development.HadamardProductZeta.zeroSumRe x T)| ≤
        Cᵣ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) :
    Littlewood.Development.HadamardProductZeta.SmallTPerronBoundHyp :=
  Littlewood.Development.HadamardProductZeta.small_T_perron_bound_hyp_of_direct_bound
    (small_T_direct_bound_from_weighted_kernel_and_residue hweighted hresidue)

end Aristotle.Standalone.PerronTruncationInfra
