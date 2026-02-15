/-
Nonvanishing of the Riemann zeta function on the real interval (0, 1).

This is needed for the Landau non-negative Dirichlet integral argument:
the formula sC/(s-α) + σs/(s-1) + σζ'/ζ(s) must be analytic on (α, 1) ⊂ ℝ,
which requires ζ(s) ≠ 0 there.

## Main Result

* `riemannZeta_ne_zero_of_real_mem_Ioo` : ζ(↑x) ≠ 0 for x ∈ (0, 1)

## Proof Strategy

The proof uses the Dirichlet eta function η(s) = Σ (-1)^{n+1}/n^s:
1. η(s) = (1 - 2^{1-s}) ζ(s) for s ≠ 1 (algebraic identity)
2. η(s) > 0 for real s > 0 (alternating series with decreasing terms)
3. 1 - 2^{1-s} < 0 for s ∈ (0, 1) (since 2^{1-s} > 1)
4. Therefore ζ(s) = η(s) / (1 - 2^{1-s}) < 0, so ζ(s) ≠ 0.

SORRY COUNT: 1 (paired eta sum identity via analytic continuation)

REFERENCES:
  - Titchmarsh, "The Theory of the Riemann Zeta-Function", §1.4
  - Hardy-Wright, "An Introduction to the Theory of Numbers", §22.2

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.ZetaRealNonvanishing

open Complex Real

/-! ## Helper: sign of 1 - 2^{1-x}

For x ∈ (0,1): 1-x > 0, so 2^{1-x} > 2^0 = 1, hence 1 - 2^{1-x} < 0. -/

private theorem one_sub_two_pow_neg (x : ℝ) (_hx0 : 0 < x) (hx1 : x < 1) :
    1 - (2 : ℝ) ^ (1 - x) < 0 := by
  have h1 := rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    (show (0 : ℝ) < 1 - x by linarith)
  rw [rpow_zero] at h1
  linarith

/-! ## Paired eta function term positivity

Each term (2k+1)^{-x} - (2k+2)^{-x} is positive for real x > 0,
since t ↦ t^{-x} is strictly decreasing for x > 0. -/

private theorem paired_term_pos (x : ℝ) (hx : 0 < x) (k : ℕ) :
    0 < (2 * (k : ℝ) + 1) ^ (-x) - (2 * (k : ℝ) + 2) ^ (-x) := by
  have hk1 : (0 : ℝ) < 2 * k + 1 := by positivity
  have hk2 : (0 : ℝ) < 2 * k + 2 := by positivity
  rw [rpow_neg hk1.le, rpow_neg hk2.le]
  have h1 : 0 < (2 * (k : ℝ) + 1) ^ x := rpow_pos_of_pos hk1 x
  have hlt : (2 * (k : ℝ) + 1) ^ x < (2 * (k : ℝ) + 2) ^ x :=
    rpow_lt_rpow hk1.le (by linarith) hx
  linarith [(inv_lt_inv₀ (rpow_pos_of_pos hk2 x) h1).mpr hlt]

/-! ## Summability of the paired eta series

**Strategy**: Prove partial sums ∑_{k<N} f(k) ≤ 1 by induction,
using the stronger inductive hypothesis:
  ∑_{k<N} f(k) + (2N)^{-x} ≤ 1  for N ≥ 1
Then apply `summable_of_sum_range_le`. -/

private theorem paired_partial_sum_aux (x : ℝ) (hx : 0 < x) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      ((2 * (k : ℝ) + 1) ^ (-x) - (2 * (k : ℝ) + 2) ^ (-x)) +
      (2 * (↑n + 1 : ℝ)) ^ (-x) ≤ 1 := by
  induction n with
  | zero =>
    rw [Finset.sum_range_one]
    simp only [Nat.cast_zero]
    -- Goal: (2*0+1)^(-x) - (2*0+2)^(-x) + (2*(0+1))^(-x) ≤ 1
    have h1 : (2 * (0 : ℝ) + 2) ^ (-x) = (2 * ((0 : ℝ) + 1)) ^ (-x) := by
      congr 1; ring
    rw [h1, sub_add_cancel]
    have h2 : (2 * (0 : ℝ) + 1) = 1 := by ring
    rw [h2, one_rpow]
  | succ m ih =>
    rw [Finset.sum_range_succ]
    -- Cancel: f(m+1) + (2(m+2))^{-x} = (2m+3)^{-x}
    have h_eq : (2 * (↑(m + 1) : ℝ) + 2) ^ (-x) = (2 * (↑(m + 1) + 1 : ℝ)) ^ (-x) := by
      congr 1; push_cast; ring
    -- After cancel: sum_{k<m+1} f(k) + (2(m+1)+1)^{-x}
    -- Monotonicity: (2(m+1)+1)^{-x} ≤ (2(m+1))^{-x}
    have hlo : (0 : ℝ) < 2 * (↑m + 1 : ℝ) := by positivity
    have hhi : (0 : ℝ) < 2 * (↑(m + 1) : ℝ) + 1 := by positivity
    have hlt : 2 * (↑m + 1 : ℝ) < 2 * (↑(m + 1) : ℝ) + 1 := by push_cast; linarith
    have h_mono : (2 * (↑(m + 1) : ℝ) + 1) ^ (-x) ≤ (2 * (↑m + 1 : ℝ)) ^ (-x) := by
      rw [rpow_neg hhi.le, rpow_neg hlo.le]
      exact le_of_lt ((inv_lt_inv₀ (rpow_pos_of_pos hhi x)
        (rpow_pos_of_pos hlo x)).mpr (rpow_lt_rpow hlo.le hlt hx))
    linarith [h_eq, h_mono]

private theorem paired_partial_sum_le_one (x : ℝ) (hx : 0 < x) (N : ℕ) :
    ∑ k ∈ Finset.range N,
      ((2 * (k : ℝ) + 1) ^ (-x) - (2 * (k : ℝ) + 2) ^ (-x)) ≤ 1 := by
  rcases N with _ | n
  · simp
  · have := paired_partial_sum_aux x hx n
    have h_tail : (0 : ℝ) ≤ (2 * (↑n + 1 : ℝ)) ^ (-x) :=
      rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * (↑n + 1 : ℝ)) (-x)
    linarith

private theorem paired_sum_summable (x : ℝ) (hx : 0 < x) :
    Summable (fun k : ℕ => (2 * (k : ℝ) + 1) ^ (-x) - (2 * (k : ℝ) + 2) ^ (-x)) :=
  summable_of_sum_range_le
    (fun k => le_of_lt (paired_term_pos x hx k))
    (paired_partial_sum_le_one x hx)

/-! ## Paired eta sum identity

The identity ∑' k, [(2k+1)^{-x} - (2k+2)^{-x}] = (1-2^{1-x})·Re(ζ(x))
for x ∈ (0,∞) \ {1}. For x > 1 this follows from rearranging the absolutely
convergent Dirichlet series ζ(x) = ∑ n^{-x}. For x ∈ (0,1) it extends by
analytic continuation (identity principle on {Re > 0} \ {1}). -/

private theorem paired_sum_identity (x : ℝ) (hx0 : 0 < x) (hx1 : x ≠ 1) :
    ∑' k : ℕ, ((2 * (k : ℝ) + 1) ^ (-x) - (2 * (k : ℝ) + 2) ^ (-x)) =
      (1 - (2 : ℝ) ^ (1 - x)) * (riemannZeta (↑x : ℂ)).re := by
  sorry

/-! ## Main result: ζ(x) < 0 for x ∈ (0, 1)

From the eta identity: η(x) = (1-2^{1-x})·ζ(x).
Since η(x) > 0 and (1-2^{1-x}) < 0, we get ζ(x) < 0. -/

private theorem zeta_neg_on_unit_interval (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (riemannZeta (↑x : ℂ)).re < 0 := by
  have hsum := paired_sum_summable x hx0
  have heq := paired_sum_identity x hx0 (ne_of_lt hx1)
  have h_factor_neg := one_sub_two_pow_neg x hx0 hx1
  -- Paired sum is positive: each term positive + summable
  have h_term_pos : ∀ k : ℕ, 0 < (2 * (k : ℝ) + 1) ^ (-x) - (2 * (k : ℝ) + 2) ^ (-x) :=
    paired_term_pos x hx0
  have h_pos : (0 : ℝ) < ∑' (k : ℕ), ((2 * (↑k : ℝ) + 1) ^ (-x) - (2 * (↑k : ℝ) + 2) ^ (-x)) :=
    hsum.tsum_pos (fun k => le_of_lt (h_term_pos k)) 0 (h_term_pos 0)
  -- positive = (negative) · ζ(x).re implies ζ(x).re < 0
  by_contra h_nn
  push_neg at h_nn
  linarith [mul_nonpos_of_nonpos_of_nonneg (le_of_lt h_factor_neg) h_nn]

/-! ## Public API -/

/-- The Riemann zeta function does not vanish on the real interval (0, 1).
This is equivalent to saying ζ has no real zeros between 0 and 1. -/
theorem riemannZeta_ne_zero_of_real_mem_Ioo (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    riemannZeta (↑x : ℂ) ≠ 0 := by
  intro h
  have := zeta_neg_on_unit_interval x hx0 hx1
  rw [h] at this
  simp at this

/-- Combined with Mathlib's `riemannZeta_ne_zero_of_one_le_re`: ζ(s) ≠ 0
for all real s > 0 (including the junk value at s = 1). -/
theorem riemannZeta_ne_zero_of_real_pos (x : ℝ) (hx : 0 < x) :
    riemannZeta (↑x : ℂ) ≠ 0 := by
  by_cases h1 : x < 1
  · exact riemannZeta_ne_zero_of_real_mem_Ioo x hx h1
  · push_neg at h1
    exact riemannZeta_ne_zero_of_one_le_re (by simp; linarith)

/-- ζ'/ζ is analytic at any real point s ∈ (α, 1) with 0 < α. -/
theorem zeta_logDeriv_analyticAt_real (x : ℝ) (hx0 : 0 < x) (hx_ne : (↑x : ℂ) ≠ 1) :
    AnalyticAt ℂ (fun s => deriv riemannZeta s / riemannZeta s) (↑x : ℂ) := by
  have h_ne := riemannZeta_ne_zero_of_real_pos x hx0
  -- ζ is differentiable on the open set {s | s ≠ 1}
  have h_diffOn : DifferentiableOn ℂ riemannZeta {s | s ≠ 1} :=
    fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
  -- ζ is analytic on {s | s ≠ 1} via Cauchy integral formula
  have h_analytic := h_diffOn.analyticOnNhd isOpen_ne
  have h_at : AnalyticAt ℂ riemannZeta (↑x : ℂ) := h_analytic (↑x) hx_ne
  exact h_at.deriv.div h_at h_ne

end Aristotle.ZetaRealNonvanishing
