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

SORRY COUNT: 1 (core positivity/identity atom)

REFERENCES:
  - Titchmarsh, "The Theory of the Riemann Zeta-Function", §1.4
  - Hardy-Wright, "An Introduction to the Theory of Numbers", §22.2

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace Aristotle.ZetaRealNonvanishing

open Complex

/-! ## Core atom: ζ is negative on (0, 1)

The proof that ζ(s) < 0 for real s ∈ (0, 1) uses the Dirichlet eta function
η(s) = (1 - 2^{1-s})ζ(s). Since η(s) > 0 (alternating series) and
1 - 2^{1-s} < 0 (for s < 1), we get ζ(s) < 0.

The sorry here is the combined identity + positivity of the eta function.

**Proof sketch for the sorry**:
For Re(s) > 1:
  η(s) = Σ (-1)^{n+1}/n^s = Σ 1/n^s - 2·Σ 1/(2n)^s = ζ(s) - 2^{1-s}ζ(s) = (1-2^{1-s})ζ(s).

For real s > 0, η(s) converges conditionally (alternating series test):
  η(s) = Σ_{k≥0} [1/(2k+1)^s - 1/(2k+2)^s] > 0.

By analytic continuation: η(s) = (1 - 2^{1-s})ζ(s) for all s ≠ 1.
For real s ∈ (0,1): η(s) > 0 and 1-2^{1-s} < 0, so ζ(s) = η(s)/(1-2^{1-s}) < 0. -/
private theorem zeta_neg_on_unit_interval (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (riemannZeta (↑x : ℂ)).re < 0 := by
  sorry

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
