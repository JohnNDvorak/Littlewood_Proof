/-
Integral representation connecting -ζ'/ζ to ψ(x).

This file establishes the connection between the logarithmic derivative of zeta
and the Chebyshev psi function, using Mathlib's infrastructure:

  -ζ'/ζ(s) = ∑ Λ(n)/n^s = L(Λ, s) for Re(s) > 1

and derives properties of this L-series.

## Main Results

* `neg_zeta_logDeriv_eq_vonMangoldt_lseries` : -ζ'/ζ(s) = L(Λ, s) for Re(s) > 1
* `vonMangoldt_lseries_summable` : L(Λ, s) is summable for Re(s) > 1
* `vonMangoldt_nonneg` : Λ(n) ≥ 0 for all n

## Mathematical Context

This is the starting point for the Landau oscillation argument:
  1. -ζ'/ζ(s) = ∑ Λ(n)/n^s (this file)
  2. Abel summation connects ∑ Λ(n)/n^s to ∫ ψ(t) t^{-s-1} dt
  3. Under |ψ(t)-t| ≤ C√t, the integral converges for Re(s) > 1/2
  4. But ζ has zeros on Re(s) = 1/2, giving poles of -ζ'/ζ there
  5. Contradiction with analyticity gives Landau's oscillation theorem

SORRY COUNT: 0

REFERENCES:
  - Montgomery-Vaughan, "Multiplicative Number Theory I", §1.3
  - Hardy-Wright, "An Introduction to the Theory of Numbers", §22.15

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Littlewood.Basic.ChebyshevFunctions

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace Aristotle.PsiIntegralRepresentation

open Complex Real Filter Topology

/-! ## Von Mangoldt nonnegativity -/

/-- Von Mangoldt's Λ(n) is nonneg for all n. -/
theorem vonMangoldt_nonneg (n : ℕ) :
    (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n :=
  ArithmeticFunction.vonMangoldt_nonneg

/-- Von Mangoldt's Λ(n) as a complex number is nonneg in the real part. -/
theorem vonMangoldt_re_nonneg (n : ℕ) :
    (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℂ).re := by
  rw [Complex.ofReal_re]
  exact vonMangoldt_nonneg n

/-! ## The identity -ζ'/ζ = L(Λ, s) -/

/-- -ζ'/ζ(s) = L(Λ, s) for Re(s) > 1.

This is a thin wrapper around Mathlib's
`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`. -/
theorem neg_zeta_logDeriv_eq_vonMangoldt_lseries (s : ℂ) (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  exact (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs).symm

/-- The L-series of von Mangoldt is summable for Re(s) > 1.

This is a thin wrapper around Mathlib's `LSeriesSummable_vonMangoldt`. -/
theorem vonMangoldt_lseries_summable (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  exact ArithmeticFunction.LSeriesSummable_vonMangoldt hs

/-! ## Zeta nonvanishing on Re(s) ≥ 1 -/

/-- ζ(s) ≠ 0 for Re(s) ≥ 1 (Mathlib).
Note: the junk value at s=1 is also nonzero, so no s≠1 condition needed. -/
theorem zeta_ne_zero_of_re_ge_one (s : ℂ) (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-! ## Differentiability of ζ -/

/-- ζ is differentiable at s for s ≠ 1 (Mathlib). -/
theorem zeta_differentiable_at (s : ℂ) (hs : s ≠ 1) :
    DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta hs

/-! ## Connection between partial sums and ψ -/

section IntegralRep

open ArithmeticFunction Filter Topology Asymptotics Finset
open scoped LSeries.notation ArithmeticFunction

private lemma ioc_zero_eq_icc_one (n : ℕ) : Finset.Ioc 0 n = Finset.Icc 1 n := by
  ext k; simp [Finset.mem_Ioc, Finset.mem_Icc, Nat.lt_iff_add_one_le]

/-- Partial sums of Λ equal ψ (real version). -/
theorem vonMangoldt_real_sum_eq_psi (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, Λ k = chebyshevPsi (n : ℝ) := by
  unfold chebyshevPsi Chebyshev.psi
  rw [Nat.floor_natCast, ← ioc_zero_eq_icc_one]

/-- Partial sums of the complex-valued von Mangoldt function are O(n^1).
    Uses Chebyshev's bound ψ(x) ≤ 6x. -/
theorem vonMangoldt_partial_sums_isBigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (↗Λ) k) =O[atTop]
    (fun n : ℕ => ((n : ℝ) ^ (1 : ℝ))) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨6, ?_⟩
  filter_upwards with n
  -- Step 1: The complex-valued sum equals the real sum cast to ℂ
  have h_sum : (∑ k ∈ Finset.Icc 1 n, (↗Λ) k : ℂ) =
      ((∑ k ∈ Finset.Icc 1 n, Λ k : ℝ) : ℂ) := by
    push_cast; congr
  -- Step 2: Simplify norms
  rw [h_sum, Complex.norm_real, vonMangoldt_real_sum_eq_psi]
  simp only [Real.rpow_one]
  have h_psi_nn : 0 ≤ chebyshevPsi (n : ℝ) := by
    unfold chebyshevPsi; exact Chebyshev.psi_nonneg _
  rw [Real.norm_of_nonneg h_psi_nn, Real.norm_of_nonneg (Nat.cast_nonneg n)]
  -- Goal: chebyshevPsi ↑n ≤ 6 * ↑n
  by_cases hn : (1 : ℝ) ≤ (n : ℝ)
  · exact ChebyshevExt.chebyshevPsi_le n hn
  · push_neg at hn
    have hn' : n < 1 := by exact_mod_cast hn
    have hn0 : n = 0 := by omega
    subst hn0
    simp only [Nat.cast_zero, mul_zero]
    unfold chebyshevPsi
    exact le_of_eq (Chebyshev.psi_eq_zero_of_lt_two (by norm_num : (0:ℝ) < 2))

/-- Integral representation of -ζ'/ζ(s):
    -ζ'/ζ(s) = s * ∫₁^∞ (∑_{k ≤ ⌊t⌋} Λ(k)) · t^{-(s+1)} dt
    for Re(s) > 1. Combines `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`
    with `LSeries_eq_mul_integral` using the Chebyshev O(n) bound. -/
theorem neg_zeta_logDeriv_eq_integral {s : ℂ} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
    s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, (↗Λ) k) *
      (t : ℂ) ^ (-(s + 1)) := by
  rw [← LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  exact LSeries_eq_mul_integral (↗Λ) (by norm_num : (0:ℝ) ≤ 1) hs
    (LSeriesSummable_vonMangoldt hs) vonMangoldt_partial_sums_isBigO

end IntegralRep

end Aristotle.PsiIntegralRepresentation
