/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# L-Series Derivative Lemmas

Wrappers and applications of Mathlib's LSeries derivative infrastructure.

## Main Results (from Mathlib)

* `LSeries_hasDerivAt` : L-series is differentiable with explicit derivative formula
* `LSeries_deriv` : deriv(L(f,s)) = -L(log·f, s)

## Explicit Formulas

The derivative of an L-series is:
  L'(f, s) = -∑ₙ (log n) · f(n) · n^(-s)

This is encoded as `LSeries (logMul f)` where `logMul f n = log n * f n`.
-/

open Complex Filter

namespace Littlewood.Development.LSeriesDerivatives

/-- Wrapper: L-series has derivative at s when s.re > abscissa of convergence -/
theorem lseries_hasDerivAt (f : ℕ → ℂ) (s : ℂ) (hs : LSeries.abscissaOfAbsConv f < s.re) :
    HasDerivAt (LSeries f) (-LSeries (LSeries.logMul f) s) s :=
  LSeries_hasDerivAt hs

/-- Wrapper: The derivative of L-series equals -L(log·f, s) -/
theorem lseries_deriv (f : ℕ → ℂ) (s : ℂ) (hs : LSeries.abscissaOfAbsConv f < s.re) :
    deriv (LSeries f) s = -LSeries (LSeries.logMul f) s :=
  LSeries_deriv hs

/-- For von Mangoldt: -ζ'/ζ = L(Λ, s) -/
theorem neg_zeta_logderiv_eq_vonMangoldt (s : ℂ) (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
  (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs).symm

/-- The von Mangoldt L-series is summable for Re(s) > 1 -/
theorem vonMangoldt_lseries_summable (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
  ArithmeticFunction.LSeriesSummable_vonMangoldt hs

/-- Abscissa of convergence for von Mangoldt is at most 1 -/
theorem vonMangoldt_abscissa_le_one :
    LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    (fun _ hy => ArithmeticFunction.LSeriesSummable_vonMangoldt hy)

end Littlewood.Development.LSeriesDerivatives
