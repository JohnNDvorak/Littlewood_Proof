import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 3200000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.ExplicitFormulaPerron

/-
The Chebyshev function ψ(x) is the sum of the von Mangoldt function Λ(n) for n ≤ x.
-/
noncomputable def chebyshevPsi (x : ℝ) : ℝ := ∑ n ∈ Finset.range (Nat.floor x + 1), ArithmeticFunction.vonMangoldt n

/-
Data class for zeta zeros and the hypothesis class for the explicit formula.
-/
open Real Complex BigOperators Finset ArithmeticFunction

class ZetaExplicitData where
  nthZetaZero : ℕ → ℂ
  zeroCountUpTo : ℝ → ℕ

export ZetaExplicitData (nthZetaZero zeroCountUpTo)

class ExplicitFormulaPsiHyp [ZetaExplicitData] : Prop where
  formula : ∀ (x : ℝ) (hx : 1 < x),
    ∃ E : ℂ, ‖E‖ ≤ Real.log x ∧
      (chebyshevPsi x : ℂ) = x - (∑ n ∈ Finset.range (zeroCountUpTo x),
        (x : ℂ) ^ (nthZetaZero n) / (nthZetaZero n)) -
        Real.log (2 * Real.pi) - (1/2 : ℂ) * Complex.log (1 - (x : ℂ) ^ (-2 : ℤ)) + E

/-
Checking for the existence of the theorem relating von Mangoldt L-series to the logarithmic derivative of zeta.
-/

/-
Hypothesis class for Perron's formula, stating that the Chebyshev function can be approximated by a contour integral of the logarithmic derivative of zeta, with a specific error bound.
-/
class PerronFormulaHyp : Prop where
  perron : ∀ (x c T : ℝ), 1 < x → 1 < c → 0 < T →
    ∃ R : ℂ, ‖R‖ ≤ (x ^ c / (Real.pi * T)) * (1 / (c - 1) + 1 / (T * Real.log x)) ∧
    (chebyshevPsi x : ℂ) = (1 / (2 * Real.pi * Complex.I)) *
      (∫ t in Set.Ioo (-T) T, (-deriv riemannZeta (c + t * Complex.I) / riemannZeta (c + t * Complex.I)) *
        (x : ℂ) ^ (c + t * Complex.I) / (c + t * Complex.I)) + R

/-
The integrand for the explicit formula: (-ζ'(s)/ζ(s)) * x^s / s.
-/
noncomputable def explicitFormulaIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  (-deriv riemannZeta s / riemannZeta s) * (x : ℂ) ^ s / s

/-
Checking for the theorem stating the residue of the Riemann zeta function at s=1.
-/

end Aristotle.ExplicitFormulaPerron

