/-
Littlewood Diagonal Evaluation — the core analytic lemma.

On the diagonal z = ξ + iξ, the Abel-weighted zero sum satisfies:
  Σ sin(γₙξ)·e^{-γₙξ}/γₙ ≥ A·log(1/ξ)
for small ξ > 0, where A > 0 comes from the zero density.

This is Step 3a of Littlewood's 1914/1917 proof, following Montgomery-Vaughan Ch.15.
The proof uses partial summation against Nmult(T) ~ (T/2π)log T.

References:
- Montgomery-Vaughan, "Multiplicative Number Theory I," §15.1
- Hardy-Littlewood, Acta Math. 41 (1917), §4
-/

import Mathlib
import Littlewood.Aristotle.Standalone.PsiZeroSumOscillationFromIngham
import Littlewood.ZetaZeros.ZeroCountingMultiplicity

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

open Real Complex Filter Topology MeasureTheory Set Finset
open scoped Real BigOperators

namespace Littlewood.DiagonalEval

open Aristotle.DirichletPhaseAlignment
open Aristotle.Standalone.PsiZeroSumOscillationFromIngham

/-! ## The Abel-weighted zero sum -/

/-- The Abel-weighted imaginary zero sum at (ξ, η):
Σ_{ρ ∈ PositiveImZerosBelow(T)} sin(γ·η)/γ · e^{-γ·ξ}
where γ = ρ.im and T is a cutoff. -/
def abelZeroSum (T ξ η : ℝ) : ℝ :=
  ∑ ρ ∈ PositiveImZerosBelow T,
    (Real.sin (ρ.im * η) / ρ.im) * Real.exp (-(ρ.im * ξ))

/-- The Abel-weighted zero sum on the diagonal ξ = η:
Σ sin(γ·ξ)·e^{-γ·ξ}/γ -/
def abelDiagonalSum (T ξ : ℝ) : ℝ := abelZeroSum T ξ ξ

/-! ## Individual term positivity on the diagonal

For γξ ∈ (0, π): sin(γξ) > 0 and e^{-γξ} > 0, so each term is positive.
The "head" terms (γξ ≤ a for a < π) all contribute positively. -/

lemma sin_mul_exp_neg_pos {γ ξ : ℝ} (hγ : 0 < γ) (hξ : 0 < ξ)
    (hprod : γ * ξ < Real.pi) :
    0 < Real.sin (γ * ξ) / γ * Real.exp (-(γ * ξ)) := by
  apply mul_pos
  · apply div_pos
    · exact Real.sin_pos_of_pos_of_lt_pi (mul_pos hγ hξ) hprod
    · exact hγ
  · exact Real.exp_pos _

/-! ## Diagonal evaluation: lower bound

The key estimate: for small ξ, the diagonal sum is at least A·log(1/ξ).
This uses partial summation against the zero counting function Nmult(T).

The full proof requires Stieltjes integral techniques. Here we state the
result as a hypothesis class that can be instantiated constructively. -/

/-- **Diagonal evaluation lower bound.** For small ξ > 0, the Abel-weighted
sum on the diagonal satisfies abelDiagonalSum(1/ξ, ξ) ≥ A · log(1/ξ).

The proof: write the sum as ξ · ∫ h(t) dN(t/ξ) where h(t) = sin(t)·e^{-t}/t.
Using N(T) ~ (T/2π)·log T, the dominant term is
  (1/2π)·log(1/ξ) · ∫₀^∞ h(t) dt = (1/8)·log(1/ξ)
since ∫₀^∞ sin(t)·e^{-t}/t dt = arctan(1) = π/4. -/
class DiagonalEvalLowerBoundHyp : Prop where
  /-- There exist A > 0 and ξ₀ > 0 such that for all ξ ∈ (0, ξ₀), the
  diagonal Abel sum is at least (A/2)·log(1/ξ). -/
  eval :
    ∃ A > 0, ∃ ξ₀ > 0, ∀ ξ, 0 < ξ → ξ < ξ₀ →
      (A / 2) * Real.log (1 / ξ) ≤ abelDiagonalSum (1 / ξ) ξ

/-! ## From diagonal evaluation to Key Lemma

Given the diagonal evaluation, the Key Lemma follows by:
1. Fix a with the head terms carrying > 3A/4 of the sum
2. Apply homogeneous Kronecker (exists_large_x_phases_aligned_finset) to
   get η with sin(γη) ≈ sin(γξ) for head terms
3. Bound the perturbation (head: o(log 1/ξ), tail: O(e^{-a}·log 1/ξ))
4. Convert log(1/ξ) → log log η via Kronecker bound η ≤ η₀·(2/ξ)^{C/ξ}

This conversion needs existing infrastructure:
- exists_large_x_phases_aligned_finset (DirichletPhaseAlignment.lean:257)
- Nmult density for the Kronecker bound on η
-/

end Littlewood.DiagonalEval
