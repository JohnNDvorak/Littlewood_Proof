/- 
Atomic sorries for Landau's oscillation argument.

Each theorem says: if ψ(x)-x (resp. π(x)-li(x)) satisfies a one-sided
o(√x) bound, then the set of critical-line zeros of ζ is finite —
contradicting HardyCriticalLineZerosHyp.

MATHEMATICAL CONTENT:
  Case A (∃ off-line zero with Re > 1/2):
    One-sided bound ψ ≤ x + √x gives ζ ≠ 0 for Re(s) > 1/2 via
    Montgomery-Vaughan Theorem 15.2. Contradicts the off-line zero.
  Case B (RH — all zeros at Re = 1/2):
    Smoothed explicit formula: G(x) = ∫₂ˣ (ψ-t)dt = -x^{3/2}·f(log x) + O(x)
    where f is absolutely convergent almost-periodic (since ∑1/|ρ(ρ+1)|<∞ under RH).
    Hardy zeros give M(|f|²) > 0, so f achieves bounded-away-from-zero values.
    But ψ-x = o(√x) gives G = o(x^{3/2}), forcing f→0. Contradiction.

REFERENCES:
  - Montgomery-Vaughan, "Multiplicative Number Theory I", §15.1, Theorems 15.2-15.3
  - Ingham, "Distribution of Prime Numbers", Chapter V, Theorem 20
  - Littlewood, "Sur la distribution des nombres premiers" (1914)

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.ZetaZeros.ZeroCountingFunction
import Littlewood.Basic.ChebyshevFunctions
import Littlewood.Basic.LogarithmicIntegral
import Littlewood.Aristotle.SmoothedExplicitFormula

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.LandauContradiction

open Filter Topology
open ZetaZeros

/-- One-sided upper o(√x) bound on ψ-x contradicts infinitely many
critical-line zeros. See module docstring for proof outline. -/
theorem psi_upper_contradicts_critical_zeros
    (h_inf : Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 })
    (h_upper : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop, chebyshevPsi x - x < c * Real.sqrt x) :
    False := by
  have h_side : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop, (1 : ℝ) * (chebyshevPsi x - x) < c * Real.sqrt x := by
    intro c hc
    simpa using h_upper c hc
  exact Aristotle.SmoothedExplicitFormula.psi_signed_contradiction
    h_inf 1 (Or.inl rfl) h_side

/-- One-sided lower o(√x) bound on ψ-x contradicts infinitely many
critical-line zeros. -/
theorem psi_lower_contradicts_critical_zeros
    (h_inf : Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 })
    (h_lower : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop, chebyshevPsi x - x > -(c * Real.sqrt x)) :
    False := by
  have h_side : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop, (-1 : ℝ) * (chebyshevPsi x - x) < c * Real.sqrt x := by
    intro c hc
    refine (h_lower c hc).mono ?_
    intro x hx
    have hneg : -(chebyshevPsi x - x) < c * Real.sqrt x := by linarith
    simpa using hneg
  exact Aristotle.SmoothedExplicitFormula.psi_signed_contradiction
    h_inf (-1) (Or.inr rfl) h_side

/-- One-sided upper o(√x/log x) bound on π-li contradicts infinitely many
critical-line zeros. -/
theorem pi_li_upper_contradicts_critical_zeros
    (h_inf : Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 })
    (h_upper : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop,
        (Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x <
        c * (Real.sqrt x / Real.log x)) :
    False := by
  have h_side : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop,
        (1 : ℝ) * Aristotle.SmoothedExplicitFormula.piLiError x <
        c * (Real.sqrt x / Real.log x) := by
    intro c hc
    simpa using h_upper c hc
  exact Aristotle.SmoothedExplicitFormula.pi_li_signed_contradiction
    h_inf 1 (Or.inl rfl) h_side

/-- One-sided lower o(√x/log x) bound on π-li contradicts infinitely many
critical-line zeros. -/
theorem pi_li_lower_contradicts_critical_zeros
    (h_inf : Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 })
    (h_lower : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop,
        (Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x >
        -(c * (Real.sqrt x / Real.log x))) :
    False := by
  have h_side : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop,
        (-1 : ℝ) * Aristotle.SmoothedExplicitFormula.piLiError x <
        c * (Real.sqrt x / Real.log x) := by
    intro c hc
    refine (h_lower c hc).mono ?_
    intro x hx
    have hx' :
        Aristotle.SmoothedExplicitFormula.piLiError x >
          -(c * (Real.sqrt x / Real.log x)) := by
      simpa [Aristotle.SmoothedExplicitFormula.piLiError,
            Aristotle.DeepSorries.piLiError] using hx
    have hneg :
        -(Aristotle.SmoothedExplicitFormula.piLiError x) <
          c * (Real.sqrt x / Real.log x) := by
      linarith [hx']
    simpa using hneg
  exact Aristotle.SmoothedExplicitFormula.pi_li_signed_contradiction
    h_inf (-1) (Or.inr rfl) h_side

end Aristotle.LandauContradiction
