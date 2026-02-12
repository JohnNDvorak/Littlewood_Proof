/-
Landau-Littlewood contradiction statements for the critical-path oscillation proof.

Both contradictions use the same mathematical machinery — Landau's oscillation
method (1905) applied to the smoothed (Cesàro-averaged) explicit formulas:
  1. Integrated explicit formula connecting ψ₁ (resp. π₁) to nontrivial zeros of ζ
  2. The resulting almost-periodic function f has M(|f|²) > 0 from ∞ critical-line zeros
  3. One-sided o₊(√x) bound forces f ≤ 0 eventually, hence M(f²) = 0
  4. Contradiction

They are derived from `Aristotle.DeepSorries.deep_mathematical_results` which
bundles Hardy's theorem and both Landau contradictions into a single atomic sorry.

REFERENCES:
  - Littlewood, "Sur la distribution des nombres premiers" (1914)
  - Landau, "Über einen Satz von Tschebyschef" (1905)
  - Montgomery-Vaughan, "Multiplicative Number Theory I", §15.1
  - Ingham, "Distribution of Prime Numbers", Chapter V, Theorem 20
-/

import Littlewood.Aristotle.DeepSorries

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.SmoothedExplicitFormula

open Filter Topology
open ZetaZeros

/-- Prime-counting error term used in the `π-li` Landau contradiction.
Transparent alias for `DeepSorries.piLiError` to ensure definitional equality. -/
abbrev piLiError := DeepSorries.piLiError

/-- Landau contradiction for `ψ`:
one-sided `o₊(√x)` control on `σ * (ψ(x)-x)` contradicts infinitely many
critical-line zeros. -/
theorem psi_signed_contradiction
    (h_inf : Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 })
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (h_side : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop, σ * (chebyshevPsi x - x) < c * Real.sqrt x) :
    False :=
  DeepSorries.deep_mathematical_results.2.1 h_inf σ hσ h_side

/-- Landau contradiction for `π-li`:
one-sided `o₊(√x/log x)` control on `σ * (π(x)-li(x))` contradicts infinitely
many critical-line zeros. -/
theorem pi_li_signed_contradiction
    (h_inf : Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 })
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (h_side : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop, σ * piLiError x < c * (Real.sqrt x / Real.log x)) :
    False :=
  DeepSorries.deep_mathematical_results.2.2 h_inf σ hσ h_side

end Aristotle.SmoothedExplicitFormula
