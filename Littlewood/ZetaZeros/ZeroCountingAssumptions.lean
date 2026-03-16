/-
Standalone sorry'd instances for zeta-zero assumptions WITHOUT importing
Assumptions.lean. This breaks the import cycle:

  Assumptions → CriticalAssumptions → ... → PerronExplicitFormulaProvider

allowing PerronExplicitFormulaProvider to import this file directly.

## Instance 1: ZeroCountingLowerBoundHyp
Sorry'd pending formalization of:
- N(T) ≥ T/(3π) log T for T ≥ T₀ (Riemann-von Mangoldt formula)

**BLOCKER ANALYSIS** (Agent4, 2026-03-15):
The goal is `∃ T0 : ℝ, ∀ T ≥ T0, T / (3 * π) * Real.log T ≤ N T`.
`N T` is `Set.ncard (zerosUpTo T)`, counting nontrivial zeros with 0 < Im ≤ T.

To close this requires the Riemann-von Mangoldt formula:
  N(T) = (T/(2π)) log(T/(2π)) - T/(2π) + O(log T)
which gives N(T) ≥ T/(3π) log T for T ≥ T₀.

The RvM formula proof requires the argument principle applied to ζ'/ζ on a
rectangular contour. Mathlib has NO `argument_principle`, `winding_number`,
or `contour_integral_of_meromorphic` lemmas. The zero-counting function `N`
is defined set-theoretically (ncard of zeros), not analytically.

**CLOSURE ROUTES**:
  (A) Formalize the argument principle in Mathlib (multi-month effort)
  (B) Accept as a deep analytic sorry — the weakest assumption in the chain
  (C) Provide `ZeroCountingRvmExplicitHyp` instance here (but that has
      the same sorry content, just moved)

VERDICT: IRREDUCIBLE sorry. No Mathlib path exists without the argument principle.

## Instance 2: zero_ord_lower_bound
All nontrivial zeta zeros with positive imaginary part have Im(ρ) ≥ 1.
This is a consequence of the classical zero-free region: the de la
Vallée-Poussin region {s : Re(s) > 1 - c/log(|Im(s)|+2)} ensures no
zeros with 0 < Im ≤ 1 (in fact the first zero has Im ≈ 14.134...).
This is logically MUCH weaker than the RvM formula.

Used by: simultaneous_dirichlet_on_interval in PerronExplicitFormulaProvider.lean
to satisfy the |γ_k| ≥ 1 hypothesis of the Dirichlet approximation theorem.

VERDICT: IRREDUCIBLE sorry. Same barrier as RvM (no argument principle / zero-free
region formalization in Mathlib), though logically simpler.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.ZetaZeros.ZeroCountingFunction

noncomputable section

namespace ZetaZeros

/-- N(T) grows at least as fast as T log T / (3π).
    This is a consequence of the Riemann-von Mangoldt formula. -/
instance zeroCountingLowerBound_from_rvm : ZeroCountingLowerBoundHyp where
  lower_bound := by sorry

/-- All nontrivial zeta zeros with positive imaginary part have Im(ρ) ≥ 1.
    This follows from the classical zero-free region (de la Vallée-Poussin 1896).
    The first nontrivial zero has imaginary part ≈ 14.134..., so the bound 1 is
    extremely conservative. -/
theorem zero_ord_lower_bound :
    ∀ ρ ∈ zetaNontrivialZerosPos, (1 : ℝ) ≤ ρ.im := by
  sorry

end ZetaZeros
