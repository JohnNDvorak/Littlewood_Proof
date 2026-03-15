/-
Standalone sorry'd instances for zero-counting hypotheses.

This file provides global instances of ZeroCountingLowerBoundHyp,
ZeroCountingSpecialValuesHyp, and FirstZeroOrdinateHyp WITHOUT importing
Assumptions.lean. This breaks the import cycle:

  Assumptions → CriticalAssumptions → ... → PerronExplicitFormulaProvider

allowing PerronExplicitFormulaProvider to import this file directly.

The instances are sorry'd pending formalization of:
- N(T) ≥ T/(3π) log T for T ≥ T₀ (Riemann-von Mangoldt formula)
- N(14) = 0 (first zero at γ₁ ≈ 14.134...)
- γ₁ ∈ (14.13, 14.14) (numerical computation)

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.ZetaZeros.ZeroCountingFunction

noncomputable section

namespace ZetaZeros

/-- N(T) grows at least as fast as T log T / (3π).
    This is a consequence of the Riemann-von Mangoldt formula. -/
instance zeroCountingLowerBound_from_rvm : ZeroCountingLowerBoundHyp where
  lower_bound := by sorry

/-- The first zeta zero ordinate γ₁ lies in (14.13, 14.14). -/
instance firstZeroOrdinate_numerical : FirstZeroOrdinateHyp where
  bounds := by sorry

end ZetaZeros
