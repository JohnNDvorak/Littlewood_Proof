/-
Standalone sorry'd instance for ZeroCountingLowerBoundHyp WITHOUT importing
Assumptions.lean. This breaks the import cycle:

  Assumptions → CriticalAssumptions → ... → PerronExplicitFormulaProvider

allowing PerronExplicitFormulaProvider to import this file directly.

The instance is sorry'd pending formalization of:
- N(T) ≥ T/(3π) log T for T ≥ T₀ (Riemann-von Mangoldt formula)

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.ZetaZeros.ZeroCountingFunction

noncomputable section

namespace ZetaZeros

/-- N(T) grows at least as fast as T log T / (3π).
    This is a consequence of the Riemann-von Mangoldt formula. -/
instance zeroCountingLowerBound_from_rvm : ZeroCountingLowerBoundHyp where
  lower_bound := by sorry

end ZetaZeros
