/-
Standalone instances for zeta-zero assumptions WITHOUT importing
Assumptions.lean. This breaks the import cycle:

  Assumptions → CriticalAssumptions → ... → PerronExplicitFormulaProvider

allowing PerronExplicitFormulaProvider to import this file directly.

## Instance 1: ZeroCountingLowerBoundHyp
NOW PROVIDED via the Riemann-von Mangoldt infrastructure chain:
  `RiemannVonMangoldtReal.rvm_explicit_hyp` provides `ZeroCountingRvmExplicitHyp`
  Instance chain in ZeroCountingFunction.lean:
    `ZeroCountingRvmExplicitHyp` → `ZeroCountingAsymptoticHyp`
      → `ZeroCountingMainTermHyp` → `ZeroCountingLowerBoundHyp`

The sorry is now localized to `riemann_von_mangoldt_explicit` in
RiemannVonMangoldtReal.lean, which decomposes into:
  (a) Argument principle for rectangles (RectArgumentPrinciple.lean)
  (b) Stirling approximation for Gamma integrals
  (c) Standard zeta bounds on vertical lines

## Instance 2: zero_ord_lower_bound
All nontrivial zeta zeros with positive imaginary part have Im(ρ) ≥ 1.
This follows from the classical zero-free region (de la Vallée-Poussin 1896).
The first nontrivial zero has imaginary part ≈ 14.134..., so the bound 1 is
extremely conservative.

Used by: simultaneous_dirichlet_on_interval in PerronExplicitFormulaProvider.lean
to satisfy the |γ_k| ≥ 1 hypothesis of the Dirichlet approximation theorem.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.ZetaZeros.RiemannVonMangoldtReal

noncomputable section

namespace ZetaZeros

-- ZeroCountingLowerBoundHyp is now automatically available via the instance chain:
-- rvm_explicit_hyp → instZeroCountingAsymptoticHyp → zeroCountingMainTermHyp_of_asymptotic
--   → zeroCountingLowerBoundHyp_of_mainTerm
-- No explicit instance needed here.

-- Verify the instance resolves:
#check (inferInstance : ZeroCountingLowerBoundHyp)

/-- All nontrivial zeta zeros with positive imaginary part have Im(ρ) ≥ 1.
    This follows from the classical zero-free region (de la Vallée-Poussin 1896).
    The first nontrivial zero has imaginary part ≈ 14.134..., so the bound 1 is
    extremely conservative. -/
theorem zero_ord_lower_bound :
    ∀ ρ ∈ zetaNontrivialZerosPos, (1 : ℝ) ≤ ρ.im := by
  sorry

end ZetaZeros
