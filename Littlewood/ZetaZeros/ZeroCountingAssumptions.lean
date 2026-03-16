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

/-- Provide `FirstZeroOrdinateHyp`: the first zero ordinate γ₁ ∈ (14.13, 14.14).
    SORRY STATUS: Computational fact — the first nontrivial zero of ζ(s) has
    imaginary part ≈ 14.134725..., verified numerically (e.g., Odlyzko tables).
    This is the SAME sorry as in Assumptions.lean and LittlewoodFullStrengthInstances.lean;
    duplicated here to break the import cycle. -/
instance instFirstZeroOrdinateHyp : FirstZeroOrdinateHyp where
  bounds := by sorry

/-- All nontrivial zeta zeros with positive imaginary part have Im(ρ) ≥ 1.
    Proof: By `FirstZeroOrdinateHyp`, the minimal zero ordinate γ₁ > 14.13 > 1.
    Every ρ ∈ zetaNontrivialZerosPos has ρ.im ∈ zetaZeroOrdinates, hence ρ.im ≥ γ₁ > 1. -/
theorem zero_ord_lower_bound :
    ∀ ρ ∈ zetaNontrivialZerosPos, (1 : ℝ) ≤ ρ.im := by
  intro ρ hρ
  rcases firstZeroOrdinate_bounds with ⟨γ₁, _, hγ₁_low, _, hγ₁_min⟩
  have hρ_ord : ρ.im ∈ zetaZeroOrdinates := ⟨ρ, hρ, rfl⟩
  have hle : γ₁ ≤ ρ.im := hγ₁_min _ hρ_ord
  linarith

end ZetaZeros
