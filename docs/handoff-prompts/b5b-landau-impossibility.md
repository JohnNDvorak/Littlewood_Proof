# Handoff Prompt: Landau-Ingham O(√x) Impossibility (B5b Atomic Sorry)

## Task

Prove the Landau-Ingham impossibility theorem in Lean 4 / Mathlib: under RH,
ψ(x) - x cannot be one-sidedly bounded by C₀√x for all large x.

This is the **sole remaining sorry** (Blocker B5b) on the ψ oscillation chain.

## Target File

**Replace the sorry** at line 110 of:
```
Littlewood/Aristotle/Standalone/PsiZeroSumOscillationFromIngham.lean
```

## Exact Signature (already in the file)

```lean
private theorem landau_psi_bounded_impossible
    (hRH : ZetaZeros.RiemannHypothesis)
    (σ : ℝ) (_hσ : σ = 1 ∨ σ = -1)
    (C₀ X₀ : ℝ)
    (h_bound : ∀ x, x ≥ X₀ →
      σ * (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x) ≤
        C₀ * Real.sqrt x) :
    False := sorry
```

**Hypothesis**: Under RH, if σ·(ψ(x)-x) ≤ C₀√x for ALL x ≥ X₀, derive False.
- For σ = +1: ψ(x)-x ≤ C₀√x always → contradiction
- For σ = -1: ψ(x)-x ≥ -C₀√x always → contradiction

## CRITICAL: Circularity Constraint

**DO NOT** use any of the following, as they transitively depend on THIS sorry:
- `LandauMellinContradiction.landau_psi_contradiction_proof` (depends on combined_atoms → B5b)
- `SmoothedExplicitFormula.psi_signed_contradiction`
- `DeepSorries.deep_mathematical_results`
- `CombinedAtomsFromDeepBlockers` (any of its bundled results)
- `NonNegDirichletIntegral` (forwards to SmoothedExplicitFormula)

The proof **must be self-contained** — it cannot depend on anything that flows through
`DeepBlockersResolved.lean`, because that file imports this file.

**Safe to use**: Mathlib, `DirichletPhaseAlignment.lean` infrastructure, RH hypothesis.

## Mathematical Content: Landau-Ingham Mellin Argument (1905/1932)

### The Direct Proof (Landau 1905, Ingham 1932 Ch. V)

Assume for contradiction: ψ(x) - x ≤ C₀√x for all x ≥ X₀ (the σ=+1 case).

**Step 1 — Mellin/Stieltjes convergence**: Define
```
F(s) = s · ∫_{X₀}^∞ (C₀√t - (ψ(t) - t)) · t^{-s-1} dt
```
The integrand is ≥ 0 (by assumption) and O(t^{1/2-Re(s)}) for large t.
So F(s) converges absolutely for Re(s) > 1/2.

**Step 2 — Connection to ζ'/ζ**: For Re(s) > 1, we have the Perron/Stieltjes identity:
```
-ζ'(s)/ζ(s) = s · ∫_1^∞ ψ(t) · t^{-s-1} dt
```
Rearranging with the assumed bound:
```
F(s) = s·C₀/(s - 1/2) + s/(s-1) + ζ'(s)/ζ(s) + (bounded analytic terms)
```
This identity, initially valid for Re(s) > 1, extends by analytic continuation
to Re(s) > 1/2 (since F converges there).

**Step 3 — Contradiction**: Under RH, ζ has infinitely many zeros at ρ = 1/2 + iγ.
At each such zero, ζ'/ζ has a pole (with residue equal to the multiplicity).
But the formula in Step 2 says ζ'(s)/ζ(s) = F(s) - (analytic terms), and F(s)
is analytic for Re(s) > 1/2. The "analytic terms" (s·C₀/(s-1/2) and s/(s-1))
have at most finitely many poles. So ζ'/ζ would have at most finitely many poles
in Re(s) > 1/2 — contradicting infinitely many RH zeros.

The σ = -1 case is symmetric (replace ψ-x with x-ψ).

### Key Sub-lemmas Needed

1. **Nontrivial zero existence under RH**: ∃ infinitely many ρ ∈ CriticalZeros
   with ρ.im ≠ 0. (Follows from RH + Hardy's theorem; infrastructure may exist
   in `HardyInfiniteZerosV2.lean` or `ZeroCountingFunction.lean`.)

2. **ζ'/ζ has poles at zeros**: If ζ(ρ) = 0 with multiplicity m, then ζ'/ζ
   has a pole of order 1 at ρ with residue -m. (Partially in
   `ZetaLogDerivNonAnalytic.lean` — proved sorry-free.)

3. **Mellin integral convergence**: Under the O(√x) bound, the integral
   ∫ (C₀√t - (ψ-t)) · t^{-s-1} dt converges for Re(s) > 1/2.
   (Infrastructure: `MellinIntegralFormulas.lean` has `mellin_rpow_alpha` sorry-free.)

4. **Perron/Stieltjes identity**: -ζ'(s)/ζ(s) = s · ∫ ψ(t) t^{-s-1} dt for Re(s) > 1.
   (Related: `PsiIntegralRepresentation.lean` has some infrastructure.)

5. **Analytic continuation argument**: The convergence of F(s) for Re(s) > 1/2
   forces ζ'/ζ to be meromorphic with known poles only — contradicting RH zeros.

## Available Infrastructure (safe to use)

### In `DirichletPhaseAlignment.lean`:
- `chebyshevPsi : ℝ → ℝ` — Chebyshev ψ function
- `CriticalZeros : Set ℂ` — nontrivial zeros of ζ
- `ZerosBelow T : Finset ℂ` — finite set of zeros with |Im(ρ)| ≤ T
- `RiemannHypothesis` — all critical zeros have Re = 1/2

### In `ZetaLogDerivNonAnalytic.lean` (sorry-free):
- Proved: ζ'/ζ has poles at nontrivial zeros of ζ

### In `MellinIntegralFormulas.lean` (sorry-free):
- `mellin_rpow_alpha` — Mellin transform of t^α converges in appropriate half-plane

### In `PsiIntegralRepresentation.lean`:
- Infrastructure relating ψ to Dirichlet series integrals

### In Mathlib:
- `differentiableAt_riemannZeta (hs : s ≠ 1)` — ζ differentiable away from s=1
- `Complex.exp`, `Complex.log`, contour integral basics
- Mellin transform definitions (`MeasureTheory.mellin`)

## Recommended Strategy

### Option A: Direct Mellin proof (PREFERRED but hard)
Formalize Steps 1-3 above. Requires:
- Convergence of the Mellin integral (doable with existing Mellin infrastructure)
- Connection to ζ'/ζ (needs Perron/Stieltjes identity)
- Analytic continuation + pole counting (needs Lean complex analysis)

Estimated: 200-400 lines.

### Option B: Factor into sub-sorry's
```lean
-- Sub-sorry 1: Mellin convergence
private theorem mellin_convergence (hRH : RH) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (C₀ X₀ : ℝ) (h : ∀ x ≥ X₀, σ*(ψ(x)-x) ≤ C₀√x) :
    ∃ F : ℂ → ℂ, AnalyticOn ℂ F {s | s.re > 1/2} ∧
      (∀ s, s.re > 1, F s = ...) := sorry

-- Sub-sorry 2: Pole contradiction
private theorem pole_contradiction (hRH : RH)
    (F : ℂ → ℂ) (hF : AnalyticOn ℂ F {s | s.re > 1/2})
    (h_id : ∀ s, s.re > 1, ζ'(s)/ζ(s) = F(s) + ...) :
    False := sorry  -- infinitely many poles of ζ'/ζ, but F is analytic
```

### Option C: Constructive approach (ALTERNATIVE)
Instead of Mellin transforms, use the explicit formula + phase alignment:
1. From B5a (ExplicitFormulaPsiGeneralHyp, available as typeclass):
   ψ(x) ≈ x - ∑ Re(x^ρ/ρ) with error O(√x(logT)²/√T + (log x)²)
2. Under RH with O(√x) bound: |∑ Re(x^ρ/ρ)| ≤ (C₀+1)√x + O((log x)²)
3. But phase alignment can make |∑ Re(x^ρ/ρ)| arbitrarily large (from ∑1/|ρ| → ∞)
4. Contradiction.

**CAVEAT for Option C**: The current phase alignment infrastructure
(`bound_real_part_of_sum_shifted`) aligns all phases to a SINGLE target w.
This captures only the convergent sum ∑Re(w/ρ). The divergent component
∑Re(I/ρ) requires per-zero targets, which needs NEW infrastructure:

```lean
-- NEEDED: Phase alignment with per-zero targets
lemma exists_large_x_phases_aligned_per_zero
    (S : Finset ℂ) (targets : ℂ → ℂ) (hT : ∀ ρ ∈ S, ‖targets ρ‖ = 1)
    (ε : ℝ) (hε : ε > 0) (X : ℝ) :
    ∃ x > X, ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - targets ρ‖ < ε
```

This follows from Kronecker's theorem / multidimensional Dirichlet approximation
but is NOT in the current codebase.

## Build Commands

```bash
lake build Littlewood.Aristotle.Standalone.PsiZeroSumOscillationFromIngham
lake build Littlewood.Aristotle.Standalone.DeepBlockersResolved
lake build 2>&1 | grep "declaration uses 'sorry'" | sort -u
```

## File Context

```lean
import Littlewood.Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
import Littlewood.Aristotle.DirichletPhaseAlignment

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.PsiZeroSumOscillationFromIngham

open Filter Complex
open GrowthDomination
open Aristotle.DirichletPhaseAlignment (ZerosBelow CriticalZeros)
open Aristotle.Standalone.RHPsiWitnessFromZeroSum (psiMainTerm)
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open ZetaZeros
```

## Constraints

- Do NOT modify files outside `PsiZeroSumOscillationFromIngham.lean`
- Do NOT add new imports that would create circular dependencies
  (especially: do NOT import from `DeepSorries`, `SmoothedExplicitFormula`,
  `LandauMellinContradiction`, or `CombinedAtomsFromDeepBlockers`)
- The proved wirings (`landau_ingham_unbounded_above`, `_below`,
  `psiZeroSumOscillation_proved`) MUST stay as-is — they depend only on
  `landau_psi_bounded_impossible`
- Build must pass: `lake build Littlewood.Aristotle.Standalone.PsiZeroSumOscillationFromIngham`

## References

- Landau, E. (1905). "Über einen Satz von Tschebyschef." *Math. Ann.* 61.
- Ingham, A. E. (1932). *The Distribution of Prime Numbers*, Chapter V.
- Montgomery & Vaughan (2007). *Multiplicative Number Theory I*, §15.2.
- Davenport, H. (2000). *Multiplicative Number Theory*, 3rd ed., §17.
