# Aristotle Prompt (B1): `afe_signed_integral_gap_bound`

You have **no repository access**. Work only from this prompt.

## Environment
- Lean: `leanprover/lean4:v4.27.0-rc1`
- Mathlib: `fdddb3ea2c8c35de4455e033bc2a5df4d3a391ee`
- Required: no `axiom`, no `postulate`, no `sorry`, no `admit`

## Objective
Fill the single `sorry` in theorem `afe_signed_integral_gap_bound`.

## Target location in repo
`Littlewood/Aristotle/Standalone/HardyMeanSquareAsymptoticFromZetaMoment.lean:210`

## Exact target theorem
```lean
private lemma afe_signed_integral_gap_bound :
    (fun T => ∫ t in (1:ℝ)..T, afeGapIntegrand t)
    =O[atTop] (fun T => T) := by
  sorry
```

## Local file context (verbatim signatures)
```lean
import Littlewood.Aristotle.ZetaMeanSquare
import Littlewood.Aristotle.HardyMeanSquareAsymptoticLeaf
import Littlewood.Bridge.HardyZTransfer
import Littlewood.Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp
import Littlewood.Aristotle.MeanSquare

namespace Aristotle.Standalone.HardyMeanSquareAsymptoticFromZetaMoment

open Filter Asymptotics MeasureTheory Set Real

private lemma integral_log_exact (T : ℝ) (hT : 1 ≤ T) :
    ∫ t in (1:ℝ)..T, Real.log t = T * Real.log T - T + 1 := by
  aesop

private lemma partial_zeta_mean_square_half_coeff :
    (fun T => (∫ t in (1:ℝ)..T,
        Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1/2 + Complex.I * t)))
      - 2⁻¹ * T * Real.log T)
    =O[atTop] (fun T => T) := by
  -- proof already present in local file (omitted in prompt context)

-- TARGET
private lemma afe_signed_integral_gap_bound :
    (fun T => ∫ t in (1:ℝ)..T, afeGapIntegrand t)
    =O[atTop] (fun T => T) := by
  sorry

private theorem afe_mean_square_bridge :
    (fun T => (∫ t in (1:ℝ)..T, ‖riemannZeta (↑(1/2 : ℝ) + Complex.I * ↑t)‖^2) -
      2 * (∫ t in (1:ℝ)..T, Complex.normSq
        (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1/2 + Complex.I * t))))
    =O[atTop] (fun T => T) := by
  -- proof already present in local file (omitted in prompt context)
```

## Additional available context from imports
You may use standard lemmas from:
- `Littlewood.Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp`
- `Littlewood.Aristotle.ZetaMeanSquare`
- `Littlewood.Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra`
- Mathlib `Asymptotics`, `IntervalIntegral`, `norm_integral_le_integral_norm`, comparison lemmas, Hölder/Cauchy-Schwarz if available.

The intended math is the signed mean-value AFE remainder bound:
`∫_1^T (|ζ|² - 2|S_N|²) dt = O(T)`.

## Constraints
- Keep theorem statement unchanged.
- Provide only a replacement proof term for this theorem.
- Do not introduce new axioms or placeholder assumptions.

## Required output format
1. `STATUS: PROVED` or `STATUS: BLOCKED`
2. `PATCH:`
```lean
-- replacement for theorem body
```
3. `IMPORT_DELTA: none` (or list)
4. `WHY_IT_COMPILES:` short note
