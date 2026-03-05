# Aristotle Prompt (B3): `rs_block_analysis`

You have **no repository access**. Work only from this prompt.

## Environment
- Lean: `leanprover/lean4:v4.27.0-rc1`
- Mathlib: `fdddb3ea2c8c35de4455e033bc2a5df4d3a391ee`
- Required: no `axiom`, no `postulate`, no `sorry`, no `admit`

## Objective
Fill `rs_block_analysis`, the single atomic RS complete-block analytic payload.

## Target location in repo
`Littlewood/Aristotle/Standalone/RSCompleteBlockAsymptotic.lean:130`

## Exact local code context
```lean
import Mathlib
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.RSBlockDecomposition
import Littlewood.Aristotle.AbelSummation

namespace Aristotle.Standalone.RSCompleteBlockAsymptotic

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

private lemma abs_convex_le_max (a b α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |(1 - α) * a + α * b| ≤ max |a| |b| := by
  -- proof already present in local file (omitted in prompt context)

def RSCompleteBlockWithResidualHyp : Prop :=
  ∃ (A B R : ℝ), A > 0 ∧ B ≥ 0 ∧ R ≥ 0 ∧
    (∀ k : ℕ,
      |(∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
        - (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)| ≤ B) ∧
    (∀ N : ℕ,
      |∑ k ∈ Finset.range N,
        ((∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
          - (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))| ≤ R) ∧
    (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
      ∃ (α : ℝ), 0 ≤ α ∧ α ≤ 1 ∧
        |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
          - α * ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))| ≤ B)

-- TARGET
private theorem rs_block_analysis :
    ∃ (A : ℝ) (c : ℕ → ℝ) (C₂ : ℝ),
      A > 0 ∧
      (∀ k, 0 ≤ c k) ∧
      AntitoneOn c (Ici (1 : ℕ)) ∧
      (∀ k : ℕ,
        (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
          = (-1 : ℝ) ^ k * (A * Real.sqrt ((k : ℝ) + 1) + c k)) ∧
      C₂ ≥ 0 ∧
      (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
        ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
          |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
            - β * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                     ErrorTerm t)| ≤ C₂) := by
  sorry

private lemma c_le_max {c : ℕ → ℝ} (hc_anti : AntitoneOn c (Ici (1 : ℕ)))
    (k : ℕ) : c k ≤ max (c 0) (c 1) := by
  -- proof already present in local file (omitted in prompt context)

theorem rsCompleteBlockWithResidual_sorry :
    RSCompleteBlockWithResidualHyp := by
  obtain ⟨A, c, C₂, hA, hc_nn, hc_anti, hblock_eq, hC₂_nn, hinterp⟩ := rs_block_analysis
  -- proof already present in local file (omitted in prompt context)

 theorem perBlockSignedBoundHyp_of_blockAsymptotic
    (hRS : RSCompleteBlockWithResidualHyp) :
    Aristotle.RSBlockDecomposition.PerBlockSignedBoundHyp := by
  -- proof already present in local file (omitted in prompt context)
```

## Constraints
- Keep theorem statement unchanged.
- Output only replacement proof body for `rs_block_analysis`.
- No axioms, no helper sorries.
- Do not rely on any external file not present in this prompt context.

## Required output format
1. `STATUS: PROVED` or `STATUS: BLOCKED`
2. `PATCH:`
```lean
-- replacement for theorem body
```
3. `IMPORT_DELTA: none` (or list)
4. `WHY_IT_COMPILES:` short note
