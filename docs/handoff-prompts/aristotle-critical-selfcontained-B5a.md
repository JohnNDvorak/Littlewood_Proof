# Aristotle Prompt (B5a): `shifted_contours_components`

You have **no repository access**. Work only from this prompt.

## Environment
- Lean: `leanprover/lean4:v4.27.0-rc1`
- Mathlib: `fdddb3ea2c8c35de4455e033bc2a5df4d3a391ee`
- Required: no `axiom`, no `postulate`, no `sorry`, no `admit`

## Objective
Fill `shifted_contours_components`, the single B5a component-package theorem.
The final `shifted_contours_bound` is already proved from this package via
`shifted_contours_bound_of_components`.

## Target location in repo
`Littlewood/Aristotle/Standalone/ExplicitFormulaPsiSkeleton.lean:61`

## Exact local code context
```lean
import Littlewood.Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aDefs
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aContourBounds

namespace Aristotle.Standalone.ExplicitFormulaPsiSkeleton

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.ExplicitFormulaPsiB5aContourBounds
open ZetaZeros

-- TARGET
private theorem shifted_contours_components :
    ∃ perronIntegralRe contourRemainderRe : ℝ → ℝ → ℝ,
      (∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
          Cₚ * (Real.log x) ^ 2)
      ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T)
      ∧
      (∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |contourRemainderRe x T| ≤
          Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) := by
  sorry

 theorem shifted_contours_bound :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  rcases shifted_contours_components with
    ⟨perronIntegralRe, contourRemainderRe, hPerronRaw, hResidue, hContour⟩
  exact shifted_contours_bound_of_components
    perronIntegralRe contourRemainderRe hPerronRaw hResidue hContour

 theorem explicitFormulaPsiGeneral_proved : ExplicitFormulaPsiGeneralHyp where
  proof := by
    obtain ⟨C₂, _, hBound⟩ := shifted_contours_bound
    exact ⟨C₂, fun x T hx hT => by
      have h_eq : Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re) =
          shiftedRemainderRe x T := by
        unfold shiftedRemainderRe zeroSumRe; ring
      rw [h_eq]; exact hBound x T hx hT⟩
```

## Required interface this theorem must satisfy downstream
```lean
namespace Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries

class ExplicitFormulaPsiGeneralHyp : Prop where
  proof : ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
    |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
      (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
    C * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)
```

## Constraints
- Keep theorem statements unchanged.
- Output only replacement proof body for `shifted_contours_components`.
- Do not modify `shifted_contours_bound` or `explicitFormulaPsiGeneral_proved`.
- No axioms, no helper sorries.

## Required output format
1. `STATUS: PROVED` or `STATUS: BLOCKED`
2. `PATCH:`
```lean
-- replacement for theorem body
```
3. `IMPORT_DELTA: none` (or list)
4. `WHY_IT_COMPILES:` short note
