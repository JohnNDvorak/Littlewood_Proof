# Self-Contained Prompt C: Close `exists_large_x_phases_aligned_to_target`

You are working in this repo:
`/Users/john.n.dvorak/Documents/Git/Littlewood_Proof`

## Goal
Prove exactly this theorem (do not change signature):

```lean
lemma exists_large_x_phases_aligned_to_target
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ.re = 1/2)
    (hS_pos : ∀ ρ ∈ S, 0 < ρ.im)
    (w : ℂ) (hw : ‖w‖ = 1) (ε : ℝ) (hε : ε > 0) (X : ℝ)
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∃ x > X, ∀ ρ ∈ S, ‖(x : ℂ)^(I * ρ.im) - w‖ < ε := by
  sorry
```

Path: `Littlewood/Aristotle/DirichletPhaseAlignment.lean`

## Hard Constraints
- No axioms.
- No `sorry`, `admit`, placeholders.
- Keep theorem statement unchanged.
- Lean/mathlib compatibility unchanged.

## Existing Local Infrastructure in Same File
Already proved here:
- `simultaneous_dirichlet_approximation`
- `exists_large_x_phases_aligned`
- `exists_large_x_phases_aligned_finset` (homogeneous target)
- `bound_real_part_of_sum_aligned`
- `bound_real_part_of_sum_shifted`
- `bound_real_part_of_sum_shifted_upper`

## Required Approach
1. Convert target phase `w` with `‖w‖=1` into argument/angle formulation.
2. Build inhomogeneous simultaneous approximation for `Real.log x * ρ.im` on finite set `S`.
3. Reconstruct the complex phase closeness objective `‖x^(iγ)-w‖<ε`.
4. Preserve strict `x > X` and strict `< ε` in final conclusion.
5. Do not weaken theorem statement.

## If You Detect a Logical Obstruction
If theorem is not derivable from given hypotheses in this repo without extra assumptions:
1. Do not add assumptions or axioms.
2. Provide a formal blocker report and a mathematically correct replacement theorem that is strongest unconditional version you can prove.
3. Keep existing theorem untouched if unresolved; add proved helper theorem(s) with full integration notes.

## Acceptance Criteria
Primary success:

```bash
cd /Users/john.n.dvorak/Documents/Git/Littlewood_Proof
lake build Littlewood.Aristotle.DirichletPhaseAlignment
```

Axiom check:

```bash
cat > /tmp/check_axioms_phase_target.lean <<'LEAN'
import Littlewood.Aristotle.DirichletPhaseAlignment
#print axioms Aristotle.DirichletPhaseAlignment.exists_large_x_phases_aligned_to_target
LEAN
lake env lean /tmp/check_axioms_phase_target.lean
```

## Deliverable
Return:
- patch summary,
- key proof idea,
- build status,
- axiom check result,
- blocker report only if unresolved.
