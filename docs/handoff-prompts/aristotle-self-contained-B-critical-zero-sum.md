# Self-Contained Prompt B: Close `critical_zero_sum_diverges`

You are working in this repo:
`/Users/john.n.dvorak/Documents/Git/Littlewood_Proof`

## Goal
Prove exactly this theorem (do not change signature):

```lean
private theorem critical_zero_sum_diverges (hRH : ZetaZeros.RiemannHypothesis) :
    ∀ M : ℝ, ∃ T : ℝ, T ≥ 2 ∧
      M ≤ ∑ ρ ∈ PositiveImZerosBelow T, ρ.im / (1/4 + ρ.im ^ 2) := by
  sorry
```

Path: `Littlewood/Aristotle/Standalone/PsiZeroSumOscillationFromIngham.lean`

## Hard Constraints
- No axioms.
- No `sorry`, `admit`, placeholders.
- Keep theorem statement unchanged.
- Do **not** use assumption-bundle files that inject `sorry`-backed instances (e.g. avoid importing `Littlewood.Assumptions`).
- Lean/mathlib compatibility unchanged.

## Local Context Already Available in Target File
Key lemmas already present in that file:
- `gamma_div_bound`
- `positiveImZerosBelow_re_half`
- `re_I_div_eq`
- `sum_re_I_div_eq`
- `re_neg_I_div_eq`
- `sum_re_neg_I_div_eq`

## Required Approach
1. Derive a lower bound for the weighted sum by comparing with a divergent reciprocal-type zero ordinate sum.
2. Use RH-based critical-line identities already in file (`ρ.re = 1/2`) to normalize terms.
3. Prove the `∀ M, ∃ T ≥ 2` statement with explicit monotone/finset-sum steps.
4. Keep all downstream statements unchanged.

## If You Discover a Genuine Mathematical Block
If this theorem is not derivable in this repo under these constraints, do **not** add assumptions.
Instead:
1. Provide a precise formal blocker report (what exact missing theorem is needed).
2. Add the strongest theorem you can prove unconditionally in this file as a replacement helper.
3. Explain exactly how close it gets to the target and what single missing ingredient remains.

## Acceptance Criteria
Primary success:
- theorem proved and builds:

```bash
cd /Users/john.n.dvorak/Documents/Git/Littlewood_Proof
lake build Littlewood.Aristotle.Standalone.PsiZeroSumOscillationFromIngham
```

- axiom check for theorem contains no `sorryAx`:

```bash
cat > /tmp/check_axioms_critical_sum.lean <<'LEAN'
import Littlewood.Aristotle.Standalone.PsiZeroSumOscillationFromIngham
#print axioms Aristotle.Standalone.PsiZeroSumOscillationFromIngham.critical_zero_sum_diverges
LEAN
lake env lean /tmp/check_axioms_critical_sum.lean
```

Secondary (if blocked):
- a compile-clean unconditional strengthening package + precise blocker report.

## Deliverable
Return:
- patch summary,
- exact proof route,
- build status,
- axiom check result,
- blocker report (only if primary target not achieved).
