# Aristotle Self-Contained Prompt Pack

This file merges four standalone copy/paste prompts.

---

## Prompt A: Digamma Atomic Closure

# Self-Contained Prompt A: Close `digamma_log_bound_atomic`

You are working in this repo:
`/Users/john.n.dvorak/Documents/Git/Littlewood_Proof`

## Goal
Prove exactly this theorem (do not change signature):

```lean
theorem digamma_log_bound_atomic :
    ∃ C > 0, ∀ s : ℂ, s.re ≥ 1/4 → |s.im| ≥ 1 →
      Gamma s ≠ 0 →
      ‖deriv Gamma s / Gamma s - Complex.log s‖ ≤ C / ‖s‖ := by
  sorry
```

Path: `Littlewood/Aristotle/DigammaBinetBound.lean`

## Hard Constraints
- No axioms.
- No `sorry`, `admit`, or placeholders.
- Keep theorem statement unchanged.
- Keep compatibility with:
  - Lean: `v4.27.0-rc1`
  - Mathlib rev: `fdddb3ea2c8c35de4455e033bc2a5df4d3a391ee`
- Prefer editing only `Littlewood/Aristotle/DigammaBinetBound.lean` unless absolutely necessary.

## Existing Infrastructure Already in This File
Use these lemmas directly (already proved):
- `gauss_term_bound`
- `norm_sq_add_natCast_ge`
- `two_le_norm_add_natCast_of_strip`
- `gauss_term_bound_add_natCast`
- `inv_norm_add_natCast_sq_le_inv_of_strip`
- `inv_norm_add_natCast_sq_le_inv_natCast_sq`
- `gauss_term_bound_by_inv_natCast_sq`
- `summable_gauss_terms_shifted_two`
- `summable_gauss_terms`
- `summable_gauss_complex_terms_shifted_two`
- `summable_gauss_complex_terms`
- `tsum_gauss_terms_eq_prefix_two_add_tail`
- `tsum_gauss_complex_terms_eq_prefix_two_add_tail`
- `norm_tsum_gauss_complex_terms_shifted_two_le`
- `tendsto_logDeriv_GammaSeq_of_locallyUniform`

## Required Approach
1. Build the bridge from `deriv Gamma s / Gamma s` to the Gauss-series expression
   involving `∑' n, (log (1 + 1/(s+n)) - 1/(s+n))`.
2. Use the already-proved summability and prefix/tail decomposition lemmas to bound the series.
3. Bound the finite prefix terms (`n=0,1`) by a constant absorbed into `C`.
4. Bound the tail by the `1/(n+2)^2` majorant and combine with strip bounds `s.re ≥ 1/4`, `|s.im| ≥ 1`.
5. Produce explicit `C > 0` and finish existential quantifiers.

## Acceptance Criteria
- The theorem is fully proved with no new axioms.
- Module builds cleanly (except normal lints):

```bash
cd /Users/john.n.dvorak/Documents/Git/Littlewood_Proof
lake build Littlewood.Aristotle.DigammaBinetBound
```

- Axiom check contains no `sorryAx`:

```bash
cat > /tmp/check_axioms_digamma.lean <<'LEAN'
import Littlewood.Aristotle.DigammaBinetBound
#print axioms Aristotle.DigammaBinetBound.digamma_log_bound_atomic
LEAN
lake env lean /tmp/check_axioms_digamma.lean
```

## Deliverable
Return:
- exact patch summary,
- key lemmas/theorems added/used,
- build output summary,
- axiom check result.

---

## Prompt B: Critical Zero Sum Divergence

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

---

## Prompt C: Inhomogeneous Phase Target Alignment

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

---

## Prompt D: RS Block Analysis Closure

# Self-Contained Prompt D: Close `rs_block_analysis`

You are working in this repo:
`/Users/john.n.dvorak/Documents/Git/Littlewood_Proof`

## Goal
Prove exactly this theorem (do not change signature):

```lean
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
```

Path: `Littlewood/Aristotle/Standalone/RSCompleteBlockAsymptotic.lean`

## Hard Constraints
- No axioms.
- No `sorry`, `admit`, placeholders.
- Keep theorem statement unchanged.
- Lean/mathlib compatibility unchanged.

## Context
Downstream theorem in same file (`rsCompleteBlockWithResidual_sorry`) consumes this exact structure.

Do not use shortcuts that pull in unresolved `sorry` from other files.
If you use a theorem from another file, confirm it is `sorry`-free in this repo state.

## Required Approach
1. Construct explicit witnesses `A`, `c`, `C₂` in this file.
2. Prove each conjunct in order:
   - `A > 0`
   - `∀ k, 0 ≤ c k`
   - `AntitoneOn c (Ici 1)`
   - exact block identity
   - `C₂ ≥ 0`
   - partial-block interpolation
3. Keep compatibility with existing proof of `rsCompleteBlockWithResidual_sorry`.
4. Avoid changing public theorem signatures unless absolutely required.

## If Blocked
If complete closure is impossible under no-axiom/no-sorry constraints:
1. Do not add assumptions.
2. Add maximal unconditional proved helper lemmas that reduce the remaining gap.
3. Provide exact minimal blocker theorem still missing.

## Acceptance Criteria
Primary success:

```bash
cd /Users/john.n.dvorak/Documents/Git/Littlewood_Proof
lake build Littlewood.Aristotle.Standalone.RSCompleteBlockAsymptotic
```

Axiom check:

```bash
cat > /tmp/check_axioms_rs_block.lean <<'LEAN'
import Littlewood.Aristotle.Standalone.RSCompleteBlockAsymptotic
#print axioms Aristotle.Standalone.RSCompleteBlockAsymptotic.rs_block_analysis
LEAN
lake env lean /tmp/check_axioms_rs_block.lean
```

## Deliverable
Return:
- patch summary,
- theorem/lemma list added,
- build status,
- axiom check result,
- blocker report only if unresolved.
