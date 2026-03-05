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
