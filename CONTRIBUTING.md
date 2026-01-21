# Contributing to Littlewood Formalization

## Current Priority: Close Low-Hanging Sorries

### Files to Review

1. **`Littlewood/Development/ZeroFreeRegion.lean`** - 8 sorries
   - 6 new theorems already proved from Mathlib
   - Remaining: Dirichlet character extraction, quantitative region
   - See: [`docs/sorry_analysis/zerofreeregion_analysis.md`](docs/sorry_analysis/zerofreeregion_analysis.md)

2. **`Littlewood/Development/TypeBridge.lean`** - 4 sorries
   - LSeries infrastructure mostly complete
   - Blocker: Landau boundary singularity theorem

3. **`Littlewood/CoreLemmas/LandauLemma.lean`** - 11 sorries
   - 10 are parametric (architecture issue, not proof issue)
   - 1 potentially provable: ZetaLogDerivPoleHyp
   - See: [`docs/sorry_analysis/landaulemma_analysis.md`](docs/sorry_analysis/landaulemma_analysis.md)

### How to Help

1. **Pick a sorry** from the files above
2. **Check Mathlib** for the needed lemma:
   - Search [mathlib4-docs](https://leanprover-community.github.io/mathlib4_docs/)
   - Check `Mathlib.NumberTheory.LSeries.*`
   - Check `Mathlib.NumberTheory.ZetaFunction.*`
3. **If Mathlib has it**: Replace sorry with proof
4. **If Mathlib doesn't**: Document precisely what's missing

### Example Contribution

```lean
-- Before (in ZeroFreeRegion.lean)
theorem zeta_ne_zero_example (s : ℂ) (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 := by
  sorry

-- After
theorem zeta_ne_zero_example (s : ℂ) (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs
```

## Mathlib Contributions Needed

See [`docs/mathlib_pr_specs/`](docs/mathlib_pr_specs/) for detailed specifications.

### Priority Order

| Priority | PR | Difficulty | Unlocks |
|----------|-----|------------|---------|
| 1 | Quantitative zero-free region | MEDIUM-HIGH | ~8 sorries |
| 2 | Perron's formula | HIGH | ~25 sorries |
| 3 | Zero counting | HIGH | ~15 sorries |
| 4 | Hardy's theorem | VERY HIGH | ~15 sorries |

### Getting Started with Mathlib

1. Read the specification in `docs/mathlib_pr_specs/`
2. Check Zulip #number-theory for ongoing work
3. Open a Mathlib issue referencing the spec
4. Start with prerequisites (listed in each spec)

## Code Style

- Follow Mathlib conventions
- Use `sorry -- BLOCKED: [reason]` for documented blockers
- Add references to Mathlib lemmas in comments
- Keep proofs readable; prefer `exact` over `simp` when clear

## Testing

```bash
# Full build
lake build

# Specific file
lake build Littlewood.Development.ZeroFreeRegion
```

## Questions?

- Open an issue on this repository
- Check the documentation in `docs/`
- Reference the blocking analysis for why something might be hard
