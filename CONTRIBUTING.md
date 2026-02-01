# Contributing to Littlewood Formalization

## Sorry Inventory (current)

| File | Sorries | Topic |
|------|---------|-------|
| `Assumptions.lean` | 61 | Hypothesis class instances (classical results not in Mathlib) |
| `Aristotle/MeanSquare.lean` | 3 | Mean square of partial zeta sums |
| `Aristotle/ChebyshevTheta.lean` | 3 | Von Mangoldt / theta function identities |
| `Aristotle/PhragmenLindelof.lean` | 3 | Convexity bounds, Gamma growth |
| `Aristotle/PartialSummation.lean` | 2 | pi(x) - li(x) via partial summation |
| `Aristotle/ZeroCounting.lean` | 2 | N(T) argument principle + asymptotic |
| `Aristotle/PerronContourIntegralsV2.lean` | 1 | Cauchy integral theorem for Perron |
| `Aristotle/HardyZConjugation.lean` | 1 | Mellin transform identity |
| `Bridge/HardySetupInstance.lean` | 3 | Hardy setup fields (mean square, first moment, L1) |
| `Bridge/HardyBuildingBlocksInstance.lean` | 2 | BuildingBlocks template |
| `Bridge/HardyAssemblyAttempt.lean` | 1 | Hardy assembly exploration |
| `Development/HardyTheorem.lean` | 2 | Hardy's theorem |
| `Development/ZeroFreeRegion.lean` | 2 | Zero-free region |
| `Development/LittlewoodTheorem.lean` | 1 | Direct approach |
| `CoreLemmas/LandauLemma.lean` | 1 | Analytic continuation identity |

## Tractable Sorries (Easy)

These are likely closeable with current Mathlib:

- **`PerronContourIntegralsV2.lean`** — Perron contour integral.
  Mathlib has `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`.

- **`DiagonalIntegralBound.lean`** — Harmonic sum bounds via induction;
  measurability via `measurable_of_countable`.

- **`ContourInfrastructure.lean`** — Measure preimage lemmas.
  Try `congr 1` or `ext; simp [Complex.equivRealProd]`.

## Medium Difficulty

See [`docs/mathlib_pr_specs/`](docs/mathlib_pr_specs/) for detailed specs.

| Priority | PR Target | Unlocks |
|----------|-----------|---------|
| 1 | Quantitative zero-free region | ~8 sorries |
| 2 | Perron's formula | ~25 sorries |
| 3 | Zero counting (uniform Riemann-von Mangoldt) | ~15 sorries |
| 4 | Hardy's theorem (approximate functional equation) | ~15 sorries |

## Hard — Aristotle-Level Proofs

These require substantial analytic number theory formalization:

- `MeanSquare.lean` sorries — off-diagonal bounds, norm-squared decomposition
- `PhragmenLindelof.lean` sorries — Phragmen-Lindelof convexity, Stirling asymptotics
- `ZeroCounting.lean` sorries — argument principle for N(T)

## Workflow

1. Pick a sorry from the tables above
2. Check [Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/)
   for the needed API (especially `Mathlib.NumberTheory.LSeries.*`,
   `Mathlib.NumberTheory.ZetaFunction.*`)
3. If Mathlib has the lemma: replace `sorry` with proof
4. If Mathlib doesn't: document what's missing in an issue
5. Run `lake build` to verify

## Code Style

- Follow Mathlib conventions
- Use `sorry -- BLOCKED: [reason]` for documented blockers
- Add references to Mathlib lemmas in comments
- Keep proofs readable; prefer `exact` over `simp` when clear
- Use `maxHeartbeats 800000` for Aristotle files (not 0)

## Testing

```bash
# Full build
lake build

# Specific file
lake build Littlewood.Aristotle.MeanSquare

# Count sorries
lake build 2>&1 | grep "uses 'sorry'" | wc -l
```

## Questions?

- Open an issue on this repository
- See [`docs/CurrentStatus.md`](docs/CurrentStatus.md) for the latest dashboard
- See [`docs/blocking_analysis.md`](docs/blocking_analysis.md) for gap analysis
