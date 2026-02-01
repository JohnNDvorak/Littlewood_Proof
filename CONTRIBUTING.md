# Contributing to Littlewood Formalization

## Sorry Inventory (audited 2026-02-01 from `lake build`)

**83 project sorry declarations** (+ 3 from PrimeNumberTheoremAnd dependency).

### Imported by build (produce warnings)

| File | Declarations | Topic |
|------|-------------|-------|
| `Assumptions.lean` | 58 | Hypothesis class instances (classical results not in Mathlib) |
| `Aristotle/HardyInfiniteZerosV2.lean` | 5 | Hardy's theorem V2 — contradiction argument structure |
| `Aristotle/MeanSquare.lean` | 3 | Mean square of partial zeta sums |
| `Aristotle/PhragmenLindelof.lean` | 3 | Convexity bounds, Gamma growth |
| `Aristotle/StirlingBernoulli.lean` | 2 | Bernoulli B1/B2, Stirling remainder |
| `Aristotle/ZeroCounting.lean` | 2 | N(T) argument principle + asymptotic |
| `Aristotle/PartialSummation.lean` | 1 | pi(x) - li(x) via partial summation |
| `Aristotle/PerronContourIntegralsV2.lean` | 1 | Cauchy integral theorem for Perron |
| `Aristotle/HardyZConjugation.lean` | 1 | Mellin transform identity |
| `Aristotle/ContourRectangle.lean` | 1 | Rectangle contour integral = 0 |
| `Bridge/HardySetupV2Instance.lean` | 3 | HardySetupV2 fields (mean square, first moment, convexity) |
| `Bridge/MeanSquareBridge.lean` | 2 | Type transfer between hardyZ variants |
| `CoreLemmas/LandauLemma.lean` | 1 | Analytic continuation identity |

### On disk but not imported

| File | Sorry tokens | Topic |
|------|-------------|-------|
| `Aristotle/HardyInfiniteZeros.lean` | 0 (vacuous) | V1 deprecated — unsatisfiable field signatures |
| `Aristotle/ChebyshevTheta.lean` | 3 | Redefines psi/theta (conflict with Basic/) |
| `Aristotle/_deprecated/PerronFormula.lean` | 5 | Deprecated, redefines chebyshevPsi |
| `Aristotle/_deprecated/PrimePowerSums.lean` | 4 | Deprecated, redefines psi |
| `Aristotle/_deprecated/FunctionalEquation.lean` | 1 | Deprecated |
| `Bridge/HardyAssemblyAttempt.lean` | 1 | V1 exploration, superseded by V2 chain |
| `Development/HardyTheorem.lean` | 2 | Hardy's theorem (WIP) |
| `Development/ZeroFreeRegion.lean` | 2 | Zero-free region (WIP) |
| `Development/LittlewoodTheorem.lean` | 1 | Direct approach (WIP) |

## Tractable Sorries (Easy)

These are likely closeable with current Mathlib:

- **`PerronContourIntegralsV2.lean`** — Perron contour integral.
  Mathlib has `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`.

- **`ContourRectangle.lean`** — Rectangle contour integral = 0.
  Edge lemmas all proved; main theorem needs `I • ∫` vs `I * ∫` coercion fix.

- **`StirlingBernoulli.lean`** — `integral_B1_eq_B2_sub_const` needs
  `∫_k^{k+1} B1 = 0` for integer k (floor-based telescoping).

- **`MeanSquareBridge.lean`** — Type transfer `hardyZ_sq_eq` between
  `HardyEstimatesPartial.hardyZ` and `HardyApproxFunctionalEq.Z`.

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

- `HardyInfiniteZerosV2.lean` — contradiction argument structure (constant sign,
  mean square decomposition, sup × L1 bound)
- `MeanSquare.lean` — off-diagonal bounds, norm-squared decomposition
- `PhragmenLindelof.lean` — Phragmén-Lindelöf convexity, Stirling asymptotics
- `ZeroCounting.lean` — argument principle for N(T)
- `HardySetupV2Instance.lean` — `first_moment_upper` (connect OscillatorySumBound
  to Hardy Z) and `Z_convexity_bound` (Phragmén-Lindelöf)

## Hardy Chain (Critical Path)

The most impactful work is closing the Hardy chain:

```
DiagonalIntegralBound (0 sorries) ✓
  → HardyApproxFunctionalEq (0 sorries) ✓
    → MeanSquarePartialSumAsymptotic (0 sorries) ✓
      → OscillatorySumBound (0 sorries) ✓
        → MeanSquareBridge (2 sorries)
          → HardySetupV2Instance (3 sorries)
            → HardyInfiniteZerosV2 (5 sorries)
              → HardyCriticalLineWiring → Schmidt
```

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
