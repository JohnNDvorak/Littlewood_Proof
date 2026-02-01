# Littlewood Proof: Current Status

**Date**: 2026-02-01

## Sorry Count Summary (from `lake build`)

| Directory | Files | Sorries | Notes |
|-----------|-------|---------|-------|
| Assumptions.lean | 1 | 58 | Hypothesis class instances (classical results not in Mathlib) |
| Aristotle/ | 12 | 28 | Analytic number theory proofs (active, imported) |
| Bridge/ | 2 | 4 | HardySetupV2Instance (3), MeanSquareBridge (1) |
| CoreLemmas/ | 1 | 1 | Landau lemma analytic continuation |
| **Total (project)** | **15** | **90** | Main proof chain: 0 sorries |

Development/ files (not imported): 5 sorries across 3 files.

## Recently Closed / Integrated

- **HardyInfiniteZerosV2.lean**: `constant_sign_of_finite` and `abs_integral_eq_of_pos` proved (5 → 3 sorries)
- **StirlingBernoulli.lean**: 2 sorry → 0 sorry (Bernoulli B1/B2 bounds)
- **MeanSquareBridge.lean**: 2 → 1 sorry (type transfer partial fix)
- **V1 Hardy deprecation**: Removed `HardyInfiniteZeros.lean` from imports (-4 sorries)
- **ZetaBoundsV2.lean**: NEW — zeta bound Re(s)>1, functional equation, sinh/Gamma bounds (3 sorries)
- **CauchyGoursatRectangle.lean**: NEW — Cauchy-Goursat rectangle theorem (3 sorries)
- **ZeroFreeRegionV3.lean**: NEW — 3-4-1 inequality, ζ(1+it)≠0, log-deriv bounds (6 sorries)

## Hypothesis Instance Status

### Fully Proved (no sorries)
- `ZeroConjZeroHyp` — conjugation symmetry of nontrivial zeros
- `ZeroOneSubZeroHyp` — functional equation symmetry of nontrivial zeros

### Pre-Wired (blocked by upstream sorries)
- `Schmidt.HardyCriticalLineZerosHyp` — in HardyCriticalLineWiring.lean
  - Conversion lemma `hardy_zeros_to_nontrivial_zeros` fully proved
  - Instance fires automatically when HardySetupV2Instance's 3 Aristotle sorries close

### All Others: Sorry (in Assumptions.lean)
- 58 instances for classical analytic number theory results
- Each corresponds to a well-known theorem not yet available in Mathlib

## Hardy Chain Status (V2 Canonical)

```
DiagonalIntegralBound: ∫|S_N|² ≥ c·T·log T          (0 sorries) ✓
  → HardyApproxFunctionalEq: ∫Z² ≥ k·∫|S_N|² - CT   (0 sorries) ✓
  → MeanSquarePartialSumAsymptotic                     (0 sorries) ✓
  → OscillatorySumBound                                (0 sorries) ✓
  → MeanSquareBridge: ∫Z² ≥ c'·T·log T on [1,T]      (1 sorry)
  → HardySetupV2Instance: fields 1-3 proved, 4-6 sorry (3 sorries)
  → HardyInfiniteZerosV2: 2/5 lemmas proved            (3 sorries)
  → HardyCriticalLineWiring → Schmidt.HardyCriticalLineZerosHyp
```

**Remaining:**
1. Close MeanSquareBridge sorry (type transfer between hardyZ variants)
2. `first_moment_upper` — connect OscillatorySumBound to Hardy Z
3. `Z_convexity_bound` — |ζ(1/2+it)| ≤ C|t|^{1/4+ε} (Phragmén-Lindelöf)
4. `mean_square_decomp` — ∂volume elaboration mismatch workaround
5. `mean_square_le_sup_times_l1` — iSup BddAbove on Ioc
6. `hardy_infinitely_many_zeros_v2` — main contradiction argument

## Aristotle Module: Active Sorries

| File | Sorries | Topic |
|------|---------|-------|
| ZeroFreeRegionV3.lean | 6 | 3-4-1 inequality, ζ(1+it)≠0, log-deriv bounds |
| HardyInfiniteZerosV2.lean | 3 | Hardy theorem proof steps (2 of 5 proved) |
| MeanSquare.lean | 3 | Mean square of partial zeta sums |
| CauchyGoursatRectangle.lean | 3 | Cauchy-Goursat rectangle theorem |
| PhragmenLindelof.lean | 3 | Convexity bounds, Gamma growth |
| ZetaBoundsV2.lean | 3 | Zeta bound Re(s)>1, functional equation |
| ZeroCounting.lean | 2 | N(T) argument principle + asymptotic |
| PerronContourIntegralsV2.lean | 1 | Cauchy integral theorem for Perron |
| PartialSummation.lean | 1 | π(x)-li(x) sign changes from ψ(x)-x |
| HardyZConjugation.lean | 1 | Mellin transform identity |
| ContourRectangle.lean | 1 | Rectangle contour integral |

## Key Gaps for Progress

1. **Hardy chain**: 7 sorries total (MeanSquareBridge through HardyInfiniteZerosV2)
2. **Zero-free region**: ZeroFreeRegionV3 has ζ(1+it)≠0 proved; needs `analyticAt_zetaResidueFunction`
3. **Zeta bounds**: `zeta_bound_re_ge_one` needs integral representation argument
4. **Explicit formulas**: Perron contour integral needs Cauchy-Goursat bookkeeping
5. **Zero counting**: Riemann-von Mangoldt needs uniform C

## Build Status

- Full `lake build` passes with 90 sorry warnings (project) + 3 (dependency)
- All 172 .lean files compile
- ~32,100 lines of Lean code
