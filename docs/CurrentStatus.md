# Littlewood Proof: Current Status

**Date**: 2026-02-02 (updated)

## Sorry Count Summary (from `lake build`)

| Directory | Files | Sorries | Notes |
|-----------|-------|---------|-------|
| Assumptions.lean | 1 | 60 | Hypothesis class instances (classical results not in Mathlib) |
| Aristotle/ | 4 | 7 | Analytic number theory proofs (active, imported) |
| Bridge/ | 0 | 0 | All bridge files sorry-free (Hardy chain complete) |
| CoreLemmas/ | 1 | 1 | Landau lemma analytic continuation |
| **Total (project)** | **6** | **68** | Main proof chain: 0 sorries |

Additionally: 3 sorries from PrimeNumberTheoremAnd dependency.
Development/ files (not imported): 4 sorries across 3 files.
Deprecated Aristotle files: not counted above.

## Hardy Chain Status (Structurally Complete)

```
DiagonalIntegralBound: integral |S_N|^2 >= c*T*log T      (0 sorries) done
  -> HardyApproxFunctionalEq: integral Z^2 >= k*integral|S|^2 - CT   (1 sorry)
  -> MeanSquarePartialSumAsymptotic                        (0 sorries) done
  -> OscillatorySumBound                                   (0 sorries) done
  -> MeanSquareBridge: integral Z^2 >= c'*T*log T          (0 sorries) done
  -> HardySetupV2Instance: ALL 6 FIELDS PROVED             (0 sorries) done
  -> HardyInfiniteZerosV2: ALL 5 LEMMAS PROVED             (0 sorries) done
  -> HardyCriticalLineWiring -> Schmidt.HardyCriticalLineZerosHyp  done
```

**The Hardy chain is structurally complete.** All files from MeanSquareBridge
through HardyCriticalLineWiring are sorry-free. The remaining analytic inputs
are encoded as hypothesis classes:

- `ZetaCriticalLineBoundHyp` -- Phragmen-Lindelof convexity (sorry in Assumptions.lean)
- `HardyFirstMomentUpperHyp` -- first moment upper bound (sorry in Assumptions.lean)
- `approx_functional_eq` (1 sorry in HardyApproxFunctionalEq.lean)

When these are proved, the sorry count drops by 3.

## Hypothesis Instance Status

### Fully Proved (no sorries)
- `ZeroConjZeroHyp` -- conjugation symmetry of nontrivial zeros
- `ZeroOneSubZeroHyp` -- functional equation symmetry of nontrivial zeros
- `FunctionalEquationHyp` -- zeta functional equation
- `LambdaSymmetryHyp` -- completed zeta symmetry

### Pre-Wired (fires automatically)
- `Schmidt.HardyCriticalLineZerosHyp` -- in HardyCriticalLineWiring.lean
  - Conversion lemma `hardy_zeros_to_nontrivial_zeros` fully proved
  - Instance fires when `ZetaCriticalLineBoundHyp` and `HardyFirstMomentUpperHyp` instances are available

### All Others: Sorry (in Assumptions.lean)
- 60 instances for classical analytic number theory results
- Each corresponds to a well-known theorem not yet available in Mathlib

## Aristotle Module: Active Sorries

| File | Sorries | Topic |
|------|---------|-------|
| PhragmenLindelof.lean | 3 | Convexity bounds, Gamma growth (Stirling) |
| ZeroCounting.lean | 2 | N(T) argument principle + asymptotic |
| HardyApproxFunctionalEq.lean | 1 | Approximate functional equation |
| PartialSummation.lean | 1 | pi(x) - li(x) via partial summation |

**Sorry-free Aristotle files** (previously had sorries): ContourRectangle,
PerronContourIntegralsV2, CauchyGoursatRectangle, StirlingBernoulli,
ZeroFreeRegionV3, HardyZConjugation, HardyInfiniteZerosV2, ZetaBoundsV2,
ContourInfrastructure, DiagonalIntegralBound, MeanSquare

**Sorry-free Bridge files**: MeanSquareBridge, HardySetupV2Instance,
HardyCriticalLineWiring, HardySetupInstance, HardyZTransfer, and all others

## Key Gaps for Progress

1. **PhragmenLindelof** (3 sorries): Convexity bounds and Gamma growth.
   Closing these would discharge `ZetaCriticalLineBoundHyp`.
2. **HardyApproxFunctionalEq** (1 sorry): Approximate functional equation.
   Last sorry on the Hardy critical path.
3. **ZeroCounting** (2 sorries): N(T) via argument principle. Not on critical path.
4. **PartialSummation** (1 sorry): Transfer from psi to pi-li oscillation.
5. **LandauLemma** (1 sorry): Identity theorem for Dirichlet series.

**Aristotle prompts**: See `docs/aristotle_prompts.md` for ready-to-use prompts.

## Build Status

- Full `lake build` passes with 71 sorry warnings (68 project + 3 dependency)
- All .lean files compile
- ~33,100 lines of Lean code
- 174 total .lean files, 169 sorry-free (97%)
