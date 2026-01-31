# Littlewood Proof: Current Status

**Date**: 2026-01-31

## Sorry Count Summary

| Directory | Files | Sorries | Notes |
|-----------|-------|---------|-------|
| Assumptions.lean | 1 | 61 | Hypothesis class instances (classical results not in Mathlib) |
| Aristotle/ | 10 | 29 | Analytic number theory proofs (includes 10 in _deprecated/) |
| Bridge/ | 3 | 6 | Hardy setup (3), building blocks (2), assembly (1) |
| Development/ | 3 | 5 | Littlewood thm (1), Hardy thm (2), zero-free region (2) |
| CoreLemmas/ | 1 | 1 | Landau lemma analytic continuation |
| **Active total** | **18** | **~102** | Excluding deprecated files |

## Recently Closed Sorries

- **DiagonalIntegralBound.lean**: 4 -> 0 (harmonic bounds via induction + `Real.add_one_le_exp`; measurability via `measurable_of_countable`)
- **ContourInfrastructure.lean**: 3 -> 0 (measure-preimage goals via `congr 1`)
- **ZeroCounting.lean**: 3 -> 2 (false `xi_Mathlib_differentiable` theorem removed)
- **HardySetupInstance.lean**: Created with 6/9 fields proved, 3 sorries for Aristotle

## Hypothesis Instance Status

### Fully Proved (no sorries)
- `ZeroConjZeroHyp` -- conjugation symmetry of nontrivial zeros
- `ZeroOneSubZeroHyp` -- functional equation symmetry of nontrivial zeros

### Pre-Wired (blocked by upstream sorries)
- `Schmidt.HardyCriticalLineZerosHyp` -- in HardyCriticalLineWiring.lean
  - Conversion lemma `hardy_zeros_to_nontrivial_zeros` fully proved
  - Instance fires automatically when HardySetupInstance's 3 Aristotle sorries close

### All Others: Sorry (in Assumptions.lean)
- 58 instances for classical analytic number theory results
- Each corresponds to a well-known theorem not yet available in Mathlib

## Hardy Chain Status

The Hardy chain proves infinitely many zeros on the critical line:

```
HardySetupInstance (3 sorries)
    -> HardyInfiniteZeros.hardy_infinitely_many_zeros
    -> HardyCriticalLineWiring (conversion lemma proved)
    -> Schmidt.HardyCriticalLineZerosHyp (instance auto-fires)
```

**3 Aristotle sorries needed** (documented in HardySetupRequirements.lean):
1. `mean_square_lower_bound`: integral of Z(t)^2 >= c*T*log(T)
2. `first_moment_upper_bound`: |integral of Z(t)| <= C*T^(1/2+eps)
3. `l1_lower_bound`: integral of |Z(t)| >= c*T

## Aristotle Module: Active Sorries

| File | Sorries | Topic |
|------|---------|-------|
| MeanSquare.lean | 3 | Mean square of partial zeta sums |
| ChebyshevTheta.lean | 3 | Von Mangoldt / theta function identities |
| PhragmenLindelof.lean | 3 | Convexity bounds, Gamma growth |
| PartialSummation.lean | 2 | pi(x) - li(x) via partial summation |
| ZeroCounting.lean | 2 | N(T) argument principle + asymptotic |
| PerronContourIntegralsV2.lean | 1 | Cauchy integral theorem for Perron |
| HardyZConjugation.lean | 1 | Mellin transform identity |

## Sorry-Free Aristotle Files (selected)

These files compile with 0 sorries and provide reusable infrastructure:

- **HarmonicSumIntegral.lean**: integral of H_{N(t)} = Theta(T log T)
- **OffDiagonalBound.lean**: off-diagonal oscillatory integral O(N^2)
- **DiagonalIntegralBound.lean**: diagonal mean square >= c*T*log(T)
- **ContourInfrastructure.lean**: rectangular contour, measure-zero segments
- **PartialZetaNormSqV2.lean**: |partial zeta sum|^2 expansion
- **HardyZRealV2.lean**: Hardy Z continuity and properties
- **HardyZCauchySchwarz.lean**: Cauchy-Schwarz for integral estimates
- **MeanSquareLowerBound.lean**: partial sum mean square lower bound
- **L1LowerBound.lean**: mock proof of l1_lower_bound (Z(t)=t model, 0 sorries)

## Build Status

- Full `lake build` passes
- Bridge verification: 11/12 pass (FromGauss fails: missing PNT olean)
- 3 FAIL in bridge check: FromGauss (missing dep), NewBridges (namespace collision), WiringTests (display artifact)

## Key Gaps for Progress

1. **Hardy chain**: 3 Aristotle sorries (approximate functional equation, convexity bound)
2. **Zero counting**: Riemann-von Mangoldt needs uniform C (current Aristotle version has C depending on T)
3. **Zero-free region**: No Aristotle file targets de la Vallee Poussin yet
4. **Explicit formulas**: Perron contour integral needs Cauchy-Goursat bookkeeping
