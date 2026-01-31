# Mathlib PR Specifications for Littlewood's Theorem

## Overview

Full formalization of Littlewood's oscillation theorem requires several Mathlib
contributions that don't currently exist. This directory contains detailed
specifications for each needed PR.

## Priority Order

| Priority | PR | Unlocks | Est. Hours | Difficulty |
|----------|-----|---------|------------|------------|
| 1 | [Perron's Formula](perron_formula.md) | Explicit formulas, ψ(x) representation | 100-200 | HIGH |
| 2 | [Zero Counting](zero_counting.md) | N(T) asymptotic, density results | 100-200 | HIGH |
| 3 | [Quantitative Zero-Free](quantitative_zero_free.md) | PNT error term, oscillation bounds | 80-150 | MEDIUM-HIGH |
| 4 | [Hardy's Theorem](hardy_theorem.md) | Critical line zeros, stronger oscillation | 200-400 | VERY HIGH |

## Specifications

### [Perron's Formula](perron_formula.md)
**Statement:** ∑_{n≤x} f(n) = (1/2πi) ∫ F(s) x^s/s ds

**Unlocks in Littlewood project:**
- ExplicitFormulaPsiHyp
- ExplicitFormulaPsiSmoothedHyp
- ExplicitFormulaIntegralHyp
- ExplicitFormulaDoubleIntegralHyp
- PsiMellinHyp
- MellinContourShiftHyp

**Status:** Mathlib has LSeries and basic contour integration, but not Perron kernel or truncation estimates.

### [Zero Counting](zero_counting.md)
**Statement:** N(T) = (T/2π) log(T/2πe) + O(log T)

**Unlocks in Littlewood project:**
- ZeroCountingAsymptoticHyp
- ZeroCountingCrudeBoundHyp
- ZeroCountingMainTermHyp
- ZeroCountingLocalDensityHyp
- ZeroCountingSummabilityHyp
- ~10 more zero-related hypotheses

**Status:** Mathlib has argument principle basics and isolated zeros, but not rectangular contour integration for zeta.

### [Quantitative Zero-Free Region](quantitative_zero_free.md)
**Statement:** ζ(s) ≠ 0 for Re(s) > 1 - c/log|Im(s)|

**Unlocks in Littlewood project:**
- ZeroFreeRegionHyp
- ChebyshevErrorBoundZeroFreeHyp
- Part of ZetaZeroSupRealPartDichotomyHyp

**Status:** Mathlib has Re(s) ≥ 1 non-vanishing and the 3-4-1 inequality for L-functions. Need to extract quantitative bounds.

### [Hardy's Theorem](hardy_theorem.md)
**Statement:** ζ(s) has infinitely many zeros on Re(s) = 1/2

**Unlocks in Littlewood project:**
- HardyCriticalLineZerosHyp
- PsiOscillationFromCriticalZerosHyp
- ThetaOscillationMinusHyp
- Development/HardyTheorem.lean (~12 sorries)

**Status:** Mathlib has functional equation and Gamma, but not Hardy Z-function or slitPlane membership for relevant Gamma arguments.

## Total Estimated Effort

| Metric | Value |
|--------|-------|
| Total hours | 480-950 |
| Number of PRs | 4 major + supporting |
| Lines of code | 3000-6000 |
| Timeline | 1-3 years (one contributor) |

## Current Mathlib State (as of Jan 2026)

### Available
- `riemannZeta`, `completedRiemannZeta`
- `riemannZeta_one_sub` (functional equation)
- `riemannZeta_ne_zero_of_one_le_re` (non-vanishing Re ≥ 1)
- `riemannZeta_eulerProduct` family (Euler product)
- `LSeries` infrastructure (Dirichlet series)
- `Complex.Gamma`, basic Stirling
- Argument principle basics

### Missing
- Perron's formula and kernel
- Rectangular contour integration
- Zero counting function N(T)
- Hardy Z-function
- Quantitative zero-free region interior
- Stirling for arg(Gamma)

## How to Contribute

If you're interested in contributing any of these to Mathlib:

1. **Open a Mathlib issue** referencing this specification
2. **Start with prerequisites:** The specs list what Mathlib has vs. needs
3. **Coordinate:** Check #number-theory on Zulip for ongoing work
4. **Small PRs:** Break the work into mergeable chunks

### Recommended Starting Points

**Easiest:** Quantitative zero-free region
- Most prerequisites exist
- Clear proof strategy
- Medium complexity

**Most impactful:** Perron's formula
- Unlocks the explicit formula path
- Foundation for analytic number theory

**Most ambitious:** Hardy's theorem
- Requires significant infrastructure
- Very high complexity

## Impact on Littlewood Project

| PRs Completed | Sorries Eliminated | % Complete |
|---------------|-------------------|------------|
| None (current) | 0 | ~15-20% |
| Quantitative ZF | ~8 | ~20-25% |
| + Perron | ~25 | ~35-45% |
| + Zero Counting | ~35 | ~55-65% |
| + Hardy | ~50 | ~75-85% |
| All remaining | ~113 | 100% |

## License

These specifications are released under the same license as the Littlewood
formalization project. They may be freely used to guide Mathlib development.
