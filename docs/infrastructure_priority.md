# Infrastructure Priority Ranking

**Date:** 2026-01-22
**Task:** 86

## Executive Summary

The **simplest infrastructure with highest impact** is:
**Real σ > 1 properties of LSeries/ζ** - would unblock ~15-20 sorries.

## Priority Ranking

### Priority 1: Real σ Properties (SIMPLEST, HIGH IMPACT)
**Complexity:** LOW - uses existing Mathlib series/positivity lemmas
**Sorries Unblocked:** ~15-20

Missing lemmas:
1. `(n : ℂ)^(-(σ : ℂ))` is real for real σ
2. `(n : ℂ)^(-(σ : ℂ)) > 0` for n > 0, real σ
3. LSeries with real non-negative coefficients has non-negative real part for real σ > 1
4. `ζ(σ) > 0` for real σ > 1
5. `-ζ'(σ)/ζ(σ) > 0` for real σ > 1

These would help:
- LandauLemma.lean (bounds for real σ)
- ZeroFreeRegion.lean (positivity arguments)
- SupremumRealPart.lean (dichotomy proofs)

### Priority 2: Mertens-Type Bounds (MEDIUM)
**Complexity:** MEDIUM - requires PNT-level results
**Sorries Unblocked:** ~10-15

Missing:
1. ∑_{p≤x} 1/p = log log x + M + O(1/log x)
2. ∏_{p≤x} (1 - 1/p)^{-1} ~ e^γ log x
3. Connection to ζ near σ = 1

### Priority 3: Dirichlet Integral Theory (COMPLEX)
**Complexity:** HIGH - not in Mathlib
**Sorries Unblocked:** ~11 (all LandauLemma)

Missing:
1. Convergence of ∫₁^∞ A(x)x^{-s} dx
2. Analyticity of integral function
3. Derivative under integral sign
4. Singularity detection

### Priority 4: Perron's Formula (COMPLEX)
**Complexity:** HIGH - requires contour integration
**Sorries Unblocked:** ~7 (WeightedAverageFormula)

Missing:
1. Inverse Mellin transform
2. Contour shifting
3. Error estimates

### Priority 5: Hardy Z-Function (COMPLEX)
**Complexity:** HIGH - requires functional equation
**Sorries Unblocked:** ~12 (HardyTheorem)

Missing:
1. Functional equation for ζ
2. Riemann-Siegel theta function
3. Z(t) is real for real t
4. Sign change detection

## Recommended Action

**Build Priority 1 infrastructure first.**

Specific targets:
```lean
-- These are provable with existing Mathlib
theorem cpow_neg_real_is_real (n : ℕ) (hn : n ≠ 0) (σ : ℝ) :
    ((n : ℂ) ^ (-(σ : ℂ))).im = 0

theorem cpow_neg_real_pos (n : ℕ) (hn : n ≠ 0) (σ : ℝ) (hσ : 0 < σ) :
    0 < ((n : ℂ) ^ (-(σ : ℂ))).re

theorem riemannZeta_pos_real (σ : ℝ) (hσ : 1 < σ) :
    0 < riemannZeta σ
```

## Sorry Distribution (Main Files)

| File | Sorries | Primary Blocker |
|------|---------|-----------------|
| Assumptions.lean | 61 | Intentional placeholders |
| HardyTheorem.lean | 12 | Functional equation |
| LandauLemma.lean | 11 | Dirichlet integrals |
| SchmidtTheorem.lean | 9 | Oscillation bounds |
| WeightedAverageFormula.lean | 7 | Perron's formula |
| ZeroFreeRegion.lean | 7 | Real σ positivity |
| SupremumRealPart.lean | 4 | Dichotomy |
| TypeBridge.lean | 2 | L-series monotonicity |
| ConversionFormulas.lean | 2 | Conversion formulas |
| FromGauss.lean | 1 | Error bounds |

**Total non-placeholder sorries:** ~55
**Provable with Priority 1:** ~15-20
