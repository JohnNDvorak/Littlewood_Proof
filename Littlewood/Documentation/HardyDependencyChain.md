# Hardy Dependency Chain

*Updated 2026-01-31*

## Overview

When Hardy's theorem (infinitely many zeta zeros on the critical line) is proved,
a cascade of assumption closures becomes possible. This document maps the full chain.

## Direct Closure: HardyCriticalLineZerosHyp

**Assumption**: `Schmidt.HardyCriticalLineZerosHyp`
**Requires**: `Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1/2 }`
**Closes when**: Hardy's theorem gives infinitely many zeros of Z(t), hence
infinitely many zeros of ζ(1/2+it), hence infinitely many nontrivial zeros
with real part 1/2.

**Wiring file**: `Bridge/HardyCriticalLineWiring.lean` (template ready)

## Indirect Chain 1: PsiOscillationFromCriticalZerosHyp

**Assumption**: `Schmidt.PsiOscillationFromCriticalZerosHyp`
**Requires**: Hardy zeros + explicit formula → ψ(x) - x oscillates
**Chain**:
1. HardyCriticalLineZerosHyp (from Hardy)
2. ExplicitFormulaPsiHyp (from Perron's formula — needs separate Aristotle work)
3. Schmidt oscillation machinery (proved: `schmidt_oscillation` in SchmidtNew.lean)
4. Combine: critical line zeros → trig polynomial with nonzero coefficients → sign changes

**Status**: Needs ExplicitFormulaPsiHyp independently of Hardy

## Indirect Chain 2: PsiOscillationSqrtHyp

**Assumption**: `Schmidt.PsiOscillationSqrtHyp`
**Requires**: ψ(x) - x = Ω±(x^{1/2})
**Chain**:
1. PsiOscillationFromCriticalZerosHyp (above)
2. Quantitative bounds on oscillation amplitude
3. Connection to zero density near Re(s) = 1/2

**Status**: Deeper than Chain 1, needs quantitative explicit formula

## What Hardy's Theorem Requires

### Already Proved (4/6 BuildingBlocks fields)

| Field | Source | Status |
|-------|--------|--------|
| `completedRiemannZeta_critical_line_real` | CompletedZetaCriticalLine | ✅ |
| `hardyZ_is_real` | HardyZRealV2 | ✅ |
| `hardyZ_eq_norm_zeta` | HardyZRealV2 | ✅ |
| `hardyZ_continuous` | HardyZRealV2 | ✅ |

### Waiting on Aristotle (2/6 fields)

| Field | What's Needed | Aristotle Prompt |
|-------|---------------|-----------------|
| `zeta_mean_square_lower_bound` | ∫₀ᵀ \|ζ(1/2+it)\|² dt ≥ c·T·log T | MeanSquareLowerBound |
| `hardyZ_integral_bound` | \|∫₀ᵀ Z(t) dt\| ≤ C·T^{1/2+ε} | HardyZIntegralBound |

### Assembly Strategy

Once both fields are available:
1. Instantiate `BuildingBlocks hardyThetaV2` (in HardyBuildingBlocksInstance.lean)
2. Apply `HardyZContradiction.hardy_infinite_zeros`
3. Wire sign changes → zeros (IVT, already proved)
4. Wire zeros → critical line zeros (Z=0 ↔ ζ(1/2+it)=0, already proved)
5. Close HardyCriticalLineZerosHyp

## Assumptions NOT Closeable by Hardy Alone

The following require independent work even after Hardy:

| Assumption | Blocker |
|------------|---------|
| ExplicitFormulaPsiHyp | Full Perron + contour integration |
| WeightedAverageFormulaRHHyp | Fejér + RH hypothesis |
| ZetaLogDerivPoleHyp | -ζ'/ζ behavior at arbitrary zeros (not just s=1) |
| ZeroFreeRegionHyp | de la Vallée-Poussin type bounds |
| LandauPringsheimHyp | Pringsheim's theorem for Dirichlet series |

## Summary

| Category | Count |
|----------|-------|
| Direct closure from Hardy | 1 (HardyCriticalLineZerosHyp) |
| Indirect, needs Hardy + more | 2 (PsiOscillation variants) |
| Independent of Hardy | ~53 |
| Already proved | 2 (ZeroConj, ZeroOneSub) |
