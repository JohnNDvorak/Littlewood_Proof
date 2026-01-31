# Hypothesis Progress Tracker

Last updated: 2026-01-21

## Summary

| Status | Count |
|--------|-------|
| **Proved** (no sorry) | 2 |
| **Assumed** (sorry in Assumptions.lean) | 61 |
| **Parametric** (sorry, need specific A/σ_c) | 9 |
| **Total** | 67 |

## Proved Hypotheses

These have real proofs without `sorry`:

| Hypothesis | File | Proof Method |
|-----------|------|--------------|
| `ZeroConjZeroHyp` | ZeroCountingFunction.lean:1618 | Uses `riemannZeta_conj` |
| `ZeroOneSubZeroHyp` | ZeroCountingFunction.lean:1640 | Uses functional equation |

## Hypotheses by Category

### Explicit Formula Hypotheses (9)
| Hypothesis | Status |
|-----------|--------|
| ExplicitFormulaPsiHyp | assumed |
| ExplicitFormulaPsiSmoothedHyp | assumed |
| ExplicitFormulaIntegralHyp | assumed |
| ExplicitFormulaDoubleIntegralHyp | assumed |
| PsiMellinHyp | assumed |
| MellinContourShiftHyp | assumed |
| ZeroSumBoundRHHyp | assumed |
| PsiErrorBoundHyp | assumed |
| PsiErrorBoundRHHyp | assumed |

### Conversion Formula Hypotheses (7)
| Hypothesis | Status |
|-----------|--------|
| ThetaPsiFirstCorrectionHyp | not instantiated |
| ThetaPsiRHHyp | not instantiated |
| PiFromThetaSummationHyp | not instantiated |
| LiExpansionHyp | not instantiated |
| PiLiFromThetaHyp | not instantiated |
| PiLiFromPsiRHHyp | not instantiated |
| OmegaPsiToThetaHyp | assumed |
| OmegaThetaToPiLiHyp | assumed |

### Weighted Average Hypotheses (7)
| Hypothesis | Status |
|-----------|--------|
| WeightedAverageFormulaRHHyp | assumed |
| IntegralPsiMinusXHyp | assumed |
| RhoToGammaErrorHyp | assumed |
| SumOverPositiveOrdinatesHyp | assumed |
| ZeroSumTailHyp | assumed |
| MainSumBoundHyp | assumed |
| AlignedSumLargeHyp | assumed |

### Schmidt/Oscillation Hypotheses (9)
| Hypothesis | Status |
|-----------|--------|
| SchmidtPsiOscillationHyp | assumed |
| PsiOscillationSqrtHyp | assumed |
| MellinPsiIdentityHyp | assumed |
| OmegaMinusNecessityHyp | assumed |
| OmegaPlusNecessityHyp | assumed |
| HardyCriticalLineZerosHyp | assumed |
| PsiOscillationFromCriticalZerosHyp | assumed |
| ThetaOscillationMinusHyp | assumed |
| ThetaOscillationRHHyp | assumed |

### Zero Density Hypotheses (7)
| Hypothesis | Status |
|-----------|--------|
| ZeroCountingSummabilityHyp | assumed |
| ZeroCountingSumInvGammaAsymptoticHyp | assumed |
| ZeroCountingSumOneEqHyp | assumed |
| ZeroCountingTailSqAsymptoticHyp | assumed |
| RiemannHypothesisInvRhoAsymptoticHyp | assumed |
| ZeroCountingSummableXPowRhoDivHyp | assumed |
| ZeroCountingAverageInvGammaHyp | not instantiated |

### Zero-Free Region Hypotheses (4)
| Hypothesis | Status |
|-----------|--------|
| ZeroFreeRegionHyp | assumed |
| ZetaZeroSupRealPartDichotomyHyp | assumed |
| ChebyshevErrorBoundZeroFreeHyp | assumed |
| ChebyshevErrorBoundThetaHyp | assumed |

### Zero Counting Hypotheses (12)
| Hypothesis | Status |
|-----------|--------|
| ZeroCountingTendstoHyp | assumed |
| ZeroCountingCrudeBoundHyp | assumed |
| ZeroCountingSpecialValuesHyp | assumed |
| ZeroCountingFifteenHyp | assumed |
| FirstZeroOrdinateHyp | assumed |
| ZeroCountingAsymptoticHyp | assumed |
| ZeroCountingRvmExplicitHyp | assumed |
| ZeroCountingAsymptoticRatioHyp | assumed |
| ZeroCountingMainTermHyp | assumed |
| ZeroCountingLowerBoundHyp | assumed |
| ZeroCountingLocalDensityHyp | assumed |
| ZeroGapsLowerBoundHyp | assumed |

### Conjugate/Symmetry Hypotheses (2)
| Hypothesis | Status |
|-----------|--------|
| ZeroConjZeroHyp | **PROVED** |
| ZeroOneSubZeroHyp | **PROVED** |

### Landau Lemma Hypotheses (9, parametric)
| Hypothesis | Status | Note |
|-----------|--------|------|
| LandauLemmaHyp A σ_c | assumed | Parametric |
| DirichletIntegralConvergesHyp A σ_c | assumed | Parametric |
| DirichletIntegralAnalyticHyp A σ_c | assumed | Parametric |
| DirichletIntegralDerivHyp A σ_c | assumed | Parametric |
| DirichletIntegralPowerSeriesHyp A σ_c | assumed | Parametric |
| RadiusExceedsAbscissaHyp A σ_c | assumed | Parametric |
| LandauExtensionHyp A σ₀ | assumed | Parametric |
| LandauLemmaSeriesHyp a σ_c | assumed | Parametric |
| ZetaLogDerivPoleHyp | assumed | |

## Priority for Proving

### High Priority (building blocks)
1. **ZeroCountingAsymptoticHyp** - N(T) ~ T/(2π) log(T/(2πe))
   - Depends on: contour integration, argument principle
   - Difficulty: HARD (requires significant analysis)

2. **ExplicitFormulaPsiHyp** - Explicit formula for ψ(x)
   - Depends on: Perron's formula, contour shifting
   - Difficulty: HARD

3. **ZeroFreeRegionHyp** - De la Vallée Poussin region
   - Depends on: trig_inequality (proved!), Euler product
   - Difficulty: HARD (see Development/ZeroFreeRegion.lean)

### Medium Priority (derivable)
4. **ZeroCountingSummabilityHyp** - Σ 1/γ converges
   - Depends on: ZeroCountingAsymptoticHyp
   - Difficulty: MEDIUM

5. **PsiErrorBoundHyp** - Error bounds
   - Depends on: ExplicitFormulaPsiHyp, zero-free region
   - Difficulty: MEDIUM

### Lower Priority (consequences)
Most oscillation and conversion hypotheses follow once the core ones are proved.

## Dependencies

```
ZeroCountingAsymptoticHyp
    └── ZeroCountingSummabilityHyp
        └── ZeroCountingSumInvGammaAsymptoticHyp

ExplicitFormulaPsiHyp
    └── PsiErrorBoundHyp
        └── OmegaPsiToThetaHyp
            └── OmegaThetaToPiLiHyp

ZeroFreeRegionHyp
    └── ChebyshevErrorBoundZeroFreeHyp
        └── ZetaZeroSupRealPartDichotomyHyp
```

## What Mathlib Provides

Key Mathlib lemmas that help with hypotheses:

1. `riemannZeta_ne_zero_of_one_le_re` - ζ(s) ≠ 0 for Re(s) ≥ 1
2. `riemannZeta_residue_one` - (s-1)ζ(s) → 1 as s → 1
3. `riemannZeta_one_sub` - Functional equation
4. `riemannZeta_conj` - ζ(s̄) = ζ(s)̄
5. `LSeries_analyticOnNhd` - L-series analyticity
6. `completedRiemannZeta_one_sub` - Completed functional equation

## Potential Next Proofs

Based on available Mathlib infrastructure:

1. **ZeroCountingSummabilityHyp** might be provable if we can show density estimates
2. **FirstZeroOrdinateHyp** (γ₁ ≈ 14.13) is computational but could be proved
3. More parametric Landau hypotheses could be instantiated for specific A

## Notes

- The 2 proved hypotheses use Mathlib's functional equation and conjugate symmetry
- Most hypotheses require analytic number theory not yet in Mathlib
- Development files (LandauLemma.lean, ZeroFreeRegion.lean) work toward proving these
- The main theorem chain works with assumptions pending proof
