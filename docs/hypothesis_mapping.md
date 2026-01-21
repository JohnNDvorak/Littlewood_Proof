# Hypothesis to Gauss Mapping

This document maps Littlewood's 67 hypothesis classes to their Gauss (PrimeNumberTheoremAnd) equivalents.

## Summary

| Category | Count | Status |
|----------|-------|--------|
| Direct Matches | ~3 | Can use Gauss theorems directly |
| Derivable | ~5 | Needs wrapper/adaptation |
| Not in Gauss | ~59 | Requires new development |

---

## Direct Matches (can replace immediately)

These hypothesis classes have direct equivalents in Gauss that match semantically.

| Our Hypothesis | Gauss Equivalent | File | Notes |
|----------------|------------------|------|-------|
| `ChebyshevErrorBoundZeroFreeHyp` | `MediumPNT` | MediumPNT.lean:3804 | MediumPNT gives `exp(-c * log^(1/10))` error, slightly weaker than `exp(-c * sqrt(log))` but same class |
| `ZeroFreeRegionHyp` | `riemannZeta.classicalZeroFree` | ZetaDefinitions.lean:52 | Same definition structure |

---

## Derivable (needs wrapper/adaptation)

These can be derived from Gauss with some work.

| Our Hypothesis | Gauss Building Blocks | Notes |
|----------------|----------------------|-------|
| `chebyshevPsi_asymptotic` (theorem) | `WeakPNT''` : `ψ ~[atTop] id` | Direct match - `WeakPNT''` proves `ψ ~[atTop] (fun x => x)` |
| `chebyshevTheta_asymptotic` (theorem) | `chebyshev_asymptotic` : `θ ~[atTop] id` | Direct match |
| `chebyshevTheta_eventually_ge` (theorem) | Derivable from `chebyshev_asymptotic` | Follows from asymptotic |
| `ThetaPsiFirstCorrectionHyp` | `chebyshevPsi_sub_chebyshevTheta_isBigO` | Littlewood already has this bound |
| `ChebyshevErrorBoundThetaHyp` | Derivable from `MediumPNT` + theta relation | Need to compose bounds |

---

## Not in Gauss (need new development)

### Landau Lemma Infrastructure (9 classes)

| Hypothesis | What's Missing |
|------------|----------------|
| `LandauLemmaHyp` | Full Dirichlet series singularity theory |
| `DirichletIntegralConvergesHyp` | Abscissa of convergence theory |
| `DirichletIntegralAnalyticHyp` | Analytic continuation of Dirichlet integrals |
| `DirichletIntegralDerivHyp` | Derivative theory for Dirichlet integrals |
| `DirichletIntegralPowerSeriesHyp` | Power series expansion at singularity |
| `RadiusExceedsAbscissaHyp` | Radius of convergence analysis |
| `LandauExtensionHyp` | Extension beyond abscissa |
| `LandauLemmaSeriesHyp` | Series version |
| `ZetaLogDerivPoleHyp` | -ζ'/ζ has simple pole at 1 |

### Explicit Formula Classes (12 classes)

| Hypothesis | What's Missing |
|------------|----------------|
| `ExplicitFormulaPsiHyp` | Full explicit formula for ψ |
| `ExplicitFormulaPsiSmoothedHyp` | Smoothed version |
| `ExplicitFormulaIntegralHyp` | Integral representation |
| `ExplicitFormulaDoubleIntegralHyp` | Double integral form |
| `PsiMellinHyp` | Mellin transform identity |
| `MellinContourShiftHyp` | Contour shifting lemmas |
| `ZeroSumBoundRHHyp` | RH zero sum bounds |
| `PsiErrorBoundHyp` | General psi error bound |
| `PsiErrorBoundRHHyp` | RH psi error bound |
| `ThetaPsiRHHyp` | RH version of theta-psi relation |
| `PiFromThetaSummationHyp` | π from θ by summation |
| `LiExpansionHyp` | Li expansion |

### Conversion Formulas (6 classes)

| Hypothesis | What's Missing |
|------------|----------------|
| `PiLiFromThetaHyp` | π - li from θ |
| `PiLiFromPsiRHHyp` | π - li from ψ under RH |
| `OmegaPsiToThetaHyp` | Oscillation transfer ψ → θ |
| `OmegaThetaToPiLiHyp` | Oscillation transfer θ → π - li |

### Zero Counting (17 classes)

| Hypothesis | What's Missing |
|------------|----------------|
| `ZeroCountingTendstoHyp` | N(T)/T → ... as T → ∞ |
| `ZeroCountingCrudeBoundHyp` | Crude bound on N(T) |
| `ZeroCountingSpecialValuesHyp` | N(T) at specific heights |
| `ZeroCountingFifteenHyp` | N(T) ≤ 15 for small T |
| `FirstZeroOrdinateHyp` | γ₁ ∈ (14.1, 14.2) |
| `ZeroCountingAsymptoticHyp` | N(T) ~ (T/2π) log(T/2πe) |
| `ZeroCountingRvmExplicitHyp` | Explicit R-vM constants |
| `ZeroCountingAsymptoticRatioHyp` | N(T) ratio limit |
| `ZeroCountingMainTermHyp` | Main term formula |
| `ZeroCountingLowerBoundHyp` | Lower bound on N(T) |
| `ZeroCountingLocalDensityHyp` | Local density estimates |
| `ZeroGapsLowerBoundHyp` | Gap between consecutive zeros |
| `ZeroConjZeroHyp` | ρ zero ⟹ ρ̄ zero |
| `ZeroOneSubZeroHyp` | ρ zero ⟹ 1-ρ zero |
| `ZeroCountingSummabilityHyp` | Summability over zeros |
| `ZeroCountingSumInvGammaAsymptoticHyp` | Sum 1/|γ| asymptotics |
| `ZeroCountingSumOneEqHyp` | Sum identity |

### Zero Density (6 classes)

| Hypothesis | What's Missing |
|------------|----------------|
| `ZeroCountingTailSqAsymptoticHyp` | Tail square sum |
| `RiemannHypothesisInvRhoAsymptoticHyp` | RH inv rho asymptotic |
| `ZeroCountingSummableXPowRhoDivHyp` | x^ρ/ρ summability |
| `ZeroCountingAverageInvGammaHyp` | Average 1/γ |

### Weighted Average / Schmidt (12 classes)

| Hypothesis | What's Missing |
|------------|----------------|
| `WeightedAverageFormulaRHHyp` | RH weighted average |
| `IntegralPsiMinusXHyp` | ∫ψ-x bounds |
| `RhoToGammaErrorHyp` | ρ to γ error terms |
| `SumOverPositiveOrdinatesHyp` | Sums over γ > 0 |
| `ZeroSumTailHyp` | Zero sum tail bounds |
| `MainSumBoundHyp` | Main sum in oscillation |
| `AlignedSumLargeHyp` | Aligned sums large |
| `SchmidtPsiOscillationHyp` | Schmidt's theorem for ψ |
| `PsiOscillationSqrtHyp` | √x oscillation |
| `MellinPsiIdentityHyp` | Mellin identity |
| `OmegaMinusNecessityHyp` | Ω- necessity |
| `OmegaPlusNecessityHyp` | Ω+ necessity |

### Oscillation Results (6 classes)

| Hypothesis | What's Missing |
|------------|----------------|
| `HardyCriticalLineZerosHyp` | Hardy's theorem (infinitely many on critical line) |
| `PsiOscillationFromCriticalZerosHyp` | Oscillation from critical zeros |
| `ThetaOscillationMinusHyp` | θ Ω- oscillation |
| `ThetaOscillationRHHyp` | θ oscillation under RH |

### Supremum Real Part (2 classes)

| Hypothesis | What's Missing |
|------------|----------------|
| `ZetaZeroSupRealPartDichotomyHyp` | Θ = 1 ∨ Θ = 1/2 |

---

## Gauss Theorems Not Matching Any Hypothesis

These Gauss theorems could be useful but don't directly match existing hypotheses:

1. `WeakPNT_AP` - PNT in arithmetic progressions
2. `BorelCaratheodoryDeriv` - derivative bounds from real part
3. Hadamard factorization results
4. Sieve method results (Brun-Titchmarsh)

---

## Recommended Bridge Implementation Order

1. **High Impact, Easy**
   - Use `WeakPNT''` for `chebyshevPsi_asymptotic` (3 sorries in ChebyshevFunctions.lean)
   - Use `chebyshev_asymptotic` for `chebyshevTheta_asymptotic`

2. **Medium Impact, Medium Effort**
   - Adapt `riemannZeta.classicalZeroFree` for `ZeroFreeRegionHyp`
   - Derive `ChebyshevErrorBoundZeroFreeHyp` from `MediumPNT`

3. **Requires Significant New Development**
   - Zero counting machinery
   - Landau lemma infrastructure
   - Schmidt oscillation theorem
