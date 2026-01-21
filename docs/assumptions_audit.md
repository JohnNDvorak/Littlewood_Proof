# Assumptions Audit

## Summary

| Category | Count |
|----------|-------|
| Total sorries | 95 |
| From Gauss (proved) | 0 instances |
| From Gauss (theorems) | 3 |
| Need development | 95 |

## Difficulty Distribution

| Difficulty | Count | Description |
|------------|-------|-------------|
| Easy | 5 | Mathlib has pieces, adaptation needed |
| Medium | 20 | Derivable with moderate effort |
| Hard | 40 | New development required |
| Very Hard | 30 | Research-level mathematics |

---

## Detailed Audit by Domain

### 1. Zero-Free Region Hypotheses

| # | Hypothesis | Mathematical Meaning | Reference | Difficulty |
|---|------------|---------------------|-----------|------------|
| 1 | `ZeroFreeRegionHyp` | de la Vallée Poussin: ∃c>0, zeros satisfy Re(ρ) < 1 - c/log|Im(ρ)|+2 | [MV] Ch.12 | Hard |
| 2 | `ZetaZeroSupRealPartDichotomyHyp` | Θ = 1 or Θ = 1/2 (dichotomy) | [MV] Ch.13 | Medium |
| 3 | `ChebyshevErrorBoundZeroFreeHyp` | \|ψ(x)-x\| ≤ Cx·exp(-c√log x) | [MV] Ch.12 | Hard |
| 4 | `ChebyshevErrorBoundThetaHyp` | \|ψ(x)-x\| ≤ 10x^Θ log x | [MV] Ch.13 | Hard |

### 2. Landau Lemma Hypotheses

| # | Hypothesis | Mathematical Meaning | Reference | Difficulty |
|---|------------|---------------------|-----------|------------|
| 5 | `LandauLemmaHyp` | Non-negative Dirichlet series has singularity at abscissa | [T] Ch.9.5 | Very Hard |
| 6 | `DirichletIntegralConvergesHyp` | ∫₁^∞ A(t)t^{-s-1}dt converges for Re(s) > σ_c | [T] Ch.9 | Hard |
| 7 | `DirichletIntegralAnalyticHyp` | Dirichlet integral is analytic for Re(s) > σ_c | [T] Ch.9 | Hard |
| 8 | `DirichletIntegralDerivHyp` | Derivatives of Dirichlet integral exist | [T] Ch.9 | Hard |
| 9 | `DirichletIntegralPowerSeriesHyp` | Power series expansion at σ_c | [T] Ch.9 | Very Hard |
| 10 | `RadiusExceedsAbscissaHyp` | Radius of convergence exceeds abscissa | [T] Ch.9 | Very Hard |
| 11 | `LandauExtensionHyp` | Extension principle for Dirichlet series | [T] Ch.9 | Very Hard |
| 12 | `LandauLemmaSeriesHyp` | Series version of Landau's lemma | [T] Ch.9 | Very Hard |
| 13 | `ZetaLogDerivPoleHyp` | -ζ'/ζ has simple pole at s=1 | [T] Ch.3 | Medium |

### 3. Explicit Formula Hypotheses

| # | Hypothesis | Mathematical Meaning | Reference | Difficulty |
|---|------------|---------------------|-----------|------------|
| 14 | `ExplicitFormulaPsiHyp` | ψ(x) = x - Σ_ρ x^ρ/ρ + bounded | [MV] Ch.5 | Very Hard |
| 15 | `ExplicitFormulaPsiSmoothedHyp` | Smoothed version with test function | [MV] Ch.5 | Very Hard |
| 16 | `ExplicitFormulaIntegralHyp` | Integral representation | [MV] Ch.5 | Hard |
| 17 | `ExplicitFormulaDoubleIntegralHyp` | Double integral form | [MV] Ch.5 | Hard |
| 18 | `PsiMellinHyp` | Mellin transform identity | [IK] Ch.5 | Hard |
| 19 | `MellinContourShiftHyp` | Contour shifting for Mellin | [IK] Ch.5 | Hard |
| 20 | `ZeroSumBoundRHHyp` | Under RH: Σ x^ρ/ρ bound | [MV] Ch.13 | Hard |
| 21 | `PsiErrorBoundHyp` | General ψ error bound | [MV] Ch.5 | Hard |
| 22 | `PsiErrorBoundRHHyp` | RH ψ error bound | [MV] Ch.13 | Medium |
| 23 | `ThetaPsiFirstCorrectionHyp` | θ = ψ - ψ(√x) + O(x^{1/3}) | [MV] Ch.2 | Medium |
| 24 | `ThetaPsiRHHyp` | RH version of θ-ψ relation | [MV] Ch.13 | Medium |

### 4. Conversion Hypotheses

| # | Hypothesis | Mathematical Meaning | Reference | Difficulty |
|---|------------|---------------------|-----------|------------|
| 25 | `PiFromThetaSummationHyp` | π(x) from θ by summation | [MV] Ch.2 | Medium |
| 26 | `LiExpansionHyp` | li(x) asymptotic expansion | [MV] Ch.2 | Easy |
| 27 | `PiLiFromThetaHyp` | π - li from θ | [MV] Ch.2 | Medium |
| 28 | `PiLiFromPsiRHHyp` | π - li from ψ under RH | [MV] Ch.13 | Medium |
| 29 | `OmegaPsiToThetaHyp` | Ω± transfer ψ → θ | [MV] Ch.15 | Hard |
| 30 | `OmegaThetaToPiLiHyp` | Ω± transfer θ → π - li | [MV] Ch.15 | Hard |

### 5. Zero Counting Hypotheses

| # | Hypothesis | Mathematical Meaning | Reference | Difficulty |
|---|------------|---------------------|-----------|------------|
| 31 | `ZeroCountingTendstoHyp` | N(T)/((T/2π)log(T/2πe)) → 1 | [T] Ch.9 | Medium |
| 32 | `ZeroCountingCrudeBoundHyp` | N(T) = O(T log T) | [T] Ch.9 | Easy |
| 33 | `ZeroCountingSpecialValuesHyp` | N(T) at specific T | [T] Ch.9 | Easy |
| 34 | `ZeroCountingFifteenHyp` | N(T) ≤ 15 for T < 14.5 | [T] Ch.9 | Easy |
| 35 | `FirstZeroOrdinateHyp` | γ₁ ∈ (14.134, 14.135) | Computation | Easy |
| 36 | `ZeroCountingAsymptoticHyp` | N(T) ~ (T/2π)log(T/2πe) | [T] Ch.9 | Hard |
| 37 | `ZeroCountingRvmExplicitHyp` | Riemann-von Mangoldt explicit | [T] Ch.9 | Hard |
| 38 | `ZeroCountingAsymptoticRatioHyp` | Asymptotic ratio | [T] Ch.9 | Medium |
| 39 | `ZeroCountingMainTermHyp` | Main term formula | [T] Ch.9 | Medium |
| 40 | `ZeroCountingLowerBoundHyp` | Lower bounds on N(T) | [T] Ch.9 | Medium |
| 41 | `ZeroCountingLocalDensityHyp` | Local density estimates | [T] Ch.9 | Hard |
| 42 | `ZeroGapsLowerBoundHyp` | γ_{n+1} - γ_n lower bound | [T] Ch.9 | Hard |
| 43 | `ZeroConjZeroHyp` | ρ zero ⟹ ρ̄ zero | [T] Ch.2 | Medium |
| 44 | `ZeroOneSubZeroHyp` | ρ zero ⟹ 1-ρ zero | [T] Ch.2 | Medium |

### 6. Zero Density Hypotheses

| # | Hypothesis | Mathematical Meaning | Reference | Difficulty |
|---|------------|---------------------|-----------|------------|
| 45 | `ZeroCountingSummabilityHyp` | Summability over zeros | [MV] Ch.10 | Hard |
| 46 | `ZeroCountingSumInvGammaAsymptoticHyp` | Σ 1/\|γ\| asymptotic | [MV] Ch.10 | Hard |
| 47 | `ZeroCountingSumOneEqHyp` | Sum identity | [MV] Ch.10 | Hard |
| 48 | `ZeroCountingTailSqAsymptoticHyp` | Tail square sum | [MV] Ch.10 | Hard |
| 49 | `RiemannHypothesisInvRhoAsymptoticHyp` | Under RH: Σ 1/ρ asymptotic | [MV] Ch.13 | Medium |
| 50 | `ZeroCountingSummableXPowRhoDivHyp` | x^ρ/ρ summability | [MV] Ch.10 | Hard |
| 51 | `ZeroCountingAverageInvGammaHyp` | Average 1/γ | [MV] Ch.10 | Hard |

### 7. Weighted Average Hypotheses

| # | Hypothesis | Mathematical Meaning | Reference | Difficulty |
|---|------------|---------------------|-----------|------------|
| 52 | `WeightedAverageFormulaRHHyp` | Weighted average under RH | [MV] Ch.15 | Very Hard |
| 53 | `IntegralPsiMinusXHyp` | ∫(ψ-x) bounds | [MV] Ch.15 | Hard |
| 54 | `RhoToGammaErrorHyp` | ρ to γ error terms | [MV] Ch.15 | Hard |
| 55 | `SumOverPositiveOrdinatesHyp` | Sums over γ > 0 | [MV] Ch.15 | Hard |
| 56 | `ZeroSumTailHyp` | Zero sum tail bounds | [MV] Ch.15 | Hard |
| 57 | `MainSumBoundHyp` | Main sum control | [MV] Ch.15 | Very Hard |
| 58 | `AlignedSumLargeHyp` | Diophantine alignment | [MV] Ch.15 | Very Hard |

### 8. Schmidt/Oscillation Hypotheses

| # | Hypothesis | Mathematical Meaning | Reference | Difficulty |
|---|------------|---------------------|-----------|------------|
| 59 | `SchmidtPsiOscillationHyp` | ψ-x = Ω±(√x logloglog x) | Schmidt 1983 | Very Hard |
| 60 | `PsiOscillationSqrtHyp` | √x oscillation magnitude | Schmidt 1983 | Very Hard |
| 61 | `MellinPsiIdentityHyp` | Mellin transform identity | [IK] Ch.5 | Hard |
| 62 | `OmegaMinusNecessityHyp` | Ω- necessity from zeros | Schmidt 1983 | Very Hard |
| 63 | `OmegaPlusNecessityHyp` | Ω+ necessity from zeros | Schmidt 1983 | Very Hard |
| 64 | `HardyCriticalLineZerosHyp` | Hardy: infinitely many on Re=1/2 | Hardy 1914 | Very Hard |
| 65 | `PsiOscillationFromCriticalZerosHyp` | Oscillation from critical zeros | [MV] Ch.15 | Very Hard |
| 66 | `ThetaOscillationMinusHyp` | θ Ω- results | [MV] Ch.15 | Very Hard |
| 67 | `ThetaOscillationRHHyp` | θ oscillation under RH | [MV] Ch.13 | Hard |

---

## Reference Key

- **[MV]**: Montgomery & Vaughan, "Multiplicative Number Theory I" (2007)
- **[T]**: Titchmarsh, "Theory of the Riemann Zeta Function" (1986)
- **[IK]**: Iwaniec & Kowalski, "Analytic Number Theory" (2004)
- **Hardy 1914**: Hardy, "Sur les zéros de la fonction ζ(s)"
- **Schmidt 1983**: Schmidt, "Über die Anzahl der Primzahlen..."

---

## Priority Recommendations

### Highest Priority (Foundation)
1. `ZetaLogDerivPoleHyp` - Entry point for Landau theory
2. `ZeroConjZeroHyp`, `ZeroOneSubZeroHyp` - Basic symmetries
3. `ZeroCountingCrudeBoundHyp` - Foundation for density
4. `LiExpansionHyp` - Elementary, useful

### Medium Priority (Infrastructure)
5-20. Landau family, Zero counting asymptotics

### Lower Priority (Research-Level)
21-67. Schmidt, Hardy, Explicit formula machinery
