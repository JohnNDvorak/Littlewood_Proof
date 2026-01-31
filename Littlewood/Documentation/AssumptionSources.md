# Assumption Class → Source Mapping

## Summary

Of the 58 hypothesis class instances in `Assumptions.lean`:
- **0** have unconditional Aristotle sources that can directly satisfy them
- **1** has partial infrastructure (`ZeroFreeRegionHyp` — 3-4-1 inequality proved but not the full zero-free region)
- **57** have no unconditional source

## Root Causes

1. **Type incompatibility**: Aristotle files define local types (`chebyshevPsi`, `NZeros`, etc.) incompatible with canonical project types
2. **Trivial proofs**: Many Aristotle ∃C results use C = LHS/RHS (vacuous)
3. **Conditional results**: Strongest results (RVM, oscillation) are conditional on unproved sub-hypotheses
4. **Missing core machinery**: No Aristotle file proves Perron's formula, Mellin inversion, zero density, or Landau's lemma

## Difficulty Breakdown

| Difficulty | Count | Examples |
|-----------|------:|---------|
| Trivial | 1 | `RiemannHypothesisInvRhoAsymptoticHyp` |
| Moderate | 10 | `OmegaPsiToThetaHyp`, `DirichletIntegralConvergesHyp`, `ZetaLogDerivPoleHyp` |
| Moderate (computational) | 3 | `ZeroCountingSpecialValuesHyp`, `ZeroCountingFifteenHyp`, `FirstZeroOrdinateHyp` |
| Hard classical | 21 | `ZeroCountingSummabilityHyp`, `DirichletIntegralAnalyticHyp` |
| Very deep | 23 | `ExplicitFormulaPsiHyp`, `HardyCriticalLineZerosHyp`, `ZeroFreeRegionHyp` |

## Detailed Table

### Section 1: Explicit Formula (11 assumptions)

| # | Class | Difficulty | Aristotle Source? | Notes |
|---|-------|-----------|-------------------|-------|
| 1 | `ExplicitFormulaPsiHyp` | Very deep | NO | Need Perron + contour integration |
| 2 | `ExplicitFormulaPsiSmoothedHyp` | Very deep | NO | Need smoothed explicit formula |
| 3 | `ExplicitFormulaIntegralHyp` | Hard | NO | Need integrated explicit formula |
| 4 | `ExplicitFormulaDoubleIntegralHyp` | Hard | NO | Need double-integrated formula |
| 5 | `PsiMellinHyp` | Very deep | NO | Need Mellin inversion |
| 6 | `MellinContourShiftHyp` | Very deep | NO | Need residue theorem in strips |
| 7 | `ZeroSumBoundRHHyp` | Hard | NO | Need RH + zero density |
| 8 | `PsiErrorBoundHyp` | Hard | NO | Need explicit formula + Theta |
| 9 | `PsiErrorBoundRHHyp` | Hard | NO | RH specialization of #8 |
| 10 | `OmegaPsiToThetaHyp` | Moderate | NO | Transfer via ψ-θ = O(√x log x) |
| 11 | `OmegaThetaToPiLiHyp` | Moderate | NO | Partial summation π ↔ θ |

### Section 2: Weighted Average (7 assumptions)

| # | Class | Difficulty | Aristotle Source? | Notes |
|---|-------|-----------|-------------------|-------|
| 12 | `WeightedAverageFormulaRHHyp` | Very deep | NO | Fejér kernel + zero sum under RH |
| 13 | `IntegralPsiMinusXHyp` | Hard | NO | Integrated explicit formula |
| 14 | `RhoToGammaErrorHyp` | Moderate | NO | 1/ρ - 1/(iγ) = O(1/γ²) under RH |
| 15 | `SumOverPositiveOrdinatesHyp` | Moderate | NO | Conjugate pairing of zeros |
| 16 | `ZeroSumTailHyp` | Hard | NO | Tail bound via N(T) |
| 17 | `MainSumBoundHyp` | Hard | NO | Zero density bound |
| 18 | `AlignedSumLargeHyp` | Very deep | PARTIAL | Dirichlet approx proved; alignment not |

### Section 3: Schmidt/Oscillation (9 assumptions)

| # | Class | Difficulty | Aristotle Source? | Notes |
|---|-------|-----------|-------------------|-------|
| 19 | `SchmidtPsiOscillationHyp` | Very deep | NO | Schmidt 1903 via Landau lemma |
| 20 | `PsiOscillationSqrtHyp` | Very deep | NO | Needs Hardy + Schmidt |
| 21 | `MellinPsiIdentityHyp` | Hard | NO | Mellin transform of ψ-x |
| 22 | `OmegaMinusNecessityHyp` | Hard | NO | Landau lemma contradiction |
| 23 | `OmegaPlusNecessityHyp` | Hard | NO | Landau lemma contradiction |
| 24 | `HardyCriticalLineZerosHyp` | Very deep | NO | **THE critical gap** |
| 25 | `PsiOscillationFromCriticalZerosHyp` | Hard | NO | Critical zeros → ψ oscillation |
| 26 | `ThetaOscillationMinusHyp` | Hard | NO | θ omega-minus |
| 27 | `ThetaOscillationRHHyp` | Very deep | NO | θ oscillation under RH |

### Section 4: Zero Density (6 assumptions)

| # | Class | Difficulty | Aristotle Source? | Notes |
|---|-------|-----------|-------------------|-------|
| 28 | `ZeroCountingSummabilityHyp` | Hard | NO | Needs N(T) asymptotics |
| 29 | `ZeroCountingSumInvGammaAsymptoticHyp` | Hard | NO | Partial summation from N(T) |
| 30 | `ZeroCountingSumOneEqHyp` | Moderate | NO | Tautological but needs formal bijection |
| 31 | `ZeroCountingTailSqAsymptoticHyp` | Hard | NO | Tail of Σ1/γ² |
| 32 | `RiemannHypothesisInvRhoAsymptoticHyp` | Trivial | NO | |ρ| ≥ |γ| under RH |
| 33 | `ZeroCountingSummableXPowRhoDivHyp` | Moderate | NO | Comparison with Σ1/|ρ| |

### Section 5: Zeta Zero Supremum (4 assumptions)

| # | Class | Difficulty | Aristotle Source? | Notes |
|---|-------|-----------|-------------------|-------|
| 34 | `ZeroFreeRegionHyp` | Very deep | PARTIAL | 3-4-1 proved; full region not |
| 35 | `ZetaZeroSupRealPartDichotomyHyp` | Hard | NO | Θ=1 or Θ=1/2 |
| 36 | `ChebyshevErrorBoundZeroFreeHyp` | Very deep | NO | exp(-c√log x) PNT error |
| 37 | `ChebyshevErrorBoundThetaHyp` | Hard | NO | Same as PsiErrorBoundHyp |

### Section 6: Zero Counting (12 assumptions)

| # | Class | Difficulty | Aristotle Source? | Notes |
|---|-------|-----------|-------------------|-------|
| 38 | `ZeroCountingTendstoHyp` | Hard | NO | N(T) → ∞ |
| 39 | `ZeroCountingCrudeBoundHyp` | Hard | NO | N(T) ≤ CT log T |
| 40 | `ZeroCountingSpecialValuesHyp` | Moderate (comp) | NO | N(14) = 0 |
| 41 | `ZeroCountingFifteenHyp` | Moderate (comp) | NO | N(15) = 1 |
| 42 | `FirstZeroOrdinateHyp` | Moderate (comp) | NO | 14.13 < γ₁ < 14.14 |
| 43 | `ZeroCountingAsymptoticHyp` | Very deep | CONDITIONAL | RVM conditional on 3 hypotheses |
| 44 | `ZeroCountingRvmExplicitHyp` | Very deep | CONDITIONAL | Same |
| 45 | `ZeroCountingAsymptoticRatioHyp` | Very deep | NO | N(T)/main → 1 |
| 46 | `ZeroCountingMainTermHyp` | Very deep | CONDITIONAL | Conditional on RVM |
| 47 | `ZeroCountingLowerBoundHyp` | Hard | NO | N(T) ≥ T/(3π) log T |
| 48 | `ZeroCountingLocalDensityHyp` | Hard | NO | Local density |
| 49 | `ZeroGapsLowerBoundHyp` | Hard | NO | Gap bound |

### Section 7: Landau Lemma (9 assumptions)

| # | Class | Difficulty | Aristotle Source? | Notes |
|---|-------|-----------|-------------------|-------|
| 50 | `LandauLemmaHyp` | Very deep | NO | Pringsheim singularity argument |
| 51 | `DirichletIntegralConvergesHyp` | Moderate | NO | Dominated convergence |
| 52 | `DirichletIntegralAnalyticHyp` | Hard | NO | Parametric integral analyticity |
| 53 | `DirichletIntegralDerivHyp` | Hard | NO | Differentiation under integral |
| 54 | `DirichletIntegralPowerSeriesHyp` | Moderate | NO | Corollary of analyticity |
| 55 | `RadiusExceedsAbscissaHyp` | Very deep | NO | Heart of Landau's lemma |
| 56 | `LandauExtensionHyp` | Hard | NO | Generalized radius argument |
| 57 | `LandauLemmaSeriesHyp` | Very deep | NO | Discrete Landau lemma |
| 58 | `ZetaLogDerivPoleHyp` | Moderate | NO | -ζ'/ζ pole at zeros |

## Relevant Unconditional Aristotle Infrastructure

These are genuine, sorry-free theorems that provide *partial progress* toward assumption classes:

| Aristotle Theorem | File | Relevant To |
|-------------------|------|-------------|
| `zeta_product_ge_one` | ThreeFourOne | `ZeroFreeRegionHyp` (#34) |
| `three_four_one_inequality` | ThreeFourOne | `ZeroFreeRegionHyp` (#34) |
| `trigPoly_zero_iff_coeffs_zero` | SchmidtNew | `SchmidtPsiOscillationHyp` (#19) |
| `schmidt_oscillation` | SchmidtNew | `SchmidtPsiOscillationHyp` (#19) |
| `simultaneous_dirichlet_approx` | CriticalZeros | `AlignedSumLargeHyp` (#18) |
| `S_T_bound_uniform` | RiemannVonMangoldt | `ZeroCountingAsymptoticHyp` (#43) |
| `riemann_von_mangoldt_reduction` | RiemannVonMangoldt | `ZeroCountingAsymptoticHyp` (#43) |
| `partial_sums_mono` | LandauLemma (Aristotle) | `LandauLemmaHyp` (#50) |
| `completedRiemannZeta_real_on_critical_line` | HardyZReal | `HardyCriticalLineZerosHyp` (#24) |
| `hardyZV4_real` | HardyZRealV4 | `HardyCriticalLineZerosHyp` (#24) |
| `continuous_hardyZV2` | HardyZRealV2 | `HardyCriticalLineZerosHyp` (#24) |
