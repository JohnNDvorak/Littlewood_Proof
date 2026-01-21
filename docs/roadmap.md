# Littlewood Formalization Roadmap

## Current Status

| Metric | Count |
|--------|-------|
| Theorem sorries | 0 (fixed via Gauss) |
| Instance sorries | 94 |
| Proved from Gauss | 3 theorems |
| Need development | ~67 hypotheses |

## Dependency Analysis

The 67 hypothesis classes fall into these families:

| Family | Hypotheses | Dependencies |
|--------|------------|--------------|
| Landau Lemma | 9 | Foundation (none) |
| Zero Counting | 17 | Landau partial |
| Zero Density | 6 | Zero Counting |
| Explicit Formula | 12 | Landau, Zero Counting |
| Supremum/Error | 4 | Zero Counting, Explicit |
| Schmidt/Oscillation | 12 | All above |
| Conversion | 7 | Schmidt, Explicit |

---

## Development Phases

### Phase 1: Landau Lemma Family
**Unlocks:** 9 hypotheses, enables Phases 2-4
**Estimated effort:** 60-120 hours
**What's needed:**
- Dirichlet series analyticity in Mathlib
- Abscissa of convergence theory
- Singularity detection for non-negative series
- Power series expansion at boundary

**Hypotheses in this family:**
1. `LandauLemmaHyp` - Core lemma
2. `DirichletIntegralConvergesHyp` - Convergence above abscissa
3. `DirichletIntegralAnalyticHyp` - Analytic in half-plane
4. `DirichletIntegralDerivHyp` - Derivatives exist
5. `DirichletIntegralPowerSeriesHyp` - Power series at σ_c
6. `RadiusExceedsAbscissaHyp` - Radius > σ_c implies extension
7. `LandauExtensionHyp` - Extension principle
8. `LandauLemmaSeriesHyp` - Series version
9. `ZetaLogDerivPoleHyp` - -ζ'/ζ pole structure

**Key Mathlib gaps:**
- `LSeries.abscissaOfAbsConv` exists but not `abscissaOfConv`
- No singularity-at-boundary theorems
- Limited Dirichlet series → analytic function bridge

---

### Phase 2: Zero Counting Machinery
**Unlocks:** 17 hypotheses
**Estimated effort:** 40-80 hours
**Dependencies:** Phase 1 partial

**Hypotheses in this family:**
1. `ZeroCountingTendstoHyp` - N(T)/T behavior
2. `ZeroCountingCrudeBoundHyp` - N(T) = O(T log T)
3. `ZeroCountingSpecialValuesHyp` - Specific T values
4. `ZeroCountingFifteenHyp` - N(T) ≤ 15 for T < 14.5
5. `FirstZeroOrdinateHyp` - γ₁ ∈ (14.1, 14.2)
6. `ZeroCountingAsymptoticHyp` - N(T) ~ (T/2π) log(T/2πe)
7. `ZeroCountingRvmExplicitHyp` - Riemann-von Mangoldt explicit
8. `ZeroCountingAsymptoticRatioHyp` - Ratio convergence
9. `ZeroCountingMainTermHyp` - Main term formula
10. `ZeroCountingLowerBoundHyp` - Lower bounds
11. `ZeroCountingLocalDensityHyp` - Local density
12. `ZeroGapsLowerBoundHyp` - Gap lower bounds
13. `ZeroConjZeroHyp` - ρ zero ⟹ ρ̄ zero
14. `ZeroOneSubZeroHyp` - ρ zero ⟹ 1-ρ zero
15. `ZeroCountingSummabilityHyp` - Summability
16. `ZeroCountingSumInvGammaAsymptoticHyp` - Σ 1/|γ| asymptotic
17. `ZeroCountingSumOneEqHyp` - Sum identity

**Key Mathlib gaps:**
- Zero set representation needs enhancement
- Argument principle connections missing
- Jensen's formula infrastructure partial

---

### Phase 3: Hardy's Theorem (Critical Line Zeros)
**Unlocks:** ~4 hypotheses directly, enables Phase 4
**Estimated effort:** 100-200 hours
**Dependencies:** Phases 1-2

**Hypotheses:**
1. `HardyCriticalLineZerosHyp` - Infinitely many zeros on Re=1/2
2. `PsiOscillationFromCriticalZerosHyp` - Oscillation from critical zeros
3. `ThetaOscillationMinusHyp` - θ Ω- results
4. `ThetaOscillationRHHyp` - θ oscillation under RH

**What's needed:**
- Hardy's 1914 theorem: infinitely many zeros on critical line
- Connection to oscillation via explicit formula
- Sign change arguments from zero locations

**Key insight:** This is research-level difficulty. Hardy's theorem requires:
- Detailed Riemann-Siegel formula
- Careful analysis of Z(t) function
- Sophisticated complex analysis

---

### Phase 4: Schmidt Oscillation
**Unlocks:** ~12 hypotheses
**Estimated effort:** 150-300 hours
**Dependencies:** Phases 1-3

**Hypotheses:**
1. `SchmidtPsiOscillationHyp` - Core oscillation
2. `PsiOscillationSqrtHyp` - √x magnitude
3. `MellinPsiIdentityHyp` - Mellin identity
4. `OmegaMinusNecessityHyp` - Ω- necessity
5. `OmegaPlusNecessityHyp` - Ω+ necessity
6. `WeightedAverageFormulaRHHyp` - Weighted average under RH
7. `IntegralPsiMinusXHyp` - ∫(ψ-x) bounds
8. `RhoToGammaErrorHyp` - Error terms
9. `SumOverPositiveOrdinatesHyp` - Sums over γ > 0
10. `ZeroSumTailHyp` - Tail bounds
11. `MainSumBoundHyp` - Main sum control
12. `AlignedSumLargeHyp` - Diophantine alignment

**What's needed:**
- Full explicit formula implementation
- Contour integration machinery
- Dirichlet approximation for alignment arguments
- Connection between zeros and sign changes

---

### Phase 5: Explicit Formula and Conversion
**Unlocks:** Remaining ~19 hypotheses
**Estimated effort:** 80-150 hours
**Dependencies:** Phases 1-4 partial

**Hypotheses:**
- ExplicitFormulaPsiHyp, ExplicitFormulaPsiSmoothedHyp
- ExplicitFormulaIntegralHyp, ExplicitFormulaDoubleIntegralHyp
- PsiMellinHyp, MellinContourShiftHyp
- ZeroSumBoundRHHyp, PsiErrorBoundHyp, PsiErrorBoundRHHyp
- ThetaPsiFirstCorrectionHyp, ThetaPsiRHHyp
- PiFromThetaSummationHyp, LiExpansionHyp
- PiLiFromThetaHyp, PiLiFromPsiRHHyp
- OmegaPsiToThetaHyp, OmegaThetaToPiLiHyp
- Zero supremum hypotheses (4)

---

### Phase 6: Final Cleanup
**Unlocks:** Complete verification
**Estimated effort:** 40-80 hours
**Dependencies:** All above

- Verify all hypotheses satisfied
- Clean up proof structure
- Documentation
- Potential Mathlib contribution prep

---

## Dependency Graph

```
Phase 1 (Landau Lemma)
    │
    ├──────────────────────┐
    ▼                      ▼
Phase 2 (Zero Counting)    Phase 5 partial
    │                      (Explicit Formula)
    ├──────────┐           │
    ▼          ▼           │
Phase 3       Phase 5      │
(Hardy)       continued    │
    │          │           │
    └────┬─────┘           │
         ▼                 │
    Phase 4 (Schmidt) ◄────┘
         │
         ▼
    Phase 6 (Cleanup)
```

---

## Timeline Estimates

| Phase | Weeks | Cumulative |
|-------|-------|------------|
| Phase 1 (Landau) | 3-6 | 3-6 |
| Phase 2 (Zero Counting) | 2-4 | 5-10 |
| Phase 3 (Hardy) | 5-10 | 10-20 |
| Phase 4 (Schmidt) | 8-15 | 18-35 |
| Phase 5 (Explicit) | 4-8 | 22-43 |
| Phase 6 (Cleanup) | 2-4 | 24-47 |

**Total: 6-12 months** for a dedicated contributor

---

## External Dependencies

### From Gauss (PrimeNumberTheoremAnd)
Currently provides:
- WeakPNT'': ψ ~ x
- chebyshev_asymptotic: θ ~ x
- MediumPNT: exp(-c log^(1/10)) error

Blocked by Gauss sorries:
- ZeroInequality
- MT_theorem_1 (classicalZeroFree)

### From Mathlib
Needed but missing:
- Better Dirichlet series analyticity
- Argument principle for zeros
- Jensen's formula
- Singularity classification

---

## Recommendations

1. **Start with Phase 1**: Landau lemma is foundational and has clearest Mathlib gaps
2. **Parallel Phase 2**: Zero counting can proceed alongside Phase 1
3. **Contribute to Mathlib**: Some infrastructure would benefit the community
4. **Consider Gauss collaboration**: Their zero-free region work overlaps significantly
5. **Document blocking gaps**: Track what Mathlib PRs would help most
