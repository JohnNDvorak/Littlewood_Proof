# Sorry Dependency Analysis

## Dependency Chain

### 1. HardyTheorem.lean (12 sorries)
```
hardyZ_is_real (needs functional equation ξ(s) = ξ(1-s))
    ↓
hardyZ_continuous (needs hardyZ_is_real + continuity composition)
    ↓
sign_change_implies_zero (needs IVT + hardyZ_is_real)
    ↓
hardyZ_sign_change_in_interval (core of Hardy's 1914 proof)
    ↓
hardy_infinitely_many_zeros_stub
```
**Blocks**: HardyCriticalLineZerosHyp instance, indirectly affects oscillation theorems

### 2. LandauLemma.lean (10 sorries)
```
LandauLemmaHyp instances
    ↓
DirichletIntegral*Hyp instances
    ↓
landau_lseries_not_analytic_at_boundary
    ↓
zeta_zero_implies_vonMangoldt_singularity
```
**Blocks**: Detection of zeros via L-series singularities

### 3. ZeroFreeRegion.lean (7 sorries)
```
mertens_inequality_stub (needs Dirichlet char specialization)
    ↓
zeta_product_lower_bound (needs product inequality)
    ↓
zeta_pole_behavior (needs filter coercion ℝ → ℂ)
    ↓
neg_zeta_logderiv_expansion (needs Laurent extraction)
    ↓
de_la_vallee_poussin_zero_free (quantitative region)
```
**Blocks**: ZeroFreeRegionHyp instance, quantitative bounds

### 4. SchmidtTheorem.lean (9 sorries)
All hypothesis instances:
- SchmidtPsiOscillationHyp
- PsiOscillationSqrtHyp
- MellinPsiIdentityHyp
- OmegaMinusNecessityHyp
- OmegaPlusNecessityHyp
- HardyCriticalLineZerosHyp
- PsiOscillationFromCriticalZerosHyp
- ThetaOscillationMinusHyp
- ThetaOscillationRHHyp

**Depends on**: HardyTheorem, Perron's formula, explicit formulas

### 5. WeightedAverageFormula.lean (7 sorries)
All hypothesis instances for weighted average explicit formula machinery.
**Depends on**: Perron's formula, contour integration

### 6. Assumptions.lean (60 sorries)
Master collection of all hypothesis instances.
**Represents**: Deep ANT theorems awaiting Mathlib infrastructure

## Independent Sorries (Can Attack in Parallel)

1. **LaurentExpansion.lean** (2 sorries)
   - neg_zeta_logderiv_laurent
   - neg_zeta_logderiv_pole_residue
   - Independent of Hardy, Landau machinery
   - Needs: MeromorphicAt coefficient extraction

2. **ConversionFormulas.lean** (2 sorries)
   - OmegaPsiToThetaHyp instance
   - OmegaThetaToPiLiHyp instance
   - Could be provable with asymptotic transfer lemmas

3. **TypeBridge.lean** (2 sorries)
   - lseries_real_tendsto_top_of_nonneg_divergent
   - landau_lseries_not_analytic_at_boundary
   - Needs: L-series boundary behavior (partial Landau)

4. **ZetaLogDeriv.lean** (1 sorry)
   - neg_zeta_logderiv_eq_vonMangoldt_series
   - Real-part extraction for LSeries
   - Independent path from main blockers

## Critical Path (Longest Chain)

```
Functional Equation (ξ(s) = ξ(1-s))
    ↓
Hardy's Z-function realness
    ↓
Hardy's Z-function sign changes
    ↓
Hardy's infinitely many critical zeros
    ↓
HardyCriticalLineZerosHyp
    ↓
PsiOscillationFromCriticalZerosHyp
    ↓
SchmidtPsiOscillationHyp
    ↓
Main oscillation theorems
```

**Length**: 8 steps
**Primary Blocker**: Completed functional equation ξ(s) = ξ(1-s)

## Parallel Path (Zero-Free Region)

```
Trigonometric inequality (DONE)
    ↓
Product inequality 3·4·1
    ↓
Pole behavior analysis
    ↓
Quantitative zero-free region
    ↓
ZeroFreeRegionHyp
    ↓
ChebyshevErrorBoundZeroFreeHyp
```

**Length**: 6 steps
**Primary Blocker**: Quantitative constant extraction from 3-4-1 argument

## Summary

| Category | Count | Status |
|----------|-------|--------|
| Hypothesis instances | ~75 | BLOCKED on deep ANT |
| Laurent expansion | 2 | BLOCKED on MeromorphicAt |
| Hardy chain | 12 | BLOCKED on ξ functional eq |
| Landau chain | 10 | BLOCKED on continuation |
| ZFR chain | 7 | BLOCKED on 3-4-1 constants |
| Independent | 5 | Potentially attackable |
