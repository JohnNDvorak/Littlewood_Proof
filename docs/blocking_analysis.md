# Blocking Analysis: Path to Removing All Sorries

Last updated: 2026-01-21 (Task 34)

## Executive Summary

| Metric | Count |
|--------|-------|
| Total sorries | 117 |
| Assumption sorries | 61 |
| Development sorries | 20 |
| Other sorries | 36 |
| **BLOCKED** (all require Mathlib extensions) | 117 |
| **Tractable with current Mathlib** | 0 |

**Conclusion:** All remaining sorries require mathematical infrastructure not present in Mathlib 2026.

## Blocker Categories

### Category A: Euler Product Infrastructure (BLOCKS 12+ hypotheses)

**What's Missing:**
- Euler product expansion in critical strip (0 < Re(s) < 1)
- Log of Euler product: log ζ(s) = Σ_p Σ_k p^(-ks)/k
- Logarithmic derivative: -ζ'/ζ(s) = Σ Λ(n) n^(-s)

**What Mathlib Has:**
- `riemannZeta : ℂ → ℂ` - basic definition
- `riemannZeta_ne_zero_of_one_lt_re` - non-vanishing for Re(s) > 1
- `differentiableAt_riemannZeta` - differentiability away from s=1

**Blocked Hypotheses:**
- `ZeroFreeRegionHyp`
- `ZetaLogDerivPoleHyp`
- `ZetaZeroSupRealPartDichotomyHyp`
- `ChebyshevErrorBoundZeroFreeHyp`
- All Development/ZeroFreeRegion.lean sorries (8)

**Dependency Chain:**
```
Euler Product Log
    ↓
-ζ'/ζ expansion
    ↓
Mertens inequality (3 + 4cos + cos2θ ≥ 0 applied)
    ↓
de_la_vallee_poussin_zero_free
    ↓
ZeroFreeRegionHyp
```

### Category B: Contour Integration / Perron's Formula (BLOCKS 15+ hypotheses)

**What's Missing:**
- Perron's formula: ψ(x) = (1/2πi) ∫ -ζ'/ζ(s) x^s/s ds
- Contour shifting techniques
- Residue calculus for analytic number theory applications

**What Mathlib Has:**
- Basic complex integration
- Some residue theory
- `riemannZeta_residue_one` - residue at s=1

**Blocked Hypotheses:**
- `ExplicitFormulaPsiHyp`
- `ExplicitFormulaPsiSmoothedHyp`
- `ExplicitFormulaIntegralHyp`
- `ExplicitFormulaDoubleIntegralHyp`
- `PsiMellinHyp`
- `MellinContourShiftHyp`
- `PsiErrorBoundHyp`
- `PsiErrorBoundRHHyp`
- `MellinPsiIdentityHyp`
- All weighted average hypotheses (7)

### Category C: Zero Counting / Argument Principle (BLOCKS 17 hypotheses)

**What's Missing:**
- Argument principle for analytic functions
- Jensen's formula
- Zero counting machinery for meromorphic functions
- N(T) ~ (T/2π) log(T/2πe) asymptotic

**What Mathlib Has:**
- Basic Cauchy integral formula
- Limited argument principle infrastructure

**Blocked Hypotheses:**
- All 12 `ZeroCountingXxxHyp` variants
- `ZeroCountingSummabilityHyp`
- `ZeroCountingSumInvGammaAsymptoticHyp`
- `ZeroCountingTailSqAsymptoticHyp`
- `ZeroCountingLocalDensityHyp`
- `ZeroGapsLowerBoundHyp`

### Category D: Hardy's Theorem / Critical Line Zeros (BLOCKS 4+ hypotheses)

**What's Missing:**
- Functional equation phase analysis (ξ(s) = ξ(1-s))
- Riemann-Siegel theta function asymptotics
- Hardy Z-function sign change detection
- Gamma function slitPlane membership proofs

**What Mathlib Has:**
- `Complex.Gamma : ℂ → ℂ`
- `Complex.continuousAt_arg` (requires slitPlane)
- `riemannZeta_one_sub` (functional equation)
- `completedRiemannZeta_one_sub`

**Blocked Hypotheses:**
- `HardyCriticalLineZerosHyp`
- `PsiOscillationFromCriticalZerosHyp`
- `ThetaOscillationMinusHyp`
- `ThetaOscillationRHHyp`
- All Development/HardyTheorem.lean sorries (12)

**Key Technical Blocker:**
```lean
-- We need to prove:
theorem hardyZ_continuous : Continuous hardyZ
-- Which requires:
-- Gamma(1/4 + t/2 * I) ∈ slitPlane for all real t
-- This is non-trivial: Gamma maps to all of ℂ, including negative reals
```

### Category E: Landau Lemma / Dirichlet Series (BLOCKS 9 parametric hypotheses)

**What's Missing:**
- Bridge between `LSeries` and `dirichletIntegral`
- Singularity-at-boundary theorems
- Tauberian-type results

**What Mathlib Has:**
- `LSeries : (ℕ → ℂ) → ℂ → ℂ`
- `LSeries.abscissaOfAbsConv`
- `LSeries_analyticOnNhd`

**Type Mismatch Problem:**
```
Development/LandauLemma.lean works with:
  LSeries f s = ∑' n, f n * n^{-s}

CoreLemmas/LandauLemma.lean hypotheses expect:
  dirichletIntegral A s = ∫ x in Ioi 1, A(x) * x^{-s} dx

Gap: No theorem connecting these representations
```

**Blocked Hypotheses:**
- `LandauLemmaHyp A σ_c` (parametric)
- `DirichletIntegralConvergesHyp A σ_c`
- `DirichletIntegralAnalyticHyp A σ_c`
- `DirichletIntegralDerivHyp A σ_c`
- `DirichletIntegralPowerSeriesHyp A σ_c`
- `RadiusExceedsAbscissaHyp A σ_c`
- `LandauExtensionHyp A σ₀`
- `LandauLemmaSeriesHyp a σ_c`
- `ZetaLogDerivPoleHyp`

## Sorries by File

### Assumptions.lean (61 sorries)

| Section | Count | Primary Blocker |
|---------|-------|-----------------|
| Explicit Formula | 11 | Perron's formula |
| Weighted Average | 7 | Contour integration |
| Schmidt/Oscillation | 9 | Hardy's theorem |
| Zero Density | 6 | Zero counting |
| Zero-Free Region | 4 | Euler product |
| Zero Counting | 12 | Argument principle |
| Landau Lemma | 12 | Dirichlet series bridge |

### Development Files (20 sorries)

| File | Sorries | Primary Blocker |
|------|---------|-----------------|
| ZeroFreeRegion.lean | 8 | Euler product log |
| HardyTheorem.lean | 12 | slitPlane membership |

### Other Files (36 sorries)

Various module files with hypotheses that propagate from Assumptions.lean.

## Critical Path Analysis

### Path 1: Zero-Free Region → Oscillation (Shortest)

```
[NEED] Euler product infrastructure
    ↓
[PROVE] zeta_product_lower_bound (Development)
    ↓
[PROVE] de_la_vallee_poussin_zero_free (Development)
    ↓
[FILL] ZeroFreeRegionHyp
    ↓
[ENABLES] ZetaZeroSupRealPartDichotomyHyp
    ↓
[ENABLES] Part of oscillation machinery
```

**Estimated effort:** 80-150 hours
**Mathlib PRs needed:** 2-3 (Euler product, log derivative)

### Path 2: Explicit Formula → Full Oscillation (Medium)

```
[NEED] Perron's formula
    ↓
[PROVE] ExplicitFormulaPsiHyp
    ↓
[PROVES] Error bounds
    ↓
[ENABLES] Weighted average machinery
    ↓
[ENABLES] Schmidt oscillation
```

**Estimated effort:** 150-250 hours
**Mathlib PRs needed:** 3-5 (contour integration, Perron)

### Path 3: Hardy's Theorem → Critical Line (Long)

```
[NEED] Gamma slitPlane analysis
    ↓
[PROVE] hardyZ_continuous (Development)
    ↓
[PROVE] hardyZ_is_real (Development)
    ↓
[PROVE] sign change detection
    ↓
[FILL] HardyCriticalLineZerosHyp
    ↓
[ENABLES] Critical line oscillation results
```

**Estimated effort:** 200-400 hours
**Mathlib PRs needed:** 4-6 (Stirling, functional equation analysis)

### Path 4: Zero Counting (Foundation)

```
[NEED] Argument principle for meromorphic functions
    ↓
[NEED] Jensen's formula
    ↓
[PROVE] N(T) asymptotic
    ↓
[FILL] ZeroCountingAsymptoticHyp
    ↓
[ENABLES] All zero density results
```

**Estimated effort:** 100-200 hours
**Mathlib PRs needed:** 3-4 (argument principle, Jensen)

## What CANNOT Be Unblocked Without Mathlib Work

1. **Everything in Category A** - Euler product is fundamental
2. **Everything in Category B** - Perron/Mellin required
3. **Everything in Category C** - Zero counting required
4. **Everything in Category D** - Gamma analysis required
5. **Everything in Category E** - Type bridge required

## Potential Shortcuts (Not Recommended)

1. **Axiomatize Euler product** - Add as hypothesis class
   - Pros: Unblocks zero-free region path
   - Cons: Moves goalposts, doesn't reduce total assumptions

2. **Axiomatize Perron's formula** - Add as hypothesis class
   - Pros: Unblocks explicit formula path
   - Cons: Core mathematical content becomes assumed

3. **Axiomatize zero counting** - Add N(T) ~ formula
   - Pros: Unblocks density results
   - Cons: Circular with some current hypotheses

## Recommendations

### Near-term (1-2 months)

1. **Focus on documentation and architecture** - Current state is well-organized
2. **Track Mathlib developments** - Euler product work may appear
3. **Contribute to Mathlib** - Prioritize argument principle

### Medium-term (3-6 months)

1. **Develop Euler product infrastructure** - High leverage
2. **Collaborate with Gauss project** - Overlapping zero-free region work
3. **Build Jensen's formula** - Foundation for zero counting

### Long-term (6-12 months)

1. **Perron's formula** - Opens explicit formula path
2. **Hardy's theorem analysis** - Complex but valuable
3. **Complete zero counting** - Enables density results

## Conclusion

The Littlewood formalization is architecturally sound but fundamentally blocked by missing Mathlib infrastructure. All 117 sorries trace back to 5 core mathematical gaps:

1. Euler product logarithm
2. Perron's formula / contour integration
3. Argument principle / zero counting
4. Hardy Z-function analysis
5. LSeries ↔ dirichletIntegral bridge

Progress requires either:
- Contributing these to Mathlib (preferred)
- Creating project-local infrastructure (significant work)
- Accepting the current hypothesis-driven architecture as the endpoint
