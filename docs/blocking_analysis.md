# Blocking Analysis: Path to Removing All Sorries

Last updated: 2026-01-21 (Task 44)

## Executive Summary

| Metric | Count | Notes |
|--------|-------|-------|
| Total sorries | ~110 | Reduced from 117 |
| Assumption sorries | ~55 | Reduced from 61 |
| Development sorries | 20 | Unchanged |
| Other sorries | ~35 | |
| **BLOCKED** (require Mathlib extensions) | ~100 | Reduced! |
| **Tractable with current Mathlib** | ~10 | NEW! |

**Major Update (Task 44):** Gap #1 (Euler Product) has been dramatically reduced!
Mathlib now has comprehensive Euler product infrastructure including non-vanishing on Re(s) ≥ 1.

**NEW Conclusion:** Some progress is now possible with current Mathlib. The remaining
blockers are primarily Gap #2 (Perron's formula), Gap #3 (zero counting), and Gap #4 (Hardy's theorem).

## Blocker Categories

### Category A: Euler Product Infrastructure - **MOSTLY RESOLVED!**

**STATUS: 80% COMPLETE IN MATHLIB**

**What Mathlib NOW Has (discovered Task 43-44):**
- `riemannZeta_eulerProduct` - Euler product: ζ(s) = Π_p (1 - p^{-s})^{-1}
- `riemannZeta_eulerProduct_exp_log` - Log form: ζ(s) = exp(Σ_p -log(1 - p^{-s}))
- `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` - Identity: L(Λ, s) = -ζ'/ζ(s)
- `riemannZeta_ne_zero_of_one_le_re` - **NON-VANISHING ON Re(s) ≥ 1!**
- `LFunction_ne_zero_of_one_le_re` - Non-vanishing for Dirichlet L-functions
- `re_log_comb_nonneg'` - The 3 + 4cos(θ) + cos(2θ) ≥ 0 inequality!
- `norm_LSeries_product_ge_one` - The |L^3 L^4 L| ≥ 1 product bound

**What's STILL Missing:**
- Zero-free region of form σ > 1 - c/log(|t|) (de la Vallée-Poussin type)
- Extension from Re(s) = 1 boundary to interior region

**Partially Unblocked Hypotheses:**
- `ZeroFreeRegionHyp` - Still needs de la Vallée-Poussin region (not just Re = 1)
- `ZetaLogDerivPoleHyp` - **CAN NOW BE PROVED** from `riemannZeta_ne_zero_of_one_le_re`
- `ZetaZeroSupRealPartDichotomyHyp` - Partially addressable

**Remaining Development/ZeroFreeRegion.lean work:**
- 4-6 sorries may now be fillable with Mathlib infrastructure
- `de_la_vallee_poussin_zero_free` still blocked (needs quantitative region)

**Revised Dependency Chain:**
```
Euler Product Log ✓ (MATHLIB HAS THIS)
    ↓
-ζ'/ζ expansion ✓ (MATHLIB HAS THIS)
    ↓
3-4-1 inequality ✓ (MATHLIB HAS THIS)
    ↓
Non-vanishing on Re(s) = 1 ✓ (MATHLIB HAS THIS)
    ↓
de_la_vallee_poussin_zero_free ✗ (STILL BLOCKED - needs quantitative region)
    ↓
ZeroFreeRegionHyp ✗ (Blocked on above)
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

### Category E: Landau Lemma / Dirichlet Series - **MOSTLY RESOLVED!**

**STATUS: 90% COMPLETE IN MATHLIB**

**What Mathlib NOW Has (discovered Tasks 36-43):**
- `LSeries : (ℕ → ℂ) → ℂ → ℂ` - L-series definition
- `LSeries.abscissaOfAbsConv` - Abscissa of absolute convergence
- `LSeries_analyticOnNhd` - Analyticity in convergence half-plane
- `LSeries_eq_mul_integral` - **THE ABEL SUMMATION BRIDGE!**
- `LSeriesSummable_vonMangoldt` - von Mangoldt summability
- `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` - **KEY IDENTITY: L(Λ,s) = -ζ'/ζ(s)**

**Type Bridge NOW EXISTS:**
```lean
-- Mathlib's LSeries_eq_mul_integral connects:
--   LSeries f s = s * ∫ t in Ioi 1, (Σ_{n≤t} f(n)) * t^{-(s+1)} dt
-- This is Abel summation - the bridge between series and integrals!
```

**Created Infrastructure (Tasks 36-43):**
- `TypeBridge.lean` - Documents the LSeries ↔ integral connection
- `LandauLemmaLSeriesHyp` - LSeries-based Landau hypothesis
- `vonMangoldt_lseries_analytic` - **PROVED** using Mathlib
- `vonMangoldt_eq_neg_zeta_logderiv` - **PROVED** using Mathlib

**What's STILL Missing:**
- Singularity theorem: non-negative divergent series → boundary singularity
- The final step of Landau's lemma (L(σ) → ∞ as σ → σ_c⁺)

**Partially Unblocked Hypotheses:**
- `LandauLemmaLSeriesHyp` - New LSeries-based version available
- `ZetaLogDerivPoleHyp` - **NOW PROVABLE** from Mathlib infrastructure
- vonMangoldt-related hypotheses - **PROVABLE**

**Still Blocked (but reduced scope):**
- `LandauLemmaHyp A σ_c` (parametric for arbitrary A)
- Integral-based hypotheses (may be replaceable with LSeries versions)
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

## Task 35 Analysis: Parametric Hypotheses

### Can Any Parametric Hypotheses Be Proved?

**Answer: NO**

The 9 Landau Lemma parametric hypotheses are defined for ALL functions A : ℝ → ℝ:

```lean
instance (A : ℝ → ℝ) (σ_c : ℝ) : LandauLemmaHyp A σ_c
instance (A : ℝ → ℝ) (σ_c : ℝ) : DirichletIntegralConvergesHyp A σ_c
-- etc.
```

**Why trivial cases don't work:**

1. **A = 0 (zero function):**
   - `dirichletIntegral A = 0` (zero function)
   - This IS analytic everywhere
   - But `LandauLemmaHyp` requires `¬AnalyticAt ℂ (dirichletIntegral A) σ_c`
   - So `LandauLemmaHyp (fun _ => 0) σ_c` is FALSE!

2. **ZetaLogDerivPoleHyp (non-parametric):**
   - Requires: if ζ(ρ) = 0, then -ζ'/ζ not analytic at ρ
   - This needs: ζ'(ρ) ≠ 0 (simple zero assumption) or pole structure analysis
   - Mathlib has `differentiableAt_riemannZeta` but not zero simplicity

**Conclusion:** The parametric hypotheses are mathematically meaningful constraints, not trivially satisfiable. They require the full Landau lemma infrastructure to prove.

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
