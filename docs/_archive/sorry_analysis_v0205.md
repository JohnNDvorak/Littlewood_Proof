# Complete Sorry and Hypothesis Analysis - v0.205

## Executive Summary

| Category | Count |
|----------|-------|
| **Total sorries** | 82 |
| **Assumptions.lean (axioms)** | 58 |
| **Non-axiom sorries** | 24 |
| **Hypothesis classes defined** | 68 |
| **Hypothesis classes with instances** | 58 (all in Assumptions.lean) |
| **Hypothesis classes proved** | 2 (ZeroConjZeroHyp, ZeroOneSubZeroHyp) |
| **Clean files** | 32 |

---

## Part 1: Non-Axiom Sorries (24 total)

### File: Development/HardyTheorem.lean (11 sorries)

| Line | Theorem | Blocker | Difficulty |
|------|---------|---------|------------|
| 90 | `riemannSiegelTheta_asymptotic_stub` | Stirling's approximation for Gamma | HARD |
| 112 | `hardyZ_real` | ξ functional equation phase analysis | HARD |
| 142 | `sign_change_implies_zero` | IVT + hardyZ_zero_iff | MEDIUM |
| 169 | `hardyZ_is_real` | Same as hardyZ_real | HARD |
| 187 | `hardyZ_continuous` | Complex.arg continuity on Gamma path | HARD |
| 201 | `hardyZ_not_zero` | First zero ordinate > 14.13 | MEDIUM |
| 208 | `hardyZ_growth_bound` | Lindelöf-type bounds | HARD |
| 220 | `hardyZ_sign_change_in_interval` | Hardy's integral method | VERY HARD |
| 235 | `sign_change_gives_zero` | IVT application | EASY |
| 262 | `hardy_infinitely_many_zeros_stub` | Combines all above | VERY HARD |
| 270 | `hardy_zeros_density_stub` | Density lower bound | VERY HARD |

**Mathematical Dependencies:**
- Riemann-Siegel theta function asymptotics
- ξ(s) = ξ(1-s) functional equation for completed zeta
- Continuity of Complex.arg ∘ Gamma on {1/4 + it/2 : t ∈ ℝ}
- Hardy's integral representation method

---

### File: Development/ZeroFreeRegion.lean (6 sorries)

| Line | Theorem | Blocker | Difficulty |
|------|---------|---------|------------|
| 257 | `mertens_inequality_stub` | Specialize DirichletCharacter to trivial char | MEDIUM |
| 281 | `zero_free_region_stub` (interior) | Quantitative de la Vallée Poussin | HARD |
| 321 | `zeta_product_lower_bound` | Same as mertens_inequality | MEDIUM |
| 360 | `zeta_pole_behavior` | Filter coercion ℝ → ℂ nhdsWithin | MEDIUM |
| 380 | `neg_zeta_logderiv_expansion` | Laurent expansion extraction | HARD |
| 403 | `neg_zeta_logderiv_re_bound` | Depends on Laurent expansion | HARD |
| 433 | `de_la_vallee_poussin_zero_free` (interior) | Quantitative constant | HARD |

**Note:** Lines 257/321 are the SAME blocker (counted once). Actual sorries: 6.

**Mathematical Dependencies:**
- `DirichletCharacter.norm_LSeries_product_ge_one` specialized to trivial character
- Laurent expansion of -ζ'/ζ near s = 1
- Filter theory: nhdsWithin on ℝ to nhdsWithin on ℂ

**What's PROVED (from Mathlib):**
- ζ(s) ≠ 0 for Re(s) ≥ 1 (boundary case!)
- Trigonometric inequality 3 + 4cos(θ) + cos(2θ) ≥ 0
- Euler product and log derivative identities

---

### File: Aristotle/LandauLemma.lean (3 sorries)

| Line | Theorem | Blocker | Difficulty |
|------|---------|---------|------------|
| 28 | `dirichlet_series_eq_tsum_real` | Complex.re_tsum + cpow manipulation | MEDIUM |
| 52 | `dirichlet_series_tendsto_atTop` | Filter limit + monotonicity argument | HARD |
| 68 | `landau_dirichlet_singularity` | Connect complex function to real tsum | HARD |

**Mathematical Dependencies:**
- Complex.re_tsum for commuting Re with infinite sums
- Monotonicity of partial sums in exponent σ
- nhdsWithin filter arguments

**What's PROVED:**
- `partial_sums_mono` - monotonicity of partial sums
- `tendsto_atTop_of_nonneg_not_summable` - divergent series tends to ∞
- `analyticAt_bounded_on_compact` - analytic functions bounded on compact sets

---

### File: Aristotle/LaurentExpansion.lean (3 sorries)

| Line | Theorem | Blocker | Difficulty |
|------|---------|---------|------------|
| 26 | `neg_zeta_logDeriv_residue_one` | Logarithmic derivative computation from riemannZeta_residue_one | MEDIUM |
| 34 | `neg_zeta_logDeriv_principal_part` | Depends on above | MEDIUM |
| 40 | `zetaMulSubOne_continuousAt_one` | nhdsWithin → nhds for continuity | EASY |

**Mathematical Dependencies:**
- `riemannZeta_residue_one` (in Mathlib)
- Logarithmic derivative calculus
- Filter limit theory

---

### File: CoreLemmas/LandauLemma.lean (1 sorry)

| Line | Theorem | Blocker | Difficulty |
|------|---------|---------|------------|
| 387 | `zeta_zero_implies_vonMangoldt_singularity` | Analytic continuation from Re(s) > 1 to ρ | HARD |

**Mathematical Dependencies:**
- `ZetaLogDerivPoleHyp` (axiom)
- Analytic continuation theory
- Identity theorem for analytic functions

---

## Part 2: Hypothesis Classes (68 total)

### Explicit Formula Classes (11 classes, 11 sorries)

| Class | Location | Purpose |
|-------|----------|---------|
| `ExplicitFormulaPsiHyp` | ExplicitFormulas/ExplicitFormulaPsi.lean:52 | ψ(x) explicit formula |
| `ExplicitFormulaPsiSmoothedHyp` | :88 | Smoothed version |
| `ExplicitFormulaIntegralHyp` | :114 | Integral form |
| `ExplicitFormulaDoubleIntegralHyp` | :128 | Double integral form |
| `PsiMellinHyp` | :165 | Mellin transform connection |
| `MellinContourShiftHyp` | :178 | Contour shift justification |
| `ZeroSumBoundRHHyp` | :221 | Zero sum under RH |
| `PsiErrorBoundHyp` | :232 | Error term bound |
| `PsiErrorBoundRHHyp` | :242 | Error term under RH |
| `OmegaPsiToThetaHyp` | ConversionFormulas.lean:195 | ψ → θ oscillation transfer |
| `OmegaThetaToPiLiHyp` | :212 | θ → π-li oscillation transfer |

---

### Weighted Average Classes (7 classes, 7 sorries)

| Class | Location | Purpose |
|-------|----------|---------|
| `WeightedAverageFormulaRHHyp` | WeightedAverageFormula.lean:46 | Main formula under RH |
| `IntegralPsiMinusXHyp` | :63 | Integral of ψ(x) - x |
| `RhoToGammaErrorHyp` | :76 | Error from ρ to γ |
| `SumOverPositiveOrdinatesHyp` | :87 | Sum over positive γ |
| `ZeroSumTailHyp` | :99 | Tail bound for zero sum |
| `MainSumBoundHyp` | :112 | Main sum bound |
| `AlignedSumLargeHyp` | :125 | Aligned sum large |

---

### Schmidt/Oscillation Classes (9 classes, 9 sorries)

| Class | Location | Purpose |
|-------|----------|---------|
| `SchmidtPsiOscillationHyp` | SchmidtTheorem.lean:40 | Main oscillation |
| `PsiOscillationSqrtHyp` | :50 | √x oscillation |
| `MellinPsiIdentityHyp` | :59 | Mellin identity |
| `OmegaMinusNecessityHyp` | :71 | Ω₋ necessity |
| `OmegaPlusNecessityHyp` | :81 | Ω₊ necessity |
| `HardyCriticalLineZerosHyp` | :91 | Hardy zeros exist |
| `PsiOscillationFromCriticalZerosHyp` | :100 | Oscillation from zeros |
| `ThetaOscillationMinusHyp` | :109 | θ oscillation Ω₋ |
| `ThetaOscillationRHHyp` | :118 | θ under RH |

---

### Zero Density Classes (7 classes, 8 sorries)

| Class | Location | Purpose |
|-------|----------|---------|
| `ZeroCountingSummabilityHyp` | ZeroDensity.lean:103 | Summability of 1/|ρ|^α |
| `ZeroCountingSumInvGammaAsymptoticHyp` | :363 | Asymptotic for Σ 1/γ |
| `ZeroCountingSumOneEqHyp` | :383 | Σ 1 = N(T) identity |
| `ZeroCountingTailSqAsymptoticHyp` | :427 | Tail Σ 1/γ² asymptotic |
| `RiemannHypothesisInvRhoAsymptoticHyp` | :523 | Σ 1/ρ under RH |
| `ZeroCountingSummableXPowRhoDivHyp` | :542 | Σ x^ρ/ρ summability |
| `ZeroCountingAverageInvGammaHyp` | :574 | Average 1/γ |

---

### Zeta Zero Supremum Classes (4 classes, 4 sorries)

| Class | Location | Purpose |
|-------|----------|---------|
| `ZeroFreeRegionHyp` | SupremumRealPart.lean:58 | Zero-free region exists |
| `ZetaZeroSupRealPartDichotomyHyp` | :68 | Θ dichotomy |
| `ChebyshevErrorBoundZeroFreeHyp` | :77 | Error from zero-free |
| `ChebyshevErrorBoundThetaHyp` | :88 | Error bound for θ |

---

### Zero Counting Classes (14 classes, 12 sorries)

| Class | Location | Purpose |
|-------|----------|---------|
| `ZeroCountingTendstoHyp` | ZeroCountingFunction.lean:447 | N(T) → ∞ |
| `ZeroCountingCrudeBoundHyp` | :506 | N(T) = O(T log T) |
| `ZeroCountingSpecialValuesHyp` | :509 | Special values |
| `ZeroCountingFifteenHyp` | :512 | N(15) = 0 |
| `FirstZeroOrdinateHyp` | :515 | First zero ≈ 14.13 |
| `ZeroCountingAsymptoticHyp` | :565 | N(T) asymptotic |
| `ZeroCountingRvmExplicitHyp` | :570 | Riemann-von Mangoldt |
| `ZeroCountingAsymptoticRatioHyp` | :576 | Asymptotic ratio |
| `ZeroCountingMainTermHyp` | :580 | Main term |
| `ZeroCountingLowerBoundHyp` | :584 | Lower bound |
| `ZeroCountingLocalDensityHyp` | :1210 | Local density |
| `ZeroGapsLowerBoundHyp` | :1492 | Gap lower bound |
| `ZeroConjZeroHyp` | :1534 | **PROVED** |
| `ZeroOneSubZeroHyp` | :1537 | **PROVED** |

---

### Landau Lemma Classes (10 classes, 10 sorries)

| Class | Location | Purpose |
|-------|----------|---------|
| `LandauLemmaHyp` | LandauLemma.lean:53 | Main Landau lemma |
| `DirichletIntegralConvergesHyp` | :62 | Integral converges |
| `DirichletIntegralAnalyticHyp` | :71 | Integral analytic |
| `DirichletIntegralDerivHyp` | :79 | Derivative exists |
| `DirichletIntegralPowerSeriesHyp` | :90 | Power series |
| `RadiusExceedsAbscissaHyp` | :102 | Radius > abscissa |
| `LandauExtensionHyp` | :113 | Extension exists |
| `LandauLemmaSeriesHyp` | :124 | Series version |
| `ZetaLogDerivPoleHyp` | :133 | -ζ'/ζ has poles at zeros |
| `LandauLemmaLSeriesHyp` | :278 | L-series version |

---

### Conversion Formula Classes (6 classes in ConversionFormulas.lean)

| Class | Line | Purpose |
|-------|------|---------|
| `ThetaPsiFirstCorrectionHyp` | 76 | θ-ψ correction |
| `ThetaPsiRHHyp` | 102 | θ-ψ under RH |
| `PiFromThetaSummationHyp` | 120 | π from θ |
| `LiExpansionHyp` | 140 | li expansion |
| `PiLiFromThetaHyp` | 157 | π-li from θ |
| `PiLiFromPsiRHHyp` | 175 | π-li from ψ under RH |

---

## Part 3: Blocker Categories

### Category A: Dirichlet Character Specialization (2 sorries)
**Impact:** Would unlock ZeroFreeRegion product bounds

Files: Development/ZeroFreeRegion.lean
- Line 257: `mertens_inequality_stub`
- Line 321: `zeta_product_lower_bound`

**Required:** Specialize `DirichletCharacter.norm_LSeries_product_ge_one` to trivial character (N=1).

---

### Category B: Complex.re_tsum / cpow Manipulation (2 sorries)
**Impact:** Would unlock Aristotle Landau lemma chain

Files: Aristotle/LandauLemma.lean
- Line 28: `dirichlet_series_eq_tsum_real`

Also blocked in LSeriesRealBridge.lean (proved files reference similar patterns).

**Required:** Prove `(∑' n, (a n : ℂ) * (n : ℂ)^(-(σ : ℂ))).re = ∑' n, a n * (n : ℝ)^(-σ)` for real σ.

---

### Category C: Laurent Expansion / Log Derivative (4 sorries)
**Impact:** Would unlock -ζ'/ζ analysis

Files: Aristotle/LaurentExpansion.lean, Development/ZeroFreeRegion.lean
- `neg_zeta_logDeriv_residue_one`
- `neg_zeta_logderiv_expansion`
- `neg_zeta_logderiv_re_bound`

**Required:** Extract Laurent expansion from `riemannZeta_residue_one`.

---

### Category D: Filter Theory (3 sorries)
**Impact:** Would unlock continuity and limit arguments

Files: Multiple
- `zeta_pole_behavior` (ℝ → ℂ nhdsWithin)
- `zetaMulSubOne_continuousAt_one` (nhdsWithin → nhds)
- `dirichlet_series_tendsto_atTop` (filter limits)

**Required:** Filter coercion lemmas, nhdsWithin theory.

---

### Category E: Analytic Continuation (2 sorries)
**Impact:** Would unlock Landau singularity theorems

Files: Aristotle/LandauLemma.lean, CoreLemmas/LandauLemma.lean
- `landau_dirichlet_singularity`
- `zeta_zero_implies_vonMangoldt_singularity`

**Required:** Identity theorem, analytic continuation from Re(s) > 1.

---

### Category F: Hardy Z-function (11 sorries)
**Impact:** Would prove infinitely many critical line zeros

Files: Development/HardyTheorem.lean

**Required:**
1. Riemann-Siegel theta asymptotics (Stirling)
2. ξ functional equation phase analysis
3. Complex.arg continuity
4. Hardy's integral representation method

---

## Part 4: Recommended Attack Order

### Phase 1: Low-Hanging Fruit (4-6 sorries)

1. **Dirichlet Specialization** (Cat A)
   - Wrap `DirichletCharacter.norm_LSeries_product_ge_one` for trivial char
   - Unlocks: 2 ZeroFreeRegion sorries

2. **Laurent from Residue** (Cat C partial)
   - Use `riemannZeta_residue_one` to get `neg_zeta_logDeriv_residue_one`
   - Unlocks: 1-2 LaurentExpansion sorries

3. **Filter Coercions** (Cat D partial)
   - `zetaMulSubOne_continuousAt_one` is marked EASY
   - Unlocks: 1 sorry

### Phase 2: Medium Infrastructure (6-8 sorries)

4. **Complex.re_tsum** (Cat B)
   - Central to Dirichlet series manipulation
   - Unlocks: 2 Aristotle sorries

5. **IVT Applications** (Cat F partial)
   - `sign_change_gives_zero` marked EASY
   - `sign_change_implies_zero` marked MEDIUM
   - Unlocks: 2 HardyTheorem sorries

### Phase 3: Deep Mathematics (10+ sorries)

6. **Landau Singularity Chain** (Cat E)
   - Requires analytic continuation theory
   - Unlocks: 2 sorries

7. **Hardy Z-function Core** (Cat F)
   - Requires ξ functional equation work
   - Unlocks: 5+ sorries

8. **Quantitative Zero-Free** (Cat A extended)
   - Interior region σ > 1 - c/log|t|
   - Unlocks: 2 ZeroFreeRegion sorries

---

## Part 5: Mathlib Dependencies

### Available and Used
- `riemannZeta_ne_zero_of_one_le_re` - Critical line non-vanishing
- `riemannZeta_residue_one` - Residue at s=1
- `riemannZeta_eulerProduct_tprod` - Euler product
- `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` - Log derivative
- `DirichletCharacter.norm_LSeries_product_ge_one` - Product bound (needs specialization)

### Would Be Helpful
- Complex.re_tsum - Real part of infinite sums
- MeromorphicAt theory - For Laurent expansions
- Better filter coercion lemmas

---

## Part 6: File Status Summary

### Sorry-Free Files (32)
```
Main/LittlewoodPsi.lean          Main/LittlewoodPi.lean
Basic/ChebyshevFunctions.lean    Basic/LogarithmicIntegral.lean
CoreLemmas/DirichletApproximation.lean  CoreLemmas/WeightedAverageFormula.lean
Development/Bridge.lean          Development/DirichletReal.lean
Development/LandauLemma.lean     Development/LSeriesDerivatives.lean
Development/LSeriesRealBridge.lean  Development/LSeriesTerms.lean
Development/MainTheoremsVerification.lean  Development/MathlibZetaAudit.lean
Development/PowerLemmas.lean     Development/PrimeHelpers.lean
Development/SumLemmas.lean       Development/TypeBridge.lean
Development/ZetaLogDeriv.lean    Development/ZetaPositivity.lean
ExplicitFormulas/* (4 files)     Mertens/MertensFirst.lean
Oscillation/SchmidtTheorem.lean  Oscillation/SchmidtPi.lean
ZetaZeros/ZeroCountingFunction.lean  ZetaZeros/ZeroDensity.lean
ZetaZeros/SupremumRealPart.lean  Tests/MainTheorems.lean
Tests/FullIntegration.lean
```

### Files with Sorries (6 + Assumptions.lean)
```
Assumptions.lean                 58 sorries (intentional axioms)
Development/HardyTheorem.lean    11 sorries
Development/ZeroFreeRegion.lean   6 sorries
Aristotle/LandauLemma.lean        3 sorries
Aristotle/LaurentExpansion.lean   3 sorries
CoreLemmas/LandauLemma.lean       1 sorry
```
