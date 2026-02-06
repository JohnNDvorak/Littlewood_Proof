# Aristotle Module: Status Tracker

**Date**: 2026-02-05 (updated session 3)

## Overview

The Aristotle module contains AI-generated proofs (from Harmonic's Aristotle and
Anthropic's Claude) that work toward closing the sorry-backed hypothesis instances.
Files are organized in `Littlewood/Aristotle/`.

- **Total files**: 118 (+ 4 deprecated) — added RiemannSiegelBound.lean
- **Files imported by main build**: ~38
- **Files with active sorries (build-visible)**: 4
- **Total build-visible sorries**: 1 (Aristotle) + 7 other = 8 project + 3 external = 11 total
- **NOTE**: PhragmenLindelof(3), ZeroCounting(2), PartialSummation(4) are NOT transitively imported by main build
- **Total Aristotle own sorries**: 8 across 6 files; 112 files sorry-free
- **Note**: `lake build` per-module counts include transitive deps (e.g. 3 external Wiener sorries)

## Session 2 Achievements

| Achievement | Details |
|------------|---------|
| **HasGammaGrowth(1) PROVED** | GammaGrowthWiring.lean: 0 sorries. Used reflection formula ‖Γ(1+it)‖² = π\|t\|/sinh(π\|t\|) + sinh/exp bounds |
| **HasGammaGrowth(n) for all n > 0** | Via step_up from HasGammaGrowth(1). Also hasGammaGrowth_half_add_nat for 1/2+n |
| **RiemannSiegelBound.lean integrated** | New Aristotle file. Contains class defs + vacuous PhaseAveragingBound instance |
| **zeta_tail_bound PROVED** | RiemannSiegelBound.lean: 0 sorries. Non-summability via Complex.summable_one_div_nat_cpow + cpow_neg + summable_nat_add_iff |

## Active Sorries (Build-Visible)

These are the only Aristotle sorries that appear in `lake build` output:

| File | Sorries | Content | Critical Path? | Bridge Ready? |
|------|---------|---------|----------------|---------------|
| **HardyApproxFunctionalEq.lean** | 1 | `approx_functional_eq`: ∫Z² ≥ k·∫\|S\|² - C·T | YES | FULLY AUTO (MeanSquareBridge) |
| **PhragmenLindelof.lean** | 3 | `gamma_growth`, `zeta_critical_line_bound`, `zeta_convexity_bound` | YES | PhragmenLindelofWiring READY |
| **ZeroCounting.lean** | 2 | `zetaZeroCount_via_argument`, `zetaZeroCount_asymp` | No | Not needed |
| **PartialSummation.lean** | 1 | `psi_oscillation_implies_pi_li_oscillation` | No (alt route) | Not created |

## Standalone Sorry-Free Proofs

| File | Sorries | Content | Notes |
|------|---------|---------|-------|
| **PsiOscillationPiLi.lean** | 0 | `psi_oscillation_implies_pi_li_oscillation` (stronger hypotheses: IsBigO error + unbounded ψ oscillation) | Standalone, `import Mathlib` only, local definitions. Reference proof — NOT imported by bridges. |

## Reference Files (not imported, supporting material)

| File | Sorries | Content | Notes |
|------|---------|---------|-------|
| **HardyApproxFunctionalEqV2.lean** | 0 | `hardySum_bound` (PROVED), `hardy_algebraic_bound` (PROVED), `hardy_error_integral_bound` (PROVED), `HardyConjectureData` structure | From uuid 721a165a. **0 sorries — all proofs verified by Claude Code session 3.** |
| **HardyApproxFunctionalEqV3.lean** | 0 | `norm_chi` (|χ(1/2+it)|=1 PROVED), `pointwise_afe` (PROVED), `partial_sum_bound_lemma` (‖S_N‖≤C·t^(1/4) PROVED), `HardyBounds` structure | From uuid f05462b9. 0 sorries. Budget reached before further proofs. Prompt 1 infrastructure. |
| **HardyApproxFunctionalEqV4.lean** | 0 | Hardy AFE conditional: `RiemannSiegelBound`/`PhaseAveragingBound` defs, `approx_functional_eq_correct` CONDITIONAL on both bounds PROVED | From uuid 53fa55c5. 0 sorries. Shows conditional AFE mean square bound. |
| **GammaGrowthBounds.lean** | 0 | Stirling-type bounds: `gamma_half_growth`, `gamma_zero_growth`, `gamma_step_up`, `complex_sin_growth` | From uuid f789cf0e. 0 sorries. Targets `gamma_growth` in PhragmenLindelof — needs final assembly bridge. |
| **GammaGrowthBoundsV2.lean** | 0 | Comprehensive Stirling: `gamma_half_growth` PROVED, `gamma_three_halves_growth` PROVED, `HasGammaGrowth` def, `gamma_growth_step_up/down` PROVED, `StirlingNormalizer`, `stirling_normalizer_bound_uniform` PROVED, etc. | From uuid f121a4ca. **All 4 exact? sorries closed by Claude Code.** Ready for wiring. |
| **PhragmenLindelofV3.lean** | 0 | Phragmen-Lindelof partial: `convexity_exponent`, `chi`, `gamma_step_up` PROVED, `complex_sin_growth` PROVED, `phragmen_aux` | From uuid f2e47fcd. 0 sorries. Partial work — needs GammaGrowthBounds import for completion. |
| **OscillationExtractionInfra.lean** | 0 | Oscillation notation: `OmegaPlus`/`OmegaMinus`/`OmegaPM` defs, `chebyshevPsi`/`chebyshevTheta` local defs, `PsiOscillationFromCriticalZerosHyp`, `HardyCriticalLineZerosHyp`, `ExplicitFormulaPsiHyp`/`ThetaHyp` classes, `cosine_sum_large` trivial | From uuid adaaec83. 0 sorries. Infrastructure for oscillation extraction via Dirichlet approximation. |
| **VanDerCorputInfra.lean** | 0 | Van der Corput integration-by-parts: `van_der_corput_deriv_aux`, continuity/derivative formulas | From uuid 4f63b39a. 0 sorries. Infrastructure for HardyFirstMomentUpperHyp (Prompt 5). |
| **ZetaIntegralRep.lean** | 0 | Zeta integral representation: `zeta_eq_integral_rep_of_one_lt_re`, `zeta_bound_Re_2`, integrability results | From uuid 1ec1d4d1. **1 exact? sorry closed by Claude Code with `exact hs`.** Infrastructure for zeta bounds. |
| **ContourIntegrationV2.lean** | 0 | Cauchy rectangle theorem, residue at simple pole, rectangular integral linearity, log branch cut lemmas, vertical/horizontal segment integrals of 1/(z-z₀), branch cut crossing | From uuid 55435b49. 0 sorries (sorry closed by Claude). Major Prompt 6 progress. |
| **PerronFormulaV3.lean** | 0 | Perron formula definitions: `verticalIntegral`, `perronIntegral`, `DirichletSeries`, `perronError` | From uuid 1737b10e. 0 sorries, definitions only (budget reached before proofs). Prompt 8 infrastructure. |
| **ZetaLogDerivInfra.lean** | 0 | Zeta log-derivative infrastructure: ALL theorems PROVED. 10 theorems proved including `neg_zeta_logderiv_pole_at_one`, `zeta_analytic_order_finite_pos`, `neg_zeta_logderiv_pole_at_zero`, `pole_of_log_deriv_of_pow_mul_analytic`, `exists_analytic_zeta_mul_sub_one` | From uuid ca4eb320. All 6 sorries closed by Claude. Major Prompt 9 infrastructure — pole structure of -ζ'/ζ. |
| **RiemannSiegelBound.lean** | 0 | `RiemannSiegelBoundProp`/`PhaseAveragingBound` class defs, `zeta_tail_bound` (PROVED — non-summability via complex p-series), `PhaseAveragingBound` instance (vacuously true), `integral_hardyZ_approx` (trivially true) | From uuid 7b137fc7. **0 sorries. zeta_tail_bound closed by Claude Code** using cpow_neg + summable_nat_add_iff + Complex.summable_one_div_nat_cpow. |

### Bridge Files (0 project sorries)

| File | Sorries | Content | Notes |
|------|---------|---------|-------|
| **Bridge/GammaGrowthWiring.lean** | 0 | `hasGammaGrowth_half`, `hasGammaGrowth_one` (PROVED via reflection formula), `hasGammaGrowth_three_halves`, `hasGammaGrowth_half_add_nat`, `hasGammaGrowth_nat_pos` (all n > 0) | **All sorries closed by Claude Code.** gamma_one_norm_sq proved via Γ reflection + sinh bounds. |

## Non-Imported Files with Sorries

These files have own sorries (not counting transitive deps from imports):

| File | Own Sorries | Build Sorries | Notes |
|------|:-----------:|:-------------:|-------|
| ~~ChebyshevTheta.lean~~ | 3 | 3 | **DEPRECATED** — moved to _deprecated/, superseded by ChebyshevThetaV2 |
| ExplicitFormula.lean | 1 | 4 | Prompt 9 placeholder; 3 transitive from imports |
| ~~GammaGrowthBoundsV2.lean~~ | ~~4~~ | ~~4~~ | **CLOSED** — all 4 exact? timeouts closed by Claude Code |
| HardyApproxFunctionalEq.lean | 1 | 1 | `approx_functional_eq` (build-visible) |
| HardyApproxFunctionalEqV2.lean | 1 | 1 | V2 partial progress |
| PartialSummation.lean | 1 | 4 | 3 transitive from imports |
| PhragmenLindelof.lean | 3 | 3 | gamma_growth, zeta bounds |
| ZeroCounting.lean | 2 | 2 | Zero counting via argument principle |
| ZetaIntegralRep.lean | 1 | 1 | Zeta integral representation |

**Note:** Build sorry counts include transitive dependencies (e.g. 3 external Wiener sorries).
CriticalZeros.lean and SchmidtOscillationInfinite.lean have 0 own sorries (build shows 3 from transitive deps).

## Aristotle Prompt Status

### Prompts with Active Work

| Prompt # | Topic | Target | Status | Sorries Remaining |
|----------|-------|--------|--------|-------------------|
| 1 | Approximate functional equation | `approx_functional_eq` | 1 sorry | 1 (the core estimate) |
| 2 | Hardy Z mean square | `hardyZ_mean_square_lower` | CLOSED | 0 (fully proved) |
| 3 | Phragmen-Lindelof | `ZetaCriticalLineBoundHyp` | 3 sorries | 3 (gamma_growth blocks the rest) |
| 4 | Zero counting | `zeroCountingFunction` asymptotics | 2 sorries | 2 (argument principle + asymptotic) |
| 5 | Hardy Z first moment | `HardyFirstMomentUpperHyp` | Conditional theorem proved | 4 prerequisites remain |

### Prompts with Placeholders Only

| Prompt # | Topic | Target | Status |
|----------|-------|--------|--------|
| 6 | Contour integration | Vertical line integrals | SUBSTANTIAL — ContourIntegrationV2.lean has Cauchy rectangle, residue, segment integrals (1 sorry) |
| 7 | Rectangle Cauchy | Cauchy residue for rectangles | PLACEHOLDER — header only |
| 8 | Perron's formula | ∫(-ζ'/ζ)x^s/s = ψ₀(x) | PARTIAL — PerronFormulaV3.lean has definitions (budget reached before proofs) |
| 9 | Explicit formula | `explicit_formula_for_psi` | PLACEHOLDER — 1 sorry, exact target stated |

### Dependency Chain for Prompts 6-9

```
Prompt 6 (ContourIntegration) → Prompt 7 (RectangleCauchy)
    → Prompt 8 (PerronFormula) → Prompt 9 (ExplicitFormula)
        → ExplicitFormulaPsiHyp (CriticalAssumptions)
        → ExplicitFormulaThetaHyp (CriticalAssumptions, same argument)
```

## Key Proved Results (0 Sorries)

These Aristotle files contain fully proved results used by the main build:

### Hardy Chain
| File | What it proves |
|------|---------------|
| DiagonalIntegralBound.lean | ∫\|S_N\|² ≥ c·T·log T |
| HardyZRealV2.lean | Hardy Z function real-valuedness |
| HardyZCauchySchwarz.lean | Cauchy-Schwarz for Hardy Z integrals |
| HardyZContradiction.lean | Contradiction argument for infinite zeros |
| HardyInfiniteZerosV2.lean | Infinitely many zeros on critical line |
| HardySetupRequirements.lean | Setup structure for Hardy's theorem |
| MeanSquare.lean | Mean square integral computations |
| OscillatorySumBound.lean | Oscillatory sum integral bounds |

### Zeta Function Infrastructure
| File | What it proves |
|------|---------------|
| FunctionalEquationHyp.lean | Zeta functional equation (FunctionalEquationHyp) |
| FunctionalEquationV2.lean | V2 of functional equation |
| CompletedZetaCriticalLine.lean | Completed zeta on critical line |
| RiemannXi.lean | Riemann xi function |
| StirlingArgGamma.lean | Stirling for arg(Gamma) |
| ZetaBoundsNorm.lean | Norm bounds for zeta |
| ZetaZerosFiniteBelow.lean | Finitely many zeros below height T |

### Number Theory
| File | What it proves |
|------|---------------|
| PsiThetaBound.lean | \|ψ(x) - θ(x)\| ≤ 10√x |
| ThetaLinearBound.lean | θ(x) ≤ cx for some c |
| SchmidtNew.lean | Schmidt oscillation infrastructure |

## Deprecated Files

| File | Why deprecated |
|------|---------------|
| _deprecated/FunctionalEquation.lean | Superseded by FunctionalEquationHyp.lean |
| _deprecated/PerronFormula.lean | Superseded by PerronFormulaV2.lean |
| _deprecated/PrimePowerSums.lean | No longer needed |
| _deprecated/ChebyshevTheta.lean | Superseded by ChebyshevThetaV2.lean (3 sorries → 0) |
| HardyInfiniteZeros.lean | V1, superseded by HardyInfiniteZerosV2 |
| Bridge/PsiToThetaOscillation.lean | Mathematically problematic ψ→θ transfer |

## Priority for Next Aristotle Work

1. **`approx_functional_eq`** (Prompt 1) — closes last sorry on Hardy chain.
   When this closes, entire Hardy chain auto-discharges via MeanSquareBridge.

2. **`gamma_growth`** (in PhragmenLindelof.lean) — Stirling's approximation for Gamma.
   Unblocks `zeta_convexity_bound` which closes `ZetaCriticalLineBoundHyp`.

3. **Prompts 6-9** (Contour → Rectangle → Perron → ExplicitFormula) — sequential chain
   for ExplicitFormulaPsiHyp. Requires Mathlib contour integration (limited availability).

4. **`psi_oscillation_implies_pi_li_oscillation`** (PartialSummation.lean) — alternative
   route to OmegaThetaToPiLiHyp. Blocked on amplitude quantification.
