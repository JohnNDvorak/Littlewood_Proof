# Sorry Status Dashboard

Generated: 2026-01-28 (Updated)

## Summary

| Metric | Count |
|--------|-------|
| Total Aristotle files | 52 |
| Sorry-free files | 46 (88%) |
| Files with sorries | 6 |
| Total sorries | 14 |
| Provable sorries | 13 |
| False statements | 1 |

## Active Sorries by File

| File | Count | Status | Notes |
|------|-------|--------|-------|
| MeanSquare | 4 | Tractable | integral_log_sqrt_asymp, norm_integral_offDiagSsq_le, normSq_partialZeta_eq, mean_square_partial_zeta_asymp |
| ZeroCounting | 4 | 1 FALSE | xi_Mathlib_differentiable is false (see corrected version) |
| PhragmenLindelof | 3 | Medium | Needs Stirling bounds for Gamma growth |
| PartialSummation | 2 | Blocked | Needs sumPrimePowers bounds infrastructure |
| PhragmenLindelofStrip | 1 | Medium | Phragmen-Lindelof interpolation |

## Recent Additions (This Session)

| File | Sorries | Key Results |
|------|---------|-------------|
| RiemannVonMangoldt.lean | 0 | NZeros, riemann_von_mangoldt_conditional, S_T_bound_uniform |
| PartialSummationPiLi.lean | 0 | li_integration_by_parts, sum_vonMangoldt_div_log, primePowerCorrection_eq_sum |

## Fixes Applied (This Session)

| File | Change |
|------|--------|
| RiemannXi.lean | 3 exact? → rfl, differentiable_completedZeta₀ (now 0 sorries) |
| RiemannXiEntire.lean | 2 exact? → differentiable_completedZeta₀, completedRiemannZeta_eq |
| XiDifferentiability.lean | 1 exact? → differentiable_completedZeta₀ |
| HarmonicSumIntegral.lean | 1 exact? → integral_harmonicSum_sub_half_log_isBigO |

## False Statements (documented, won't prove)

| File | Statement | Issue |
|------|-----------|-------|
| ZeroCounting:114 | xi_Mathlib_differentiable | completedRiemannZeta discontinuity at poles |

**Fix**: Use `xi_Mathlib_corrected_entire` instead (PROVED).

## Proved Hypothesis Instances (4)

| Class | Location | Proof |
|-------|----------|-------|
| FunctionalEquationHyp | FunctionalEquationHyp.lean | riemannZeta_eq_chiFE_mul |
| LambdaSymmetryHyp | FunctionalEquationHyp.lean | completedRiemannZeta_one_sub |
| ZeroConjZeroHyp | ZeroCountingFunction.lean | riemannZeta_conj |
| ZeroOneSubZeroHyp | ZeroCountingFunction.lean | riemannZeta_one_sub |

## Bridge Lemmas Proved (AristotleBridges.lean)

| Bridge | Theorem | Status |
|--------|---------|--------|
| chebyshevPsiV3 = Chebyshev.psi | chebyshevPsiV3_eq_psi | PROVED |
| chebyshevPsiV3 = chebyshevPsi | chebyshevPsiV3_eq_chebyshevPsi | PROVED |
| zeroCountingFunction sets equal | zeroCountingFunction_set_eq | PROVED |
| zeroCountingFunction = N | zeroCountingFunction_eq_NAsymptotic_N | PROVED |

## Critical Path Status

| Blocker | Status | Unlocks |
|---------|--------|---------|
| h_RVM | ✅ Conditional proof in RiemannVonMangoldt.lean | N(T) asymptotic |
| h_Stirling | ⏳ Waiting H1 from Aristotle | N(T) unconditional, gamma_growth |
| Hardy theorem | 📝 Prompt ready (HARDY) | Critical line zero existence |
| Explicit formula | 📝 Prompt ready (EXPLICIT) | ψ oscillation chain |

## Definition Conflicts to Watch

Multiple `chebyshevPsi` definitions exist:
- `Littlewood/Basic/ChebyshevFunctions.lean:34` (canonical)
- `Littlewood/Aristotle/PiLiOscillation.lean:40`
- `Littlewood/Aristotle/PerronNew.lean:40`
- `Littlewood/Aristotle/ExplicitFormulaV3.lean:34` (as chebyshevPsiV3)
- `Littlewood/Aristotle/PsiDominance.lean:43`
- `Littlewood/Aristotle/PartialSummationPiLi.lean` (namespaced)

Bridge lemma `chebyshevPsiV3_eq_chebyshevPsi` proves equivalence.

## Progress Trajectory

```
Session Start:  50 files, 43 sorry-free (86%), ~16 sorries
Session End:    52 files, 46 sorry-free (88%), 14 sorries

Next targets:
├── Aristotle prompts in flight for remaining 13 provable sorries
├── h_Stirling delivery unlocks N(T) asymptotic chain
└── Final push: Assumptions.lean wiring (~58 sorries)
```
