# Sorry Status Dashboard

Generated: 2026-01-28

## Summary

| Metric | Count |
|--------|-------|
| Total Aristotle files | 49 |
| Sorry-free files | 42 (86%) |
| Files with sorries | 7 |
| Total sorries | 16 |
| Deprecated files | 3 |
| False statements | 1 |

## Active Sorries by File

| File | Count | Status | Notes |
|------|-------|--------|-------|
| MeanSquare | 4 | Tractable | Aristotle has integral_log_sqrt_asymp, normSq_partialZeta_eq |
| ZeroCounting | 4 | 1 FALSE | xi_Mathlib_differentiable is false (see corrected version) |
| PhragmenLindelof | 3 | Medium | Needs Stirling bounds |
| PartialSummation | 2 | Easy | Arithmetic manipulation |
| PerronFormulaV2 | 1 | Blocked | Needs contour integration |
| PhragmenLindelofStrip | 1 | Medium | Phragmen-Lindelof interpolation |
| HarmonicSumIntegral | 1 | Easy | Harmonic bounds |

## Deprecated Files (moved to _deprecated/)

| File | Sorries | Replacement |
|------|---------|-------------|
| FunctionalEquation.lean | 2 | FunctionalEquationV2.lean |
| PerronFormula.lean | 5 | PerronNew.lean |
| PrimePowerSums.lean | 8 | (incomplete, budget exhausted) |

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

## Blocked Hypotheses

| Hypothesis | Blocker | Needed For |
|------------|---------|------------|
| h_Stirling | Stirling approximation for Gamma argument | NAsymptotic.N_asymptotic |
| h_RVM | Argument principle application | NAsymptotic.N_asymptotic |

## Deprecated Files (use V2/New versions)

| Deprecated | Use Instead |
|------------|-------------|
| FunctionalEquation.lean | FunctionalEquationV2.lean |
| PerronFormula.lean | PerronNew.lean |

## Definition Conflicts to Watch

Multiple `chebyshevPsi` definitions exist:
- `Littlewood/Basic/ChebyshevFunctions.lean:34` (canonical)
- `Littlewood/Aristotle/PiLiOscillation.lean:40`
- `Littlewood/Aristotle/PerronNew.lean:40`
- `Littlewood/Aristotle/ExplicitFormulaV3.lean:34` (as chebyshevPsiV3)
- `Littlewood/Aristotle/PsiDominance.lean:43`

Bridge lemma `chebyshevPsiV3_eq_chebyshevPsi` proves equivalence.
