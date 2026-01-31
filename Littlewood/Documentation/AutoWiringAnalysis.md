# Automatic Wiring Analysis

Examining which sorries might be closable with existing theorems.

## ZeroCounting Analysis

### xi_Mathlib_differentiable

This sorry uses the 'wrong' definition of xi (from completedRiemannZeta).
ZeroCountingXi.xi_entire proves differentiability for the corrected definition.
**Status**: NOT directly wireable - different definitions

### xi_Mathlib_corrected_entire

**Status**: ALREADY PROVED in ZeroCounting.lean (not a sorry)

## N(T) Related Sorries

### Available N(T) theorems:
```
The main theorem `dirichlet_simultaneous_approximation` states that for any `N ≥ 1` and real numbers `α₁, ..., α_n`, there exists an integer `q` with `1 ≤ q ≤ N^n` such that `|q α_j - round(q α_j)| < 1/N` for all `j`. This was proven using the pigeonhole principle on the fractional parts of `q α_j`.
theorem N_from_S_and_Stirling (T : ℝ) (hT : 2 ≤ T)
theorem NZeros_eq_Theta_S (T : ℝ) (hT : 2 ≤ T) :
theorem N_eq_main_plus_S (T : ℝ) (hT : 2 ≤ T) :
theorem zetaZeroCount_via_argument (T : ℝ) (hT : 0 < T) :
theorem zetaZeroCount_asymp :
Proved the main theorem `zero_counting_main_term`: assuming `RiemannVonMangoldtProperty`, N(T) is asymptotically `(T/2π) log(T/2πe)` with error `O(log T)`.
The main theorem: Assuming the Riemann-von Mangoldt formula, the number of zeros N(T) is asymptotically (T/2π) log(T/2πe) with an error of O(log T).
theorem zetaZeroCount_via_argument (T : ℝ) (hT : 0 < T)
```

## RiemannVonMangoldtV2.lean (1 sorry)

The sorry in N_eq_main_plus_S is for Complex.arg algebra manipulation.
This requires careful handling of if-then-else in arg definition.
**Difficulty**: Medium - needs ring_nf and Complex.arg lemmas

## PerronContourIntegralsV2.lean (1 sorry)

The sorry is for Cauchy theorem rewrite with type coercion issues.
**Difficulty**: High - HMul ℂ ℝ type class failures

## Summary of Wiring Feasibility

| Sorry | Wireable? | Notes |
|-------|-----------|-------|
| ZeroCounting.xi_Mathlib_differentiable | No (FALSE) | Wrong def, documented |
| ZeroCounting.zetaZeroCount_via_argument | Maybe | Check vs ZeroCountingXi |
| ZeroCounting.riemann_von_mangoldt | Maybe | Check vs RiemannVonMangoldt |
| ZeroCounting.zetaZeroCount_asymp | Maybe | Check vs NZerosStirling |
| MeanSquare (4) | No | Need new proofs |
| PhragmenLindelof (3) | No | Need Gamma growth |
| PartialSummation (2) | No | Need sum bounds |
| PerronContourIntegralsV2 (1) | No | Type issues |
| RiemannVonMangoldtV2 (1) | No | Algebra tedious |
