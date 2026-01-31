# Potential Wiring Opportunities

Theorems that might close sorries in other files.

## Files with Sorries and Their Contexts

### HarmonicSumIntegral
```
```

### MeanSquare
```
lemma integral_log_sqrt_asymp :
lemma norm_integral_offDiagSsq_le (T : ℝ) (hT : T ≥ 1) :
lemma normSq_partialZeta_eq (t : ℝ) :
theorem mean_square_partial_zeta_asymp :
```

### PartialSummation
```
theorem psi_oscillation_implies_pi_li_oscillation
```

### PerronContourIntegralsV2
```
lemma integral_boundary_rect_perron_neg (y : ℝ) (hy : 0 < y) (hy1 : y < 1) (c : ℝ) (hc : 0 < c) (T : ℝ) (hT : 0 < T) (R : ℝ) (hR : c < R) :
```

### PerronFormulaV2
```
lemma zetaZerosInStrip_finite (T : ℝ) : (zetaZerosInStrip T).Finite := by
```

### PhragmenLindelof
```
theorem zeta_critical_line_bound :
theorem zeta_convexity_bound (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
lemma gamma_growth (σ : ℝ) (hσ : 0 < σ) :
```

### RiemannVonMangoldtV2
```
theorem riemann_von_mangoldt_argument (T : ℝ) (hT : 2 ≤ T) :
theorem N_eq_main_plus_S (T : ℝ) (hT : 2 ≤ T) :
lemma N_main_term_eq (T : ℝ) (hT : 2 ≤ T) :
```

### ZeroCounting
```
theorem xi_Mathlib_eq_corrected (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
theorem xi_Mathlib_differentiable : Differentiable ℂ xi_Mathlib := by
theorem zetaZeroCount_via_argument (T : ℝ) (hT : 0 < T) :
theorem riemann_von_mangoldt (T : ℝ) (hT : 1 < T) :
theorem zetaZeroCount_asymp :
lemma completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta (s : ℂ) (hs : 0 < s.re) (_hs1 : s ≠ 1) :
```


## Cross-File Matches

Searching for potential cross-file matches...

### Known Patterns

- ZeroCounting.xi_Mathlib_differentiable: ZeroCountingXi.xi_entire proves this (different def)
- ZeroCounting.xi_Mathlib_corrected_entire: ALREADY PROVED in ZeroCounting.lean
- N(T) theorems: May be closable via NZerosStirling or RiemannVonMangoldt
