# Wiring Summary

## Successfully Closed

| Target | Source | Sorries Closed |
|--------|--------|----------------|
| ThetaLinearBound (2 sorries) | ThetaLinearBoundV2 | 2 |

## Wiring Analysis Results (21 sorries across 11 files)

### MeanSquare.lean (3 sorries)

| Sorry | Line | Wireable | Why |
|-------|------|----------|-----|
| `norm_integral_offDiagSsq_le` | 215 | NO | Definition mismatch: t-varying N_t(t) vs fixed N; complex vs real; Icc vs range |
| `normSq_partialZeta_eq` | 230 | NO | Available theorems compute cosine expansion, not diagonal/off-diagonal split |
| `mean_square_partial_zeta_asymp` | 244 | BLOCKED | Depends on sorries #1 and #2 |

### PhragmenLindelof.lean (3 sorries)

| Sorry | Line | Wireable | Source |
|-------|------|----------|--------|
| `zeta_critical_line_bound` | 153 | YES (medium) | PhragmenLindelofV2 + StirlingGammaBounds |
| `zeta_convexity_bound` | 167 | YES (medium) | PhragmenLindelofV2 + boundary estimates |
| `gamma_growth` | 177 | YES (medium) | StirlingGammaBounds.gamma_one_bound + gamma_step_down |

### ZeroCounting.lean (4 sorries)

| Sorry | Line | Wireable | Source |
|-------|------|----------|--------|
| `xi_Mathlib_differentiable` | 117 | IMPOSSIBLE | Statement is FALSE (completedRiemannZeta has poles) |
| `zetaZeroCount_via_argument` | 123 | YES (high) | ZeroCountingXi.zetaZeroCount_via_argument |
| `riemann_von_mangoldt` | 128 | YES (medium) | ZeroCountingNew.zero_counting_main_term |
| `zetaZeroCount_asymp` | 134 | YES (very high) | ZeroCountingNew directly |

### ChebyshevTheta.lean (3 sorries, commented out - conflicts)

| Sorry | Line | Wireable | Source |
|-------|------|----------|--------|
| `sum_vonMangoldt_eq_sum_prime_powers_nat` | 65 | YES (trivial) | ChebyshevThetaV2 exact match |
| `psi_nat_eq_sum_theta_nat` | 73 | YES (moderate) | ChebyshevThetaV2 with reindexing |
| `theta_diff_le_log_choose` | 225 | YES (trivial) | ChebyshevThetaV2 exact match |

### PsiThetaBound.lean (1 sorry)

| Sorry | Line | Wireable | Source |
|-------|------|----------|--------|
| Prime power bijection | 108 | YES (moderate) | Extract from ChebyshevThetaV2.sum_vonMangoldt proof |

### Other files (7 sorries)

| File | Line | Wireable | Notes |
|------|------|----------|-------|
| HardyZConjugation | 116 | NO | Mellin transform identity, alt proof exists |
| ZeroFreeRegionV2 | 117 | MAYBE | tsum_add + tsum_nonneg from Mathlib |
| PartialSummation | 238,241 | NO | Different definition approach |
| PerronContourIntegralsV2 | 442 | NO | Cauchy integral theorem |
| RiemannVonMangoldtV2 | 75 | NO | Algebraic verification |

## Priority Recommendations

1. **PhragmenLindelof** (3 sorries): All wireable via existing sorry-free files
2. **ZeroCounting** (3 of 4): Three wireable, one false (skip)
3. **ChebyshevTheta** (3): All wireable but file is commented out (conflicts)
4. **PsiThetaBound** (1): Wireable from ChebyshevThetaV2
5. **ZeroFreeRegionV2** (1): Possibly closeable with Mathlib tsum lemmas
