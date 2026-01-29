# Sorry Closing Checklist

## MeanSquare.lean (4 sorries)

| Line | Sorry | Potential Wire | Status |
|------|-------|----------------|--------|
| 112 | `integral_log_sqrt_asymp` | Different integrand than IntegralLogSqrtAsymp | Needs new proof |
| 214 | `norm_integral_offDiagSsq_le` | OffDiagonalBound.norm_integral_offDiagSsqReal_le | Need bridge (different N param) |
| 229 | `normSq_partialZeta_eq` | PartialZetaNormSqV2.normSq_partialZeta_general | Need diagonal/off-diag split |
| 243 | `mean_square_partial_zeta_asymp` | Depends on above | Waiting |

## ZeroCounting.lean (4 sorries)

| Line | Sorry | Potential Wire | Status |
|------|-------|----------------|--------|
| 117 | `xi_Mathlib_differentiable` | **FALSE** - skip | Deprecated, use corrected |
| 123 | `zetaZeroCount_via_argument` | ZeroCountingXi (different defs) | Needs bridge |
| 128 | `riemann_von_mangoldt` | RiemannVonMangoldt.riemann_von_mangoldt | Different N defs |
| 134 | `zetaZeroCount_asymp` | Derive from above | Waiting |

## PhragmenLindelof.lean (3 sorries)

| Line | Sorry | Potential Wire | Status |
|------|-------|----------------|--------|
| 138 | `gamma_growth_bound` | StirlingGammaBounds or GammaGrowth | Check |
| 156 | `zeta_convexity_bound` | ZetaBoundsNorm (partial) | Check types |
| 170 | `zeta_bound_sigma_one` | Needs new proof | Waiting |

## ExplicitFormulaInfrastructure.lean (2 sorries)

| Line | Sorry | Notes |
|------|-------|-------|
| 138 | Residue limit | Complex analysis |
| 213 | Compact+discrete → finite | Need topology lemma |

## Other Files

| File | Line | Sorry | Notes |
|------|------|-------|-------|
| PartialSummation | 238 | oscillation proof | Needs ChebyshevTheta |
| PartialSummation | 241 | oscillation proof | Needs ChebyshevTheta |
| PerronContourIntegralsV2 | 422 | Cauchy integral | Complex analysis |
| RiemannVonMangoldtV2 | 70 | arg algebra | Ring tactics |
| HardyZConjugation | 116 | Mellin transform | Analysis |

## ChebyshevTheta.lean (3 sorries - commented out)

| Sorry | Notes |
|-------|-------|
| `sum_vonMangoldt_eq_sum_prime_powers_nat` | Prime powers |
| `psi_nat_eq_sum_theta_nat` | ψ = Σ θ(x^{1/k}) |
| `theta_diff_le_log_choose` | Binomial bound |

## Priority Actions

1. **MeanSquare**: Create bridge showing `offDiagSsq t = offDiagSsqReal (N_t t) t`
2. **ZeroCounting**: Accept xi_Mathlib_differentiable is FALSE, use corrected version
3. **PhragmenLindelof**: Check GammaGrowth.lean for gamma bounds
4. **ExplicitFormulaInfrastructure**: Topology lemma for compact+discrete

## Blocking Dependencies

```
mean_square_partial_zeta_asymp
  ├── normSq_partialZeta_eq (need diagonal split)
  ├── norm_integral_offDiagSsq_le (need bridge)
  └── integral_log_sqrt_asymp (need proof for √(t/2π))

zetaZeroCount_asymp
  └── riemann_von_mangoldt (need definition bridge)
```
