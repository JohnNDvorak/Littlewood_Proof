# Bridge File Inventory

Updated: 2026-01-29

## Existing Bridges

| Bridge File | Source | Target | Status |
|-------------|--------|--------|--------|
| ThetaEquivalence.lean | ThetaLinearBoundV2 | ThetaLinearBound | 2 sorries closed |
| ZeroCountingBridge.lean | RiemannVonMangoldt, ZeroCountingNew | zeroCountingFunction | Equivalences proved |
| AristotleBridges.lean | Various | Hypothesis classes | chebyshevPsi equiv, N(T) equiv |
| HypothesisInstances.lean | Mathlib | Assumptions | 4 instances proved |
| AristotleWiring.lean | All Aristotle | Re-exports | Complete |
| WiringTests.lean | All Aristotle | Compilation tests | Type signatures verified |

## Remaining Aristotle Sorries (16 in imported files)

### Assessed as NOT WIREABLE

| File | Sorries | Theorem | Reason |
|------|---------|---------|--------|
| ZeroCounting | 1 | xi_Mathlib_differentiable | FALSE statement |
| ZeroCounting | 1 | zetaZeroCount_via_argument | Needs argument principle computation |
| ZeroCounting | 1 | riemann_von_mangoldt | Uses zetaZeroCount (not NZeros), trivial C(T) |
| ZeroCounting | 1 | zetaZeroCount_asymp | Depends on riemann_von_mangoldt |
| PsiThetaBound | 1 | psi_eq_sum_log_p_mul_count (inner) | Finset equality, not sum equality |
| HardyZConjugation | 1 | HurwitzZeta_Lambda0_conj | Specialized Mellin transform |
| PerronContourIntegralsV2 | 1 | integral_boundary_rect_perron_neg | Cauchy integral theorem |
| RiemannVonMangoldtV2 | 1 | N_eq_main_plus_S | Formula includes S(T), different from RvM |
| PartialSummation | 2 | psi_oscillation_implies_pi_li | Underspecified hypotheses |

### Assessed as PARTIALLY WIREABLE (need substantial bridge)

| File | Sorries | Theorem | Source | Gap |
|------|---------|---------|-------|-----|
| MeanSquare | 1 | norm_integral_offDiagSsq_le | OffDiagonalBound | Complex -> real |
| MeanSquare | 1 | normSq_partialZeta_eq | PartialZetaNormSqV2 | Index shift + decomposition |
| MeanSquare | 1 | mean_square_partial_zeta_asymp | Internal composition | Needs sorries 1-2 first |
| PhragmenLindelof | 1 | zeta_critical_line_bound | StirlingGammaBounds | Need interpolation |
| PhragmenLindelof | 1 | zeta_convexity_bound | PhragmenLindelofV2 | Growth bounds |
| PhragmenLindelof | 1 | gamma_growth | StirlingGammaBounds | General sigma, not just 1,2 |

## Available Sorry-Free Aristotle Theorems (Key Results)

| Theorem | File | Type |
|---------|------|------|
| xi_entire | ZeroCountingXi | Differentiable C xi |
| S_isBigO_log | ZeroCountingNew | S =O[atTop] log |
| N_asymptotic | NAsymptotic | N(T) - main =O[atTop] log (conditional) |
| S_bound | NZerosStirling | |S(T)| <= C log T |
| N_from_S_and_Stirling | NZerosStirling | N(T) from S + Stirling |
| trigPoly_zero_iff_coeffs_zero | SchmidtNew | Trig poly = 0 iff coeffs = 0 |
| hardyZ_infinitely_many_zeros | HardyZRealV4 | Infinitely many Z(t) = 0 |
| landau_dirichlet_singularity | LandauLemma | Singularity at abscissa |
| psi_as_trig_sum | TruncatedExplicitFormula | Explicit formula for psi |
| theta_O_n | ThetaLinearBoundV2 | theta(n) = O(n) |
| theta_le_linear | ThetaLinearBound | theta(x) <= Cx (via V2 bridge) |
| sum_vonMangoldt_eq_sum_prime_powers_nat | ChebyshevThetaV2 | Von Mangoldt decomposition |
| psi_nat_eq_sum_theta_nat | ChebyshevThetaV2 | psi = sum of theta at roots |
| stirling_arg_gamma | StirlingArgGamma | Stirling for arg Gamma |
| gamma_one_bound | StirlingGammaBounds | |Gamma(1+it)| bound |
| gamma_two_bound | StirlingGammaBounds | |Gamma(2+it)| bound |
| completedRiemannZeta_conj | HardyZConjugation | Lambda(conj s) = conj Lambda(s) |
| zetaZeros_finite_below | ZetaZerosFiniteBelowV2 | Finite zeros below T |

## Strategy for Next Steps

1. **MeanSquare wiring**: Most impactful (3 sorries). Needs someone to write
   the complex-to-real bridge for offDiagSsq. Request Aristotle proof that
   directly proves the real-valued version matching MeanSquare's definitions.

2. **PhragmenLindelof wiring**: Request Aristotle proof of gamma_growth for
   general sigma, or zeta_critical_line_bound directly.

3. **ZeroCounting**: Request Aristotle proof using `zetaZeroCount` definition
   (Set.ncard based) instead of `NZeros` (Nat.card based).

4. **Hardy integration**: When Hardy's theorem returns, wire to
   HardyCriticalLineZerosHyp to complete the main theorem chain.
