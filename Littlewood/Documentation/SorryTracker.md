# Master Sorry Tracker

Updated: 2026-01-29

## Summary

| Category | Count | Status |
|----------|-------|--------|
| Aristotle sorries | 20 | In progress (16 imported, 4 commented-out) |
| Assumptions.lean sorries | 62 | Waiting for Aristotle + wiring |
| Other sorries | ~61 | CoreLemmas (~46), Main (~9), other (~6) |
| **TOTAL** | **~145** | |
| **Proved hypothesis instances** | **4** | |

---

## Aristotle Sorries (22 across 11 files, 18 imported + 4 commented-out)

### CompletedZetaCriticalLine (0 sorries) CLOSED
```
-- CLOSED: completedRiemannZeta_conj (wired to HardyZConjugation.completedRiemannZeta_conj)
```

### ChebyshevTheta (3 sorries) [commented out - conflicts]
```
lemma sum_vonMangoldt_eq_sum_prime_powers_nat
    -- von Mangoldt decomposition into prime powers
lemma psi_nat_eq_sum_theta_nat
    -- psi = sum of theta at k-th roots
lemma theta_diff_le_log_choose
    -- theta(2n) - theta(n) <= log C(2n,n)
```
**Priority**: HIGH (core identities)
**Aristotle prompt**: Submitted

### ExplicitFormulaInfrastructure (0 sorries) CLOSED
```
-- CLOSED: riemannZeta_ne_zero_near_one (wired via HurwitzZeta.hurwitzZetaEven_residue_one 0)
-- CLOSED: zetaZerosBelow_finite_complex (wired via h_compact.finite h_discrete.isDiscrete)
```

### HardyZConjugation (1 sorry)
```
theorem HurwitzZeta_Lambda_0_conj
    -- Mellin transform conjugation
```
**Priority**: MEDIUM (same technique as completedRiemannZeta_conj)

### HarmonicSumIntegral (0 sorries) CLOSED
```
-- No actual sorries (word "sorry" only in a comment)
```

### MeanSquare (3 sorries, was 4)
```
-- CLOSED: integral_log_sqrt_asymp (wired to IntegralLogAsymp.integral_log_sqrt_asymp)
lemma norm_integral_offDiagSsq_le
    -- off-diagonal integral bound
lemma normSq_partialZeta_eq
    -- |zeta|^2 diagonal + off-diagonal split
lemma mean_square_partial_zeta_asymp
    -- mean square asymptotic
```
**Priority**: HIGH (mean square infrastructure)

### PartialSummation (2 sorries)
```
-- theta diff oscillation proofs (lines 238, 241)
```
**Priority**: LOW (depends on Chebyshev infrastructure)

### PerronContourIntegralsV2 (1 sorry)
```
-- Cauchy integral residue (line 442)
```
**Priority**: MEDIUM

### PhragmenLindelof (3 sorries)
```
lemma gamma_growth_bound
lemma zeta_convexity_bound
lemma zeta_bound_sigma_one
```
**Priority**: HIGH
**Aristotle prompt**: Submitted

### PsiThetaBound (1 sorry)
```
-- finset bijection in psi_eq_sum_log_p_mul_count (line 108)
-- {prime powers <= n} <-> {(p,v) : p prime, p^v <= n}
```
**Priority**: LOW (finset bookkeeping)

### RiemannVonMangoldtV2 (1 sorry)
```
theorem N_eq_main_plus_S
    -- N(T) = main_term + S(T) + O(1/T) algebraic verification
```
**Priority**: MEDIUM
**Aristotle prompt**: Submitted

### ThetaLinearBound (0 sorries) CLOSED
```
-- CLOSED: prod_primes_divides_centralBinom (wired via ThetaEquivalence bridge to V2)
-- CLOSED: theta_two_mul_sub_theta_le (wired via ThetaEquivalence bridge to V2)
```
**Priority**: HIGH (Chebyshev bound foundation)
**Aristotle prompt**: Submitted

### ZeroCounting (4 sorries)
```
theorem xi_Mathlib_differentiable  -- NOTE: FALSE, skip
theorem zetaZeroCount_via_argument
theorem riemann_von_mangoldt
theorem zetaZeroCount_asymp
```
**Priority**: MEDIUM
**Note**: xi_Mathlib_differentiable is FALSE; use corrected version from ZeroCountingXi

### PerronFormulaV2 (1 sorry) [commented out]
```
-- Perron formula variant
```
**Priority**: LOW

---

## Assumptions.lean Sorries (62)

See HypothesisMapping.md for detailed breakdown by category:
- Explicit Formula: 11 classes (0 proved)
- Weighted Average: 7 classes (0 proved)
- Schmidt/Oscillation: 9 classes (0 proved)
- Zero Density: 6 classes (0 proved)
- Zero Supremum: 4 classes (0 proved)
- Zero Counting: 12 classes (2 proved: ZeroConjZeroHyp, ZeroOneSubZeroHyp)
- Landau Lemma: 9 classes (0 proved)
- Also proved elsewhere: FunctionalEquationHyp, LambdaSymmetryHyp

---

## Closing Priority

### Phase 1: Current Aristotle batch (targeting -15 sorries)
1. ~~completedRiemannZeta_conj (1)~~ DONE
2. ChebyshevTheta sorries (3)
3. ~~ThetaLinearBound sorries (2)~~ DONE
4. PhragmenLindelof sorries (3)
5. ~~MeanSquare integral_log_sqrt_asymp (1)~~ DONE
6. RiemannVonMangoldtV2 N_eq_main_plus_S (1)
7. Hardy's theorem (new file)

### Phase 2: Wiring (targeting -10-15 hypothesis sorries)
1. ZeroCountingAsymptoticHyp via RiemannVonMangoldt bridge
2. OmegaPsiToThetaHyp via PsiThetaBound bridge
3. ZeroCountingCrudeBoundHyp from asymptotic
4. ZeroCountingTendstoHyp from asymptotic
5. ExplicitFormulaPsiHyp partial connection
