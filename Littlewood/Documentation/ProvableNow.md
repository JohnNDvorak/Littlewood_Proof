# Lemmas That Should Be Provable Now

## From HardyZRealV4.lean (0 sorries)
- [x] `hardyZV4_real` - Z(t) is real
- [x] `gamma_duplication_hardyV4` - Γ duplication
- [x] `gamma_reflection_hardyV4` - Γ reflection

## From FunctionalEquationV2.lean (0 sorries)
- [x] `LambdaV2_eq_completedZeta` - Λ = completedZeta for Re(s) > 0
- [x] `LambdaV2_one_sub` - Λ(1-s) = Λ(s) in critical strip

## From SchmidtNew.lean (0 sorries)
- [x] `trigPoly_zero_iff_coeffs_zero` - trig linear independence
- [x] `schmidt_oscillation` - Schmidt oscillation theorem

## From NAsymptotic.lean (0 sorries)
- [x] `ZetaZeroCount.N_asymptotic` - N(T) ~ (T/2π)log(T/2πe) + O(log T)

## From RiemannXi.lean (1 sorry - algebraic)
- [x] `RiemannXiModule.xi_one_sub` - xi(1-s) = xi(s)
- [x] `RiemannXiModule.differentiable_RiemannXi` - Xi is entire
- [ ] `RiemannXiModule.RiemannXi_eq_completedRiemannZeta` - 1 algebraic sorry

## From CriticalZeros.lean (0 sorries - FIXED!)
- [x] `critical_zeros_finite` - finitely many zeros up to height T
- [x] `critical_zeros_upto` - finite set of critical zeros

## Hypothesis Instances Status

### Already Connected (ZeroCountingFunction.lean)
1. `ZeroConjZeroHyp` ✓ (via riemannZeta_conj)
2. `ZeroOneSubZeroHyp` ✓ (via functional equation)

### Could Connect Now
3. `SchmidtOscillationHyp` ← use `trigPoly_zero_iff_coeffs_zero` + `schmidt_oscillation`
4. `ZeroCountingHyp` ← use `ZetaZeroCount.N_asymptotic` (needs definition alignment)

### Still Need Work
5. `ExplicitFormulaHyp` ← needs Perron (6 sorries in PerronFormula.lean)
6. `HardyInfiniteZerosHyp` ← needs Hardy theorem (deep result)

## Summary

| Category | Files | Sorry-free | Key Results |
|----------|-------|------------|-------------|
| Hardy Z | 5 | 5 | Z(t) real, Γ identities |
| Functional eq | 2 | 2 | Λ(1-s)=Λ(s), xi symmetry |
| Schmidt | 2 | 2 | Trig independence, oscillation |
| Zero counting | 3 | 2 | N(T) asymptotic, critical zeros finite |
| Riemann Xi | 1 | 0 | Xi entire (1 algebraic sorry) |
