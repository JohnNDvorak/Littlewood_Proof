# Quick Reference - Key Theorems

## Zeta Properties (Sorry-Free)

| Theorem | File | Statement |
|---------|------|-----------|
| `riemannZeta_conj_V4` | HardyZRealV4 | ζ(conj s) = conj(ζ(s)) |
| `riemannZeta_eq_chi_mulV2` | FunctionalEquationV2 | ζ(s) = χ(s)ζ(1-s) |
| `zeta_ne_zero_re_one` | ThreeFourOne | ζ(1+it) ≠ 0 |
| `three_four_one` | ThreeFourOne | 3+4cos(θ)+cos(2θ) ≥ 0 |

## Hardy Z Function (Sorry-Free)

| Theorem | File | Statement |
|---------|------|-----------|
| `hardyZV4_real` | HardyZRealV4 | Im(Z(t)) = 0 |
| `hardyZV4_conj_eq` | HardyZRealV4 | Z(t) = conj(Z(t)) |

## Xi Function (Sorry-Free)

| Theorem | File | Statement |
|---------|------|-----------|
| `xi_LiteralCorrected_entire` | XiDifferentiability | Corrected ξ is entire |
| `RiemannXiAlt_entire` | RiemannXiEntire | Alternative ξ is entire |
| `xi_Mathlib_corrected_entire` | ZeroCounting | xi_Mathlib_corrected is entire |

## Oscillation Results (Sorry-Free)

| Theorem | File | Statement |
|---------|------|-----------|
| `trigPoly_zero_iff_coeffs_zero` | TrigPolyIndependence | Linear independence of trig polys |
| `schmidt_oscillation` | SchmidtNew | Non-zero trig poly oscillates infinitely |
| `schmidt_oscillation_infinite` | SchmidtOscillationInfinite | Infinite sign changes |

## Zero Counting (Sorry-Free)

| Theorem | File | Statement |
|---------|------|-----------|
| `N_asymptotic` | NAsymptotic | N(T) = (T/2π)log(T/2πe) + O(log T) (conditional) |
| `S_isBigO_log` | ZeroCountingNew | S(T) = O(log T) |
| `zero_counting_main_term` | ZeroCountingNew | Main term expansion |

## Explicit Formula (Sorry-Free)

| Theorem | File | Statement |
|---------|------|-----------|
| `explicit_formula_psi_v3` | ExplicitFormulaV3 | ψ(x) explicit formula |

## Bridge Lemmas (Sorry-Free)

| Theorem | File | Statement |
|---------|------|-----------|
| `chebyshevPsiV3_eq_psi` | AristotleBridges | chebyshevPsiV3 = Chebyshev.psi |
| `chebyshevPsiV3_eq_chebyshevPsi` | AristotleBridges | chebyshevPsiV3 = chebyshevPsi |
| `zeroCountingFunction_eq_NAsymptotic_N` | AristotleBridges | (zeroCountingFunction T : ℝ) = N T |

## Functional Equation (Sorry-Free)

| Theorem | File | Statement |
|---------|------|-----------|
| `completedRiemannZeta_one_sub` | Mathlib | Λ(1-s) = Λ(s) |
| `riemannZeta_ne_zero_of_one_le_re` | Mathlib | ζ(s) ≠ 0 for Re(s) ≥ 1 |

## Hypothesis Instances (4 Proved)

| Class | Instance Location |
|-------|-------------------|
| FunctionalEquationHyp | FunctionalEquationHyp.lean:70 |
| LambdaSymmetryHyp | FunctionalEquationHyp.lean:80 |
| ZeroConjZeroHyp | ZeroCountingFunction.lean:1618 |
| ZeroOneSubZeroHyp | ZeroCountingFunction.lean:1640 |

## File Status Summary

- **Total Aristotle files**: 52
- **Sorry-free**: 42 (81%)
- **Files with sorries**: 10 (31 total sorries)
- **Deprecated**: FunctionalEquation.lean, PerronFormula.lean
