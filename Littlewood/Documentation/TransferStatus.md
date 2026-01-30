# Aristotle Transfer Status

## Overview

**19 theorems** transferred to canonical project types in `Bridge/AristotleTransfers.lean`.
All compile with zero sorries.

## Category A: Already Canonical (14 theorems)

These Aristotle theorems already use Mathlib types directly — no bridging needed.

| # | Name | Source File | Statement |
|---|------|------------|-----------|
| A1 | `zeta_ne_zero_on_re_one` | ThreeFourOneV2 | `ζ(1+it) ≠ 0` for `t ≠ 0` |
| A2 | `three_four_one` | ThreeFourOneV2 | `‖ζ(σ)‖³ ‖ζ(σ+it)‖⁴ ‖ζ(σ+2it)‖ ≥ 1` for `σ > 1` |
| A3 | `trig_inequality` | ThreeFourOneV2 | `3 + 4cos θ + cos 2θ ≥ 0` |
| A4 | `zeta_logderiv_residue` | LaurentExpansion | `(s-1)(-ζ'/ζ) → 1` at `s = 1` |
| A5 | `zeta_deriv_residue` | LaurentExpansion | `(s-1)²ζ'(s) → -1` at `s = 1` |
| A6 | `zeta_ne_zero_near_one` | LaurentExpansion | `∀ᶠ s near 1, ζ(s) ≠ 0` |
| A7 | `zeta_mul_sub_one_analytic` | LaurentExpansion | `(s-1)ζ(s)` is analytic at `s = 1` |
| A8 | `schmidt_oscillation_theorem` | SchmidtNew | Non-trivial trig poly oscillates infinitely |
| A9 | `trig_poly_zero_iff` | SchmidtNew | Trig poly = 0 ↔ all coefficients = 0 |
| A10 | `hardyZ_is_real` | HardyZRealV2 | `Z(t)` is real-valued |
| A10 | `hardyZ_zero_iff` | HardyZRealV2 | `Z(t) = 0 ↔ ζ(1/2+it) = 0` |
| A10 | `hardyZ_abs_eq` | HardyZRealV2 | `‖Z(t)‖ = ‖ζ(1/2+it)‖` |
| A10 | `hardyZ_continuous` | HardyZRealV2 | `Z` is continuous |
| A11 | `xi_functional_eq` | RiemannXi | `ξ(1-s) = ξ(s)` |
| A11 | `xi_entire` | RiemannXi | `ξ` is entire |
| A12 | `completed_zeta_real_on_critical_line` | CompletedZetaCriticalLine | `Im Λ(1/2+it) = 0` |
| A13 | `completed_zeta_conj` | CompletedZetaCriticalLine | `Λ(s̄) = Λ̄(s)` |
| A14 | `zeta_bound_re_two` | ZetaBoundsNorm | `‖ζ(2+it)‖ < 2` |

## Category B: Transferred via Bridge (3 theorems)

These use Aristotle local types and are transferred to canonical `chebyshevTheta`
via the bridge lemmas in `Tests/EquivalenceTest.lean`.

| # | Name | Source | Original Type | Canonical Type |
|---|------|--------|---------------|----------------|
| B1 | `chebyshevTheta_linear_bound` | ThetaLinearBoundV2 | `theta n ≤ C * n` | `chebyshevTheta n ≤ C * n` |
| B2 | `chebyshevTheta_doubling` | ThetaLinearBoundV2 | `theta(2n) - theta(n) ≤ 2n log 2` | Same in canonical types |
| B3 | `chebyshevTheta_diff_le_log_choose` | ChebyshevThetaV2 | `theta(2n) - theta(n) ≤ log C(2n,n)` | Same in canonical types |

## Category C: Conditional Reductions (2 theorems)

These require hypotheses but prove non-trivial algebraic reductions.

| # | Name | Source | Hypotheses | Conclusion |
|---|------|--------|------------|------------|
| C1 | `riemann_von_mangoldt_from_hypotheses` | RiemannVonMangoldt | Stirling + S(T) bound + Arg Principle | RvM with uniform error |
| C2 | `S_T_uniform_bound` | RiemannVonMangoldt | None (unconditional) | `‖S(T)‖ ≤ C log T` uniformly |

## What Is NOT Transferred

### Vacuous Results
- `RiemannVonMangoldtModule.riemann_von_mangoldt` — C = |LHS|/log T (depends on T)
- `RiemannVonMangoldtModule.Theta_asymp` — C = |LHS|*T
- `RiemannVonMangoldtModule.S_T_bound` — C = |LHS|/log T
- `RiemannVonMangoldtModule.NZeros_eq_Theta_S` — C = |LHS|

### Requires Unproved Sub-Hypotheses
- `SchmidtOscillationInfinite.psi_minus_x_oscillates_v5` — needs Hardy zeros + explicit formula
- `ZeroCountingNew.zero_counting_main_term` — needs `RiemannVonMangoldtProperty`

### Additional Aristotle Theorems Available (not yet transferred)
These are sorry-free but were not included in the initial transfer because they
are either highly specialized infrastructure or would need additional bridge work:

- **IntegralLogAsymp**: `integral_log_asymp` (∫ log = T log T - T + 1)
- **HarmonicSumIntegral**: `harmonicSum_eq_harmonic`, `integral_harmonicSum_asymp`
- **BinetStirling**: Various Stirling approximation lemmas
- **ZetaConjugation**: Alternative conjugation proofs
- **FunctionalEquationHyp**: `riemannZeta_eq_chiFE_mul` (already an instance)

## Assumption Class Impact

Of the 58 hypothesis classes in `Assumptions.lean`, these transfers satisfy **0** directly.
The transferred theorems provide *building blocks* but no single transfer fills an
assumption class because:

1. Most assumption classes require deep analytic results (Perron, Landau, explicit formula)
2. The Chebyshev bounds (B1-B3) are weaker than what the classes need
3. The 3-4-1 inequality (A1-A2) needs to be extended to a full zero-free region
4. The Schmidt oscillation (A8) needs the explicit formula to connect to ψ(x)

## Bridge Architecture

```
Mathlib (Chebyshev.psi, riemannZeta, ...)
  ↑
Basic/ (chebyshevPsi, chebyshevTheta — thin wrappers)
  ↑
Tests/EquivalenceTest.lean (bridge lemmas: theta_bridge, psi_bridge, nzeros_bridge)
  ↑
Bridge/AristotleTransfers.lean (19 transferred theorems)
  ↑
Aristotle/ (sorry-free source theorems)
```
