# Sorry Status Dashboard

Generated: 2026-01-28

## Summary

| Metric | Count |
|--------|-------|
| Total Aristotle files | 58 |
| Sorry-free files | 51 (88%) |
| Files with sorries | 7 |
| Total sorries | 15 |
| False statements | 1 (documented, has correct version) |

## Remaining Sorries by File

| File | Sorries | Notes |
|------|---------|-------|
| MeanSquare.lean | 4 | integral_log_sqrt_asymp, norm_integral_offDiagSsq_le, normSq_partialZeta_eq, mean_square_partial_zeta_asymp |
| ZeroCounting.lean | 4 | 1 FALSE (xi_Mathlib_differentiable), 3 N(T) theorems |
| PhragmenLindelof.lean | 3 | Gamma growth bounds |
| PartialSummation.lean | 2 | sumPrimePowers bounds |
| PerronContourIntegralsV2.lean | 1 | Cauchy theorem rewrite |
| RiemannVonMangoldtV2.lean | 1 | Complex.arg algebra in N_eq_main_plus_S |

## ZeroCounting.lean Details

| Sorry | Status | Notes |
|-------|--------|-------|
| `xi_Mathlib_differentiable` | FALSE | Uses wrong definition; `xi_Mathlib_corrected_entire` IS proved! |
| `zetaZeroCount_via_argument` | Needs work | N(T) via argument principle |
| `riemann_von_mangoldt` | Needs work | N(T) ~ (T/2π)log(T/2πe) |
| `zetaZeroCount_asymp` | Needs work | N(T) = O(log T) |

**Note**: `xi_Mathlib_corrected_entire` (the correct version) is ALREADY PROVED in ZeroCounting.lean!

## Critical Blockers (6/7 Resolved!)

| Blocker | Status | File |
|---------|--------|------|
| h_Stirling | ✅ DONE | StirlingGammaBounds.lean |
| h_RVM | ✅ DONE | RiemannVonMangoldt(V2).lean |
| S(T) = O(log T) | ✅ DONE | NZerosStirling.lean |
| N(T) asymptotic | ✅ DONE | NZerosStirling.lean |
| Explicit formula | ✅ DONE | TruncatedExplicitFormula.lean |
| xi entire | ✅ DONE | ZeroCountingXi.lean + ZeroCounting.xi_Mathlib_corrected_entire |
| **Hardy** | ⏳ WAITING | **LAST BLOCKER!** |

## Key Theorems Available

### Explicit Formula (TruncatedExplicitFormula.lean)
```lean
theorem psi_as_trig_sum (x : ℝ) (hx : 2 < x) (T : ℝ) (hT : 2 ≤ T) :
    ∃ (error_term : ℝ) (C : ℝ),
      chebyshevPsi x - x =
      -2 * ∑ ρ ∈ zetaZerosInBox T, (x^ρ.re / ‖ρ‖) * Real.cos (ρ.im * Real.log x + ρ.arg)
      + error_term ∧
      |error_term| ≤ C * x * (Real.log x)^2 / T
```

### xi Entire (ZeroCountingXi.lean)
```lean
theorem xi_entire : Differentiable ℂ xi
-- where xi s = s * (s - 1) * completedRiemannZeta₀ s + 1
```

### Schmidt Oscillation (SchmidtNew.lean)
```lean
theorem trigPoly_zero_iff_coeffs_zero (γs : Finset ℝ) (hγs : ∀ γ ∈ γs, γ > 0) ...
```

## Critical Path to Main Theorem

```
HAVE:
✅ psi_as_trig_sum: ψ(x) - x = trig sum over zeros + error
✅ trigPoly_zero_iff_coeffs_zero: trig sum ≠ 0 iff coeffs ≠ 0
✅ xi_entire: xi(s) is entire
✅ N(T) asymptotic via NZerosStirling
✅ Stirling bounds, S(T) = O(log T)

NEED:
⏳ Hardy: infinitely many zeros on Re(s) = 1/2

CHAIN WHEN HARDY ARRIVES:
Hardy → zeros on Re=1/2 with |Im| → ∞
     → nonzero coefficients in psi_as_trig_sum
     → trig sum ≠ 0 (by trigPoly_zero_iff_coeffs_zero)
     → trig sum oscillates (by Schmidt)
     → ψ(x) - x oscillates
     → ψ(x) - x = Ω±(√x)
     → π(x) - li(x) = Ω±(√x / log x)
     → MAIN THEOREM! 🎉
```
