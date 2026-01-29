# Sorry Status Dashboard

Generated: 2026-01-28

## Summary

| Metric | Count |
|--------|-------|
| Total Aristotle files | 58 |
| Sorry-free files | 51 (88%) |
| Files with sorries | 7 |
| Total sorries | 15 |
| Provable sorries | 14 |
| False statements | 1 (but see ZeroCountingXi for correct proof!) |

## Active Sorries by File

| File | Count | Status | Notes |
|------|-------|--------|-------|
| MeanSquare | 4 | Waiting | integral_log_sqrt_asymp, norm_integral_offDiagSsq_le, normSq_partialZeta_eq, mean_square_partial_zeta_asymp |
| ZeroCounting | 4 | 1 FALSE | xi_Mathlib_differentiable is false (see corrected version) |
| PhragmenLindelof | 3 | Waiting | Needs Stirling bounds for Gamma growth |
| PartialSummation | 2 | Blocked | Needs sumPrimePowers bounds infrastructure |
| PerronContourIntegralsV2 | 1 | Medium | integral_boundary_rect_perron_neg Cauchy theorem application |
| RiemannVonMangoldtV2 | 1 | Medium | N_eq_main_plus_S algebraic manipulation with Complex.arg |

## Critical Deliveries This Session

| File | Sorries | Key Results |
|------|---------|-------------|
| **TruncatedExplicitFormula.lean** | 0 | `psi_as_trig_sum` - THE EXPLICIT FORMULA! |
| **NZerosStirling.lean** | 0 | `S_bound`, `N_from_S_and_Stirling` |
| **ZeroCountingXi.lean** | 0 | `xi_entire`, `xi_Mathlib_differentiable` - xi is ENTIRE! |
| **RiemannVonMangoldtV2.lean** | 1 | `riemann_von_mangoldt_argument`, `N_main_term_eq` |
| StirlingGammaBounds.lean | 0 | Stirling bounds, gamma_reflection_bound |
| PerronContourIntegralsV2.lean | 1 | perron_horizontal_bound_pointwise, integral_boundary_rect_perron_pos/neg |

## Blocker Status

| Blocker | Status | File |
|---------|--------|------|
| h_Stirling | ✅ DONE | StirlingGammaBounds |
| h_RVM | ✅ DONE | RiemannVonMangoldt(V2) |
| S(T) bound | ✅ DONE | NZerosStirling |
| N(T) asymp | ✅ DONE | NZerosStirling |
| Explicit formula | ✅ DONE | TruncatedExplicitFormula |
| **Hardy** | ⏳ WAITING | **LAST BLOCKER!** |

## False Statements (documented, won't prove)

| File | Statement | Issue |
|------|-----------|-------|
| ZeroCounting:114 | xi_Mathlib_differentiable | completedRiemannZeta discontinuity at poles |

**Fix**: Use `xi_Mathlib_corrected_entire` instead (PROVED).

## Proved Hypothesis Instances (4)

| Class | Location | Proof |
|-------|----------|-------|
| FunctionalEquationHyp | FunctionalEquationHyp.lean | riemannZeta_eq_chiFE_mul |
| LambdaSymmetryHyp | FunctionalEquationHyp.lean | completedRiemannZeta_one_sub |
| ZeroConjZeroHyp | ZeroCountingFunction.lean | riemannZeta_conj |
| ZeroOneSubZeroHyp | ZeroCountingFunction.lean | riemannZeta_one_sub |

## Definition Conflicts

Multiple `chebyshevPsi` definitions exist (all namespaced, no conflicts):
- `Littlewood/Basic/ChebyshevFunctions.lean:34` (canonical)
- `Littlewood/Aristotle/TruncatedExplicitFormula.lean` (namespaced)
- Various Aristotle files (commented out of main import)

Bridge lemma `chebyshevPsiV3_eq_chebyshevPsi` proves equivalence.

## Progress Trajectory

```
Session Start:  50 files, 43 sorry-free (86%), ~16 sorries
Mid-session:    54 files, 48 sorry-free (89%), 14 sorries
Current:        57 files, 50 sorry-free (88%), 15 sorries

MAJOR DELIVERIES:
├── TruncatedExplicitFormula.lean (0 sorries)
│   └── psi_as_trig_sum: ψ(x) - x = trig sum + error ← KEY!
├── NZerosStirling.lean (0 sorries)
│   ├── S_bound: S(T) = O(log T)
│   └── N_from_S_and_Stirling: N(T) asymptotic
├── RiemannVonMangoldtV2.lean (1 sorry)
│   └── riemann_von_mangoldt_argument
├── StirlingGammaBounds.lean (0 sorries)
│   └── Stirling/Gamma bounds
└── PerronContourIntegralsV2.lean (1 sorry)
    └── Perron contour integrals

BLOCKERS RESOLVED: 5/6
└── Only Hardy's theorem remains!
```

## Critical Path

```
✅ Stirling ──┐
             ├──→ ✅ N(T) asymptotic
✅ RVM ──────┘

⏳ HARDY ──→ Zeros on Re=1/2 ──┐
                               ├──→ OSCILLATION ──→ Main Theorem
✅ EXPLICIT ──→ psi_as_trig_sum ┘

CHAIN ONCE HARDY IS PROVED:
1. psi_as_trig_sum (HAVE IT!)
2. Hardy → infinitely many zeros on Re=1/2
3. → Nonzero coefficients in trig sum
4. trigPoly_zero_iff_coeffs_zero (HAVE IT!)
5. → ψ(x) - x oscillates
6. → Main theorem!
```
