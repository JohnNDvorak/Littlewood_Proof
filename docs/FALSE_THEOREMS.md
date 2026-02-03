# Theorems That Are FALSE as Stated

## Issue
Several theorems in the Aristotle files are FALSE at trivial zeros of zeta(s),
specifically at s = -2, -4, -6, ... where Gamma(s/2) has poles (and Lean's
`Complex.Gamma` returns 0 at these points).

## Affected Theorems

### FunctionalEquation.lean

- **`zeta_functional_equation`** (line 33-36)
  - States: `pi^(-s/2) * Gamma(s/2) * zeta(s) = pi^(-(1-s)/2) * Gamma((1-s)/2) * zeta(1-s)`
  - Hypotheses: `s != 0`, `s != 1`
  - **Counterexample**: At s = -2:
    - LHS = `pi^1 * Gamma(-1) * zeta(-2)` = `pi * 0 * 0` = `0`
    - RHS = `Gamma_R(3) * zeta(3)` = `completedRiemannZeta(3)` != 0
  - **Fix**: Add hypothesis `Gamma_R s != 0` or `0 < s.re`

- **`completed_zeta_zeros_eq_zeta_zeros`** (line 43-45)
  - States: `completedRiemannZeta s = 0 <-> riemannZeta s = 0`
  - Hypotheses: `s != 0`, `s != 1`
  - **Counterexample**: At s = -2:
    - `riemannZeta(-2) = completedRiemannZeta(-2) / Gamma_R(-2) = .../0 = 0` in Lean
    - But `completedRiemannZeta(-2) = completedRiemannZeta(3)` != 0
    - So `riemannZeta(-2) = 0` but `completedRiemannZeta(-2) != 0`
  - **Fix**: Add `0 < s.re` or `0 < s.re /\ s.re < 1`

### ZeroCounting.lean

- **`xi_Mathlib_eq_RiemannXi`** (line 120-122)
  - States: `xi_Mathlib s = RiemannXi s`
  - Hypotheses: `s != 0`, `s != 1`
  - **Counterexample**: At s = -2:
    - `xi_Mathlib(-2) = (1/2)*(-2)*(-3)*completedRiemannZeta(-2)` != 0
    - `RiemannXi(-2) = (1/2)*(-2)*(-3)*pi^1*Gamma(-1)*zeta(-2)` = `...* 0 * 0` = 0
  - **Fix**: Add `Gamma_R s != 0` or `0 < s.re`

### CoreLemmas/LandauLemma.lean

- **`zeta_zero_implies_vonMangoldt_singularity`** (line 379-395)
  - States: `¬AnalyticAt ℂ (LSeries (fun n => vonMangoldt n)) ρ` for a zeta zero ρ
    with 0 < Re(ρ) < 1
  - **The statement is FALSE.**
  - **Reason**: `LSeries f s = ∑' n, LSeries.term f s n` uses Lean's `tsum`, which
    returns 0 when the series is not summable (via `tsum_eq_zero_of_not_summable`).
    The von Mangoldt Dirichlet series has abscissa of convergence at Re(s) = 1.
    For Re(ρ) < 1, the series is not summable, so `LSeries Λ s = 0` for all s near ρ.
    The constant zero function IS analytic, so `AnalyticAt ℂ (LSeries Λ) ρ` is TRUE,
    making `¬AnalyticAt` FALSE.
  - **Impact**: This sorry is isolated — not used by any other theorem in the project.
  - **Fix**: The intended argument requires using the *analytic continuation* of the
    Dirichlet series (which equals `-ζ'/ζ(s)` for Re(s) > 1) rather than the raw
    `LSeries` function. This would need either:
    1. A different function definition (e.g., `-deriv riemannZeta s / riemannZeta s`)
    2. Or use Mathlib's `meromorphicAt` framework
    The identity theorem argument would then show: if `-ζ'/ζ` were analytic at ρ
    (contradicting `ZetaLogDerivPoleHyp`), derive False.

## Root Cause

In Lean's Mathlib formalization:
- `Complex.Gamma` returns 0 at non-positive integers (s = 0, -1, -2, ...)
- `riemannZeta s = completedRiemannZeta s / Gamma_R s`
- When `Gamma_R s = 0`, Lean's division-by-zero convention gives `riemannZeta s = 0`
- But `completedRiemannZeta s` != 0 at these points (it's entire and satisfies the functional equation)

This creates a discrepancy: `Gamma_R s * riemannZeta s` = `0 * 0` = 0, but
`completedRiemannZeta s` != 0.

## Impact on Main Proof

The main theorems (littlewood_psi, littlewood_pi_li) are **NOT affected** because:
1. They work within the critical strip (0 < Re(s) < 1)
2. Trivial zeros at s = -2, -4, ... are outside this region
3. `Gamma_R s != 0` for `Re(s) > 0`, so the issue never arises
4. The correctly-stated `xi_Mathlib_zeros_eq_zeta_zeros` in ZeroCounting.lean
   (with hypotheses `0 < s.re` and `s.re < 1`) IS proved and correct

## Recommended Fix

For each affected theorem, either:
1. Add hypothesis `(hs : 0 < s.re)` to restrict to the right half-plane
2. Or add `(hs : 0 < s.re /\ s.re < 1)` for critical strip only
3. Or replace `sorry` with a comment `-- FALSE as stated, see docs/FALSE_THEOREMS.md`

For now, leaving as `sorry` is correct behavior -- Lean won't accept a false proof.
