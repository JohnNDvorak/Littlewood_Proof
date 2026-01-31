/-
# Aristotle Transfers

Master file transferring all sorry-free Aristotle theorems to canonical project types.

## Organization

### Category A: Already Canonical (no bridging needed)
These Aristotle theorems already use Mathlib types directly.

### Category B: Bridged via EquivalenceTest
These use local Aristotle types (theta : ℕ → ℝ, psi : ℕ → ℝ, NZeros)
and are transferred to canonical types via bridge lemmas.

### Category C: Conditional but Genuine
These require hypotheses but prove non-trivial reductions.

## What Is NOT Transferred

### Vacuous Results (C depends on T)
- RiemannVonMangoldtModule.riemann_von_mangoldt: C = |LHS|/log T
- RiemannVonMangoldtModule.Theta_asymp: C = |LHS|*T
- RiemannVonMangoldtModule.S_T_bound: C = |LHS|/log T
- RiemannVonMangoldtModule.NZeros_eq_Theta_S: C = |LHS|

### Conditional on Unproved Sub-Hypotheses
- SchmidtOscillationInfinite.psi_minus_x_oscillates_v5: requires Hardy zeros + explicit formula
- ZeroCountingNew.zero_counting_main_term: requires RiemannVonMangoldtProperty
-/

import Mathlib
import Littlewood.Aristotle.ThreeFourOneV2
import Littlewood.Aristotle.LaurentExpansion
import Littlewood.Aristotle.ThetaLinearBoundV2
import Littlewood.Aristotle.ChebyshevThetaV2
import Littlewood.Aristotle.SchmidtNew
import Littlewood.Aristotle.HardyZRealV2
import Littlewood.Aristotle.RiemannXi
import Littlewood.Aristotle.CompletedZetaCriticalLine
import Littlewood.Aristotle.ZetaBoundsNorm
import Littlewood.Aristotle.RiemannVonMangoldt
import Littlewood.Basic.ChebyshevFunctions
import Littlewood.ZetaZeros.ZeroCountingFunction
import Littlewood.Tests.EquivalenceTest

set_option maxHeartbeats 400000

noncomputable section

namespace AristotleTransfers

open Complex ChebyshevExt

-- ============================================================
-- CATEGORY A: Already Canonical (Mathlib types, no bridging)
-- ============================================================

/-! ### A1: Zeta Non-Vanishing on Re(s) = 1

From ThreeFourOneV2. Uses only Mathlib's `riemannZeta`.
This is a key ingredient for the Prime Number Theorem. -/

theorem zeta_ne_zero_on_re_one (t : ℝ) (ht : t ≠ 0) :
    riemannZeta (1 + I * t) ≠ 0 :=
  zeta_ne_zero_re_one_v2 t ht

/-! ### A2: 3-4-1 Product Inequality

From ThreeFourOneV2. For σ > 1: |ζ(σ)|³ |ζ(σ+it)|⁴ |ζ(σ+2it)| ≥ 1 -/

theorem three_four_one (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    ‖riemannZeta σ‖ ^ 3 * ‖riemannZeta (σ + I * t)‖ ^ 4 *
    ‖riemannZeta (σ + 2 * I * t)‖ ≥ 1 :=
  three_four_one_v2 σ hσ t

/-! ### A3: Trigonometric Inequality (3 + 4cos θ + cos 2θ ≥ 0)

From ThreeFourOneV2. Foundation of the 3-4-1 method. -/

theorem trig_inequality (θ : ℝ) : 3 + 4 * Real.cos θ + Real.cos (2 * θ) ≥ 0 :=
  trig_ineq_v2 θ

/-! ### A4: Laurent Expansion — Residue of -ζ'/ζ at s = 1

From LaurentExpansion. The key fact that (s-1)·(-ζ'/ζ(s)) → 1 as s → 1. -/

theorem zeta_logderiv_residue :
    Filter.Tendsto (fun s => (s - 1) * (-deriv riemannZeta s / riemannZeta s))
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds 1) :=
  neg_zeta_logDeriv_residue_one

/-! ### A5: (s-1)² ζ'(s) → -1 as s → 1

From LaurentExpansion. Characterizes the Laurent expansion of ζ near its pole. -/

theorem zeta_deriv_residue :
    Filter.Tendsto (fun s => (s - 1) ^ 2 * deriv riemannZeta s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds (-1)) :=
  sub_sq_mul_zeta_deriv_tendsto

/-! ### A6: ζ(s) ≠ 0 near s = 1

From LaurentExpansion. Expressed as an eventually-holds filter statement. -/

theorem zeta_ne_zero_near_one :
    ∀ᶠ s in nhdsWithin 1 {(1 : ℂ)}ᶜ, riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_near_one

/-! ### A7: (s-1)·ζ(s) is analytic at s = 1

From LaurentExpansion. Shows the pole is simple. -/

theorem zeta_mul_sub_one_analytic : AnalyticAt ℂ zetaMulSubOne 1 :=
  zetaMulSubOne_analyticAt_one

/-! ### A8: Schmidt Oscillation Theorem

From SchmidtNew. If a non-trivial trigonometric polynomial
  f(t) = Σ_{γ ∈ S} c_γ cos(γt + φ_γ)
has some c_γ ≠ 0, then f changes sign infinitely often.

This is the key oscillation detection tool. -/

theorem schmidt_oscillation_theorem (γs : Finset ℝ) (hγs : ∀ γ ∈ γs, γ > 0)
    (c phi : ℝ → ℝ) (hc : ∃ γ ∈ γs, c γ ≠ 0) :
    ∀ M, ∃ t₁ t₂, t₁ > M ∧ t₂ > M ∧
    (∑ γ ∈ γs, c γ * Real.cos (γ * t₁ + phi γ)) > 0 ∧
    (∑ γ ∈ γs, c γ * Real.cos (γ * t₂ + phi γ)) < 0 :=
  schmidt_oscillation γs hγs c phi hc

/-! ### A9: Trig Polynomial Zero ↔ All Coefficients Zero

From SchmidtNew. Characterizes when a trig polynomial is identically zero. -/

theorem trig_poly_zero_iff (γs : Finset ℝ) (hγs : ∀ γ ∈ γs, γ > 0)
    (c phi : ℝ → ℝ) :
    (∀ t : ℝ, ∑ γ ∈ γs, c γ * Real.cos (γ * t + phi γ) = 0) ↔ ∀ γ ∈ γs, c γ = 0 :=
  trigPoly_zero_iff_coeffs_zero γs hγs c phi

/-! ### A10: Hardy Z Function Properties

From HardyZRealV2. The Hardy Z function satisfies:
  - Z(t) is real-valued
  - Z(t) = 0 ↔ ζ(1/2 + it) = 0
  - |Z(t)| = |ζ(1/2 + it)|
  - Z is continuous
  - Z has constant sign between consecutive zeros -/

theorem hardyZ_is_real (t : ℝ) : (hardyZV2 t).im = 0 :=
  hardyZV2_real t

theorem hardyZ_zero_iff (t : ℝ) : hardyZV2 t = 0 ↔ riemannZeta (1/2 + I * t) = 0 :=
  hardyZV2_zero_iff_zeta_zero t

theorem hardyZ_abs_eq (t : ℝ) : ‖hardyZV2 t‖ = ‖riemannZeta (1/2 + I * t)‖ :=
  hardyZV2_abs_eq_zeta_abs t

theorem hardyZ_continuous : Continuous hardyZV2 :=
  continuous_hardyZV2

/-! ### A11: ξ Function Properties

From RiemannXi (namespace RiemannXiModule).
  - ξ(1-s) = ξ(s) (functional equation)
  - ξ is entire (differentiable everywhere) -/

theorem xi_functional_eq (s : ℂ) :
    RiemannXiModule.RiemannXi (1 - s) = RiemannXiModule.RiemannXi s :=
  RiemannXiModule.RiemannXi_one_sub s

theorem xi_entire : Differentiable ℂ RiemannXiModule.RiemannXi :=
  RiemannXiModule.differentiable_RiemannXi

/-! ### A12: Completed Zeta Real on Critical Line

From CompletedZetaCriticalLine.
  Λ(1/2 + it) has zero imaginary part for all real t. -/

theorem completed_zeta_real_on_critical_line (t : ℝ) :
    (completedRiemannZeta (1/2 + I * t)).im = 0 :=
  CompletedZetaCriticalLine.completedRiemannZeta_critical_line_real t

/-! ### A13: Completed Zeta Conjugation Symmetry

From CompletedZetaCriticalLine.
  Λ(s̄) = Λ̄(s) -/

theorem completed_zeta_conj (s : ℂ) :
    completedRiemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (completedRiemannZeta s) :=
  completedRiemannZeta_conj s

/-! ### A14: Zeta Bound on Re(s) = 2

From ZetaBoundsNorm. -/

theorem zeta_bound_re_two (t : ℝ) :
    ‖riemannZeta (2 + I * t)‖ ≤ ‖riemannZeta 2‖ ∧ ‖riemannZeta 2‖ < 2 :=
  zeta_bound_two_line t

-- ============================================================
-- CATEGORY B: Transferred via Bridge Lemmas
-- ============================================================

/-! ### B1: Chebyshev θ(n) = O(n)

From ThetaLinearBoundV2, transferred to canonical `chebyshevTheta`.
Original: ∃ C, ∀ n, ThetaLinearBoundV2.theta n ≤ C * n
Transfer: ∃ C, ∀ n : ℕ, chebyshevTheta n ≤ C * n -/

theorem chebyshevTheta_linear_bound :
    ∃ C : ℝ, ∀ n : ℕ, chebyshevTheta (n : ℝ) ≤ C * n :=
  EquivalenceTest.chebyshev_theta_linear_from_aristotle

/-! ### B2: θ(2n) - θ(n) ≤ 2n log 2

From ThetaLinearBoundV2, transferred to canonical `chebyshevTheta`. -/

theorem chebyshevTheta_doubling (n : ℕ) (hn : 0 < n) :
    chebyshevTheta ((2 * n : ℕ) : ℝ) - chebyshevTheta (n : ℝ) ≤ 2 * n * Real.log 2 := by
  rw [EquivalenceTest.theta_bridge (2 * n), EquivalenceTest.theta_bridge n]
  exact ThetaLinearBoundV2.theta_two_mul_sub_theta_le n hn

/-! ### B3: θ(2n) - θ(n) ≤ log C(2n, n)

From ChebyshevThetaV2, transferred to canonical `chebyshevTheta`. -/

theorem chebyshevTheta_diff_le_log_choose (n : ℕ) (hn : 0 < n) :
    chebyshevTheta ((2 * n : ℕ) : ℝ) - chebyshevTheta (n : ℝ) ≤
    Real.log (Nat.choose (2 * n) n) := by
  rw [EquivalenceTest.theta_bridge (2 * n), EquivalenceTest.theta_bridge n]
  rw [EquivalenceTest.aristotle_thetas_agree, EquivalenceTest.aristotle_thetas_agree]
  exact ChebyshevThetaV2.theta_diff_le_log_choose n hn

-- ============================================================
-- CATEGORY C: Conditional but Genuine Reductions
-- ============================================================

/-! ### C1: Riemann-von Mangoldt Reduction

From RiemannVonMangoldt. Given three standard analytic number theory
inputs (Stirling approximation, S(T) bound, Argument Principle connection),
proves the Riemann-von Mangoldt formula with uniform error bound.

This is a genuine reduction — the algebra of combining three bounds
into the final asymptotic is non-trivial. -/

theorem riemann_von_mangoldt_from_hypotheses
    (hTheta : ∃ C, ∀ T : ℝ, 2 ≤ T →
      |RiemannVonMangoldtModule.Theta_cont T - RiemannVonMangoldtModule.Theta_approx T| ≤ C / T)
    (hS : ∃ C, ∀ T, 2 ≤ T → |RiemannVonMangoldtModule.S_T T| ≤ C * Real.log T)
    (hN : ∃ C, ∀ T, 2 ≤ T →
      |(RiemannVonMangoldtModule.NZeros T : ℝ) -
        (1 / Real.pi * RiemannVonMangoldtModule.Theta_cont T + 1 +
          RiemannVonMangoldtModule.S_T T)| ≤ C) :
    ∃ C, ∀ T, 2 ≤ T →
    |(RiemannVonMangoldtModule.NZeros T : ℝ) -
      ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7/8)| ≤
    C * Real.log T :=
  RiemannVonMangoldtModule.riemann_von_mangoldt_conditional hTheta hS hN

/-! ### C2: S(T) Uniform Bound

From RiemannVonMangoldt. A genuine uniform bound (not vacuous).
|S(T)| ≤ C log T for all T ≥ 2, where C does NOT depend on T.

NOTE: This uses the trivial bound |arg(z)| ≤ π, giving C ≈ π²/(log 2)².
A sharp bound would use Backlund's theorem. -/

theorem S_T_uniform_bound :
    ∃ C, ∀ T, 2 ≤ T → |RiemannVonMangoldtModule.S_T T| ≤ C * Real.log T :=
  RiemannVonMangoldtModule.S_T_bound_uniform

-- ============================================================
-- SUMMARY
-- ============================================================

/-!
## Transfer Summary

### Category A (14 theorems, already canonical):
- A1: zeta_ne_zero_on_re_one — ζ(1+it) ≠ 0 for t ≠ 0
- A2: three_four_one — |ζ(σ)|³|ζ(σ+it)|⁴|ζ(σ+2it)| ≥ 1
- A3: trig_inequality — 3 + 4cos θ + cos 2θ ≥ 0
- A4: zeta_logderiv_residue — (s-1)(-ζ'/ζ) → 1 at s = 1
- A5: zeta_deriv_residue — (s-1)²ζ'(s) → -1 at s = 1
- A6: zeta_ne_zero_near_one — ζ ≠ 0 in punctured neighborhood of 1
- A7: zeta_mul_sub_one_analytic — (s-1)ζ(s) analytic at s = 1
- A8: schmidt_oscillation_theorem — trig polynomial sign changes
- A9: trig_poly_zero_iff — trig polynomial = 0 ↔ all coefficients = 0
- A10: hardyZ_is_real, hardyZ_zero_iff, hardyZ_abs_eq, hardyZ_continuous
- A11: xi_functional_eq, xi_entire
- A12: completed_zeta_real_on_critical_line
- A13: completed_zeta_conj
- A14: zeta_bound_re_two

### Category B (3 theorems, transferred via bridge):
- B1: chebyshevTheta_linear_bound — θ(n) = O(n) in canonical types
- B2: chebyshevTheta_doubling — θ(2n) - θ(n) ≤ 2n log 2
- B3: chebyshevTheta_diff_le_log_choose — θ(2n) - θ(n) ≤ log C(2n,n)

### Category C (2 theorems, conditional reductions):
- C1: riemann_von_mangoldt_from_hypotheses — RvM conditional on 3 inputs
- C2: S_T_uniform_bound — |S(T)| ≤ C log T (genuine uniform bound)
-/

end AristotleTransfers
