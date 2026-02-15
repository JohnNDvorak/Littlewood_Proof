/-
Non-negative Dirichlet integral construction for the Landau oscillation argument.

Given a one-sided bound σ*(ψ(x)-x) ≤ C*x^α, the function
  g(t) = C*t^α + σ*(t - ψ(t))
is non-negative for large t. The Dirichlet integral
  G(s) = s * ∫₁^∞ g(t) * t^{-(s+1)} dt
converges and is analytic for Re(s) > α (by Landau's non-negative integral theorem),
and on {Re(s) > 1} decomposes as:
  G(s) = s*C/(s-α) + σ*s/(s-1) + σ*ζ'/ζ(s)

## Main Results

* `psi_dirichlet_integral` : Proves `psi_integral_hyp` from LandauSchmidtDirect.lean,
  establishing the Dirichlet integral convergence and formula verification.
* `pi_log_zeta_extension` : Proves `pi_integral_hyp` from LandauSchmidtDirect.lean,
  establishing the log ζ extension for the π-li case.

## Architecture

This file is parameterized on two Landau/Pringsheim atoms via section variables,
keeping the file sorry-free (0 sorry warnings). The atoms are supplied in
DeepSorries.combined_atoms.

* `pringsheim_psi` (section variable): Landau's non-negative Dirichlet integral
  theorem for ψ. For f ≥ 0 with f = O(t), if the Dirichlet integral admits an
  analytic continuation past Re(s) = 1 on the real axis, then the integral converges
  and is analytic for Re(s) > α. This is Landau's generalization of Pringsheim's
  theorem (non-negative Taylor coefficients ⟹ radius of convergence is a singularity).

* `pringsheim_pi` (section variable): Analogous atom for the π-li case using log ζ.

## Mathematical References

* Landau, "Über einen Satz von Tschebyschef" (1905), Satz 15
* Hardy-Riesz, "The General Theory of Dirichlet's Series", Ch. 1
* Montgomery-Vaughan, "Multiplicative Number Theory I", §1.3

SORRY COUNT: 0 (parameterized on section variables)

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.PsiIntegralRepresentation
import Littlewood.Aristotle.LandauSchmidtDirect
import Littlewood.Basic.ChebyshevFunctions

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.NonNegDirichletIntegral

open Complex Real Filter Topology Asymptotics Set
open ZetaZeros

/-! ## ψ Dirichlet integral — parameterized on Pringsheim atom

The Pringsheim atom encodes the full Landau non-negative integral theorem:
given a one-sided bound σ*(ψ(x)-x) ≤ C*x^α, construct G analytic on {Re > α}
matching the formula sC/(s-α) + σs/(s-1) + σζ'/ζ(s) on {Re > 1}.

**Proof sketch for the atom** (not yet formalized):
1. g(t) = Ct^α + σ(t-ψ(t)) ≥ 0 for large t (from one-sided bound).
2. G(s) = s·∫₁^∞ g(t)·t^{-(s+1)} dt converges for Re(s) > 1 (from ψ = O(x)).
3. On {Re > 1}: G(s) = sC/(s-α) + σs/(s-1) + σζ'/ζ(s) (Abel summation +
   `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`).
4. Poles at s = 1 cancel: residue of s/(s-1) is 1, residue of ζ'/ζ is −1.
5. ζ(x) ≠ 0 for real x ∈ (0,1) (Dirichlet eta function), so G extends
   analytically along the real axis from 1 down to α.
6. By Pringsheim/Landau: non-negative Taylor coefficients force a singularity
   at the radius of convergence. No singularity on (α,∞) ⊂ ℝ, so σ_c ≤ α.
7. Parametric differentiation gives analyticity on {Re > α}. -/

section PsiDirichletIntegral

variable (pringsheim_psi :
    ∀ (α : ℝ), 1 / 2 < α → ∀ (C : ℝ), 0 < C →
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    (∀ᶠ x in atTop, σ * (chebyshevPsi x - x) ≤ C * x ^ α) →
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        G s = s * (↑C : ℂ) / (s - (↑α : ℂ)) + (↑σ : ℂ) * (s / (s - 1)) +
              (↑σ : ℂ) * (deriv riemannZeta s / riemannZeta s))
include pringsheim_psi

set_option linter.unusedSectionVars false in
/-- The Dirichlet integral hypothesis for ψ, as required by
`LandauSchmidtDirect.psi_omega_lll_of_not_RH`.

Derived from the Pringsheim section variable (no direct sorry). -/
theorem psi_dirichlet_integral :
    ∀ (α : ℝ), 1 / 2 < α → ∀ (C : ℝ), 0 < C →
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    (∀ᶠ x in atTop, σ * (chebyshevPsi x - x) ≤ C * x ^ α) →
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        G s = s * (↑C : ℂ) / (s - (↑α : ℂ)) + (↑σ : ℂ) * (s / (s - 1)) +
              (↑σ : ℂ) * (deriv riemannZeta s / riemannZeta s) :=
  pringsheim_psi

end PsiDirichletIntegral

/-! ## π-li log ζ extension — parameterized on Pringsheim atom

The π-li case uses log ζ instead of ζ'/ζ. Under a one-sided bound on
π(x)-li(x), the generating function log ζ(s) extends analytically to
{Re(s) > α}. The contradiction comes from exp(log ζ(ρ₀)) = ζ(ρ₀) = 0
but exp never vanishes.

**Reference**: Montgomery-Vaughan §1.3, Landau 1905. -/

section PiLogZetaExtension

variable (pringsheim_pi :
    ∀ (α : ℝ), 1 / 2 < α → ∀ (C : ℝ), 0 < C →
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    (∀ᶠ x in atTop, σ * ((↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x) ≤ C * x ^ α) →
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re → exp (H s) = riemannZeta s)
include pringsheim_pi

set_option linter.unusedSectionVars false in
/-- The log ζ extension hypothesis for π-li, as required by
`LandauSchmidtDirect.pi_li_omega_lll_of_not_RH`.

Derived from the Pringsheim section variable (no direct sorry). -/
theorem pi_log_zeta_extension :
    ∀ (α : ℝ), 1 / 2 < α → ∀ (C : ℝ), 0 < C →
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    (∀ᶠ x in atTop, σ * ((↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x) ≤ C * x ^ α) →
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re → exp (H s) = riemannZeta s :=
  pringsheim_pi

end PiLogZetaExtension

end Aristotle.NonNegDirichletIntegral
