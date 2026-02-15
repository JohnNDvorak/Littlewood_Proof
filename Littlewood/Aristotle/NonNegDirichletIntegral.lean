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

The proof reduces to a single mathematical atom:
* `landau_nonneg_integral_analytic` (SORRY): For f ≥ 0 with f = O(t),
  if s ∫₁^∞ f(t)*t^{-(s+1)} dt admits an analytic continuation past Re(s)=1
  on the real axis, then the integral converges and is analytic for Re(s) > α.
  This is Landau's generalization of Pringsheim's theorem.

## Mathematical References

* Landau, "Über einen Satz von Tschebyschef" (1905), Satz 15
* Hardy-Riesz, "The General Theory of Dirichlet's Series", Ch. 1
* Montgomery-Vaughan, "Multiplicative Number Theory I", §1.3

SORRY COUNT: 2 (landau_nonneg_integral_analytic, pi_log_zeta_analytic)

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

/-! ## Landau's theorem for non-negative Dirichlet integrals

This is the core analytical atom. For a non-negative function f with f = O(t),
convergence of the Dirichlet integral for Re(s) > 1 extends to Re(s) > α
provided the resulting function has no singularity on the real interval (α, 1].

The proof requires Pringsheim's theorem (non-negative Taylor coefficients
force a singularity at the radius of convergence) which is not in Mathlib.

We formulate the sorry as the final conclusion needed: existence of an
analytic function G on {Re > α} matching the expected formula on {Re > 1}. -/

/-- **Landau's non-negative Dirichlet integral theorem** (for ψ).

Given a one-sided bound σ*(ψ(x)-x) ≤ C*x^α with α > 1/2, the function
g(t) = C*t^α + σ*(t-ψ(t)) is non-negative for large t, and the associated
Dirichlet integral defines G analytic on {Re(s) > α} with the formula
G(s) = s*C/(s-α) + σ*s/(s-1) + σ*ζ'/ζ(s) holding on {Re(s) > 1}.

**Proof outline** (not yet formalized):
1. g(t) ≥ 0 for t large (from the one-sided bound).
2. Each piece of ∫₁^∞ g(t)*t^{-(s+1)} dt converges for Re(s) > 1.
3. On {Re(s) > 1}: G(s) = sC/(s-α) + σ*s/(s-1) + σ*ζ'/ζ(s).
4. The poles at s = 1 cancel: sC/(s-α) → C/(1-α), and
   s/(s-1) + ζ'/ζ(s) → finite (residue cancellation).
5. ζ has no real zeros for σ > 0 (Euler product), so G extends
   analytically along the real axis from 1 down to α.
6. By Pringsheim/Landau: for non-negative integrands, the abscissa
   of convergence is a singularity. Since no singularity exists on
   (α, ∞) ⊂ ℝ, convergence extends to Re(s) > α.
7. Analyticity on {Re(s) > α} follows from parametric differentiation.

**Reference**: Landau, "Über einen Satz von Tschebyschef" (1905). -/
private theorem landau_nonneg_integral_analytic
    (α : ℝ) (hα : 1 / 2 < α) (C : ℝ) (hC : 0 < C)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (h_bound : ∀ᶠ x in atTop, σ * (chebyshevPsi x - x) ≤ C * x ^ α) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        G s = s * (↑C : ℂ) / (s - (↑α : ℂ)) + (↑σ : ℂ) * (s / (s - 1)) +
              (↑σ : ℂ) * (deriv riemannZeta s / riemannZeta s) := by
  sorry

/-! ## Main theorem: psi_integral_hyp -/

/-- The Dirichlet integral hypothesis for ψ, as required by
`LandauSchmidtDirect.psi_omega_lll_of_not_RH`.

This packages `landau_nonneg_integral_analytic` with the exact type
signature expected by the section variable in LandauSchmidtDirect. -/
theorem psi_dirichlet_integral :
    ∀ (α : ℝ), 1 / 2 < α → ∀ (C : ℝ), 0 < C →
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    (∀ᶠ x in atTop, σ * (chebyshevPsi x - x) ≤ C * x ^ α) →
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        G s = s * (↑C : ℂ) / (s - (↑α : ℂ)) + (↑σ : ℂ) * (s / (s - 1)) +
              (↑σ : ℂ) * (deriv riemannZeta s / riemannZeta s) :=
  fun α hα C hC σ hσ h_bound =>
    landau_nonneg_integral_analytic α hα C hC σ hσ h_bound

/-! ## Landau's theorem for π-li (log ζ extension)

The π-li case uses log ζ instead of ζ'/ζ. Under a one-sided bound on
π(x)-li(x), the generating function log ζ(s) extends analytically to
{Re(s) > α}. The contradiction then comes from exp(log ζ(ρ₀)) = ζ(ρ₀) = 0
but exp never vanishes.

The proof parallels the ψ case but uses the Chebyshev-type identity
  log ζ(s) = ∑ Λ(n)/(n^s · log n)
and the corresponding integral representation.

**Reference**: Montgomery-Vaughan §1.3, Landau 1905. -/

/-- **Landau's log ζ extension theorem** (for π-li).

Given a one-sided bound σ*(π(x)-li(x)) ≤ C*x^α, there exists H analytic
on {Re > α} with exp(H(s)) = ζ(s) for Re(s) > 1.

**Proof outline** (not yet formalized):
1. Define g(t) using the prime-counting analogue.
2. The generating function for π(x) is log ζ(s) (on Re(s) > 1).
3. Under the one-sided bound, construct an analytic branch of log ζ
   on {Re > α} via the non-negative integral trick.
4. This branch satisfies exp(H(s)) = ζ(s) on {Re > 1}. -/
private theorem pi_log_zeta_analytic
    (α : ℝ) (hα : 1 / 2 < α) (C : ℝ) (hC : 0 < C)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (h_bound : ∀ᶠ x in atTop, σ * ((↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x) ≤ C * x ^ α) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re → exp (H s) = riemannZeta s := by
  sorry

/-! ## Main theorem: pi_integral_hyp -/

/-- The log ζ extension hypothesis for π-li, as required by
`LandauSchmidtDirect.pi_li_omega_lll_of_not_RH`.

This packages `pi_log_zeta_analytic` with the exact type signature
expected by the section variable in LandauSchmidtDirect. -/
theorem pi_log_zeta_extension :
    ∀ (α : ℝ), 1 / 2 < α → ∀ (C : ℝ), 0 < C →
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    (∀ᶠ x in atTop, σ * ((↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x) ≤ C * x ^ α) →
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re → exp (H s) = riemannZeta s :=
  fun α hα C hC σ hσ h_bound =>
    pi_log_zeta_analytic α hα C hC σ hσ h_bound

end Aristotle.NonNegDirichletIntegral
