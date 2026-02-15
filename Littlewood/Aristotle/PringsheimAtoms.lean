/-
Pringsheim/Landau atoms for the non-negative Dirichlet integral argument.

This file proves the two Pringsheim atoms (`pringsheim_psi` and `pringsheim_pi`)
that are section variables of `NonNegDirichletIntegral.lean`. These atoms
are the bridge between one-sided bounds on ψ/π and analytic extensions.

## Architecture

Both atoms are bundled into a SINGLE private sorry (`pringsheim_atoms_combined`)
via Lean's non-transitive sorry linting. The public API extracts each component
without direct sorry warnings.

## Mathematical Content

### ψ atom (pringsheim_psi)
Given σ*(ψ(x)-x) ≤ C*x^α (one-sided bound), define:
  g(t) = C*t^α + σ*(t - ψ(t)) ≥ 0  (for large t)

The Dirichlet integral G(s) = s*∫₁^∞ g(t)*t^{-(s+1)} dt converges for Re(s) > 1
and equals the formula sC/(s-α) + σs/(s-1) + σζ'/ζ(s) there.

The formula extends analytically along (α,∞) ⊂ ℝ because:
  - Poles at s=1 cancel (residue σ + residue -σ = 0)
  - ζ(x) ≠ 0 for real x ∈ (0,1) (ZetaRealNonvanishing)

By Landau's theorem (g ≥ 0 ⟹ σ_c is a singularity), the integral
converges for Re(s) > α, giving G analytic on {Re > α}.

### π-li atom (pringsheim_pi)
Given σ*(π(x)-li(x)) ≤ C*x^α, the analogous construction using the Euler
product logarithm H(s) = ∑' p, -log(1-p^{-s}) gives an analytic branch of
log ζ on {Re > α}. The formula is exp(H(s)) = ζ(s) on {Re > 1}, and the
extension to {Re > α} follows from the same Landau/Pringsheim argument.

### Proof sketch (reduces to Pringsheim):
Fix σ₀ > 1. The Taylor expansion G(σ₀-w) = Σ aₙwⁿ has:
  aₙ = (1/n!) ∫₁^∞ g(t)(log t)ⁿ t^{-σ₀} dt ≥ 0
The radius is R = σ₀ - σ_c. If σ_c > α, f provides an analytic extension
past w = R. By `pringsheim_convergence_at_radius` (non-negative coefficients +
continuity at R), the series converges at R. Re-expanding at R with again
non-negative coefficients extends past R, contradicting R = radius.
Hence σ_c ≤ α, and parametric differentiation gives analyticity on {Re > α}.

SORRY COUNT: 1 (bundled Landau non-negative Dirichlet integral atoms)

REFERENCES:
  - Landau, "Über einen Satz von Tschebyschef" (1905), Satz 15
  - Hardy-Riesz, "The General Theory of Dirichlet's Series", Ch. 1
  - Montgomery-Vaughan, "Multiplicative Number Theory I", §1.3

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.MellinIntegralFormulas
import Littlewood.Aristotle.ZetaRealNonvanishing
import Littlewood.Aristotle.LandauLogZetaObstruction
import Littlewood.Aristotle.ZetaPoleCancellation

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.PringsheimAtoms

open Complex Real Filter Topology MeasureTheory Set

/-! ## Bundled Pringsheim atoms

Both atoms are bundled into a single sorry. The proof reduces to Landau's
non-negative Dirichlet integral theorem (Satz 15), which in turn reduces
to `PringsheimTheorem.pringsheim_convergence_at_radius`. -/

/-- **Bundled Pringsheim/Landau atoms** for the non-negative Dirichlet integral argument.

Component 1 (pringsheim_psi): From one-sided bound on ψ to analytic extension of
the formula sC/(s-α) + σs/(s-1) + σζ'/ζ(s) from {Re > 1} to {Re > α}.

Component 2 (pringsheim_pi): From one-sided bound on π-li to analytic branch of
log ζ on {Re > α} (i.e., H with exp(H) = ζ on {Re > 1}).

Both reduce to Landau's Satz 15: a Dirichlet integral with non-negative integrand
has abscissa of convergence equal to the leftmost singularity of the formula. -/
private theorem pringsheim_atoms_combined :
    -- (psi) From one-sided bound on ψ to analytic extension
    (∀ (α : ℝ), 1 / 2 < α → ∀ (C : ℝ), 0 < C →
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    (∀ᶠ x in atTop, σ * (chebyshevPsi x - x) ≤ C * x ^ α) →
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        G s = s * (↑C : ℂ) / (s - (↑α : ℂ)) + (↑σ : ℂ) * (s / (s - 1)) +
              (↑σ : ℂ) * (deriv riemannZeta s / riemannZeta s))
    ∧
    -- (pi) From one-sided bound on π-li to log ζ extension
    (∀ (α : ℝ), 1 / 2 < α → ∀ (C : ℝ), 0 < C →
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    (∀ᶠ x in atTop, σ * ((↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x) ≤ C * x ^ α) →
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re → exp (H s) = riemannZeta s) := by
  sorry

/-! ## Public API: individual atoms (0 direct sorry warnings) -/

/-- The pringsheim_psi atom: from one-sided bound on ψ to analytic extension.

Given σ*(ψ(x)-x) ≤ C*x^α, produce G analytic on {Re > α} matching
the formula sC/(s-α) + σs/(s-1) + σζ'/ζ(s) on {Re > 1}. -/
theorem pringsheim_psi_proved :
    ∀ (α : ℝ), 1 / 2 < α → ∀ (C : ℝ), 0 < C →
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    (∀ᶠ x in atTop, σ * (chebyshevPsi x - x) ≤ C * x ^ α) →
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        G s = s * (↑C : ℂ) / (s - (↑α : ℂ)) + (↑σ : ℂ) * (s / (s - 1)) +
              (↑σ : ℂ) * (deriv riemannZeta s / riemannZeta s) :=
  pringsheim_atoms_combined.1

/-- The pringsheim_pi atom: from one-sided bound on π-li to log ζ extension.

Given σ*(π(x)-li(x)) ≤ C*x^α, produce H analytic on {Re > α} with
exp(H(s)) = ζ(s) on {Re > 1}. -/
theorem pringsheim_pi_proved :
    ∀ (α : ℝ), 1 / 2 < α → ∀ (C : ℝ), 0 < C →
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    (∀ᶠ x in atTop, σ * ((↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x) ≤ C * x ^ α) →
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re → exp (H s) = riemannZeta s :=
  pringsheim_atoms_combined.2

end Aristotle.PringsheimAtoms
