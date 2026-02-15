/-
Pringsheim/Landau atoms: infrastructure and documentation.

This file provides proved infrastructure for the Landau non-negative Dirichlet
integral argument (Landau, Satz 15), which is the core of Littlewood's proof.

## Architecture

The Pringsheim atoms (one-sided bound → analytic extension) are supplied as
`sorry` within `DeepSorries.combined_atoms`. This file provides the surrounding
infrastructure:

* `g_nonneg_eventually` : g(t) = C·t^α + σ·(t-ψ(t)) ≥ 0 from one-sided bound
* `ZetaPoleCancellation.landau_formula_analyticAt_real` : corrected formula analytic at real x > α
* `ZetaPoleCancellation.corrected_logDeriv_eq` : corrected formula = original on {Re > 1}

## Mathematical Content

### ψ atom (pringsheim_psi)
Given σ*(ψ(x)-x) ≤ C*x^α (one-sided bound), define:
  g(t) = C*t^α + σ*(t - ψ(t)) ≥ 0  (for large t)

The Dirichlet integral G(s) = s*∫₁^∞ g(t)*t^{-(s+1)} dt converges for Re(s) > 1
and equals the formula sC/(s-α) + σs/(s-1) + σζ'/ζ(s) there.

The formula extends analytically along (α,∞) ⊂ ℝ because:
  - Poles at s=1 cancel (residue σ + residue -σ = 0) [ZetaPoleCancellation]
  - ζ(x) ≠ 0 for real x ∈ (0,1) [ZetaRealNonvanishing]

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

### Key missing infrastructure for full proof:
- Parametric differentiation of Dirichlet integrals (∂ⁿ/∂sⁿ ∫f(t)t^{-s}dt = ∫f(t)(-log t)ⁿt^{-s}dt)
- Fubini interchange for the Taylor expansion (∫ Σ → Σ ∫)
- Abscissa of convergence theory (not in Mathlib)

SORRY COUNT: 0

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

/-! ## Non-negativity of the generating function

The generating function g(t) = C·t^α + σ·(t - ψ(t)) is non-negative for
large t, following directly from the one-sided bound hypothesis. -/

/-- From a one-sided bound σ*(ψ(x)-x) ≤ C*x^α, the generating function
g(t) = C*t^α + σ*(t-ψ(t)) is eventually non-negative. -/
theorem g_nonneg_eventually (α : ℝ) (C : ℝ) (_hC : 0 < C)
    (σ : ℝ) (_hσ : σ = 1 ∨ σ = -1)
    (hbound : ∀ᶠ x in atTop, σ * (chebyshevPsi x - x) ≤ C * x ^ α) :
    ∀ᶠ t in atTop, (0 : ℝ) ≤ C * t ^ α + σ * (t - chebyshevPsi t) := by
  filter_upwards [hbound] with t ht
  -- From ht: σ * (ψ(t) - t) ≤ C * t^α
  -- Goal: 0 ≤ C * t^α + σ * (t - ψ(t))
  -- Note: σ * (t - ψ(t)) = -(σ * (ψ(t) - t)) ≥ -(C * t^α)
  -- Wait: C * t^α + σ * (t - ψ(t)) = C * t^α - σ * (ψ(t) - t) ≥ C * t^α - C * t^α = 0
  linarith [ht]

/-! ## Corrected Landau formula infrastructure

Re-exports from ZetaPoleCancellation for convenience and documentation. -/

/-- The corrected Landau formula `s*C/(s-α) + σ*(1 + zrf'/zrf(s))` is analytic
at every real point x > α, including x = 1 where poles cancel.
See `ZetaPoleCancellation.landau_formula_analyticAt_real`. -/
theorem corrected_formula_analyticAt_real (α : ℝ) (hα : 1 / 2 < α) (C σ : ℝ)
    (x : ℝ) (hx : α < x) :
    AnalyticAt ℂ (fun s => s * (↑C : ℂ) / (s - (↑α : ℂ)) +
      (↑σ : ℂ) * (1 + deriv ZetaPoleCancellation.zrf s /
        ZetaPoleCancellation.zrf s)) (↑x : ℂ) :=
  ZetaPoleCancellation.landau_formula_analyticAt_real α hα C σ x hx

/-! ## Formula type signatures (for documentation)

These type signatures document exactly what the Landau Satz needs to provide.
The atoms are supplied as `sorry` in `DeepSorries.combined_atoms`. -/

/-- Type of the ψ Pringsheim atom. -/
def PsiAtomType : Prop :=
    ∀ (α : ℝ), 1 / 2 < α → ∀ (C : ℝ), 0 < C →
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    (∀ᶠ x in atTop, σ * (chebyshevPsi x - x) ≤ C * x ^ α) →
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        G s = s * (↑C : ℂ) / (s - (↑α : ℂ)) + (↑σ : ℂ) * (s / (s - 1)) +
              (↑σ : ℂ) * (deriv riemannZeta s / riemannZeta s)

/-- Type of the π Pringsheim atom. -/
def PiAtomType : Prop :=
    ∀ (α : ℝ), 1 / 2 < α → ∀ (C : ℝ), 0 < C →
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    (∀ᶠ x in atTop, σ * ((↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x) ≤ C * x ^ α) →
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re → exp (H s) = riemannZeta s

end Aristotle.PringsheimAtoms
