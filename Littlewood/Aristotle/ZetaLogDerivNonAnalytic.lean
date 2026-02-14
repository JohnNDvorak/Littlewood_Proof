/-
Infrastructure connecting ZetaLogDerivPole to the Landau oscillation argument.

The key result: ζ'/ζ cannot be analytically extended through any nontrivial zero.
This is the "pole obstruction" step of the Landau argument:
  If ψ(x) - x ≤ Cx^α, then the Landau convergence theorem would make
  -ζ'/ζ(s) analytic for Re(s) > α. But -ζ'/ζ has a pole at any zero ρ₀
  with Re(ρ₀) > α (this file). Contradiction.

## Main Results

* `nontrivial_zero_ne_one` : ρ ∈ zetaNontrivialZeros → ρ ≠ 1
* `nontrivial_zero_vanishes` : ρ ∈ zetaNontrivialZeros → ζ(ρ) = 0
* `nontrivial_zero_re_bounds` : ρ ∈ zetaNontrivialZeros → 0 < Re(ρ) < 1
* `zeta_logDeriv_not_analyticAt` : ζ'/ζ is NOT analytic at nontrivial zeros
* `zeta_logDeriv_not_continuousAt` : ζ'/ζ is NOT continuous at nontrivial zeros

SORRY COUNT: 0

REFERENCES:
  - ZetaLogDerivPole (this project)
  - Landau, "Über einen Satz von Tschebyschef" (1905)
  - Montgomery-Vaughan, "Multiplicative Number Theory I", §15.1

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ZetaLogDerivPole
import Littlewood.ZetaZeros.ZeroCountingFunction
import Mathlib.Topology.MetricSpace.Bounded

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace Aristotle.ZetaLogDerivNonAnalytic

open Complex Filter Topology Bornology ZetaZeros

/-! ## Utility lemmas for nontrivial zeros -/

/-- A nontrivial zero satisfies ρ ≠ 1 (since Re(ρ) < 1 = Re(1)). -/
theorem nontrivial_zero_ne_one (ρ : ℂ) (hρ : ρ ∈ zetaNontrivialZeros) : ρ ≠ 1 := by
  intro h
  rw [h] at hρ
  exact absurd hρ.2.2 (by simp : ¬(1 : ℂ).re < 1)

/-- A nontrivial zero satisfies ζ(ρ) = 0. -/
theorem nontrivial_zero_vanishes (ρ : ℂ) (hρ : ρ ∈ zetaNontrivialZeros) :
    riemannZeta ρ = 0 := hρ.1

/-- A nontrivial zero satisfies 0 < Re(ρ) < 1. -/
theorem nontrivial_zero_re_bounds (ρ : ℂ) (hρ : ρ ∈ zetaNontrivialZeros) :
    0 < ρ.re ∧ ρ.re < 1 := ⟨hρ.2.1, hρ.2.2⟩

/-! ## Non-analyticity and non-continuity of ζ'/ζ at zeros -/

/-- ζ'/ζ is NOT continuous at any nontrivial zero.

This is because ζ'/ζ has a pole there: ‖ζ'/ζ(s)‖ → ∞ as s → ρ₀
(from `ZetaLogDerivPole.zeta_logDeriv_tendsto_cobounded`).
Continuity would give a finite limit, contradicting the pole. -/
theorem zeta_logDeriv_not_continuousAt (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ zetaNontrivialZeros) :
    ¬ContinuousAt (fun s => deriv riemannZeta s / riemannZeta s) ρ₀ := by
  intro h_cont
  -- ζ'/ζ → ∞ at ρ₀ (pole, from ZetaLogDerivPole)
  have h_pole := ZetaLogDerivPole.zeta_logDeriv_tendsto_cobounded ρ₀
    (nontrivial_zero_ne_one ρ₀ hρ₀) (nontrivial_zero_vanishes ρ₀ hρ₀)
  -- Continuous → tends to nhds along punctured nhds
  have h_nhds : Tendsto (fun s => deriv riemannZeta s / riemannZeta s)
      (𝓝[≠] ρ₀) (𝓝 (deriv riemannZeta ρ₀ / riemannZeta ρ₀)) :=
    h_cont.tendsto.mono_left nhdsWithin_le_nhds
  -- But cobounded and nhds are disjoint, and 𝓝[≠] ρ₀ is NeBot
  exact absurd h_nhds (h_pole.not_tendsto (Metric.disjoint_cobounded_nhds _))

/-- ζ'/ζ is NOT analytic at any nontrivial zero.

Analyticity would imply continuity, contradicting the pole.
This is the key obstruction for the Landau argument:
if -ζ'/ζ could be analytically extended past Re(s) = α, then
it would be continuous (and hence bounded) near any zero ρ₀
with Re(ρ₀) > α. But ζ'/ζ blows up at ρ₀. -/
theorem zeta_logDeriv_not_analyticAt (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ zetaNontrivialZeros) :
    ¬AnalyticAt ℂ (fun s => deriv riemannZeta s / riemannZeta s) ρ₀ := by
  intro h_anal
  exact zeta_logDeriv_not_continuousAt ρ₀ hρ₀ h_anal.continuousAt

/-- Any function analytic at ρ₀ that agrees with ζ'/ζ in a punctured neighborhood
leads to a contradiction.

This is the abstract form needed for the Landau argument: one constructs an
analytic function F(s) on Re(s) > α from the Dirichlet integral, shows F = ζ'/ζ
on Re(s) > 1 (hence on Re(s) > α by analytic continuation), and gets the
contradiction because F is analytic at ρ₀ but ζ'/ζ is not. -/
theorem zeta_logDeriv_no_analytic_extension (ρ₀ : ℂ) (hρ₀ : ρ₀ ∈ zetaNontrivialZeros)
    (F : ℂ → ℂ) (hF_anal : AnalyticAt ℂ F ρ₀)
    (hF_eq : ∀ᶠ s in 𝓝[≠] ρ₀, F s = deriv riemannZeta s / riemannZeta s) :
    False := by
  -- ζ'/ζ → ∞ at ρ₀
  have h_pole := ZetaLogDerivPole.zeta_logDeriv_tendsto_cobounded ρ₀
    (nontrivial_zero_ne_one ρ₀ hρ₀) (nontrivial_zero_vanishes ρ₀ hρ₀)
  -- F is continuous at ρ₀, so F → F(ρ₀) along punctured nhds
  have hF_cont := hF_anal.continuousAt
  have hF_nhds : Tendsto F (𝓝[≠] ρ₀) (𝓝 (F ρ₀)) :=
    hF_cont.tendsto.mono_left nhdsWithin_le_nhds
  -- F = ζ'/ζ near ρ₀, so ζ'/ζ also tends to F(ρ₀)
  have h_eq_nhds : Tendsto (fun s => deriv riemannZeta s / riemannZeta s)
      (𝓝[≠] ρ₀) (𝓝 (F ρ₀)) :=
    hF_nhds.congr' hF_eq
  -- But ζ'/ζ tends to cobounded (pole), contradicting nhds limit
  exact absurd h_eq_nhds (h_pole.not_tendsto (Metric.disjoint_cobounded_nhds _))

end Aristotle.ZetaLogDerivNonAnalytic
