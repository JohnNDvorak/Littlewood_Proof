import Littlewood.Aristotle.Standalone.LandauPiCorrectedExtensionChain
import Littlewood.ZetaZeros.SupremumRealPart
import Littlewood.CoreLemmas.GrowthDomination

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Asymptotics

namespace Aristotle.Standalone.PiAtomHardCaseCorrectedCore

open Complex Real Filter Topology Set
open ZetaZeros GrowthDomination

/-- One-sided hard-case `π-li` bound in the range `1/2 < α < 1`. -/
def PiLiHardBound (α C σ : ℝ) : Prop :=
  ∀ᶠ x in atTop, σ * ((↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
    LogarithmicIntegral.logarithmicIntegral x) ≤ C * x ^ α

/-- Corrected hard-case core: analytic `G` on the full half-plane `{Re > α}`
with `exp(G s) = (s - 1) * ζ(s)` for `Re(s) > 1`.

This replaces `PiAtomHardCasePuncturedCore` which required `exp(H) = ζ(s)` on
the punctured domain `{Re > α} \ {1}`. That formulation is **mathematically false**
due to monodromy: `ζ'/ζ` has residue −1 at `s = 1`, so `log ζ` picks up `−2πi`
around any loop encircling `s = 1`, preventing single-valuedness.

The corrected version uses `(s-1)*ζ(s)` instead. The log-derivative residues
cancel (`+1` from `1/(s-1)` and `−1` from `ζ'/ζ`), giving zero monodromy.
Therefore `log((s-1)ζ(s))` is single-valued on `{Re > α}`. -/
def PiAtomHardCaseCorrectedCore : Prop :=
  ∀ (α : ℝ), 1 / 2 < α → α < 1 →
  ∀ (C : ℝ), 0 < C →
  ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
  PiLiHardBound α C σ →
  ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {s : ℂ | α < s.re} ∧
    ∀ s : ℂ, 1 < s.re → exp (G s) = (s - 1) * riemannZeta s

/-- Wiring theorem: the corrected core is exactly the corrected Landau hypothesis.
Since both restrict to `1/2 < α < 1` (the only nontrivial range), the wiring
is definitionally trivial. -/
theorem piIntegralHypCorrected_of_corrected_core
    (hCore : PiAtomHardCaseCorrectedCore) :
    Aristotle.Standalone.LandauPiCorrectedExtensionChain.PiIntegralHypCorrected := by
  intro α hα hα1 C hC σ hσ hbound
  exact hCore α hα hα1 C hC σ hσ hbound

/-- Non-RH `π-li` oscillation from the corrected hard-range core. -/
theorem pi_li_omega_lll_of_not_RH_from_corrected_core
    (hCore : PiAtomHardCaseCorrectedCore)
    (hRH : ¬ZetaZeros.RiemannHypothesis) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x * lll x] := by
  exact Aristotle.Standalone.LandauPiCorrectedExtensionChain.pi_li_omega_lll_of_not_RH_of_corrected_extension
    (piIntegralHypCorrected_of_corrected_core hCore) hRH

end Aristotle.Standalone.PiAtomHardCaseCorrectedCore
