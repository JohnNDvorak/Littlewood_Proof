import Mathlib
import Littlewood.Aristotle.PringsheimPiAtom
import Littlewood.Aristotle.LandauLogZetaObstruction
import Littlewood.Aristotle.CorrectionTermAnalyticity
import Littlewood.Aristotle.Standalone.LandauPiPuncturedExtensionChain
import Littlewood.ZetaZeros.SupremumRealPart
import Littlewood.CoreLemmas.GrowthDomination

set_option linter.mathlibStandardSet false

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Asymptotics

namespace Aristotle.Standalone.PiAtomHardCaseConstructiveStrict

open Complex Real Filter Topology MeasureTheory Set
open ZetaZeros
open GrowthDomination

/-- One-sided hard-case `π-li` error bound used in the `PiAtomHardCase` signature. -/
def PiLiHardBound (α C σ : ℝ) : Prop :=
  ∀ᶠ x in atTop, σ * ((↑(Nat.primeCounting ⌊x⌋₊) : ℝ) -
    LogarithmicIntegral.logarithmicIntegral x) ≤ C * x ^ α

/-- Strict constructive obstruction for the hard range `1/2 < α < 1`:
no analytic branch `H` on `{Re > α}` can satisfy `exp(H)=ζ` on `{Re > 1}`. -/
theorem hard_case_no_full_log_branch
    (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (C : ℝ) (hC : 0 < C)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hbound : PiLiHardBound α C σ) :
    ¬∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re → exp (H s) = riemannZeta s :=
  Aristotle.PringsheimPiAtom.pi_atom_hard_case_obstruction
    α hα hα1 C hC σ hσ hbound

/-- Any *realized* hard-case bound refutes `PringsheimPiAtom.PiAtomHardCase`.

This is maximal with current foundations: the contradiction is fully formal once
the bound hypothesis is provided, but no unconditional proof of such a bound is
available in this development. -/
theorem not_pi_atom_hard_case_of_bound
    (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (C : ℝ) (hC : 0 < C)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hbound : PiLiHardBound α C σ) :
    ¬Aristotle.PringsheimPiAtom.PiAtomHardCase := by
  intro hHard
  exact (hard_case_no_full_log_branch α hα hα1 C hC σ hσ hbound)
    (hHard α hα hα1 C hC σ hσ hbound)

/-- **Exact missing constructive bridge theorem** for the hard case.

The current obstruction only rules out analyticity at `s = 1`. What the Landau
contradiction pipeline actually needs is an analytic branch on the punctured
half-plane `{Re > α} \ {1}` that still agrees with `ζ` via exponentiation on
`{Re > 1}`. -/
def PiAtomHardCasePuncturedBridge : Prop :=
  ∀ (α : ℝ), 1 / 2 < α → α < 1 →
  ∀ (C : ℝ), 0 < C →
  ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
  PiLiHardBound α C σ →
  ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H ({s : ℂ | α < s.re} \ {(1 : ℂ)}) ∧
    ∀ s : ℂ, 1 < s.re → exp (H s) = riemannZeta s

/-- Any full hard-case witness would in particular yield the punctured bridge. -/
theorem full_hard_case_implies_punctured_bridge
    (hHard : Aristotle.PringsheimPiAtom.PiAtomHardCase) :
    PiAtomHardCasePuncturedBridge := by
  intro α hα hα1 C hC σ hσ hbound
  obtain ⟨H, hH_analytic, hH_eq⟩ := hHard α hα hα1 C hC σ hσ hbound
  refine ⟨H, ?_, hH_eq⟩
  intro s hs
  exact hH_analytic s hs.1

private theorem punctured_extension_hyp_of_bridge
    (hBridge : PiAtomHardCasePuncturedBridge) :
    Aristotle.Standalone.LandauPiPuncturedExtensionChain.PiIntegralHypPunctured := by
  intro α hα C hC σ hσ hbound
  by_cases hα_lt_one : α < 1
  · exact hBridge α hα hα_lt_one C hC σ hσ hbound
  · have hα_ge_one : 1 ≤ α := by linarith
    refine ⟨LandauLogZetaObstruction.H_zeta_log, ?_, fun s hs =>
      LandauLogZetaObstruction.H_zeta_log_exp_eq hs⟩
    intro s hs
    have hs_re : α < s.re := hs.1
    exact CorrectionTermAnalyticity.H_zeta_log_analyticOnNhd
      ((1 + s.re) / 2) (by linarith) s (by
        simp only [mem_setOf_eq]
        linarith)

/-- Main import theorem for Claude wiring:
if the punctured hard-case bridge is proved, then the full non-RH `π-li`
oscillation follows via the punctured Landau chain. -/
theorem pi_li_omega_lll_of_not_RH_from_punctured_bridge
    (hBridge : PiAtomHardCasePuncturedBridge)
    (hRH : ¬ZetaZeros.RiemannHypothesis) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x * lll x] := by
  exact Aristotle.Standalone.LandauPiPuncturedExtensionChain.pi_li_omega_lll_of_not_RH_of_punctured_extension
    (punctured_extension_hyp_of_bridge hBridge) hRH

end Aristotle.Standalone.PiAtomHardCaseConstructiveStrict
