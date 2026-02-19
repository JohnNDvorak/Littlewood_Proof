import Littlewood.Aristotle.PringsheimPiAtom
import Littlewood.Aristotle.LandauLogZetaObstruction
import Littlewood.Aristotle.CorrectionTermAnalyticity
import Littlewood.Aristotle.Standalone.LandauPiPuncturedExtensionChain
import Littlewood.ZetaZeros.SupremumRealPart
import Littlewood.CoreLemmas.GrowthDomination
import Littlewood.Basic.LogarithmicIntegral

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Asymptotics

namespace Aristotle.Standalone.PiHardCasePuncturedBridgeConstructive

open Complex Real Filter Topology Set
open ZetaZeros GrowthDomination

/--
Constructive bridge from the hard `π` Pringsheim case (`1/2 < α < 1`) to the
punctured-half-plane Landau extension hypothesis used by
`LandauPiPuncturedExtensionChain`.

For `α < 1`, this is exactly the hard-case witness restricted from `{Re > α}` to
`{Re > α} \ {1}`. For `α ≥ 1`, use the explicit Euler-product logarithm branch
`H_zeta_log`, analytic on every right half-plane `{Re > β}` with `β > 1`, and
hence at each point of `{Re > α} \ {1}`.
-/
theorem piIntegralHypPunctured_of_piAtomHardCase
    (hHard : Aristotle.PringsheimPiAtom.PiAtomHardCase) :
    Aristotle.Standalone.LandauPiPuncturedExtensionChain.PiIntegralHypPunctured := by
  intro α hα C hC σ hσ hbound
  by_cases hα_lt_one : α < 1
  · obtain ⟨H, hH_analytic, hH_eq⟩ := hHard α hα hα_lt_one C hC σ hσ hbound
    refine ⟨H, ?_, hH_eq⟩
    intro s hs
    exact hH_analytic s hs.1
  · have hα_ge_one : 1 ≤ α := by linarith
    refine ⟨LandauLogZetaObstruction.H_zeta_log, ?_, ?_⟩
    · intro s hs
      have hs_re : α < s.re := hs.1
      exact CorrectionTermAnalyticity.H_zeta_log_analyticOnNhd
        ((1 + s.re) / 2) (by linarith) s (by
          simp only [mem_setOf_eq]
          linarith)
    · intro s hs
      exact LandauLogZetaObstruction.H_zeta_log_exp_eq hs

/--
Non-RH `π-li` oscillation consequence obtained by wiring the hard-case
Pringsheim input through the punctured-half-plane Landau chain.
-/
theorem pi_li_omega_lll_of_not_RH_from_piAtomHardCase
    (hHard : Aristotle.PringsheimPiAtom.PiAtomHardCase)
    (hRH : ¬ZetaZeros.RiemannHypothesis) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x * lll x] := by
  exact Aristotle.Standalone.LandauPiPuncturedExtensionChain.pi_li_omega_lll_of_not_RH_of_punctured_extension
    (piIntegralHypPunctured_of_piAtomHardCase hHard) hRH

end Aristotle.Standalone.PiHardCasePuncturedBridgeConstructive
