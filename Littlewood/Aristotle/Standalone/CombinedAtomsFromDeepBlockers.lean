import Littlewood.Aristotle.HardyInfiniteZerosV2
import Littlewood.Aristotle.HardyMeanSquareAsymptoticLeaf
import Littlewood.Aristotle.HardyFirstMomentUpperLeaf
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.RiemannSiegelFirstMoment
import Littlewood.Aristotle.Standalone.LandauSigmaLtOneFromCauchyDomination
import Littlewood.Aristotle.Standalone.RHWitnessConstructiveStrict
import Littlewood.Aristotle.Standalone.PiAtomHardCaseCorrectedCore
import Littlewood.Bridge.HardySetupInstance
import Littlewood.Bridge.HardyFirstMomentWiring
import Littlewood.Bridge.HardyChainHyp
import Littlewood.CoreLemmas.GrowthDomination
import Littlewood.ZetaZeros.SupremumRealPart

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Asymptotics

namespace Aristotle.Standalone.CombinedAtomsFromDeepBlockers

open Filter Set MeasureTheory
open GrowthDomination
open HardyEstimatesPartial
open ZetaZeros

/-- RH-branch constructive witness payload for `ψ - x = Ω±(√x · lll x)`. -/
def RhPsiWitnessData : Prop :=
  ∀ (_hRH : ZetaZeros.RiemannHypothesis),
    ∃ psiMain : ℝ → ℝ,
      (∀ᶠ x in atTop,
        |(chebyshevPsi x - x) + psiMain x| ≤ Real.sqrt x * lll x) ∧
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧
        psiMain x ≤ -(2 * (Real.sqrt x * lll x))) ∧
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧
        2 * (Real.sqrt x * lll x) ≤ psiMain x)

/-- RH-branch constructive witness payload for
`π(x) - li(x) = Ω±((√x / log x) · lll x)`. -/
def RhPiWitnessData : Prop :=
  ∀ (_hRH : ZetaZeros.RiemannHypothesis),
    ∃ piMain : ℝ → ℝ,
      (∀ᶠ x in atTop,
        |((Nat.primeCounting (Nat.floor x) : ℝ) -
            LogarithmicIntegral.logarithmicIntegral x) + piMain x|
          ≤ Real.sqrt x / Real.log x * lll x) ∧
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧
        piMain x ≤ -(2 * (Real.sqrt x / Real.log x * lll x))) ∧
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧
        2 * (Real.sqrt x / Real.log x * lll x) ≤ piMain x)

/-- Hardy's critical-line infinitude atom from:
1) mean-square asymptotic input,
2) main-term first-moment input,
3) RS per-block signed decomposition input,
4) critical-line convexity input. -/
theorem hardy_critical_line_infinitely_many_zeros_from_blockers
    [Aristotle.HardyMeanSquareAsymptoticLeaf.HardyMeanSquareAsymptoticHyp]
    [HardyFirstMomentWiring.MainTermFirstMomentBoundHyp]
    [ZetaCriticalLineBoundHyp]
    (hRS : Aristotle.RSBlockDecomposition.PerBlockSignedBoundHyp) :
    Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 } := by
  letI : HardyFirstMomentWiring.ErrorTermFirstMomentBoundHyp :=
    RiemannSiegelFirstMoment.errorTermFirstMomentBound_from_quarter hRS
  letI : HardyInfiniteZerosV2.HardySetupV2 := {
    Z := hardyZ
    Z_continuous := HardySetupInstance.hardyZ_continuous
    Z_zero_iff := HardySetupInstance.hardyZ_zero_iff
    mean_square_lower := Aristotle.HardyMeanSquareAsymptoticLeaf.hardy_mean_square_lower_for_setup_v2
    first_moment_upper := Aristotle.HardyFirstMomentUpperLeaf.hardy_first_moment_upper_for_setup_v2
    Z_convexity_bound := by
      intro ε hε
      obtain ⟨C, hC, hbound⟩ := ZetaCriticalLineBoundHyp.bound ε hε
      refine ⟨C, hC, ?_⟩
      intro t ht
      exact le_trans (hardyZ_abs_le t) (hbound t ht)
  }
  have h_real := HardyInfiniteZerosV2.hardy_infinitely_many_zeros_v2
  have hinj : Function.Injective
      (fun t : ℝ => (1 / 2 : ℂ) + Complex.I * (t : ℂ)) := by
    intro a b hab
    have him := congrArg Complex.im hab
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im] at him
    exact him
  apply Set.Infinite.mono _ (h_real.image (fun a _ b _ hab => hinj hab))
  intro ρ hρ
  rcases hρ with ⟨t, ht, rfl⟩
  refine ⟨⟨ht, ?_, ?_⟩, ?_⟩
  · norm_num [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]
  · norm_num [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]
  · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]

/-- `ψ - x = Ω±(√x · lll x)` from:
1) non-RH constructive Landau sigma<1 domination data, and
2) RH-side constructive Perron/explicit/alignment witnesses. -/
theorem psi_omega_lll_from_blockers
    (hLandau : Aristotle.LandauAbscissaProof.SigmaLtOneHyp)
    (hRhPsi : RhPsiWitnessData) :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x] := by
  by_cases hRH : ZetaZeros.RiemannHypothesis
  · rcases hRhPsi hRH with ⟨psiMain, h_error, h_plus, h_minus⟩
    exact Aristotle.Standalone.RHWitnessConstructiveStrict.rh_psi_oscillation_from_perron_explicit_alignment
      hRH psiMain h_error h_plus h_minus
  · exact Aristotle.Standalone.LandauSigmaLtOneFromCauchyDomination.psi_omega_lll_of_not_RH_from_sigmaLtOne
      hLandau hRH

/-- `π - li = Ω±((√x / log x) · lll x)` from:
1) non-RH corrected hard-case constructive core, and
2) RH-side constructive Perron/explicit/alignment witnesses. -/
theorem pi_li_omega_lll_from_blockers
    (hPiCore :
      Aristotle.Standalone.PiAtomHardCaseCorrectedCore.PiAtomHardCaseCorrectedCore)
    (hRhPi : RhPiWitnessData) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x * lll x] := by
  by_cases hRH : ZetaZeros.RiemannHypothesis
  · rcases hRhPi hRH with ⟨piMain, h_error, h_plus, h_minus⟩
    exact Aristotle.Standalone.RHWitnessConstructiveStrict.rh_pi_li_oscillation_from_perron_explicit_alignment
      hRH piMain h_error h_plus h_minus
  · exact Aristotle.Standalone.PiAtomHardCaseCorrectedCore.pi_li_omega_lll_of_not_RH_from_corrected_core
      hPiCore hRH

/-- Full `combined_atoms`-shape theorem from explicit deep blocker hypotheses.

This theorem is `sorry`-free and supplies the exact triple consumed by
`DeepSorries.combined_atoms`. -/
theorem combined_atoms_from_blockers
    [Aristotle.HardyMeanSquareAsymptoticLeaf.HardyMeanSquareAsymptoticHyp]
    [HardyFirstMomentWiring.MainTermFirstMomentBoundHyp]
    [ZetaCriticalLineBoundHyp]
    (hRS : Aristotle.RSBlockDecomposition.PerBlockSignedBoundHyp)
    (hLandau : Aristotle.LandauAbscissaProof.SigmaLtOneHyp)
    (hRhPsi : RhPsiWitnessData)
    (hPiCore :
      Aristotle.Standalone.PiAtomHardCaseCorrectedCore.PiAtomHardCaseCorrectedCore)
    (hRhPi : RhPiWitnessData) :
    (Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 })
    ∧
    ((fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x])
    ∧
    ((fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
      =Ω±[fun x => Real.sqrt x / Real.log x * lll x]) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hardy_critical_line_infinitely_many_zeros_from_blockers hRS
  · exact psi_omega_lll_from_blockers hLandau hRhPsi
  · exact pi_li_omega_lll_from_blockers hPiCore hRhPi

end Aristotle.Standalone.CombinedAtomsFromDeepBlockers
