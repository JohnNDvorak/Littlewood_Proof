import Littlewood.Aristotle.HardyMeanSquareAsymptoticLeaf
import Littlewood.Aristotle.HardyMeanSquareLowerStandalone
import Littlewood.Aristotle.HardyFirstMomentUpperStandalone
import Littlewood.Bridge.HardyFirstMomentWiring
import Littlewood.Aristotle.Standalone.RSFirstMomentQuarterFromCenteredBlocks
import Littlewood.Aristotle.Standalone.LandauSigmaLtOneFromCauchyDomination
import Littlewood.Aristotle.Standalone.RHWitnessConstructiveStrict
import Littlewood.Aristotle.Standalone.PiAtomHardCaseCorrectedCore
import Littlewood.Aristotle.Standalone.LandauPiCorrectedExtensionChain
import Littlewood.Aristotle.Standalone.CombinedAtomsFromDeepBlockers
import Littlewood.ZetaZeros.SupremumRealPart
import Littlewood.CoreLemmas.GrowthDomination

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open scoped Asymptotics

namespace Aristotle.Standalone.DeepBlockerAssembly

open MeasureTheory Set Filter
open HardyEstimatesPartial
open GrowthDomination
open ZetaZeros

/-- Exact Hardy mean-square atom shape used by `HardySetupV2`, supplied from the
critical-line second-moment asymptotic package. -/
theorem hardy_mean_square_lower_atom
    [Aristotle.HardyMeanSquareAsymptoticLeaf.HardyMeanSquareAsymptoticHyp] :
    ∃ c > 0, ∃ T₀ : ℝ, T₀ ≥ 2 ∧
      ∀ T : ℝ, T ≥ T₀ →
        ∫ t in Ioc 1 T, (hardyZ t) ^ 2 ≥ c * T * Real.log T := by
  exact Aristotle.HardyMeanSquareLowerStandalone.hardy_mean_square_lower_for_setup_v2

/-- Exact Hardy first-moment atom shape used by `HardySetupV2`, assembled from:
1) the main-term first-moment hypothesis and
2) centered RS block residual control. -/
theorem hardy_first_moment_upper_atom_from_mainTerm_and_centered_blocks
    [HardyFirstMomentWiring.MainTermFirstMomentBoundHyp]
    {A R : ℝ} (hA : 0 < A)
    (hcenter :
      ∀ T : ℝ, T ≥ 2 * Real.pi →
        |∑ k ∈ Finset.range (hardyN T),
          ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
              ErrorTerm t)
            - ((-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1) * A))| ≤ R) :
    ∀ ε : ℝ, ε > 0 →
      ∃ C : ℝ, C > 0 ∧ ∃ T₀ : ℝ, T₀ ≥ 2 ∧
        ∀ T : ℝ, T ≥ T₀ →
          |∫ t in Ioc 1 T, hardyZ t| ≤ C * T ^ (1 / 2 + ε) := by
  -- Rewrite the centered residual input into the exact shape expected by the
  -- existing RS-centered-block bridge (`(-1)^k * A * sqrt(k+1)` ordering).
  have hcenter' :
      ∀ T : ℝ, T ≥ 2 * Real.pi →
        |∑ k ∈ Finset.range (hardyN T),
          ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
              ErrorTerm t)
            - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))| ≤ R := by
    intro T hT
    have hEq :
        (∑ k ∈ Finset.range (hardyN T),
          ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
              ErrorTerm t)
            - ((-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1) * A)))
          =
        (∑ k ∈ Finset.range (hardyN T),
          ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
              ErrorTerm t)
            - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      ring
    simpa [hEq] using hcenter T hT
  exact Aristotle.HardyFirstMomentUpperStandalone.hardy_first_moment_upper_for_setup_v2_from_centered_blocks
    hA hcenter'

/-- Constructive Landau-`σ₀ < 1` atom:
`LandauAbscissaHyp` from direct `SigmaLtOneHyp` tail-integrability data. -/
theorem landau_abscissa_atom_from_sigmaLtOne
    (hyp : Aristotle.LandauAbscissaProof.SigmaLtOneHyp) :
    Aristotle.PringsheimPsiAtom.LandauAbscissaHyp := by
  exact Aristotle.Standalone.LandauSigmaLtOneFromCauchyDomination.landauAbscissaHyp_of_sigmaLtOne
    hyp

/-- RH-side `ψ-x = Ω±(√x·lll x)` atom from explicit-formula/Perron/alignment
cofinal witnesses. -/
theorem rh_psi_oscillation_atom_from_perron_explicit_alignment
    (hRH : ZetaZeros.RiemannHypothesis)
    (psiMain : ℝ → ℝ)
    (h_error : ∀ᶠ x in atTop,
      |(chebyshevPsi x - x) + psiMain x| ≤ Real.sqrt x * lll x)
    (h_main_plus : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      psiMain x ≤ -(2 * (Real.sqrt x * lll x)))
    (h_main_minus : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      2 * (Real.sqrt x * lll x) ≤ psiMain x) :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x * lll x] := by
  exact Aristotle.Standalone.RHWitnessConstructiveStrict.rh_psi_oscillation_from_perron_explicit_alignment
    hRH psiMain h_error h_main_plus h_main_minus

/-- RH-side `π-li = Ω±((√x/log x)·lll x)` atom from explicit-formula/Perron/
alignment cofinal witnesses. -/
theorem rh_pi_li_oscillation_atom_from_perron_explicit_alignment
    (hRH : ZetaZeros.RiemannHypothesis)
    (piMain : ℝ → ℝ)
    (h_error : ∀ᶠ x in atTop,
      |((Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x) + piMain x|
        ≤ Real.sqrt x / Real.log x * lll x)
    (h_main_plus : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      piMain x ≤ -(2 * (Real.sqrt x / Real.log x * lll x)))
    (h_main_minus : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      2 * (Real.sqrt x / Real.log x * lll x) ≤ piMain x) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x * lll x] := by
  exact Aristotle.Standalone.RHWitnessConstructiveStrict.rh_pi_li_oscillation_from_perron_explicit_alignment
    hRH piMain h_error h_main_plus h_main_minus

/-- Constructive `π` hard-case atom in the corrected `(s-1)*ζ` shape used by
the non-RH corrected extension chain. -/
theorem pi_corrected_extension_atom_from_core
    (hCore :
      Aristotle.Standalone.PiAtomHardCaseCorrectedCore.PiAtomHardCaseCorrectedCore) :
    Aristotle.Standalone.LandauPiCorrectedExtensionChain.PiIntegralHypCorrected := by
  exact Aristotle.Standalone.PiAtomHardCaseCorrectedCore.piIntegralHypCorrected_of_corrected_core
    hCore

/-- Full `DeepSorries.combined_atoms` target from explicit deep-blocker data. -/
theorem combined_atoms_from_five_blockers
    [Aristotle.HardyMeanSquareAsymptoticLeaf.HardyMeanSquareAsymptoticHyp]
    [HardyFirstMomentWiring.MainTermFirstMomentBoundHyp]
    [ZetaCriticalLineBoundHyp]
    (hRS : Aristotle.RSBlockDecomposition.PerBlockSignedBoundHyp)
    (hLandau : Aristotle.LandauAbscissaProof.SigmaLtOneHyp)
    (hRhPsi :
      Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPsiWitnessData)
    (hPiCore :
      Aristotle.Standalone.PiAtomHardCaseCorrectedCore.PiAtomHardCaseCorrectedCore)
    (hRhPi :
      Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData) :
    (Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 })
    ∧
    ((fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x])
    ∧
    ((fun x => (Nat.primeCounting (Nat.floor x) : ℝ) -
      LogarithmicIntegral.logarithmicIntegral x)
      =Ω±[fun x => Real.sqrt x / Real.log x * lll x]) := by
  exact Aristotle.Standalone.CombinedAtomsFromDeepBlockers.combined_atoms_from_blockers
    hRS hLandau hRhPsi hPiCore hRhPi

end Aristotle.Standalone.DeepBlockerAssembly
