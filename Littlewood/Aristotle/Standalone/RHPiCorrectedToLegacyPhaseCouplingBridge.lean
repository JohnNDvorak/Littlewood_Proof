import Littlewood.Aristotle.Standalone.RHPi7a7cFromPerronPhase
import Littlewood.Aristotle.Standalone.RHPiCorrectedCanonicalWitnessClasses
import Littlewood.Aristotle.Standalone.RHPiPhaseCouplingConstructiveFamilies

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiCorrectedToLegacyPhaseCouplingBridge

open Filter Complex ZetaZeros
open GrowthDomination
open PiLiDirectOscillationBridge
open Aristotle.Standalone.CombinedAtomsFromDeepBlockers
open Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase
open Aristotle.Standalone.RHPiCorrectedCanonicalWitnessClasses
open Aristotle.Standalone.RHPi7a7cFromPerronPhase

/-- Corrected canonical positive payload class implies the current legacy
phase-coupling positive payload class. -/
instance
    [TargetTowerPhaseCouplingFamilyHyp_corrected] :
    TargetTowerPhaseCouplingFamilyHyp where
  witness := TargetTowerPhaseCouplingFamilyHyp_corrected.witness

/-- Corrected canonical negative payload class implies the current legacy
phase-coupling negative payload class. -/
instance
    [AntiTargetTowerPhaseCouplingFamilyHyp_corrected] :
    AntiTargetTowerPhaseCouplingFamilyHyp where
  witness := AntiTargetTowerPhaseCouplingFamilyHyp_corrected.witness

/-- Full RH-`pi` witness endpoint from corrected canonical payload classes. -/
theorem rhPiWitnessData_of_correctedHyp
    [TargetTowerPhaseCouplingFamilyHyp_corrected]
    [AntiTargetTowerPhaseCouplingFamilyHyp_corrected] :
    RhPiWitnessData := by
  exact Aristotle.Standalone.RHPiPhaseCouplingConstructiveFamilies.rhPiWitnessData_of_phaseCouplingHyp

/-- 7a/7c pair endpoint from corrected canonical payload classes. -/
theorem rh_pi_7a_7c_pair_of_correctedHyp
    [TargetTowerPhaseCouplingFamilyHyp_corrected]
    [AntiTargetTowerPhaseCouplingFamilyHyp_corrected]
    (hRH : ZetaZeros.RiemannHypothesis) :
    (∃ piMain : ℝ → ℝ,
      (∀ᶠ x in atTop,
        |((Nat.primeCounting (Nat.floor x) : ℝ) -
            LogarithmicIntegral.logarithmicIntegral x) + piMain x|
          ≤ Real.sqrt x / Real.log x * lll x))
    ∧
    ((∀ X : ℝ, ∃ x : ℝ, X < x ∧
      ((Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x)
        ≤ -(3 * (Real.sqrt x / Real.log x * lll x)))
    ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      3 * (Real.sqrt x / Real.log x * lll x) ≤
        ((Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x))) := by
  exact rh_pi_7a_7c_pair_from_perron_phase_hyp hRH

end Aristotle.Standalone.RHPiCorrectedToLegacyPhaseCouplingBridge
