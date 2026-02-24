import Littlewood.Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt
import Littlewood.Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase
import Littlewood.Aristotle.Standalone.RHPiWitnessFromExplicitFormula

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPi7a7cFromPerronPhase

open Filter Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.CombinedAtomsFromDeepBlockers
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge
open Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt
open Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase
open Aristotle.Standalone.RHPiWitnessFromExplicitFormula

/-- Concrete bridge instance: positive phase-coupling payload gives the positive
tower witness class consumed by the 7a/7c endpoint. -/
instance targetTowerSqrtHyp_of_perronPhase
    [TargetTowerPhaseCouplingFamilyHyp] :
    RhPiTargetTowerSqrtWitnessHyp := by
  infer_instance

/-- Concrete bridge instance: negative phase-coupling payload gives the
negative tower witness class consumed by the 7a/7c endpoint. -/
instance antiTargetTowerSqrtHyp_of_perronPhase
    [AntiTargetTowerPhaseCouplingFamilyHyp] :
    RhPiAntiTargetTowerSqrtWitnessHyp := by
  infer_instance

/-- 7a payload from the RH-π tower witness payload classes:
eventual explicit-formula error witness at Littlewood's `piScale`. -/
theorem rh_pi_explicit_formula_error_from_perron_phase_payloads
    [RhPiTargetTowerSqrtWitnessHyp]
    [RhPiAntiTargetTowerSqrtWitnessHyp]
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∃ piMain : ℝ → ℝ,
      (∀ᶠ x in atTop,
        |((Nat.primeCounting (Nat.floor x) : ℝ) -
            LogarithmicIntegral.logarithmicIntegral x) + piMain x|
          ≤ Real.sqrt x / Real.log x * lll x) := by
  have hRhPi : RhPiWitnessData := rhPiWitness_proved_of_target_tower_sqrt_hyp
  rcases hRhPi hRH with ⟨piMain, hError, _hNeg, _hPos⟩
  exact ⟨piMain, hError⟩

/-- 7c payload from the RH-π tower witness payload classes:
cofinal `±3` oscillation witnesses for `π(x)-li(x)` at Littlewood scale. -/
theorem rh_pi_minus_li_oscillates_large_from_perron_phase_payloads
    [RhPiTargetTowerSqrtWitnessHyp]
    [RhPiAntiTargetTowerSqrtWitnessHyp]
    (hRH : ZetaZeros.RiemannHypothesis) :
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      ((Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x)
        ≤ -(3 * (Real.sqrt x / Real.log x * lll x))) ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      3 * (Real.sqrt x / Real.log x * lll x) ≤
        ((Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x)) := by
  exact rh_pi_minus_li_oscillates_large_of_coeff_control hRH
    (RhPiTargetHeightCoeffControlHyp.witness hRH)
    (RhPiAntiTargetHeightCoeffControlHyp.witness hRH)

/-- Combined 7a/7c endpoint for wiring into the RH branch. -/
theorem rh_pi_7a_7c_pair_from_perron_phase_payloads
    [RhPiTargetTowerSqrtWitnessHyp]
    [RhPiAntiTargetTowerSqrtWitnessHyp]
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
  refine ⟨?_, ?_⟩
  · exact rh_pi_explicit_formula_error_from_perron_phase_payloads hRH
  · exact rh_pi_minus_li_oscillates_large_from_perron_phase_payloads hRH

/-- Perron/phase-coupling entry point:
once the three deep payload families are proved, 7a and 7c follow with no
additional wiring. -/
theorem rh_pi_7a_7c_pair_from_perron_phase_hyp
    [TargetTowerPhaseCouplingFamilyHyp]
    [AntiTargetTowerPhaseCouplingFamilyHyp]
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
  exact rh_pi_7a_7c_pair_from_perron_phase_payloads hRH

end Aristotle.Standalone.RHPi7a7cFromPerronPhase
