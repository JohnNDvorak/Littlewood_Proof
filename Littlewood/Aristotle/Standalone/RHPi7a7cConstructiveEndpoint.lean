import Littlewood.Aristotle.Standalone.RHPi7a7cFromPerronPhase
import Littlewood.Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPi7a7cConstructiveEndpoint

open Filter Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.CombinedAtomsFromDeepBlockers
open Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase
open Aristotle.Standalone.RHPi7a7cFromPerronPhase

/-- Positive constructive goal for 7a/7c: full target phase-coupled tower family.
This is exactly the data expected by `TargetTowerPhaseCouplingFamilyHyp.witness`. -/
abbrev TargetTowerPhaseCouplingGoal : Prop :=
  TargetTowerPhaseCouplingFamily

/-- Negative constructive goal for 7a/7c: full anti-target phase-coupled tower family.
This is exactly the data expected by `AntiTargetTowerPhaseCouplingFamilyHyp.witness`. -/
abbrev AntiTargetTowerPhaseCouplingGoal : Prop :=
  AntiTargetTowerPhaseCouplingFamily

/-- Package a proved positive constructive goal into the typeclass consumed by
`RHPiTowerWitnessFromPerronAndPhase`. -/
theorem target_phase_class_of_goal
    (hTarget : TargetTowerPhaseCouplingGoal) :
    TargetTowerPhaseCouplingFamilyHyp :=
  ⟨hTarget⟩

/-- Package a proved negative constructive goal into the typeclass consumed by
`RHPiTowerWitnessFromPerronAndPhase`. -/
theorem anti_target_phase_class_of_goal
    (hAntiTarget : AntiTargetTowerPhaseCouplingGoal) :
    AntiTargetTowerPhaseCouplingFamilyHyp :=
  ⟨hAntiTarget⟩

/-- Direct endpoint: once the two constructive 7a/7c goals are proved,
`RhPiWitnessData` follows immediately with no additional assembly work. -/
theorem rhPiWitnessData_of_constructive_goals
    (hTarget : TargetTowerPhaseCouplingGoal)
    (hAntiTarget : AntiTargetTowerPhaseCouplingGoal) :
    RhPiWitnessData := by
  letI : TargetTowerPhaseCouplingFamilyHyp :=
    target_phase_class_of_goal hTarget
  letI : AntiTargetTowerPhaseCouplingFamilyHyp :=
    anti_target_phase_class_of_goal hAntiTarget
  exact rhPiWitnessData_of_hyp

/-- 7a/7c endpoint from the two constructive goals.
This is the exact pair consumed on the RH-`pi` branch in `DeepSorries`. -/
theorem rh_pi_7a_7c_pair_of_constructive_goals
    (hTarget : TargetTowerPhaseCouplingGoal)
    (hAntiTarget : AntiTargetTowerPhaseCouplingGoal)
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
  letI : TargetTowerPhaseCouplingFamilyHyp :=
    target_phase_class_of_goal hTarget
  letI : AntiTargetTowerPhaseCouplingFamilyHyp :=
    anti_target_phase_class_of_goal hAntiTarget
  exact rh_pi_7a_7c_pair_from_perron_phase_hyp hRH

end Aristotle.Standalone.RHPi7a7cConstructiveEndpoint
