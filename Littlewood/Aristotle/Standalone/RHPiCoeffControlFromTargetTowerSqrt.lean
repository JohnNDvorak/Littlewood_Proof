import Littlewood.Aristotle.Standalone.LllUpperControl
import Littlewood.Aristotle.Standalone.RHPiPerronTowerWitness
import Littlewood.Aristotle.Standalone.RHPiWitnessFromExplicitFormula

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt

open Filter Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge
open Aristotle.Standalone.LllUpperControl
open Aristotle.Standalone.RHPiPerronTowerWitness
open Aristotle.Standalone.RHPiWitnessFromExplicitFormula

/-- Convert target-height tower witnesses (at baseline `sqrt/log` error scale)
into the coefficient-control input shape consumed by
`RHPiWitnessFromExplicitFormula`. -/
theorem target_height_coeff_control_of_target_tower_sqrt
    (hTarget : ∀ _hRH : ZetaZeros.RiemannHypothesis, TargetHeightTowerSqrtWitness) :
    ∀ _hRH : ZetaZeros.RiemannHypothesis,
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
        4 ≤ T ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ (finite_zeros_le T).toFinset,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) ∧
          2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1))) := by
  intro hRH X
  let X0 : ℝ := Real.exp (Real.exp (Real.exp 1))
  have hTargetPi : TargetHeightTowerPiScaleWitness :=
    target_tower_sqrt_to_piScale (hTarget hRH)
  rcases hTargetPi (max X X0) with
    ⟨x, hx, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hxUpper⟩
  have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx
  have hX0x : X0 ≤ x := le_trans (le_max_right _ _) (le_of_lt hx)
  have hcoeff : 2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1)) := by
    simpa [X0] using two_mul_lll_le_of_le_exp_exp_exp_half hX0x hxUpper
  exact ⟨x, hXx, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hcoeff⟩

/-- Convert anti-target-height tower witnesses (at baseline `sqrt/log` error
scale) into the anti-target coefficient-control input shape consumed by
`RHPiWitnessFromExplicitFormula`. -/
theorem antitarget_height_coeff_control_of_target_tower_sqrt
    (hAntiTarget :
      ∀ _hRH : ZetaZeros.RiemannHypothesis, AntiTargetHeightTowerSqrtWitness) :
    ∀ _hRH : ZetaZeros.RiemannHypothesis,
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
        4 ≤ T ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ (finite_zeros_le T).toFinset,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) ∧
          2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1))) := by
  intro hRH X
  let X0 : ℝ := Real.exp (Real.exp (Real.exp 1))
  have hAntiTargetPi : AntiTargetHeightTowerPiScaleWitness :=
    antitarget_tower_sqrt_to_piScale (hAntiTarget hRH)
  rcases hAntiTargetPi (max X X0) with
    ⟨x, hx, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hxUpper⟩
  have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx
  have hX0x : X0 ≤ x := le_trans (le_max_right _ _) (le_of_lt hx)
  have hcoeff : 2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1)) := by
    simpa [X0] using two_mul_lll_le_of_le_exp_exp_exp_half hX0x hxUpper
  exact ⟨x, hXx, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hcoeff⟩

/-- Full Blocker-7 payload from Perron-style target/anti-target tower witness
families, routed through the coefficient-control bridge. -/
theorem rhPiWitness_proved_of_target_tower_sqrt_via_coeff
    (hTarget : ∀ _hRH : ZetaZeros.RiemannHypothesis, TargetHeightTowerSqrtWitness)
    (hAntiTarget :
      ∀ _hRH : ZetaZeros.RiemannHypothesis, AntiTargetHeightTowerSqrtWitness) :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData := by
  exact rhPiWitness_proved_of_coeff_control
    (target_height_coeff_control_of_target_tower_sqrt hTarget)
    (antitarget_height_coeff_control_of_target_tower_sqrt hAntiTarget)

/-- Deep positive payload class: Perron-style target tower witness family. -/
class RhPiTargetTowerSqrtWitnessHyp : Prop where
  witness : ∀ _hRH : ZetaZeros.RiemannHypothesis, TargetHeightTowerSqrtWitness

/-- Deep negative payload class: Perron-style anti-target tower witness family. -/
class RhPiAntiTargetTowerSqrtWitnessHyp : Prop where
  witness : ∀ _hRH : ZetaZeros.RiemannHypothesis, AntiTargetHeightTowerSqrtWitness

/-- Typeclass instance bridge from tower-sqrt witness payload to the positive
coefficient-control payload required by `RHPiWitnessFromExplicitFormula`. -/
instance [RhPiTargetTowerSqrtWitnessHyp] : RhPiTargetHeightCoeffControlHyp where
  witness := target_height_coeff_control_of_target_tower_sqrt
    RhPiTargetTowerSqrtWitnessHyp.witness

/-- Typeclass instance bridge from tower-sqrt witness payload to the negative
coefficient-control payload required by `RHPiWitnessFromExplicitFormula`. -/
instance [RhPiAntiTargetTowerSqrtWitnessHyp] :
    RhPiAntiTargetHeightCoeffControlHyp where
  witness := antitarget_height_coeff_control_of_target_tower_sqrt
    RhPiAntiTargetTowerSqrtWitnessHyp.witness

/-- Convenience endpoint: once the Perron-style target/anti-target tower
witness families are provided, `RHPiWitnessFromExplicitFormula.rhPiWitness_proved`
is available directly by typeclass resolution. -/
theorem rhPiWitness_proved_of_target_tower_sqrt_hyp
    [RhPiTargetTowerSqrtWitnessHyp]
    [RhPiAntiTargetTowerSqrtWitnessHyp] :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData := by
  exact rhPiWitness_proved

end Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt
