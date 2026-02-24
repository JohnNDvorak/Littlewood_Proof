import Littlewood.Aristotle.Standalone.RHPiWitnessFromPointwiseFamilies

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiWitnessFromExplicitFormulaHeightControl

open Filter Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.CombinedAtomsFromDeepBlockers
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge
open Aristotle.Standalone.RHPiWitnessFromPointwiseFamilies
open Aristotle.Standalone.RHPiWitnessFromTargetHeightControl

/-- Positive-main RH pointwise witness family from target-height control data. -/
theorem rh_pi_pointwise_witness_main_positive_of_target_height_control
    (hRH : ZetaZeros.RiemannHypothesis)
    (h_target_height :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
        4 ≤ T ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ (finite_zeros_le T).toFinset,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) ∧
          2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1)))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
      |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
      4 * piScale x ≤ piMainFromZeros S x :=
  rh_pi_positive_main_witness_family_from_target_height_control hRH h_target_height

/-- Negative-main RH pointwise witness family from anti-target-height control
data. -/
theorem rh_pi_pointwise_witness_main_negative_of_target_height_control
    (hRH : ZetaZeros.RiemannHypothesis)
    (h_antitarget_height :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
        4 ≤ T ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ (finite_zeros_le T).toFinset,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) ∧
          2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1)))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
      |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
      piMainFromZeros S x ≤ -(4 * piScale x) :=
  rh_pi_negative_main_witness_family_from_antitarget_height_control hRH h_antitarget_height

/-- Full `RhPiWitnessData` from the two deep target-height RH inputs.

This is a no-sorry replacement path for the two atomic sorries currently in
`RHPiWitnessFromExplicitFormula.lean`. -/
theorem rhPiWitness_proved_of_target_height_control
    (hRH : ZetaZeros.RiemannHypothesis)
    (h_target_height :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
        4 ≤ T ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ (finite_zeros_le T).toFinset,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) ∧
          2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1))))
    (h_antitarget_height :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
        4 ≤ T ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ (finite_zeros_le T).toFinset,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) ∧
          2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1)))) :
    RhPiWitnessData :=
  rhPiWitness_from_target_height_control hRH h_target_height h_antitarget_height

end Aristotle.Standalone.RHPiWitnessFromExplicitFormulaHeightControl
