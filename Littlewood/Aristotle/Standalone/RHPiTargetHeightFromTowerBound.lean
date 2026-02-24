import Littlewood.Aristotle.Standalone.LllUpperControl
import Littlewood.Aristotle.Standalone.RHPiWitnessFromPointwiseFamilies
import Littlewood.Aristotle.Standalone.RHPiWitnessFromTargetHeightControl

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiTargetHeightFromTowerBound

open Filter Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge
open Aristotle.Standalone.LllUpperControl
open Aristotle.Standalone.RHPiWitnessFromPointwiseFamilies
open Aristotle.Standalone.RHPiWitnessFromTargetHeightControl

/-- Positive-main RH pointwise witness family from target-height data where the
`2*lll` coefficient condition is replaced by a quantitative tower upper bound
for `x`. -/
theorem rh_pi_positive_main_witness_family_from_target_height_control_with_tower_bound
    (hRH : ∀ ρ ∈ zetaNontrivialZeros, ρ.re = 1 / 2)
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
        4 ≤ T ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ (finite_zeros_le T).toFinset,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) ∧
          x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2))))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
      |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
      4 * piScale x ≤ piMainFromZeros S x := by
  let X0 : ℝ := Real.exp (Real.exp (Real.exp 1))
  have h_target_height :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
        4 ≤ T ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ (finite_zeros_le T).toFinset,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) ∧
          2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1))) := by
    intro X
    rcases h_witness (max X X0) with
      ⟨x, hx, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hxUpper⟩
    have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx
    have hX0x : X0 ≤ x := le_trans (le_max_right _ _) (le_of_lt hx)
    have hcoeff :
        2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1)) := by
      exact two_mul_lll_le_of_le_exp_exp_exp_half hX0x hxUpper
    exact ⟨x, hXx, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hcoeff⟩
  exact rh_pi_positive_main_witness_family_from_target_height_control hRH h_target_height

/-- Negative-main RH pointwise witness family from anti-target-height data where
the `2*lll` coefficient condition is replaced by a quantitative tower upper
bound for `x`. -/
theorem rh_pi_negative_main_witness_family_from_antitarget_height_control_with_tower_bound
    (hRH : ∀ ρ ∈ zetaNontrivialZeros, ρ.re = 1 / 2)
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
        4 ≤ T ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ (finite_zeros_le T).toFinset,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) ∧
          x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2))))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
      |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
      piMainFromZeros S x ≤ -(4 * piScale x) := by
  let X0 : ℝ := Real.exp (Real.exp (Real.exp 1))
  have h_target_height :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
        4 ≤ T ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ (finite_zeros_le T).toFinset,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) ∧
          2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1))) := by
    intro X
    rcases h_witness (max X X0) with
      ⟨x, hx, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hxUpper⟩
    have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx
    have hX0x : X0 ≤ x := le_trans (le_max_right _ _) (le_of_lt hx)
    have hcoeff :
        2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1)) := by
      exact two_mul_lll_le_of_le_exp_exp_exp_half hX0x hxUpper
    exact ⟨x, hXx, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hcoeff⟩
  exact rh_pi_negative_main_witness_family_from_antitarget_height_control hRH h_target_height

/-- Full `RhPiWitnessData` from tower-bounded target/anti-target height control
families. -/
theorem rhPiWitness_from_target_height_with_tower_bounds
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
          x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2)))))
    (h_antitarget_height :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
        4 ≤ T ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ (finite_zeros_le T).toFinset,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) ∧
          x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2))))) :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData := by
  have h_minus :=
    rh_pi_positive_main_witness_family_from_target_height_control_with_tower_bound hRH
      h_target_height
  have h_plus :=
    rh_pi_negative_main_witness_family_from_antitarget_height_control_with_tower_bound hRH
      h_antitarget_height
  exact rhPiWitness_from_pointwise_witness_pair hRH h_minus h_plus

end Aristotle.Standalone.RHPiTargetHeightFromTowerBound
