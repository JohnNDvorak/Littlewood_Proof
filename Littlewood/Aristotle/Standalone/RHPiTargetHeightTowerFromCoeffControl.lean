import Littlewood.Aristotle.Standalone.LllUpperControl
import Littlewood.Aristotle.Standalone.RHPiZeroSumAlignmentBridge

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiTargetHeightTowerFromCoeffControl

open Filter Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.LllUpperControl
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge

/-- Convert the RH π positive target-height control family (with coefficient
inequality) into the corresponding tower-bounded target-height family.

This is a pure real-analysis/logarithm inversion step; it introduces no new
coefficient-domination arguments. -/
theorem positive_target_height_tower_of_coeff_control
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
        4 ≤ T ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ (finite_zeros_le T).toFinset,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) ∧
          2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1)))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
      4 ≤ T ∧
      1 < x ∧
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
      (∃ ε : ℝ,
        0 < ε ∧ ε < 1 ∧
        (∀ ρ ∈ (finite_zeros_le T).toFinset,
          ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) ∧
        x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2)))) := by
  let X0 : ℝ := Real.exp (Real.exp (Real.exp 1))
  intro X
  rcases h_witness (max X X0) with
    ⟨x, hx, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hcoeff⟩
  have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx
  have hX0x : X0 ≤ x := le_trans (le_max_right _ _) (le_of_lt hx)
  have hxUpper :
      x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2))) := by
    simpa [X0] using
      (le_exp_exp_exp_half_of_two_mul_lll_le hX0x hcoeff)
  exact ⟨x, hXx, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hxUpper⟩

/-- Convert the RH π negative anti-target-height control family (with
coefficient inequality) into the corresponding tower-bounded anti-target-height
family.

This is the anti-target analogue of
`positive_target_height_tower_of_coeff_control`. -/
theorem antitarget_height_tower_of_coeff_control
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
        4 ≤ T ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ (finite_zeros_le T).toFinset,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) ∧
          2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1)))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
      4 ≤ T ∧
      1 < x ∧
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
      (∃ ε : ℝ,
        0 < ε ∧ ε < 1 ∧
        (∀ ρ ∈ (finite_zeros_le T).toFinset,
          ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) ∧
        x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2)))) := by
  let X0 : ℝ := Real.exp (Real.exp (Real.exp 1))
  intro X
  rcases h_witness (max X X0) with
    ⟨x, hx, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hcoeff⟩
  have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx
  have hX0x : X0 ≤ x := le_trans (le_max_right _ _) (le_of_lt hx)
  have hxUpper :
      x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2))) := by
    simpa [X0] using
      (le_exp_exp_exp_half_of_two_mul_lll_le hX0x hcoeff)
  exact ⟨x, hXx, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hxUpper⟩

/-- Constructor alias (positive branch) with explicit "witness family" naming.

This theorem is definitionally the same as
`positive_target_height_tower_of_coeff_control`. -/
theorem construct_positive_target_height_tower_witness_family
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
        4 ≤ T ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ (finite_zeros_le T).toFinset,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) ∧
          2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1)))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
      4 ≤ T ∧
      1 < x ∧
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
      (∃ ε : ℝ,
        0 < ε ∧ ε < 1 ∧
        (∀ ρ ∈ (finite_zeros_le T).toFinset,
          ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) ∧
        x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2)))) :=
  positive_target_height_tower_of_coeff_control h_witness

/-- Constructor alias (negative branch) with explicit "witness family" naming.

This theorem is definitionally the same as
`antitarget_height_tower_of_coeff_control`. -/
theorem construct_negative_antitarget_height_tower_witness_family
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
        4 ≤ T ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ (finite_zeros_le T).toFinset,
            ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) ∧
          2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1)))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
      4 ≤ T ∧
      1 < x ∧
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
      (∃ ε : ℝ,
        0 < ε ∧ ε < 1 ∧
        (∀ ρ ∈ (finite_zeros_le T).toFinset,
          ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) ∧
        x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2)))) :=
  antitarget_height_tower_of_coeff_control h_witness

end Aristotle.Standalone.RHPiTargetHeightTowerFromCoeffControl
