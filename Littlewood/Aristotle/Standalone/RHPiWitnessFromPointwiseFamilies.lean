import Littlewood.Aristotle.Standalone.CombinedAtomsFromDeepBlockers
import Littlewood.Aristotle.Standalone.RHPiLargeOscillationFromPointwise
import Littlewood.Aristotle.Standalone.RHPiWitnessFromFrequentScale
import Littlewood.Aristotle.Standalone.RHPiWitnessFromTargetHeightControl

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiWitnessFromPointwiseFamilies

open Filter Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.CombinedAtomsFromDeepBlockers
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge
open Aristotle.Standalone.RHPiLargeOscillationFromPointwise
open Aristotle.Standalone.RHPiWitnessFromFrequentScale
open Aristotle.Standalone.RHPiWitnessFromTargetHeightControl

/-- Eventual nonnegativity of the RH π comparison scale. -/
private lemma piScale_eventually_nonneg :
    ∀ᶠ x in atTop, 0 ≤ piScale x := by
  filter_upwards [lll_eventually_ge_one, eventually_ge_atTop (Real.exp 1)] with x hlll hx
  have h_exp1_gt_one : (1 : ℝ) < Real.exp 1 :=
    Real.one_lt_exp_iff.mpr zero_lt_one
  have hx_one : 1 < x := lt_of_lt_of_le h_exp1_gt_one hx
  have hlog_pos : 0 < Real.log x := Real.log_pos hx_one
  have hdiv_nonneg : 0 ≤ Real.sqrt x / Real.log x :=
    div_nonneg (Real.sqrt_nonneg x) (le_of_lt hlog_pos)
  have hlll_nonneg : 0 ≤ lll x := le_trans (by norm_num) hlll
  exact mul_nonneg hdiv_nonneg hlll_nonneg

/-- Convert cofinal `±3*piScale` oscillation of `piLiErr` into cofinal
`±piScale` witnesses. -/
private theorem frequent_unit_of_large_oscillation
    (h_osc :
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧ piLiErr x ≤ -(3 * piScale x)) ∧
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧ 3 * piScale x ≤ piLiErr x)) :
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧ piScale x ≤ piLiErr x) ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧ piLiErr x ≤ -piScale x) := by
  rcases (Filter.eventually_atTop.1 piScale_eventually_nonneg) with ⟨B, hB⟩
  constructor
  · intro X
    rcases h_osc.2 (max X B) with ⟨x, hx, hplus3⟩
    have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx
    have hBx : B ≤ x := le_trans (le_max_right _ _) (le_of_lt hx)
    have hscale_nonneg : 0 ≤ piScale x := hB x hBx
    refine ⟨x, hXx, ?_⟩
    nlinarith
  · intro X
    rcases h_osc.1 (max X B) with ⟨x, hx, hminus3⟩
    have hXx : X < x := lt_of_le_of_lt (le_max_left _ _) hx
    have hBx : B ≤ x := le_trans (le_max_right _ _) (le_of_lt hx)
    have hscale_nonneg : 0 ≤ piScale x := hB x hBx
    refine ⟨x, hXx, ?_⟩
    nlinarith

/-- Build `RhPiWitnessData` from pointwise finite-zero witness families with
`±4*piScale` main-term margins. -/
theorem rhPiWitness_from_pointwise_witness_pair
    (hRH : ZetaZeros.RiemannHypothesis)
    (h_witness_minus :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
        |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
        4 * piScale x ≤ piMainFromZeros S x)
    (h_witness_plus :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
        |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
        piMainFromZeros S x ≤ -(4 * piScale x)) :
    RhPiWitnessData := by
  have h_osc :
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧ piLiErr x ≤ -(3 * piScale x)) ∧
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧ 3 * piScale x ≤ piLiErr x) :=
    rh_pi_minus_li_oscillates_large_from_pointwise_witness_pair
      hRH h_witness_minus h_witness_plus
  have h_unit :
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧ piScale x ≤ piLiErr x) ∧
      (∀ X : ℝ, ∃ x : ℝ, X < x ∧ piLiErr x ≤ -piScale x) :=
    frequent_unit_of_large_oscillation h_osc
  exact rhPiWitness_from_frequent_unit h_unit.1 h_unit.2

/-- Height-indexed witness shape for the positive-main branch. -/
private abbrev TargetHeightPositiveWitness : Prop :=
  ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
    4 ≤ T ∧
    1 < x ∧
    |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
    (∃ ε : ℝ,
      0 < ε ∧ ε < 1 ∧
      (∀ ρ ∈ (finite_zeros_le T).toFinset,
        ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) ∧
      2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1)))

/-- Height-indexed witness shape for the negative-main branch. -/
private abbrev TargetHeightNegativeWitness : Prop :=
  ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
    4 ≤ T ∧
    1 < x ∧
    |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ piScale x ∧
    (∃ ε : ℝ,
      0 < ε ∧ ε < 1 ∧
      (∀ ρ ∈ (finite_zeros_le T).toFinset,
        ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) ∧
      2 * lll x ≤ (1 - ε) * ((N T : ℝ) / (T + 1)))

/-- Build `RhPiWitnessData` directly from the two deep target-height witness
families (positive and anti-target negative). -/
theorem rhPiWitness_from_target_height_control
    (hRH : ZetaZeros.RiemannHypothesis)
    (h_target_height : TargetHeightPositiveWitness)
    (h_antitarget_height : TargetHeightNegativeWitness) :
    RhPiWitnessData := by
  have h_witness_minus :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
        |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
        4 * piScale x ≤ piMainFromZeros S x :=
    rh_pi_positive_main_witness_family_from_target_height_control hRH h_target_height
  have h_witness_plus :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
        |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
        piMainFromZeros S x ≤ -(4 * piScale x) :=
    rh_pi_negative_main_witness_family_from_antitarget_height_control hRH h_antitarget_height
  exact rhPiWitness_from_pointwise_witness_pair hRH h_witness_minus h_witness_plus

end Aristotle.Standalone.RHPiWitnessFromPointwiseFamilies
