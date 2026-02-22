import Littlewood.Aristotle.Standalone.RHPiZeroSumAlignmentBridge

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiLargeOscillationFromPointwise

open Filter Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge

/-- Strengthened alignment lower bound:
if the coefficient inequality holds with `2 * lll x`, then the finite-zero
main term is at least `4 * piScale x`. -/
theorem piMain_from_alignment_lower_four
    (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ.re = 1 / 2)
    {x : ℝ} (hx : 1 < x)
    {ε : ℝ} (hε : 0 < ε)
    (h_phases : ∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - 1‖ < ε)
    (h_coeff2 : 2 * lll x ≤
      (∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    4 * piScale x ≤ piMainFromZeros S x := by
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  have hlog_pos : 0 < Real.log x := Real.log_pos hx
  have hsum :=
    Aristotle.DirichletPhaseAlignment.bound_real_part_of_sum_aligned
      hS hx_pos hε h_phases
  unfold piScale piMainFromZeros
  have hmul :
      2 * (Real.sqrt x * (2 * lll x))
        ≤ 2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re) := by
    calc
      2 * (Real.sqrt x * (2 * lll x))
          ≤ 2 * (Real.sqrt x * ((∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖))) := by
            have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h_coeff2 hsqrt_nonneg) (by positivity)
      _ ≤ 2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re) := by
            have hsum_le :
                Real.sqrt x * ((∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖))
                  ≤ (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re) := by
              simpa using hsum
            exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
  have hdiv :
      (2 * (Real.sqrt x * (2 * lll x))) / Real.log x
        ≤ (2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)) / Real.log x := by
    exact div_le_div_of_nonneg_right hmul (le_of_lt hlog_pos)
  have hscaled :
      4 * (Real.sqrt x / Real.log x * lll x)
        ≤ (2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)) / Real.log x := by
    calc
      4 * (Real.sqrt x / Real.log x * lll x)
          = (2 * (Real.sqrt x * (2 * lll x))) / Real.log x := by
              field_simp [hlog_pos.ne']
              ring
      _ ≤ (2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)) / Real.log x := hdiv
  simpa [piScale, piMainFromZeros, mul_assoc, mul_comm, mul_left_comm] using hscaled

/-- Pointwise minus witness extraction with strengthened coefficient domination:
error at `piScale` + aligned main term at `4*piScale` implies
`piLiErr ≤ -3*piScale`. -/
theorem pi_minus_pointwise_from_explicit_error_alignment_coeff_four
    (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ.re = 1 / 2)
    {x : ℝ} (hx : 1 < x)
    {ε : ℝ} (hε : 0 < ε)
    (h_error_at_x : |piLiErr x + piMainFromZeros S x| ≤ piScale x)
    (h_phases : ∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - 1‖ < ε)
    (h_coeff2 : 2 * lll x ≤
      (∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    piLiErr x ≤ -(3 * piScale x) := by
  have hmain4 : 4 * piScale x ≤ piMainFromZeros S x :=
    piMain_from_alignment_lower_four S hS hx hε h_phases h_coeff2
  have hupp : piLiErr x + piMainFromZeros S x ≤ piScale x :=
    (abs_le.mp h_error_at_x).2
  nlinarith

/-- Pointwise minus witness extraction at `4*piScale`:
error at `piScale` + sufficiently positive main term implies
`piLiErr ≤ -3*piScale`. -/
theorem pi_minus_pointwise_from_explicit_error_main_positive_four
    (S : Finset ℂ)
    {x : ℝ}
    (h_error_at_x : |piLiErr x + piMainFromZeros S x| ≤ piScale x)
    (h_main_positive : 4 * piScale x ≤ piMainFromZeros S x) :
    piLiErr x ≤ -(3 * piScale x) := by
  have hupp : piLiErr x + piMainFromZeros S x ≤ piScale x :=
    (abs_le.mp h_error_at_x).2
  nlinarith

/-- Pointwise plus witness extraction at `4*piScale`:
error at `piScale` + sufficiently negative main term implies
`3*piScale ≤ piLiErr`. -/
theorem pi_plus_pointwise_from_explicit_error_main_negative_four
    (S : Finset ℂ)
    {x : ℝ}
    (h_error_at_x : |piLiErr x + piMainFromZeros S x| ≤ piScale x)
    (h_main_negative : piMainFromZeros S x ≤ -(4 * piScale x)) :
    3 * piScale x ≤ piLiErr x := by
  have hlow : -piScale x ≤ piLiErr x + piMainFromZeros S x :=
    (abs_le.mp h_error_at_x).1
  nlinarith

/-- Convert a minus-branch alignment/coefficient witness family into a
minus-branch main-positive witness family (`4*piScale ≤ piMainFromZeros`).
This isolates the deterministic conversion from the deep phase-alignment input. -/
theorem rh_pi_minus_witness_main_positive_from_alignment_coeff
    (ε : ℝ) (hε : 0 < ε)
    (h_witness_minus_alignment :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
        (∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - 1‖ < ε) ∧
        2 * lll x ≤
          (∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
      |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
      4 * piScale x ≤ piMainFromZeros S x := by
  intro X
  obtain ⟨x, hxX, S, hS, hx1, herr, hphases, hcoeff2⟩ := h_witness_minus_alignment X
  have hSre : ∀ ρ ∈ S, ρ.re = 1 / 2 := fun ρ hρ => (hS ρ hρ).2
  have hmainpos : 4 * piScale x ≤ piMainFromZeros S x :=
    piMain_from_alignment_lower_four S hSre hx1 hε hphases hcoeff2
  exact ⟨x, hxX, S, hS, herr, hmainpos⟩

/-- Cofinal `±3` oscillation for `piLiErr` from pointwise witness families.
The minus branch uses sufficiently positive finite-zero main term;
the plus branch uses sufficiently negative finite-zero main term. -/
theorem rh_pi_minus_li_oscillates_large_from_pointwise_witness_pair
    (_hRH : ZetaZeros.RiemannHypothesis)
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
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧ piLiErr x ≤ -(3 * piScale x)) ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧ 3 * piScale x ≤ piLiErr x) := by
  constructor
  · intro X
    obtain ⟨x, hxX, S, _hS, herr, hmainpos⟩ := h_witness_minus X
    refine ⟨x, hxX, ?_⟩
    exact pi_minus_pointwise_from_explicit_error_main_positive_four
      S herr hmainpos
  · intro X
    obtain ⟨x, hx, S, _hS, herr, hmainneg⟩ := h_witness_plus X
    refine ⟨x, hx, ?_⟩
    exact pi_plus_pointwise_from_explicit_error_main_negative_four
      S herr hmainneg

end Aristotle.Standalone.RHPiLargeOscillationFromPointwise
