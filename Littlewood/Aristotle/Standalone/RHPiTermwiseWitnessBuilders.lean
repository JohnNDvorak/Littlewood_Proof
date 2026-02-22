import Littlewood.Aristotle.Standalone.RHPiZeroSumAlignmentBridge

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiTermwiseWitnessBuilders

open Filter Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge

/--
Deterministic lower bound for the finite-zero main term from a termwise lower
bound against `((1-ε)/‖ρ‖)` and a coefficient-domination inequality.

This isolates the purely algebraic transfer:
termwise control + coefficient domination -> `4 * piScale x ≤ piMainFromZeros S x`.
-/
theorem piMain_from_termwise_lower_four
    (S : Finset ℂ)
    {x : ℝ} (hx : 1 < x)
    {ε : ℝ}
    (hterm :
      ∀ ρ ∈ S,
        Real.sqrt x * ((1 - ε) / ‖ρ‖)
          ≤ ((x : ℂ) ^ ρ / ρ).re)
    (hcoeff :
      2 * lll x ≤ (1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    4 * piScale x ≤ piMainFromZeros S x := by
  have hlog_pos : 0 < Real.log x := Real.log_pos hx
  have hsum_termwise :
      (∑ ρ ∈ S, Real.sqrt x * ((1 - ε) / ‖ρ‖))
        ≤ (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re) := by
    exact Finset.sum_le_sum (fun ρ hρ => hterm ρ hρ)
  have hsum_rewrite :
      (∑ ρ ∈ S, Real.sqrt x * ((1 - ε) / ‖ρ‖))
        = Real.sqrt x * ((1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖)) := by
    calc
      (∑ ρ ∈ S, Real.sqrt x * ((1 - ε) / ‖ρ‖))
          = Real.sqrt x * (∑ ρ ∈ S, ((1 - ε) / ‖ρ‖)) := by
              rw [Finset.mul_sum]
      _ = Real.sqrt x * ((1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖)) := by
            congr 1
            calc
              (∑ ρ ∈ S, ((1 - ε) / ‖ρ‖))
                  = ∑ ρ ∈ S, ((1 - ε) * (1 / ‖ρ‖)) := by
                      refine Finset.sum_congr rfl (fun ρ hρ => ?_)
                      ring
              _ = (1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖) := by
                    rw [Finset.mul_sum]
  have hsum_lower :
      Real.sqrt x * ((1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖))
        ≤ (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re) := by
    rw [← hsum_rewrite]
    exact hsum_termwise
  have hcoeff_scaled :
      Real.sqrt x * (2 * lll x)
        ≤ Real.sqrt x * ((1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖)) := by
    exact mul_le_mul_of_nonneg_left hcoeff (Real.sqrt_nonneg x)
  have hmain_lower :
      Real.sqrt x * (2 * lll x)
        ≤ (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re) := by
    exact le_trans hcoeff_scaled hsum_lower
  unfold piMainFromZeros piScale
  have hmul :
      2 * (Real.sqrt x * (2 * lll x))
        ≤ 2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re) := by
    exact mul_le_mul_of_nonneg_left hmain_lower (by positivity)
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

/--
Deterministic upper bound for the finite-zero main term from a termwise upper
bound against `-((1-ε)/‖ρ‖)` and a coefficient-domination inequality.
-/
theorem piMain_from_termwise_upper_four
    (S : Finset ℂ)
    {x : ℝ} (hx : 1 < x)
    {ε : ℝ}
    (hterm :
      ∀ ρ ∈ S,
        ((x : ℂ) ^ ρ / ρ).re
          ≤ -(Real.sqrt x * ((1 - ε) / ‖ρ‖)))
    (hcoeff :
      2 * lll x ≤ (1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    piMainFromZeros S x ≤ -(4 * piScale x) := by
  have hlog_pos : 0 < Real.log x := Real.log_pos hx
  have hsum_termwise :
      (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)
        ≤ (∑ ρ ∈ S, -(Real.sqrt x * ((1 - ε) / ‖ρ‖))) := by
    exact Finset.sum_le_sum (fun ρ hρ => hterm ρ hρ)
  have hsum_rewrite :
      (∑ ρ ∈ S, -(Real.sqrt x * ((1 - ε) / ‖ρ‖)))
        = -(Real.sqrt x * ((1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖))) := by
    calc
      (∑ ρ ∈ S, -(Real.sqrt x * ((1 - ε) / ‖ρ‖)))
          = -(∑ ρ ∈ S, Real.sqrt x * ((1 - ε) / ‖ρ‖)) := by
              rw [Finset.sum_neg_distrib]
      _ = -(Real.sqrt x * ((1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖))) := by
            congr 1
            calc
              (∑ ρ ∈ S, Real.sqrt x * ((1 - ε) / ‖ρ‖))
                  = Real.sqrt x * (∑ ρ ∈ S, ((1 - ε) / ‖ρ‖)) := by
                      rw [Finset.mul_sum]
              _ = Real.sqrt x * ((1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖)) := by
                    congr 1
                    calc
                      (∑ ρ ∈ S, ((1 - ε) / ‖ρ‖))
                          = ∑ ρ ∈ S, ((1 - ε) * (1 / ‖ρ‖)) := by
                              refine Finset.sum_congr rfl (fun ρ hρ => ?_)
                              ring
                      _ = (1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖) := by
                            rw [Finset.mul_sum]
  have hsum_upper :
      (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)
        ≤ -(Real.sqrt x * ((1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖))) := by
    rw [hsum_rewrite] at hsum_termwise
    exact hsum_termwise
  have hcoeff_neg :
      -((1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖)) ≤ -(2 * lll x) := by
    nlinarith [hcoeff]
  have hcoeff_scaled :
      Real.sqrt x * (-( (1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖)))
        ≤ Real.sqrt x * (-(2 * lll x)) := by
    exact mul_le_mul_of_nonneg_left hcoeff_neg (Real.sqrt_nonneg x)
  have hmain_upper :
      (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)
        ≤ -(Real.sqrt x * (2 * lll x)) := by
    have htmp :
        (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)
          ≤ Real.sqrt x * (-(2 * lll x)) := by
      calc
        (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)
            ≤ -(Real.sqrt x * ((1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖))) := hsum_upper
        _ = Real.sqrt x * (-((1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖))) := by ring
        _ ≤ Real.sqrt x * (-(2 * lll x)) := hcoeff_scaled
    nlinarith [htmp]
  unfold piMainFromZeros piScale
  have hmul :
      2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)
        ≤ -(4 * (Real.sqrt x * lll x)) := by
    nlinarith [hmain_upper]
  have hdiv :
      (2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)) / Real.log x
        ≤ (-(4 * (Real.sqrt x * lll x))) / Real.log x := by
    exact div_le_div_of_nonneg_right hmul (le_of_lt hlog_pos)
  have hscaled :
      (2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)) / Real.log x
        ≤ -(4 * (Real.sqrt x / Real.log x * lll x)) := by
    calc
      (2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)) / Real.log x
          ≤ (-(4 * (Real.sqrt x * lll x))) / Real.log x := hdiv
      _ = -(4 * ((Real.sqrt x * lll x) / Real.log x)) := by ring
      _ = -(4 * (Real.sqrt x / Real.log x * lll x)) := by ring
  simpa [piMainFromZeros, piScale, mul_assoc, mul_comm, mul_left_comm] using hscaled

/--
Build the positive pointwise finite-zero RH witness family from:
1. pointwise explicit-formula error witnesses, and
2. termwise lower-bound witnesses strong enough to force `4*piScale` positivity.
-/
theorem rh_pi_positive_main_witness_family_from_termwise_lower
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ S,
            Real.sqrt x * ((1 - ε) / ‖ρ‖)
              ≤ ((x : ℂ) ^ ρ / ρ).re) ∧
          2 * lll x ≤ (1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
      |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
      4 * piScale x ≤ piMainFromZeros S x := by
  intro X
  obtain ⟨x, hxX, S, hS, hx1, herr, ε, _hεpos, _hεlt1, hterm, hcoeff⟩ := h_witness X
  have hmain : 4 * piScale x ≤ piMainFromZeros S x :=
    piMain_from_termwise_lower_four S hx1 hterm hcoeff
  exact ⟨x, hxX, S, hS, herr, hmain⟩

/--
Build the negative pointwise finite-zero RH witness family from:
1. pointwise explicit-formula error witnesses, and
2. termwise upper-bound witnesses strong enough to force `-4*piScale` negativity.
-/
theorem rh_pi_negative_main_witness_family_from_termwise_upper
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ S,
            ((x : ℂ) ^ ρ / ρ).re
              ≤ -(Real.sqrt x * ((1 - ε) / ‖ρ‖))) ∧
          2 * lll x ≤ (1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
      |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
      piMainFromZeros S x ≤ -(4 * piScale x) := by
  intro X
  obtain ⟨x, hxX, S, hS, hx1, herr, ε, _hεpos, _hεlt1, hterm, hcoeff⟩ := h_witness X
  have hmain : piMainFromZeros S x ≤ -(4 * piScale x) :=
    piMain_from_termwise_upper_four S hx1 hterm hcoeff
  exact ⟨x, hxX, S, hS, herr, hmain⟩

end Aristotle.Standalone.RHPiTermwiseWitnessBuilders
