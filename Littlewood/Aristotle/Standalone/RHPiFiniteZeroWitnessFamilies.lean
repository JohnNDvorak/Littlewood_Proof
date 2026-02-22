import Littlewood.Aristotle.Standalone.RHPiZeroSumAlignmentBridge
import Littlewood.CoreLemmas.GrowthDomination
import Littlewood.ZetaZeros.SupremumRealPart

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiFiniteZeroWitnessFamilies

open Filter Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge

/--
Ground-up transfer for the RH `π-li` explicit-formula witness family.

If a fixed finite critical-line set `S` satisfies an eventual explicit-formula
bound at scale `√x / log x`, then the canonical Littlewood scale
`(√x / log x) * lll x` follows cofinally. This supplies the exact witness
shape used in the RH `π-li` payload.
-/
theorem rh_pi_finite_zero_error_witness_family_from_eventual_formula
    (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2)
    (h_formula : ∀ᶠ x in atTop,
      |piLiErr x + piMainFromZeros S x| ≤ Real.sqrt x / Real.log x) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S' : Finset ℂ,
      (∀ ρ ∈ S', ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
      |piLiErr x + piMainFromZeros S' x| ≤ piScale x := by
  have h_event :
      ∀ᶠ x in atTop,
        |piLiErr x + piMainFromZeros S x| ≤ Real.sqrt x / Real.log x
          ∧ (1 : ℝ) ≤ lll x ∧ Real.exp 1 ≤ x := by
    have h_ge_exp1 : ∀ᶠ x : ℝ in atTop, Real.exp 1 ≤ x := eventually_ge_atTop (a := Real.exp 1)
    exact h_formula.and (lll_eventually_ge_one.and h_ge_exp1)
  rcases (Filter.eventually_atTop.1 h_event) with ⟨B, hB⟩
  intro X
  refine ⟨max X B + 1, ?_, S, hS, ?_⟩
  · have hXB : X ≤ max X B := le_max_left X B
    linarith
  · have hBB : B ≤ max X B := le_max_right X B
    have hB' : B ≤ max X B + 1 := by linarith
    obtain ⟨h_err, hlll, hexp1⟩ := hB (max X B + 1) hB'
    have h_exp1_gt_one : (1 : ℝ) < Real.exp 1 := by
      simpa using (Real.one_lt_exp_iff.mpr zero_lt_one)
    have hx_gt_one : (1 : ℝ) < max X B + 1 := lt_of_lt_of_le h_exp1_gt_one hexp1
    have hlog_pos : 0 < Real.log (max X B + 1) :=
      Real.log_pos hx_gt_one
    have hdiv_nonneg :
        0 ≤ Real.sqrt (max X B + 1) / Real.log (max X B + 1) :=
      div_nonneg (Real.sqrt_nonneg _) (le_of_lt hlog_pos)
    have hscale_le :
        Real.sqrt (max X B + 1) / Real.log (max X B + 1)
          ≤ piScale (max X B + 1) := by
      calc
        Real.sqrt (max X B + 1) / Real.log (max X B + 1)
            ≤ (Real.sqrt (max X B + 1) / Real.log (max X B + 1)) * lll (max X B + 1) :=
              le_mul_of_one_le_right hdiv_nonneg hlll
        _ = piScale (max X B + 1) := by
              simp [piScale, mul_assoc, mul_comm, mul_left_comm]
    exact le_trans h_err hscale_le

/--
Ground-up witness-family transfer at varying finite zero sets.

Input: for each threshold `X`, one can choose `x > X` and a finite critical-line
set `S` with explicit-formula error at scale `√x / log x`.
Output: the same cofinal witness family at Littlewood scale `piScale`.
-/
theorem rh_pi_finite_zero_error_witness_family
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
        |piLiErr x + piMainFromZeros S x| ≤ Real.sqrt x / Real.log x) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
      |piLiErr x + piMainFromZeros S x| ≤ piScale x := by
  have h_event :
      ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ lll x ∧ Real.exp 1 ≤ x := by
    exact lll_eventually_ge_one.and (eventually_ge_atTop (a := Real.exp 1))
  rcases Filter.eventually_atTop.1 h_event with ⟨B, hB⟩
  intro X
  obtain ⟨x, hxMax, S, hS, h_err⟩ := h_witness (max X B)
  have hxX : X < x := lt_of_le_of_lt (le_max_left X B) hxMax
  have hxB : B < x := lt_of_le_of_lt (le_max_right X B) hxMax
  have hB_at_x : (1 : ℝ) ≤ lll x ∧ Real.exp 1 ≤ x := hB x (le_of_lt hxB)
  obtain ⟨hlll, hexp1⟩ := hB_at_x
  have h_exp1_gt_one : (1 : ℝ) < Real.exp 1 := by
    simpa using (Real.one_lt_exp_iff.mpr zero_lt_one)
  have hx_gt_one : (1 : ℝ) < x := lt_of_lt_of_le h_exp1_gt_one hexp1
  have hlog_pos : 0 < Real.log x := Real.log_pos hx_gt_one
  have hdiv_nonneg : 0 ≤ Real.sqrt x / Real.log x :=
    div_nonneg (Real.sqrt_nonneg _) (le_of_lt hlog_pos)
  have hscale_le : Real.sqrt x / Real.log x ≤ piScale x := by
    calc
      Real.sqrt x / Real.log x
          ≤ (Real.sqrt x / Real.log x) * lll x := le_mul_of_one_le_right hdiv_nonneg hlll
      _ = piScale x := by
            simp [piScale, mul_assoc, mul_comm, mul_left_comm]
  exact ⟨x, hxX, S, hS, le_trans h_err hscale_le⟩

/-- Alias matching the RH π explicit-formula witness-family target shape. -/
theorem rh_pi_explicit_formula_witness_family
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
        |piLiErr x + piMainFromZeros S x| ≤ Real.sqrt x / Real.log x) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
      |piLiErr x + piMainFromZeros S x| ≤ piScale x :=
  rh_pi_finite_zero_error_witness_family h_witness

/--
Anti-alignment upper bound for the finite-zero main term.

If all phases satisfy `x^{iγ_ρ} ≈ -1` and the coefficient domination
`2*lll x ≤ Σ Re(1/ρ) - ε Σ 1/|ρ|` holds, then
`piMainFromZeros S x ≤ -(4 * piScale x)`.
-/
theorem piMain_from_antialignment_upper_four
    (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ.re = 1 / 2)
    {x : ℝ} (hx : 1 < x)
    {ε : ℝ} (_hε : 0 < ε)
    (h_phases_neg : ∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) + 1‖ < ε)
    (h_coeff2 : 2 * lll x ≤
      (∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    piMainFromZeros S x ≤ -(4 * piScale x) := by
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  have hlog_pos : 0 < Real.log x := Real.log_pos hx
  have h_re_expr (ρ : ℂ) (hρ : ρ ∈ S) :
      Complex.re ((x : ℂ) ^ ρ / ρ)
        = Real.sqrt x * Complex.re ((x : ℂ) ^ (Complex.I * ρ.im) / ρ) := by
    rw [show ρ = 1 / 2 + Complex.I * ρ.im by
      simp [Complex.ext_iff, hS ρ hρ]]
    norm_num [Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im,
      Complex.cpow_def_of_ne_zero, hx_pos.ne']
    ring
    norm_num [Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx_pos]
    ring
    norm_num [Complex.arg_ofReal_of_nonneg hx_pos.le, Real.sin_add, Real.cos_add,
      mul_assoc, ← Real.exp_add]
    ring
  have h_term (ρ : ℂ) (hρ : ρ ∈ S) :
      Complex.re ((x : ℂ) ^ (Complex.I * ρ.im) / ρ)
        ≤ -(1 / ρ).re + ε / ‖ρ‖ := by
    have hρ_ne : ρ ≠ 0 := by
      intro h0
      have : (0 : ℝ) = 1 / 2 := by simpa [h0] using hS ρ hρ
      norm_num at this
    have hρ_norm_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ_ne
    have h_re_plus_le :
        Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) + 1) / ρ) ≤ ε / ‖ρ‖ := by
      have hnorm_le :
          ‖((x : ℂ) ^ (Complex.I * ρ.im) + 1) / ρ‖ ≤ ε / ‖ρ‖ := by
        have hnorm_lt :
            ‖((x : ℂ) ^ (Complex.I * ρ.im) + 1) / ρ‖ < ε / ‖ρ‖ := by
          have hdiv : ‖(x : ℂ) ^ (Complex.I * ρ.im) + 1‖ / ‖ρ‖ < ε / ‖ρ‖ :=
            div_lt_div_of_pos_right (h_phases_neg ρ hρ) hρ_norm_pos
          simpa [norm_div] using hdiv
        exact le_of_lt hnorm_lt
      have h_re_le_abs :
          Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) + 1) / ρ)
            ≤ |Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) + 1) / ρ)| :=
        le_abs_self _
      have h_abs_le_norm :
          |Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) + 1) / ρ)|
            ≤ ‖((x : ℂ) ^ (Complex.I * ρ.im) + 1) / ρ‖ :=
        Complex.abs_re_le_norm _
      exact le_trans (le_trans h_re_le_abs h_abs_le_norm) hnorm_le
    have h_decomp :
        Complex.re ((x : ℂ) ^ (Complex.I * ρ.im) / ρ)
          = Complex.re (((x : ℂ) ^ (Complex.I * ρ.im) + 1) / ρ) - (1 / ρ).re := by
      have h_eq :
          ((x : ℂ) ^ (Complex.I * ρ.im) / ρ)
            = (((x : ℂ) ^ (Complex.I * ρ.im) + 1) / ρ) - (1 / ρ) := by
        ring
      rw [h_eq, Complex.sub_re]
    nlinarith [h_re_plus_le, h_decomp]
  have hsum_u :
      (∑ ρ ∈ S, Complex.re ((x : ℂ) ^ (Complex.I * ρ.im) / ρ))
        ≤ (∑ ρ ∈ S, (-(1 / ρ).re + ε / ‖ρ‖)) := by
    exact Finset.sum_le_sum (fun ρ hρ => h_term ρ hρ)
  have hsum_repr :
      (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)
        = Real.sqrt x *
          (∑ ρ ∈ S, Complex.re ((x : ℂ) ^ (Complex.I * ρ.im) / ρ)) := by
    calc
      (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)
          = ∑ ρ ∈ S,
              (Real.sqrt x * Complex.re ((x : ℂ) ^ (Complex.I * ρ.im) / ρ)) := by
            refine Finset.sum_congr rfl (fun ρ hρ => ?_)
            simpa using h_re_expr ρ hρ
      _ = Real.sqrt x *
            (∑ ρ ∈ S, Complex.re ((x : ℂ) ^ (Complex.I * ρ.im) / ρ)) := by
            rw [Finset.mul_sum]
  have hsum_upper :
      (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)
        ≤ Real.sqrt x *
            (∑ ρ ∈ S, (-(1 / ρ).re + ε / ‖ρ‖)) := by
    rw [hsum_repr]
    exact mul_le_mul_of_nonneg_left hsum_u (Real.sqrt_nonneg x)
  have hsum_upper' :
      (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)
        ≤ Real.sqrt x *
            (ε * (∑ ρ ∈ S, 1 / ‖ρ‖) - (∑ ρ ∈ S, (1 / ρ).re)) := by
    have hsum_rewrite :
        (∑ ρ ∈ S, (-(1 / ρ).re + ε / ‖ρ‖))
          = ε * (∑ ρ ∈ S, 1 / ‖ρ‖) - (∑ ρ ∈ S, (1 / ρ).re) := by
      calc
        (∑ ρ ∈ S, (-(1 / ρ).re + ε / ‖ρ‖))
            = ∑ ρ ∈ S, (ε * (1 / ‖ρ‖) + (-(1 / ρ).re)) := by
                refine Finset.sum_congr rfl (fun ρ hρ => ?_)
                ring
        _ = (∑ ρ ∈ S, ε * (1 / ‖ρ‖)) + (∑ ρ ∈ S, (-(1 / ρ).re)) := by
              rw [Finset.sum_add_distrib]
        _ = ε * (∑ ρ ∈ S, 1 / ‖ρ‖) - (∑ ρ ∈ S, (1 / ρ).re) := by
              rw [Finset.mul_sum, Finset.sum_neg_distrib, sub_eq_add_neg]
    rw [hsum_rewrite] at hsum_upper
    exact hsum_upper
  have hcoeff_scaled :
      Real.sqrt x *
          (ε * (∑ ρ ∈ S, 1 / ‖ρ‖) - (∑ ρ ∈ S, (1 / ρ).re))
        ≤ Real.sqrt x * (-(2 * lll x)) := by
    have hcoeff_neg :
        ε * (∑ ρ ∈ S, 1 / ‖ρ‖) - (∑ ρ ∈ S, (1 / ρ).re) ≤ -(2 * lll x) := by
      nlinarith [h_coeff2]
    exact mul_le_mul_of_nonneg_left hcoeff_neg (Real.sqrt_nonneg x)
  have hsum_le_two :
      (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)
        ≤ -(Real.sqrt x * (2 * lll x)) := by
    have htmp : (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re) ≤ Real.sqrt x * (-(2 * lll x)) :=
      le_trans hsum_upper' hcoeff_scaled
    nlinarith [htmp]
  unfold piMainFromZeros piScale
  have hmul :
      2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)
        ≤ -(4 * (Real.sqrt x * lll x)) := by
    nlinarith [hsum_le_two]
  have hdiv :
      (2 * (∑ ρ ∈ S, ((x : ℂ) ^ ρ / ρ).re)) / Real.log x
        ≤ (-(4 * (Real.sqrt x * lll x))) / Real.log x :=
    div_le_div_of_nonneg_right hmul (le_of_lt hlog_pos)
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
Ground-up transfer to the RH negative-main witness family.

Analytic input (deep): for each threshold `X`, one has a pointwise anti-aligned
finite-zero witness with coefficient domination. Deterministic output: the exact
cofinal negative-main family used in the RH `π-li` payload.
-/
theorem rh_pi_negative_main_witness_family_from_antialignment_coeff
    (ε : ℝ) (hε : 0 < ε)
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
        1 < x ∧
        (∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) + 1‖ < ε) ∧
        2 * lll x ≤
          (∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
      piMainFromZeros S x ≤ -(4 * piScale x) := by
  intro X
  obtain ⟨x, hxX, S, hS, hx1, hanti, hcoeff2⟩ := h_witness X
  have hSre : ∀ ρ ∈ S, ρ.re = 1 / 2 := fun ρ hρ => (hS ρ hρ).2
  have hmain : piMainFromZeros S x ≤ -(4 * piScale x) :=
    piMain_from_antialignment_upper_four S hSre hx1 hε hanti hcoeff2
  exact ⟨x, hxX, S, hS, hmain⟩

/-- Alias matching the RH π anti-alignment negative-main witness-family target shape. -/
theorem rh_pi_negative_main_family
    (ε : ℝ) (hε : 0 < ε)
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
        1 < x ∧
        (∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) + 1‖ < ε) ∧
        2 * lll x ≤
          (∑ ρ ∈ S, (1 / ρ).re) - ε * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
      piMainFromZeros S x ≤ -(4 * piScale x) :=
  rh_pi_negative_main_witness_family_from_antialignment_coeff ε hε h_witness

end Aristotle.Standalone.RHPiFiniteZeroWitnessFamilies
