import Littlewood.Aristotle.Standalone.RHPiTermwiseWitnessBuilders

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiTargetPhaseWitnessBuilders

open Filter Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge
open Aristotle.Standalone.RHPiTermwiseWitnessBuilders

/--
If `u` is within `ε` of the unit direction `ρ / ‖ρ‖`, then
`Re(u / ρ)` is at least `(1-ε)/‖ρ‖`.
-/
lemma re_div_lower_of_close_target
    {u ρ : ℂ} (hρne : ρ ≠ 0)
    {ε : ℝ}
    (hclose : ‖u - ρ / ‖ρ‖‖ ≤ ε) :
    (1 - ε) / ‖ρ‖ ≤ Complex.re (u / ρ) := by
  have hnorm_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
  have hnorm_ne : ‖ρ‖ ≠ 0 := ne_of_gt hnorm_pos
  have hsplit :
      u / ρ = ((ρ / ‖ρ‖) / ρ) + ((u - ρ / ‖ρ‖) / ρ) := by
    ring
  have htarget :
      ((ρ / ‖ρ‖ : ℂ) / ρ) = ((1 / ‖ρ‖ : ℝ) : ℂ) := by
    calc
      ((ρ / ‖ρ‖ : ℂ) / ρ)
          = (ρ * ((‖ρ‖ : ℂ)⁻¹)) * ρ⁻¹ := by
              simp [div_eq_mul_inv, mul_assoc]
      _ = ((‖ρ‖ : ℂ)⁻¹) * (ρ * ρ⁻¹) := by ring
      _ = ((‖ρ‖ : ℂ)⁻¹) := by simp [hρne]
      _ = ((1 / ‖ρ‖ : ℝ) : ℂ) := by simp [one_div]
  have hbound :
      -‖(u - ρ / ‖ρ‖) / ρ‖ ≤ Complex.re ((u - ρ / ‖ρ‖) / ρ) := by
    have h1 : |Complex.re ((u - ρ / ‖ρ‖) / ρ)| ≤ ‖(u - ρ / ‖ρ‖) / ρ‖ :=
      Complex.abs_re_le_norm _
    exact (abs_le.mp h1).1
  have hre_ge :
      Complex.re (u / ρ)
        ≥ Complex.re (((ρ / ‖ρ‖ : ℂ) / ρ)) - ‖(u - ρ / ‖ρ‖) / ρ‖ := by
    rw [hsplit, Complex.add_re]
    nlinarith [hbound]
  have hnorm_div :
      ‖(u - ρ / ‖ρ‖) / ρ‖ = ‖u - ρ / ‖ρ‖‖ / ‖ρ‖ := by
    simpa [norm_div]
  have hdiv :
      ‖u - ρ / ‖ρ‖‖ / ‖ρ‖ ≤ ε / ‖ρ‖ :=
    div_le_div_of_nonneg_right hclose (le_of_lt hnorm_pos)
  have hre_ge' :
      Complex.re (u / ρ) ≥ (1 / ‖ρ‖) - ε / ‖ρ‖ := by
    rw [htarget] at hre_ge
    rw [hnorm_div] at hre_ge
    have hre_target : Complex.re (((1 / ‖ρ‖ : ℝ) : ℂ)) = 1 / ‖ρ‖ := by simp
    nlinarith [hre_ge, hdiv, hre_target]
  have hrewrite : (1 - ε) / ‖ρ‖ = (1 / ‖ρ‖) - ε / ‖ρ‖ := by
    ring
  rw [hrewrite]
  exact hre_ge'

/--
If `u` is within `ε` of the opposite direction `-(ρ / ‖ρ‖)`, then
`Re(u / ρ)` is at most `-(1-ε)/‖ρ‖`.
-/
lemma re_div_upper_of_close_antitarget
    {u ρ : ℂ} (hρne : ρ ≠ 0)
    {ε : ℝ}
    (hclose : ‖u - (-(ρ / ‖ρ‖))‖ ≤ ε) :
    Complex.re (u / ρ) ≤ -((1 - ε) / ‖ρ‖) := by
  have hnorm_pos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
  have hnorm_ne : ‖ρ‖ ≠ 0 := ne_of_gt hnorm_pos
  have hsplit :
      u / ρ = ((-(ρ / ‖ρ‖)) / ρ) + ((u - (-(ρ / ‖ρ‖))) / ρ) := by
    ring
  have htarget0 :
      ((ρ / ‖ρ‖ : ℂ) / ρ) = ((1 / ‖ρ‖ : ℝ) : ℂ) := by
    calc
      ((ρ / ‖ρ‖ : ℂ) / ρ)
          = (ρ * ((‖ρ‖ : ℂ)⁻¹)) * ρ⁻¹ := by
              simp [div_eq_mul_inv, mul_assoc]
      _ = ((‖ρ‖ : ℂ)⁻¹) * (ρ * ρ⁻¹) := by ring
      _ = ((‖ρ‖ : ℂ)⁻¹) := by simp [hρne]
      _ = ((1 / ‖ρ‖ : ℝ) : ℂ) := by simp [one_div]
  have htarget :
      ((-(ρ / ‖ρ‖) : ℂ) / ρ) = ((-(1 / ‖ρ‖ : ℝ)) : ℂ) := by
    calc
      ((-(ρ / ‖ρ‖) : ℂ) / ρ) = -((ρ / ‖ρ‖ : ℂ) / ρ) := by ring
      _ = ((-(1 / ‖ρ‖ : ℝ)) : ℂ) := by simpa [htarget0]
  have hbound :
      Complex.re ((u - (-(ρ / ‖ρ‖))) / ρ) ≤ ‖(u - (-(ρ / ‖ρ‖))) / ρ‖ :=
    Complex.re_le_norm _
  have hre_le :
      Complex.re (u / ρ)
        ≤ Complex.re (((-(ρ / ‖ρ‖) : ℂ) / ρ)) + ‖(u - (-(ρ / ‖ρ‖))) / ρ‖ := by
    rw [hsplit, Complex.add_re]
    nlinarith [hbound]
  have hnorm_div :
      ‖(u - (-(ρ / ‖ρ‖))) / ρ‖ = ‖u - (-(ρ / ‖ρ‖))‖ / ‖ρ‖ := by
    simpa [norm_div]
  have hdiv :
      ‖u - (-(ρ / ‖ρ‖))‖ / ‖ρ‖ ≤ ε / ‖ρ‖ :=
    div_le_div_of_nonneg_right hclose (le_of_lt hnorm_pos)
  have hre_le' :
      Complex.re (u / ρ) ≤ (-(1 / ‖ρ‖)) + ε / ‖ρ‖ := by
    rw [htarget] at hre_le
    rw [hnorm_div] at hre_le
    have hre_target : Complex.re (((-(1 / ‖ρ‖ : ℝ)) : ℂ)) = -(1 / ‖ρ‖) := by simp
    nlinarith [hre_le, hdiv, hre_target]
  have hrewrite : -((1 - ε) / ‖ρ‖) = (-(1 / ‖ρ‖)) + ε / ‖ρ‖ := by
    ring
  rw [hrewrite]
  exact hre_le'

/--
For `ρ.re = 1/2` and `x > 0`, rewrite the explicit-formula term as
`√x * Re(x^{i·Im(ρ)} / ρ)`.
-/
lemma re_cpow_div_of_re_half
    (ρ : ℂ) (hρ : ρ.re = 1 / 2)
    {x : ℝ} (hx : 0 < x) :
    Complex.re ((x : ℂ) ^ ρ / ρ)
      = Real.sqrt x * Complex.re ((x : ℂ) ^ (Complex.I * ρ.im) / ρ) := by
  rw [show ρ = 1 / 2 + Complex.I * ρ.im by
    simp [Complex.ext_iff, hρ]]
  norm_num [Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im,
    Complex.cpow_def_of_ne_zero, hx.ne']
  ring
  norm_num [Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im,
    Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  ring
  norm_num [Complex.arg_ofReal_of_nonneg hx.le, Real.sin_add, Real.cos_add,
    mul_assoc, ← Real.exp_add]
  ring

/--
Pointwise lower termwise bound from phase-target closeness.
-/
lemma termwise_lower_of_phase_target
    {x : ℝ} (hx : 0 < x)
    {ρ : ℂ} (hρre : ρ.re = 1 / 2)
    {ε : ℝ}
    (hphase : ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) :
    Real.sqrt x * ((1 - ε) / ‖ρ‖) ≤ ((x : ℂ) ^ ρ / ρ).re := by
  have hρne : ρ ≠ 0 := by
    intro h0
    have : (0 : ℝ) = 1 / 2 := by simpa [h0] using hρre
    norm_num at this
  have hre_phase :
      (1 - ε) / ‖ρ‖ ≤ Complex.re (((x : ℂ) ^ (Complex.I * ρ.im)) / ρ) :=
    re_div_lower_of_close_target hρne hphase
  have hscaled :
      Real.sqrt x * ((1 - ε) / ‖ρ‖)
        ≤ Real.sqrt x * Complex.re (((x : ℂ) ^ (Complex.I * ρ.im)) / ρ) :=
    mul_le_mul_of_nonneg_left hre_phase (Real.sqrt_nonneg x)
  calc
    Real.sqrt x * ((1 - ε) / ‖ρ‖)
        ≤ Real.sqrt x * Complex.re (((x : ℂ) ^ (Complex.I * ρ.im)) / ρ) := hscaled
    _ = ((x : ℂ) ^ ρ / ρ).re := by
          symm
          exact re_cpow_div_of_re_half ρ hρre hx

/--
Pointwise upper termwise bound from anti-target phase closeness.
-/
lemma termwise_upper_of_phase_antitarget
    {x : ℝ} (hx : 0 < x)
    {ρ : ℂ} (hρre : ρ.re = 1 / 2)
    {ε : ℝ}
    (hphase : ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) :
    ((x : ℂ) ^ ρ / ρ).re ≤ -(Real.sqrt x * ((1 - ε) / ‖ρ‖)) := by
  have hρne : ρ ≠ 0 := by
    intro h0
    have : (0 : ℝ) = 1 / 2 := by simpa [h0] using hρre
    norm_num at this
  have hre_phase :
      Complex.re (((x : ℂ) ^ (Complex.I * ρ.im)) / ρ) ≤ -((1 - ε) / ‖ρ‖) :=
    re_div_upper_of_close_antitarget hρne hphase
  have hscaled :
      Real.sqrt x * Complex.re (((x : ℂ) ^ (Complex.I * ρ.im)) / ρ)
        ≤ Real.sqrt x * (-((1 - ε) / ‖ρ‖)) :=
    mul_le_mul_of_nonneg_left hre_phase (Real.sqrt_nonneg x)
  have hscaled' :
      Real.sqrt x * Complex.re (((x : ℂ) ^ (Complex.I * ρ.im)) / ρ)
        ≤ -(Real.sqrt x * ((1 - ε) / ‖ρ‖)) := by
    simpa [neg_mul] using hscaled
  calc
    ((x : ℂ) ^ ρ / ρ).re
        = Real.sqrt x * Complex.re (((x : ℂ) ^ (Complex.I * ρ.im)) / ρ) :=
          re_cpow_div_of_re_half ρ hρre hx
    _ ≤ -(Real.sqrt x * ((1 - ε) / ‖ρ‖)) := hscaled'

/--
Deterministic main-term lower bound from target-phase control.
-/
theorem piMain_from_target_phase_lower_four
    (S : Finset ℂ)
    {x : ℝ} (hx : 1 < x)
    {ε : ℝ}
    (hSre : ∀ ρ ∈ S, ρ.re = 1 / 2)
    (hphase : ∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε)
    (hcoeff : 2 * lll x ≤ (1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    4 * piScale x ≤ piMainFromZeros S x := by
  have hterm :
      ∀ ρ ∈ S,
        Real.sqrt x * ((1 - ε) / ‖ρ‖)
          ≤ ((x : ℂ) ^ ρ / ρ).re := by
    intro ρ hρ
    exact termwise_lower_of_phase_target (lt_trans zero_lt_one hx)
      (hSre ρ hρ) (hphase ρ hρ)
  exact piMain_from_termwise_lower_four S hx hterm hcoeff

/--
Deterministic main-term upper bound from anti-target phase control.
-/
theorem piMain_from_target_phase_upper_four
    (S : Finset ℂ)
    {x : ℝ} (hx : 1 < x)
    {ε : ℝ}
    (hSre : ∀ ρ ∈ S, ρ.re = 1 / 2)
    (hphase : ∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε)
    (hcoeff : 2 * lll x ≤ (1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖)) :
    piMainFromZeros S x ≤ -(4 * piScale x) := by
  have hterm :
      ∀ ρ ∈ S,
        ((x : ℂ) ^ ρ / ρ).re
          ≤ -(Real.sqrt x * ((1 - ε) / ‖ρ‖)) := by
    intro ρ hρ
    exact termwise_upper_of_phase_antitarget (lt_trans zero_lt_one hx)
      (hSre ρ hρ) (hphase ρ hρ)
  exact piMain_from_termwise_upper_four S hx hterm hcoeff

/--
Build the positive RH pointwise witness family from phase-target control.
-/
theorem rh_pi_positive_main_witness_family_from_phase_target
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) ∧
          2 * lll x ≤ (1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
      |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
      4 * piScale x ≤ piMainFromZeros S x := by
  intro X
  obtain ⟨x, hxX, S, hS, hx1, herr, ε, hεpos, _hεlt1, hphase, hcoeff⟩ := h_witness X
  have hSre : ∀ ρ ∈ S, ρ.re = 1 / 2 := fun ρ hρ => (hS ρ hρ).2
  have hmain : 4 * piScale x ≤ piMainFromZeros S x :=
    piMain_from_target_phase_lower_four S hx1 hSre hphase hcoeff
  exact ⟨x, hxX, S, hS, herr, hmain⟩

/--
Build the negative RH pointwise witness family from anti-target phase control.
-/
theorem rh_pi_negative_main_witness_family_from_phase_target
    (h_witness :
      ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
        (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
        1 < x ∧
        |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
        (∃ ε : ℝ,
          0 < ε ∧ ε < 1 ∧
          (∀ ρ ∈ S, ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) ∧
          2 * lll x ≤ (1 - ε) * (∑ ρ ∈ S, 1 / ‖ρ‖))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ S : Finset ℂ,
      (∀ ρ ∈ S, ρ ∈ zetaNontrivialZeros ∧ ρ.re = 1 / 2) ∧
      |piLiErr x + piMainFromZeros S x| ≤ piScale x ∧
      piMainFromZeros S x ≤ -(4 * piScale x) := by
  intro X
  obtain ⟨x, hxX, S, hS, hx1, herr, ε, hεpos, _hεlt1, hphase, hcoeff⟩ := h_witness X
  have hSre : ∀ ρ ∈ S, ρ.re = 1 / 2 := fun ρ hρ => (hS ρ hρ).2
  have hmain : piMainFromZeros S x ≤ -(4 * piScale x) :=
    piMain_from_target_phase_upper_four S hx1 hSre hphase hcoeff
  exact ⟨x, hxX, S, hS, herr, hmain⟩

end Aristotle.Standalone.RHPiTargetPhaseWitnessBuilders
