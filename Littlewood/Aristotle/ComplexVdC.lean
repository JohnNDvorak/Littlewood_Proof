/-
Complex Van der Corput first derivative test via angular velocity.

For a C¹ function F : ℝ → ℂ satisfying F'(t) = i·ω(t)·F(t) with ‖F‖ ≤ 1,
if ω ≥ m > 0 and ω is C¹ with ω' ≥ 0 on [a,b], then ‖∫_a^b F(t) dt‖ ≤ 3/m.

This avoids needing the phase function to be globally defined or differentiable —
only the unit-norm oscillatory function F needs to be smooth.

## Main results

- `complex_vdc_angular`: ‖∫_a^b F dt‖ ≤ 3/m for F with F' = iω·F, ‖F‖ ≤ 1

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.ComplexVdC

open MeasureTheory Set Real Filter Topology intervalIntegral Complex

/-! ### FTC infrastructure for ∫ ω'/ω² -/

/-- FTC for -1/ω: ∫_a^b ω'/ω² = 1/ω(a) - 1/ω(b). -/
private lemma ftc_inv_omega (ω : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hω_diff : Differentiable ℝ ω) (hω_cont' : Continuous (deriv ω))
    (hω_pos : ∀ t ∈ Icc a b, 0 < ω t) :
    ∫ t in a..b, deriv ω t / (ω t) ^ 2 = 1 / ω a - 1 / ω b := by
  have hω_ne : ∀ t ∈ Icc a b, ω t ≠ 0 :=
    fun t ht => ne_of_gt (hω_pos t ht)
  have h_deriv : ∀ t ∈ uIcc a b, HasDerivAt (fun t => -(ω t)⁻¹)
      (deriv ω t / (ω t) ^ 2) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    convert ((hω_diff t).hasDerivAt.inv (hω_ne t ht)).neg using 1; ring
  have h_int : IntervalIntegrable (fun t => deriv ω t / (ω t) ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    apply ContinuousOn.div hω_cont'.continuousOn
      ((hω_diff.continuous.pow 2).continuousOn)
    intro t ht; exact pow_ne_zero 2 (hω_ne t ht)
  have hFTC := integral_eq_sub_of_hasDerivAt h_deriv h_int
  simp only [neg_sub_neg] at hFTC
  rw [hFTC]; simp [one_div]

/-- ∫ ω'/ω² ≤ 1/m when ω ≥ m > 0. -/
private lemma correction_le (ω : ℝ → ℝ) (a b m : ℝ) (hab : a ≤ b) (hm : 0 < m)
    (hω_diff : Differentiable ℝ ω) (hω_cont' : Continuous (deriv ω))
    (hω_lower : ∀ t ∈ Icc a b, m ≤ ω t) :
    ∫ t in a..b, deriv ω t / (ω t) ^ 2 ≤ 1 / m := by
  have hω_pos : ∀ t ∈ Icc a b, 0 < ω t :=
    fun t ht => lt_of_lt_of_le hm (hω_lower t ht)
  rw [ftc_inv_omega ω a b hab hω_diff hω_cont' hω_pos]
  have hb_pos : 0 < ω b := hω_pos b (right_mem_Icc.mpr hab)
  linarith [one_div_le_one_div_of_le hm (hω_lower a (left_mem_Icc.mpr hab)),
            div_pos one_pos hb_pos]

/-! ### Main theorem -/

/-- **Complex Van der Corput bound (angular velocity form)**:
    If F : ℝ → ℂ is differentiable with F'(t) = i·ω(t)·F(t),
    ‖F(t)‖ ≤ 1, ω ≥ m > 0, and ω is C¹ with ω' ≥ 0 on [a,b],
    then ‖∫_a^b F(t) dt‖ ≤ 3/m.

    Proof: IBP on G(t) = F(t)/(iω(t)).
    G'(t) = F(t) + F(t)·i·ω'(t)/ω(t)²
    So ∫ F = G(b) - G(a) - ∫ F·i·ω'/ω²
    Boundary terms: ‖G‖ = ‖F‖/ω ≤ 1/m each → 2/m total
    Correction: ‖∫ F·i·ω'/ω²‖ ≤ ∫ ω'/ω² ≤ 1/m -/
theorem complex_vdc_angular (F : ℝ → ℂ) (ω : ℝ → ℝ) (a b m : ℝ)
    (hab : a ≤ b) (hm : 0 < m)
    (hF_deriv : ∀ t ∈ Icc a b, HasDerivAt F (Complex.I * ↑(ω t) * F t) t)
    (hF_norm : ∀ t ∈ Icc a b, ‖F t‖ ≤ 1)
    (hω_diff : Differentiable ℝ ω)
    (hω_cont' : Continuous (deriv ω))
    (hω_lower : ∀ t ∈ Icc a b, m ≤ ω t)
    (hω'_nonneg : ∀ t ∈ Icc a b, 0 ≤ deriv ω t) :
    ‖∫ t in a..b, F t‖ ≤ 3 / m := by
  -- Setup
  have hω_pos : ∀ t ∈ Icc a b, 0 < ω t :=
    fun t ht => lt_of_lt_of_le hm (hω_lower t ht)
  have hω_ne : ∀ t ∈ Icc a b, (ω t : ℂ) ≠ 0 :=
    fun t ht => ofReal_ne_zero.mpr (ne_of_gt (hω_pos t ht))
  have hF_cont : ContinuousOn F (Icc a b) :=
    fun t ht => (hF_deriv t ht).continuousAt.continuousWithinAt
  have hω_cont : Continuous ω := hω_diff.continuous
  have hiω_ne : ∀ t ∈ Icc a b, (Complex.I * (ω t : ℂ)) ≠ 0 :=
    fun t ht => mul_ne_zero Complex.I_ne_zero (hω_ne t ht)
  -- Define G(t) = F(t) / (I * ω(t)) and the correction term
  let G : ℝ → ℂ := fun t => F t / (Complex.I * ↑(ω t))
  let corr : ℝ → ℂ := fun t => F t * Complex.I * ↑(deriv ω t) / ↑(ω t) ^ 2
  -- HasDerivAt for ofReal ∘ ω
  have h_ofReal_ω : ∀ t, HasDerivAt (fun t => (ω t : ℂ)) (↑(deriv ω t)) t := by
    intro t
    have h1 := (hω_diff t).hasDerivAt
    exact h1.ofReal_comp
  -- G has derivative G'(t) = F(t) + corr(t) on [a,b]
  have hG_deriv : ∀ t ∈ uIcc a b, HasDerivAt G (F t + corr t) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have hωt_ne := hω_ne t ht
    have hiωt_ne := hiω_ne t ht
    -- HasDerivAt for I * ω(t)
    have h_iω_deriv : HasDerivAt (fun t => Complex.I * ↑(ω t))
        (Complex.I * ↑(deriv ω t)) t :=
      (h_ofReal_ω t).const_mul Complex.I
    -- HasDerivAt for G via quotient rule
    have hG_quot : HasDerivAt G
        ((Complex.I * ↑(ω t) * F t * (Complex.I * ↑(ω t)) -
          F t * (Complex.I * ↑(deriv ω t))) /
          (Complex.I * ↑(ω t)) ^ 2) t :=
      (hF_deriv t ht).div h_iω_deriv hiωt_ne
    -- Simplify the derivative expression
    refine hG_quot.congr_deriv ?_
    have hωt_c : (ω t : ℂ) ≠ 0 := hωt_ne
    show _ = F t + F t * Complex.I * ↑(deriv ω t) / ↑(ω t) ^ 2
    field_simp
    -- Goal: F t * (I * ↑(ω t) ^ 2 - ↑(deriv ω t)) = I * F t * (↑(ω t) ^ 2 + I * ↑(deriv ω t))
    ring_nf
    simp [I_sq]
    ring
  -- Integrability of F
  have hF_int : IntervalIntegrable F volume a b :=
    hF_cont.intervalIntegrable_of_Icc hab
  -- Continuity of corr on [a,b]
  have hcorr_cont : ContinuousOn corr (Icc a b) := by
    show ContinuousOn (fun t => F t * Complex.I * ↑(deriv ω t) / ↑(ω t) ^ 2) (Icc a b)
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · exact hF_cont.mul continuousOn_const
      · exact (continuous_ofReal.comp hω_cont').continuousOn
    · exact ((continuous_ofReal.comp hω_cont).continuousOn.pow 2)
    · intro t ht
      exact pow_ne_zero 2 (ofReal_ne_zero.mpr (ne_of_gt (hω_pos t ht)))
  -- Integrability of corr
  have hcorr_int : IntervalIntegrable corr volume a b :=
    hcorr_cont.intervalIntegrable_of_Icc hab
  -- Integrability of G'
  have hGderiv_int : IntervalIntegrable (fun t => F t + corr t) volume a b :=
    hF_int.add hcorr_int
  -- FTC: ∫ G' = G(b) - G(a)
  have hFTC : ∫ t in a..b, (F t + corr t) = G b - G a :=
    integral_eq_sub_of_hasDerivAt hG_deriv hGderiv_int
  -- Therefore: ∫ F = G(b) - G(a) - ∫ corr
  have h_split : ∫ t in a..b, F t = G b - G a - ∫ t in a..b, corr t := by
    have h_add := intervalIntegral.integral_add hF_int hcorr_int
    -- h_add : ∫ (F + corr) = ∫ F + ∫ corr
    -- hFTC : ∫ (F + corr) = G b - G a
    have : (∫ x in a..b, F x) + ∫ x in a..b, corr x = G b - G a := by
      rw [← h_add]; exact hFTC
    linear_combination this
  -- Now bound ‖∫ F‖ ≤ ‖G(b)‖ + ‖G(a)‖ + ‖∫ corr‖ ≤ 1/m + 1/m + 1/m
  rw [h_split]
  -- Helper for ‖G(t)‖ ≤ 1/m
  have hG_norm : ∀ t ∈ Icc a b, ‖G t‖ ≤ 1 / m := by
    intro t ht
    show ‖F t / (Complex.I * ↑(ω t))‖ ≤ 1 / m
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (hω_pos t ht)]
    calc ‖F t‖ / ω t ≤ 1 / ω t :=
          div_le_div_of_nonneg_right (hF_norm t ht) (le_of_lt (hω_pos t ht))
      _ ≤ 1 / m := by
          apply div_le_div_of_nonneg_left zero_le_one hm (hω_lower t ht)
  -- Triangle inequality + bounds
  calc ‖G b - G a - ∫ t in a..b, corr t‖
      ≤ ‖G b - G a‖ + ‖∫ t in a..b, corr t‖ := norm_sub_le _ _
    _ ≤ (‖G b‖ + ‖G a‖) + ‖∫ t in a..b, corr t‖ := by
        linarith [norm_sub_le (G b) (G a)]
    _ ≤ (1 / m + 1 / m) + 1 / m := by
        have hGb := hG_norm b (right_mem_Icc.mpr hab)
        have hGa := hG_norm a (left_mem_Icc.mpr hab)
        -- Bound ‖∫ corr‖ ≤ ∫ ‖corr‖ ≤ ∫ ω'/ω² ≤ 1/m
        have hcorr_bound : ‖∫ t in a..b, corr t‖ ≤ 1 / m := by
          -- ‖∫ corr‖ ≤ ∫ ‖corr‖
          have h1 : ‖∫ t in a..b, corr t‖ ≤ ∫ t in a..b, ‖corr t‖ :=
            norm_integral_le_integral_norm hab
          -- ‖corr t‖ ≤ ω'/ω² pointwise on [a,b]
          have h_pw : ∀ t ∈ Icc a b,
              ‖corr t‖ ≤ deriv ω t / (ω t) ^ 2 := by
            intro t ht
            show ‖F t * Complex.I * ↑(deriv ω t) / ↑(ω t) ^ 2‖ ≤ _
            have hωt_pos := hω_pos t ht
            have hω't_nn := hω'_nonneg t ht
            have h_num : ‖F t * Complex.I * ↑(deriv ω t)‖ = ‖F t‖ * deriv ω t := by
              rw [norm_mul, norm_mul, Complex.norm_I, mul_one,
                  Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hω't_nn]
            have h_den : ‖(↑(ω t) : ℂ) ^ 2‖ = (ω t) ^ 2 := by
              rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hωt_pos]
            rw [norm_div, h_num, h_den]
            apply div_le_div_of_nonneg_right _ (pow_pos hωt_pos 2).le
            exact mul_le_of_le_one_left hω't_nn (hF_norm t ht)
          -- ∫ ‖corr‖ ≤ ∫ ω'/ω²
          have h_norm_int : IntervalIntegrable (fun t => ‖corr t‖) volume a b :=
            hcorr_int.norm
          have h_omegaquot_int : IntervalIntegrable
              (fun t => deriv ω t / (ω t) ^ 2) volume a b := by
            apply ContinuousOn.intervalIntegrable_of_Icc hab
            apply ContinuousOn.div hω_cont'.continuousOn
              ((hω_cont.pow 2).continuousOn)
            intro t ht; exact pow_ne_zero 2 (ne_of_gt (hω_pos t ht))
          have h2 : ∫ t in a..b, ‖corr t‖ ≤
              ∫ t in a..b, deriv ω t / (ω t) ^ 2 := by
            apply integral_mono_on hab h_norm_int h_omegaquot_int
            intro t ht
            exact h_pw t ht
          have h3 := correction_le ω a b m hab hm hω_diff hω_cont' hω_lower
          linarith
        linarith
    _ = 3 / m := by ring

/-- Corollary: the real-part integral also satisfies the 3/m bound.
    Uses |∫ Re(F)| = |Re(∫ F)| ≤ ‖∫ F‖ ≤ 3/m. -/
theorem complex_vdc_angular_re (F : ℝ → ℂ) (ω : ℝ → ℝ) (a b m : ℝ)
    (hab : a ≤ b) (hm : 0 < m)
    (hF_deriv : ∀ t ∈ Icc a b, HasDerivAt F (Complex.I * ↑(ω t) * F t) t)
    (hF_norm : ∀ t ∈ Icc a b, ‖F t‖ ≤ 1)
    (hω_diff : Differentiable ℝ ω)
    (hω_cont' : Continuous (deriv ω))
    (hω_lower : ∀ t ∈ Icc a b, m ≤ ω t)
    (hω'_nonneg : ∀ t ∈ Icc a b, 0 ≤ deriv ω t) :
    |∫ t in a..b, (F t).re| ≤ 3 / m := by
  have hF_cont : ContinuousOn F (Icc a b) :=
    fun t ht => (hF_deriv t ht).continuousAt.continuousWithinAt
  have hF_int : IntervalIntegrable F volume a b := hF_cont.intervalIntegrable_of_Icc hab
  -- ∫ Re(F) = Re(∫ F)
  have h_re_comm : ∫ t in a..b, (F t).re = (∫ t in a..b, F t).re := by
    have := Complex.reCLM.intervalIntegral_comp_comm hF_int
    simp only [Complex.reCLM_apply] at this
    exact this
  rw [h_re_comm]
  exact le_trans (abs_re_le_norm _)
    (complex_vdc_angular F ω a b m hab hm hF_deriv hF_norm hω_diff hω_cont' hω_lower hω'_nonneg)

end Aristotle.ComplexVdC
