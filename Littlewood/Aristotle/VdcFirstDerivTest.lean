/-
Van der Corput first derivative test for oscillatory integrals.

KEY RESULT:
  vdc_cos_bound: If phi is C² with phi' ≥ m > 0 and phi'' ≥ 0 on [a,b], then
    |∫_a^b cos(phi(t)) dt| ≤ 3/m

This is the fundamental oscillatory integral bound needed for the Hardy
first moment analysis. The proof uses integration by parts on sin(phi)/phi'.

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

namespace VdcFirstDerivTest

open MeasureTheory Set Real Filter Topology intervalIntegral

/-- Derivative of sin(phi(t))/phi'(t). -/
private lemma hasDerivAt_sin_div_deriv (phi : ℝ → ℝ) (t : ℝ)
    (hphi : Differentiable ℝ phi) (hphi' : Differentiable ℝ (deriv phi))
    (hne : deriv phi t ≠ 0) :
    HasDerivAt (fun t => Real.sin (phi t) / deriv phi t)
      (Real.cos (phi t) - Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2) t := by
  have h1 : HasDerivAt (fun t => Real.sin (phi t)) (Real.cos (phi t) * deriv phi t) t :=
    (Real.hasDerivAt_sin (phi t)).comp t (hphi t).hasDerivAt
  have h2 : HasDerivAt (deriv phi) (deriv (deriv phi) t) t := (hphi' t).hasDerivAt
  have h3 := h1.div h2 hne
  convert h3 using 1
  field_simp

/-- Continuity of deriv(deriv phi)/(deriv phi)^2 on [a,b]. -/
private lemma continuousOn_corr (phi : ℝ → ℝ) (a b : ℝ)
    (hphi' : Differentiable ℝ (deriv phi))
    (hphi'' : Continuous (deriv (deriv phi)))
    (hne : ∀ t ∈ Icc a b, deriv phi t ≠ 0) :
    ContinuousOn (fun t => deriv (deriv phi) t / (deriv phi t) ^ 2) (Icc a b) := by
  apply ContinuousOn.div hphi''.continuousOn
    ((continuous_pow 2).comp_continuousOn hphi'.continuous.continuousOn)
  intro t ht; exact pow_ne_zero 2 (hne t ht)

/-- Key IBP identity: ∫ cos(phi) = sin(phi(b))/phi'(b) - sin(phi(a))/phi'(a)
    + ∫ sin(phi)·phi''/(phi')². -/
theorem ibp_cos_identity (phi : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b)
    (hphi : Differentiable ℝ phi) (hphi' : Differentiable ℝ (deriv phi))
    (hphi'' : Continuous (deriv (deriv phi)))
    (hne : ∀ t ∈ Icc a b, deriv phi t ≠ 0) :
    ∫ t in a..b, Real.cos (phi t) =
      Real.sin (phi b) / deriv phi b - Real.sin (phi a) / deriv phi a +
      ∫ t in a..b, Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2 := by
  have h_cont_deriv : ContinuousOn
      (fun t => Real.cos (phi t) - Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2)
      (Icc a b) := by
    apply ContinuousOn.sub
    · exact (continuous_cos.comp hphi.continuous).continuousOn
    · apply ContinuousOn.div
      · exact (continuous_sin.comp hphi.continuous).continuousOn.mul hphi''.continuousOn
      · exact (continuous_pow 2).comp_continuousOn hphi'.continuous.continuousOn
      · intro t ht; exact pow_ne_zero 2 (hne t ht)
  have h_int : IntervalIntegrable
      (fun t => Real.cos (phi t) - Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2)
      volume a b := h_cont_deriv.intervalIntegrable_of_Icc hab
  have h_ftc := integral_eq_sub_of_hasDerivAt
    (f := fun t => Real.sin (phi t) / deriv phi t)
    (f' := fun t => Real.cos (phi t) - Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2)
    (a := a) (b := b)
    (fun t ht => by
      rw [Set.uIcc_of_le hab] at ht
      exact hasDerivAt_sin_div_deriv phi t hphi hphi' (hne t ht))
    h_int
  -- Split integral of difference
  have h_int_cos : IntervalIntegrable (fun t => Real.cos (phi t)) volume a b :=
    (continuous_cos.comp hphi.continuous).intervalIntegrable a b
  have h_int_corr : IntervalIntegrable
      (fun t => Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    apply ContinuousOn.div
    · exact (continuous_sin.comp hphi.continuous).continuousOn.mul hphi''.continuousOn
    · exact (continuous_pow 2).comp_continuousOn hphi'.continuous.continuousOn
    · intro t ht; exact pow_ne_zero 2 (hne t ht)
  have h_split : ∫ t in a..b, (Real.cos (phi t) -
      Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2) =
    (∫ t in a..b, Real.cos (phi t)) -
    (∫ t in a..b, Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2) :=
    integral_sub h_int_cos h_int_corr
  -- h_ftc : ∫ (cos - sin*stuff) = boundary
  -- h_split : ∫ (cos - sin*stuff) = (∫ cos) - (∫ sin*stuff)
  -- Combine: (∫ cos) - (∫ sin*stuff) = boundary, hence ∫ cos = boundary + ∫ sin*stuff
  have key := h_split.symm.trans h_ftc
  dsimp at key
  exact sub_eq_iff_eq_add.mp key

/-- Correction integral via FTC:
    ∫ phi''/(phi')² = 1/phi'(a) - 1/phi'(b). -/
theorem correction_integral_bound (phi : ℝ → ℝ) (a b m : ℝ)
    (hab : a ≤ b) (hm : 0 < m)
    (hphi' : Differentiable ℝ (deriv phi))
    (hphi'' : Continuous (deriv (deriv phi)))
    (hphi'_lower : ∀ t ∈ Icc a b, m ≤ deriv phi t) :
    ∫ t in a..b, deriv (deriv phi) t / (deriv phi t) ^ 2 =
      1 / deriv phi a - 1 / deriv phi b := by
  have hne : ∀ t ∈ Icc a b, deriv phi t ≠ 0 := by
    intro t ht; exact ne_of_gt (lt_of_lt_of_le hm (hphi'_lower t ht))
  have h_deriv : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t => -(deriv phi t)⁻¹)
      (deriv (deriv phi) t / (deriv phi t) ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have h := ((hphi' t).hasDerivAt).inv (hne t ht)
    convert h.neg using 1; ring
  have h_int : IntervalIntegrable
      (fun t => deriv (deriv phi) t / (deriv phi t) ^ 2) volume a b := by
    exact (continuousOn_corr phi a b hphi' hphi'' hne).intervalIntegrable_of_Icc hab
  have h_ftc := integral_eq_sub_of_hasDerivAt h_deriv h_int
  simp only [neg_sub_neg] at h_ftc
  rw [h_ftc]; simp [one_div]

/-- The correction integral is bounded by 1/m. -/
theorem correction_integral_le (phi : ℝ → ℝ) (a b m : ℝ)
    (hab : a ≤ b) (hm : 0 < m)
    (hphi' : Differentiable ℝ (deriv phi))
    (hphi'' : Continuous (deriv (deriv phi)))
    (hphi'_lower : ∀ t ∈ Icc a b, m ≤ deriv phi t) :
    ∫ t in a..b, deriv (deriv phi) t / (deriv phi t) ^ 2 ≤ 1 / m := by
  rw [correction_integral_bound phi a b m hab hm hphi' hphi'' hphi'_lower]
  have ha_pos : 0 < deriv phi a :=
    lt_of_lt_of_le hm (hphi'_lower a (left_mem_Icc.mpr hab))
  have hb_pos : 0 < deriv phi b :=
    lt_of_lt_of_le hm (hphi'_lower b (right_mem_Icc.mpr hab))
  have h1 : 0 ≤ 1 / deriv phi b := by positivity
  have h2 : 1 / deriv phi a ≤ 1 / m :=
    one_div_le_one_div_of_le hm (hphi'_lower a (left_mem_Icc.mpr hab))
  linarith

/-- Van der Corput first derivative test: If phi : ℝ → ℝ is C² on [a,b] with
    phi' ≥ m > 0 and phi'' ≥ 0 (i.e., phi' is increasing), then
    |∫_a^b cos(phi(t)) dt| ≤ 3/m. -/
theorem vdc_cos_bound (phi : ℝ → ℝ) (a b m : ℝ) (hab : a ≤ b) (hm : 0 < m)
    (hphi : Differentiable ℝ phi) (hphi' : Differentiable ℝ (deriv phi))
    (hphi'' : Continuous (deriv (deriv phi)))
    (hphi'_lower : ∀ t ∈ Icc a b, m ≤ deriv phi t)
    (hphi''_nonneg : ∀ t ∈ Icc a b, 0 ≤ deriv (deriv phi) t) :
    |∫ t in a..b, Real.cos (phi t)| ≤ 3 / m := by
  have hne : ∀ t ∈ Icc a b, deriv phi t ≠ 0 := by
    intro t ht; exact ne_of_gt (lt_of_lt_of_le hm (hphi'_lower t ht))
  -- Step 1: Apply the IBP identity
  rw [ibp_cos_identity phi a b hab hphi hphi' hphi'' hne]
  -- Step 2: Bound boundary terms by 1/m each
  have hb_bound : |Real.sin (phi b) / deriv phi b| ≤ 1 / m := by
    have hb_pos : 0 < deriv phi b := lt_of_lt_of_le hm (hphi'_lower b (right_mem_Icc.mpr hab))
    rw [abs_div, abs_of_pos hb_pos]
    calc |Real.sin (phi b)| / deriv phi b
        ≤ 1 / deriv phi b :=
          div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (le_of_lt hb_pos)
      _ ≤ 1 / m := one_div_le_one_div_of_le hm (hphi'_lower b (right_mem_Icc.mpr hab))
  have ha_bound : |Real.sin (phi a) / deriv phi a| ≤ 1 / m := by
    have ha_pos : 0 < deriv phi a := lt_of_lt_of_le hm (hphi'_lower a (left_mem_Icc.mpr hab))
    rw [abs_div, abs_of_pos ha_pos]
    calc |Real.sin (phi a)| / deriv phi a
        ≤ 1 / deriv phi a :=
          div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (le_of_lt ha_pos)
      _ ≤ 1 / m := one_div_le_one_div_of_le hm (hphi'_lower a (left_mem_Icc.mpr hab))
  -- Step 3: Bound correction integral by 1/m
  have h_corr_nonneg : ∀ t ∈ Icc a b,
      0 ≤ deriv (deriv phi) t / (deriv phi t) ^ 2 := fun t ht =>
    div_nonneg (hphi''_nonneg t ht) (sq_nonneg _)
  have h_int_corr : IntervalIntegrable
      (fun t => deriv (deriv phi) t / (deriv phi t) ^ 2) volume a b :=
    (continuousOn_corr phi a b hphi' hphi'' hne).intervalIntegrable_of_Icc hab
  have h_int_sin_corr : IntervalIntegrable
      (fun t => Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    apply ContinuousOn.div
    · exact (continuous_sin.comp hphi.continuous).continuousOn.mul hphi''.continuousOn
    · exact (continuous_pow 2).comp_continuousOn hphi'.continuous.continuousOn
    · intro t ht; exact pow_ne_zero 2 (hne t ht)
  -- Upper bound: ∫ sin*g ≤ ∫ g (since sin ≤ 1 and g ≥ 0)
  have h_upper : ∫ t in a..b, Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2
      ≤ ∫ t in a..b, deriv (deriv phi) t / (deriv phi t) ^ 2 := by
    apply integral_mono_on hab h_int_sin_corr h_int_corr
    intro t ht
    calc Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2
        ≤ 1 * deriv (deriv phi) t / (deriv phi t) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_right (Real.sin_le_one _) (hphi''_nonneg t ht)
      _ = deriv (deriv phi) t / (deriv phi t) ^ 2 := by ring
  -- Lower bound: -∫ g ≤ ∫ sin*g (since -1 ≤ sin and g ≥ 0)
  have h_lower : -(∫ t in a..b, deriv (deriv phi) t / (deriv phi t) ^ 2)
      ≤ ∫ t in a..b, Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2 := by
    rw [← intervalIntegral.integral_neg]
    apply integral_mono_on hab h_int_corr.neg h_int_sin_corr
    intro t ht
    calc -(deriv (deriv phi) t / (deriv phi t) ^ 2)
        = (-1) * (deriv (deriv phi) t / (deriv phi t) ^ 2) := by ring
      _ ≤ Real.sin (phi t) * (deriv (deriv phi) t / (deriv phi t) ^ 2) :=
          mul_le_mul_of_nonneg_right (Real.neg_one_le_sin _) (h_corr_nonneg t ht)
      _ = Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2 := by ring
  -- Combine: |∫ sin*g| ≤ ∫ g ≤ 1/m
  have h_corr_bound : |∫ t in a..b,
      Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2| ≤ 1 / m := by
    rw [abs_le]
    exact ⟨by linarith [correction_integral_le phi a b m hab hm hphi' hphi'' hphi'_lower],
           by linarith [correction_integral_le phi a b m hab hm hphi' hphi'' hphi'_lower]⟩
  -- Step 4: Triangle inequality
  have h_sub_bound : |Real.sin (phi b) / deriv phi b - Real.sin (phi a) / deriv phi a|
      ≤ 1 / m + 1 / m := by
    calc |Real.sin (phi b) / deriv phi b - Real.sin (phi a) / deriv phi a|
        = |Real.sin (phi b) / deriv phi b + -(Real.sin (phi a) / deriv phi a)| :=
          by rw [sub_eq_add_neg]
      _ ≤ |Real.sin (phi b) / deriv phi b| + |-(Real.sin (phi a) / deriv phi a)| :=
          abs_add_le _ _
      _ = |Real.sin (phi b) / deriv phi b| + |Real.sin (phi a) / deriv phi a| :=
          by rw [abs_neg]
      _ ≤ 1 / m + 1 / m := by linarith
  calc |Real.sin (phi b) / deriv phi b - Real.sin (phi a) / deriv phi a +
         ∫ t in a..b, Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2|
      ≤ |Real.sin (phi b) / deriv phi b - Real.sin (phi a) / deriv phi a| +
        |∫ t in a..b, Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2| :=
        abs_add_le _ _
    _ ≤ (1 / m + 1 / m) + 1 / m := by linarith
    _ = 3 / m := by ring

end VdcFirstDerivTest
