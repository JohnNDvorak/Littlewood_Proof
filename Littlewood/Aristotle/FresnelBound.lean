/-
Fresnel cosine integral uniform bound.

KEY RESULT:
  fresnel_cos_bounded: |∫_1^X cos(t²) dt| ≤ 3/2 for all X ≥ 1.

PROOF:
  Integration by parts: cos(t²) = d/dt[sin(t²)/(2t)] + sin(t²)/(2t²).
  So ∫_1^X cos(t²) = sin(X²)/(2X) - sin(1)/2 + ∫_1^X sin(t²)/(2t²).
  Each piece is bounded by 1/2, giving total bound 3/2.

  The remainder integral ∫_1^X sin(t²)/(2t²) is bounded by
  ∫_1^X 1/(2t²) = 1/2 - 1/(2X) ≤ 1/2.

APPLICATIONS:
  - Stationary phase analysis in Hardy first moment
  - Van der Corput second-derivative test
  - Riemann-Siegel block amplitude bounds

SORRY COUNT: 0

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace FresnelBound

open MeasureTheory intervalIntegral Set Filter Real

/-! ## Derivative lemmas -/

/-- d/dt[(2t)·1] = 2. Helper for quotient rule. -/
private lemma hasDerivAt_2x (t : ℝ) : HasDerivAt (fun x => 2 * x) 2 t := by
  have := (hasDerivAt_id t).const_mul (2 : ℝ); simp at this; exact this

/-- d/dt[sin(t²)/(2t)] = cos(t²) - sin(t²)/(2t²).
Product/quotient rule applied to sin(t²)/(2t). -/
lemma hasDerivAt_sin_sq_div_2t (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun x => Real.sin (x ^ 2) / (2 * x))
      (Real.cos (t ^ 2) - Real.sin (t ^ 2) / (2 * t ^ 2)) t := by
  have hsin : HasDerivAt (fun x => Real.sin (x ^ 2)) (2 * t * Real.cos (t ^ 2)) t := by
    exact (hasDerivAt_sin _).comp t (by simpa using hasDerivAt_pow 2 t) |>.congr_deriv (by ring)
  exact (hsin.div (hasDerivAt_2x t) (mul_ne_zero two_ne_zero ht)).congr_deriv (by field_simp)

/-- d/dt[-1/(2t)] = 1/(2t²). Used to evaluate ∫ 1/(2t²) via FTC. -/
lemma hasDerivAt_neg_inv_2t (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun x => -1 / (2 * x)) (1 / (2 * t ^ 2)) t := by
  have h := (hasDerivAt_inv ht).const_mul (-1/2 : ℝ)
  rwa [show (fun y : ℝ => -1/2 * y⁻¹) = (fun x => -1 / (2 * x)) from by ext; ring,
       show -1/2 * (-(t ^ 2)⁻¹) = 1 / (2 * t ^ 2) from by field_simp] at h

/-! ## Positivity helpers -/

private lemma uIcc_pos' {X : ℝ} (hX : 1 ≤ X) {t : ℝ} (ht : t ∈ uIcc 1 X) : 0 < t := by
  rw [uIcc_of_le hX] at ht; linarith [ht.1]

private lemma uIcc_ne' {X : ℝ} (hX : 1 ≤ X) {t : ℝ} (ht : t ∈ uIcc 1 X) : t ≠ 0 :=
  ne_of_gt (uIcc_pos' hX ht)

/-! ## Continuity and integrability -/

private lemma cont_rem {X : ℝ} (hX : 1 ≤ X) :
    ContinuousOn (fun t => Real.sin (t ^ 2) / (2 * t ^ 2)) (uIcc 1 X) :=
  ContinuousOn.div (Real.continuous_sin.comp (continuous_pow 2)).continuousOn
    (continuousOn_const.mul (continuous_pow 2).continuousOn)
    (fun _t ht => mul_ne_zero two_ne_zero (pow_ne_zero 2 (uIcc_ne' hX ht)))

private lemma int_inv_2t_sq {X : ℝ} (hX : 1 ≤ X) :
    IntervalIntegrable (fun t => 1 / (2 * t ^ 2)) volume 1 X :=
  (ContinuousOn.div continuousOn_const (continuousOn_const.mul (continuous_pow 2).continuousOn)
    (fun _t ht => mul_ne_zero two_ne_zero (pow_ne_zero 2 (uIcc_ne' hX ht)))).intervalIntegrable

/-! ## Integration by parts identity -/

/-- IBP identity: ∫_1^X cos(t²) = sin(X²)/(2X) - sin(1)/2 + ∫_1^X sin(t²)/(2t²).
Proved via FTC applied to sin(t²)/(2t), whose derivative is cos(t²) - sin(t²)/(2t²). -/
theorem ibp_fresnel {X : ℝ} (hX : 1 ≤ X) :
    ∫ t in (1:ℝ)..X, Real.cos (t ^ 2) =
    Real.sin (X ^ 2) / (2 * X) - Real.sin 1 / 2 +
    ∫ t in (1:ℝ)..X, Real.sin (t ^ 2) / (2 * t ^ 2) := by
  have hint_cos : IntervalIntegrable (fun t => Real.cos (t ^ 2)) volume 1 X :=
    (Real.continuous_cos.comp (continuous_pow 2)).continuousOn.intervalIntegrable
  have hint_rem := (cont_rem hX).intervalIntegrable (a := 1) (b := X) (μ := volume)
  have hftc : ∫ t in (1:ℝ)..X, (Real.cos (t ^ 2) - Real.sin (t ^ 2) / (2 * t ^ 2)) =
    Real.sin (X ^ 2) / (2 * X) - Real.sin 1 / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_sin_sq_div_2t t (uIcc_ne' hX ht))
      (((Real.continuous_cos.comp (continuous_pow 2)).continuousOn.sub (cont_rem hX)).intervalIntegrable)]
    simp [one_pow, mul_one]
  rw [show ∫ t in (1:ℝ)..X, Real.cos (t ^ 2) =
    (∫ t in (1:ℝ)..X, (Real.cos (t ^ 2) - Real.sin (t ^ 2) / (2 * t ^ 2))) +
    ∫ t in (1:ℝ)..X, Real.sin (t ^ 2) / (2 * t ^ 2) from by
    rw [← intervalIntegral.integral_add (hint_cos.sub hint_rem) hint_rem]
    congr 1; ext t; ring, hftc]

/-! ## Remainder bound -/

/-- The remainder integral satisfies |∫_1^X sin(t²)/(2t²) dt| ≤ 1/2.
Proved by pointwise domination |sin(t²)/(2t²)| ≤ 1/(2t²) and
FTC: ∫_1^X 1/(2t²) = 1/2 - 1/(2X) ≤ 1/2. -/
theorem remainder_bound {X : ℝ} (hX : 1 ≤ X) :
    |∫ t in (1:ℝ)..X, Real.sin (t ^ 2) / (2 * t ^ 2)| ≤ 1 / 2 := by
  have hint_rem := (cont_rem hX).intervalIntegrable (a := 1) (b := X) (μ := volume)
  have hint_bnd := int_inv_2t_sq hX
  calc |∫ t in (1:ℝ)..X, Real.sin (t ^ 2) / (2 * t ^ 2)|
      ≤ ∫ t in (1:ℝ)..X, ‖Real.sin (t ^ 2) / (2 * t ^ 2)‖ := by
        rw [← Real.norm_eq_abs]
        exact intervalIntegral.norm_integral_le_integral_norm hX
    _ ≤ ∫ t in (1:ℝ)..X, (1 / (2 * t ^ 2)) := by
        apply intervalIntegral.integral_mono_on hX hint_rem.norm hint_bnd
        intro t ht
        have htp := uIcc_pos' hX (Icc_subset_uIcc ht)
        rw [Real.norm_eq_abs, abs_div,
            abs_of_pos (mul_pos two_pos (sq_pos_of_pos htp))]
        exact div_le_div_of_nonneg_right (abs_sin_le_one _)
          (mul_pos two_pos (sq_pos_of_pos htp)).le
    _ ≤ 1 / 2 := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t ht => hasDerivAt_neg_inv_2t t (uIcc_ne' hX ht)) hint_bnd]
        have hXp : (0 : ℝ) < X := by linarith
        have h2Xp : (0 : ℝ) < 2 * X := by linarith
        rw [show -1 / (2 * X) - (-1 / (2 * 1)) = (X - 1) / (2 * X) from by field_simp; ring]
        rw [div_le_div_iff₀ h2Xp two_pos]
        nlinarith

/-! ## Main theorem -/

/-- **Fresnel cosine integral bound**: |∫_1^X cos(t²) dt| ≤ 3/2 for all X ≥ 1.

Proved by integration by parts:
  ∫_1^X cos(t²) = sin(X²)/(2X) - sin(1)/2 + ∫_1^X sin(t²)/(2t²)
Each summand is bounded by 1/2 in absolute value. -/
theorem fresnel_cos_bounded :
    ∀ X : ℝ, 1 ≤ X → |∫ t in (1:ℝ)..X, Real.cos (t ^ 2)| ≤ 3 / 2 := by
  intro X hX
  rw [ibp_fresnel hX]
  have hXp : (0 : ℝ) < X := by linarith
  have hb1 : |Real.sin (X ^ 2) / (2 * X)| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (mul_pos two_pos hXp)]
    exact (div_le_div_of_nonneg_right (abs_sin_le_one _) (mul_pos two_pos hXp).le).trans
      (by rw [div_le_div_iff₀ (mul_pos two_pos hXp) two_pos]; nlinarith)
  have hb2 : |Real.sin 1 / 2| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact div_le_div_of_nonneg_right (abs_sin_le_one _) (by norm_num)
  calc |Real.sin (X ^ 2) / (2 * X) - Real.sin 1 / 2 +
      ∫ t in (1:ℝ)..X, Real.sin (t ^ 2) / (2 * t ^ 2)|
      ≤ |Real.sin (X ^ 2) / (2 * X) - Real.sin 1 / 2| +
        |∫ t in (1:ℝ)..X, Real.sin (t ^ 2) / (2 * t ^ 2)| := abs_add_le _ _
    _ ≤ (|Real.sin (X ^ 2) / (2 * X)| + |Real.sin 1 / 2|) +
        |∫ t in (1:ℝ)..X, Real.sin (t ^ 2) / (2 * t ^ 2)| := by
        gcongr
        calc |Real.sin (X ^ 2) / (2 * X) - Real.sin 1 / 2|
            ≤ |Real.sin (X ^ 2) / (2 * X)| + |-(Real.sin 1 / 2)| := abs_add_le _ _
          _ = |Real.sin (X ^ 2) / (2 * X)| + |Real.sin 1 / 2| := by rw [abs_neg]
    _ ≤ (1/2 + 1/2) + 1/2 := by linarith [remainder_bound hX]
    _ = 3/2 := by ring

/-! ## Sine version infrastructure -/

/-- d/dt[-cos(t²)/(2t)] = sin(t²) + cos(t²)/(2t²). -/
lemma hasDerivAt_neg_cos_sq_div_2t (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun x => -Real.cos (x ^ 2) / (2 * x))
      (Real.sin (t ^ 2) + Real.cos (t ^ 2) / (2 * t ^ 2)) t := by
  have hcos_neg : HasDerivAt (fun x => -Real.cos (x ^ 2)) (2 * t * Real.sin (t ^ 2)) t := by
    exact ((hasDerivAt_cos _).comp t (by simpa using hasDerivAt_pow 2 t)).neg.congr_deriv (by ring)
  have h2x : HasDerivAt (fun x => 2 * x) 2 t := by
    have := (hasDerivAt_id t).const_mul (2 : ℝ); simp at this; exact this
  exact (hcos_neg.div h2x (mul_ne_zero two_ne_zero ht)).congr_deriv (by field_simp; ring)

private lemma cont_rem_cos {X : ℝ} (hX : 1 ≤ X) :
    ContinuousOn (fun t => Real.cos (t ^ 2) / (2 * t ^ 2)) (uIcc 1 X) :=
  ContinuousOn.div (Real.continuous_cos.comp (continuous_pow 2)).continuousOn
    (continuousOn_const.mul (continuous_pow 2).continuousOn)
    (fun _t ht => mul_ne_zero two_ne_zero (pow_ne_zero 2 (uIcc_ne' hX ht)))

/-- IBP for sine: ∫_1^X sin(t²) = -cos(X²)/(2X) + cos(1)/2 - ∫_1^X cos(t²)/(2t²). -/
private theorem ibp_fresnel_sin {X : ℝ} (hX : 1 ≤ X) :
    ∫ t in (1:ℝ)..X, Real.sin (t ^ 2) =
    -Real.cos (X ^ 2) / (2 * X) - (-Real.cos 1 / 2) -
    ∫ t in (1:ℝ)..X, Real.cos (t ^ 2) / (2 * t ^ 2) := by
  have hint_sin : IntervalIntegrable (fun t => Real.sin (t ^ 2)) volume 1 X :=
    (Real.continuous_sin.comp (continuous_pow 2)).continuousOn.intervalIntegrable
  have hint_rem := (cont_rem_cos hX).intervalIntegrable (a := 1) (b := X) (μ := volume)
  -- sin(t²) = d/dt[-cos(t²)/(2t)] - cos(t²)/(2t²)
  -- ∫ sin(t²) = [-cos(t²)/(2t)]_1^X - ∫ cos(t²)/(2t²)
  -- FTC: ∫ (sin + cos/2t²) = [-cos/(2t)]_1^X
  have hftc : ∫ t in (1:ℝ)..X, (Real.sin (t ^ 2) + Real.cos (t ^ 2) / (2 * t ^ 2)) =
    -Real.cos (X ^ 2) / (2 * X) - (-Real.cos 1 / 2) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_neg_cos_sq_div_2t t (uIcc_ne' hX ht))
      (((Real.continuous_sin.comp (continuous_pow 2)).continuousOn.add (cont_rem_cos hX)).intervalIntegrable)]
    simp [one_pow, mul_one]
  -- ∫ sin = ∫(sin + cos/2t²) - ∫cos/2t²
  rw [show ∫ t in (1:ℝ)..X, Real.sin (t ^ 2) =
    (∫ t in (1:ℝ)..X, (Real.sin (t ^ 2) + Real.cos (t ^ 2) / (2 * t ^ 2))) -
    ∫ t in (1:ℝ)..X, Real.cos (t ^ 2) / (2 * t ^ 2) from by
    rw [← intervalIntegral.integral_sub (hint_sin.add hint_rem) hint_rem]
    congr 1; ext t; ring, hftc]

/-- |∫_1^X cos(t²)/(2t²)| ≤ 1/2. -/
private theorem remainder_bound_cos {X : ℝ} (hX : 1 ≤ X) :
    |∫ t in (1:ℝ)..X, Real.cos (t ^ 2) / (2 * t ^ 2)| ≤ 1 / 2 := by
  have hint_rem := (cont_rem_cos hX).intervalIntegrable (a := 1) (b := X) (μ := volume)
  have hint_bnd := int_inv_2t_sq hX
  calc |∫ t in (1:ℝ)..X, Real.cos (t ^ 2) / (2 * t ^ 2)|
      ≤ ∫ t in (1:ℝ)..X, ‖Real.cos (t ^ 2) / (2 * t ^ 2)‖ := by
        rw [← Real.norm_eq_abs]
        exact intervalIntegral.norm_integral_le_integral_norm hX
    _ ≤ ∫ t in (1:ℝ)..X, (1 / (2 * t ^ 2)) := by
        apply intervalIntegral.integral_mono_on hX hint_rem.norm hint_bnd
        intro t ht
        have htp := uIcc_pos' hX (Icc_subset_uIcc ht)
        rw [Real.norm_eq_abs, abs_div,
            abs_of_pos (mul_pos two_pos (sq_pos_of_pos htp))]
        exact div_le_div_of_nonneg_right (abs_cos_le_one _)
          (mul_pos two_pos (sq_pos_of_pos htp)).le
    _ ≤ 1 / 2 := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t ht => hasDerivAt_neg_inv_2t t (uIcc_ne' hX ht)) hint_bnd]
        have hXp : (0 : ℝ) < X := by linarith
        have h2Xp : (0 : ℝ) < 2 * X := by linarith
        rw [show -1 / (2 * X) - (-1 / (2 * 1)) = (X - 1) / (2 * X) from by field_simp; ring]
        rw [div_le_div_iff₀ h2Xp two_pos]
        nlinarith

/-- **Fresnel sine integral bound**: |∫_1^X sin(t²) dt| ≤ 3/2 for all X ≥ 1. -/
theorem fresnel_sin_bounded :
    ∀ X : ℝ, 1 ≤ X → |∫ t in (1:ℝ)..X, Real.sin (t ^ 2)| ≤ 3 / 2 := by
  intro X hX
  rw [ibp_fresnel_sin hX]
  have hXp : (0 : ℝ) < X := by linarith
  have hb1 : |-Real.cos (X ^ 2) / (2 * X)| ≤ 1 / 2 := by
    rw [abs_div, abs_neg, abs_of_pos (mul_pos two_pos hXp)]
    exact (div_le_div_of_nonneg_right (abs_cos_le_one _) (mul_pos two_pos hXp).le).trans
      (by rw [div_le_div_iff₀ (mul_pos two_pos hXp) two_pos]; nlinarith)
  have hb2 : |-Real.cos 1 / 2| ≤ 1 / 2 := by
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact div_le_div_of_nonneg_right (abs_cos_le_one _) (by norm_num)
  calc |-Real.cos (X ^ 2) / (2 * X) - (-Real.cos 1 / 2) -
      ∫ t in (1:ℝ)..X, Real.cos (t ^ 2) / (2 * t ^ 2)|
      ≤ |-Real.cos (X ^ 2) / (2 * X) - (-Real.cos 1 / 2)| +
        |∫ t in (1:ℝ)..X, Real.cos (t ^ 2) / (2 * t ^ 2)| := by
        rw [show -Real.cos (X ^ 2) / (2 * X) - (-Real.cos 1 / 2) -
          ∫ t in (1:ℝ)..X, Real.cos (t ^ 2) / (2 * t ^ 2) =
          (-Real.cos (X ^ 2) / (2 * X) - (-Real.cos 1 / 2)) +
          (-(∫ t in (1:ℝ)..X, Real.cos (t ^ 2) / (2 * t ^ 2))) from by ring]
        exact (abs_add_le _ _).trans (by rw [abs_neg])
    _ ≤ (|-Real.cos (X ^ 2) / (2 * X)| + |-Real.cos 1 / 2|) +
        |∫ t in (1:ℝ)..X, Real.cos (t ^ 2) / (2 * t ^ 2)| := by
        gcongr
        calc |-Real.cos (X ^ 2) / (2 * X) - (-Real.cos 1 / 2)|
            ≤ |-Real.cos (X ^ 2) / (2 * X)| + |-(- Real.cos 1 / 2)| := abs_add_le _ _
          _ = |-Real.cos (X ^ 2) / (2 * X)| + |-Real.cos 1 / 2| := by rw [abs_neg]
    _ ≤ (1/2 + 1/2) + 1/2 := by linarith [remainder_bound_cos hX]
    _ = 3/2 := by ring

end FresnelBound
