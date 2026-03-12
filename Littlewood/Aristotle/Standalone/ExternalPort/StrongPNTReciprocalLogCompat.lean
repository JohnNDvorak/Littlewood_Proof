import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTReciprocalLogCompat

open scoped Real

/-- External-port adaptation of strongpnt's `norm_reciprocal_inequality_1`. -/
theorem norm_reciprocal_inequality_1
    (x : ℝ) (x₁ : ℝ) (hx₁ : x₁ ≥ 1) :
    ‖x ^ 2 + x₁ ^ 2‖₊⁻¹ ≤ (‖x₁‖₊ ^ 2)⁻¹ := by
  rw [← NNReal.coe_le_coe]
  have hx1_nonneg : 0 ≤ x₁ := by linarith
  have hsum_nonneg : 0 ≤ x ^ 2 + x₁ ^ 2 := by positivity
  have hx1_sq_pos : 0 < x₁ ^ 2 := by nlinarith [hx₁]
  have hsum_pos : 0 < x ^ 2 + x₁ ^ 2 := by nlinarith [sq_nonneg x, hx1_sq_pos]
  have h_inv : (x ^ 2 + x₁ ^ 2)⁻¹ ≤ (x₁ ^ 2)⁻¹ := by
    exact (inv_le_inv₀ hsum_pos hx1_sq_pos).2 (by nlinarith [sq_nonneg x])
  simpa [NNReal.coe_inv, NNReal.coe_pow, Real.nnnorm_of_nonneg hsum_nonneg,
    Real.nnnorm_of_nonneg hx1_nonneg] using h_inv

/-- External-port adaptation of strongpnt's `norm_reciprocal_inequality`. -/
theorem norm_reciprocal_inequality
    (x : ℝ) (x₁ : ℝ) (hx₁ : x₁ ≤ -1) :
    ‖x ^ 2 + x₁ ^ 2‖₊⁻¹ ≤ (‖x₁‖₊ ^ 2)⁻¹ := by
  have hx1_neg : -x₁ ≥ 1 := by linarith
  simpa [neg_sq] using norm_reciprocal_inequality_1 x (-x₁) hx1_neg

/-- External-port adaptation of strongpnt's `one_add_inv_log` helper. -/
lemma one_add_inv_log
    {X : ℝ} (X_ge : 3 ≤ X) :
    (1 + (Real.log X)⁻¹) < 2 := by
  have hX_pos : 0 < X := by linarith
  have hlog_gt_one : 1 < Real.log X := by
    exact (Real.lt_log_iff_exp_lt hX_pos).2 (by linarith [Real.exp_one_lt_d9, X_ge])
  nlinarith [inv_lt_one_of_one_lt₀ hlog_gt_one]

/-- External-port adaptation of strongpnt's `log_pos` helper. -/
theorem log_pos
    (T : ℝ) (T_gt : 3 < T) :
    Real.log T > 1 := by
  exact (Real.lt_log_iff_exp_lt (by linarith)).2 (by linarith [Real.exp_one_lt_d9, T_gt])

end Aristotle.Standalone.ExternalPort.StrongPNTReciprocalLogCompat
