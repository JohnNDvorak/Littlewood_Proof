/-
Saddle-point method infrastructure for the Riemann-Siegel formula.

This file provides sorry-free sub-lemmas toward closing the
`rs_formula_remainder_bound` sorry in SiegelSaddleExpansionHyp.lean.

## Contents

### Part 1: Siegel phase function
The phase function φ(w) = -πw² + t·log(w) and its Taylor coefficients at the
saddle point w₀ = √(t/(2π)). All derivatives verified constructively.

### Part 2: Gaussian integral infrastructure
The complex Gaussian integral ∫ exp(-bx²) dx = (π/b)^{1/2} from Mathlib,
wrapped for the saddle-point application.

### Part 3: rpow identities
Key exponent arithmetic for converting between the RS formula remainder
t^{-3/4} and the normalized remainder t^{-1/2}.

### Part 4: Amplitude-division bound
The algebraic step converting |E - lead| ≤ C·t^{-3/4} into the
normalized bound |R| ≤ (C/(2π)^{1/4})·t^{-1/2} by dividing by (2π/t)^{1/4}.

SORRY COUNT: 0

Reference: Siegel 1932 §3; Edwards Ch. 7; Gabcke 1979 Satz 1.

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace SaddlePointMethod

open Real MeasureTheory Set

/-! ## Part 1: Siegel phase function -/

/-- The Siegel phase function φ(w) = -πw² + t·log(w).
    The Siegel integral involves exp(iφ(w)), and the saddle-point method
    approximates this by expanding φ around its critical point. -/
def siegelPhase (t w : ℝ) : ℝ := -Real.pi * w ^ 2 + t * Real.log w

/-- φ is differentiable with φ'(w) = -2πw + t/w for w > 0. -/
theorem siegelPhase_hasDerivAt (t w : ℝ) (hw : 0 < w) :
    HasDerivAt (siegelPhase t) (-2 * Real.pi * w + t / w) w := by
  unfold siegelPhase
  have h1 : HasDerivAt (fun w => -Real.pi * w ^ 2) (-2 * Real.pi * w) w := by
    have h := (hasDerivAt_pow 2 w).const_mul (-Real.pi)
    simp only [Nat.cast_ofNat, Nat.sub_one, Nat.pred, pow_one] at h
    exact h.congr_deriv (by ring)
  have h2 : HasDerivAt (fun w => t * Real.log w) (t / w) w :=
    ((Real.hasDerivAt_log (ne_of_gt hw)).const_mul t).congr_deriv (by field_simp)
  exact (h1.add h2).congr_deriv (by ring)

/-- At the saddle point w₀ = √(t/(2π)), the first derivative vanishes: φ'(w₀) = 0.
    This is the fundamental saddle-point condition. -/
theorem siegelPhase_critical_point (t : ℝ) (ht : 0 < t) :
    -2 * Real.pi * Real.sqrt (t / (2 * Real.pi)) +
    t / Real.sqrt (t / (2 * Real.pi)) = 0 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_pos : 0 < t / (2 * Real.pi) := div_pos ht hpi
  have h_sq := Real.sq_sqrt h_pos.le
  have key : 2 * Real.pi * (Real.sqrt (t / (2 * Real.pi)))^2 = t := by
    rw [h_sq]; field_simp
  field_simp; linarith

/-- The second derivative at the saddle: φ''(w₀) = -4π.
    The Fresnel integral ∫ exp(-i·2π·u²) du arises from this quadratic term.
    (Note: φ''(w) = -2π - t/w², and t/w₀² = 2π.) -/
theorem siegelPhase_second_deriv (t : ℝ) (ht : 0 < t) :
    -2 * Real.pi - t / (Real.sqrt (t / (2 * Real.pi)))^2 = -4 * Real.pi := by
  rw [Real.sq_sqrt (div_nonneg ht.le (by positivity))]; field_simp; ring

/-- The second derivative magnitude: |φ''(w₀)| = 4π.
    The Fresnel amplitude (2π/t)^{1/4} comes from |φ''|^{-1/2}. -/
theorem siegelPhase_second_deriv_abs :
    |(-4 : ℝ) * Real.pi| = 4 * Real.pi := by
  rw [show (-4 : ℝ) * Real.pi = -(4 * Real.pi) from by ring, abs_neg]
  exact abs_of_pos (by positivity)

/-- The quartic Taylor coefficient at the saddle: φ⁽⁴⁾(w₀)/24 = π²/t.
    This coefficient, together with the quartic integral bound,
    controls the O(t^{-1/2}) remainder in the Fresnel expansion.
    (Here: 6t/(24·w₀⁴) with w₀⁴ = (t/(2π))², so the result is π²/t.) -/
theorem siegelPhase_quartic_coeff (t : ℝ) (ht : 0 < t) :
    6 * t / (24 * (Real.sqrt (t / (2 * Real.pi)))^4) = Real.pi ^ 2 / t := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_pos : 0 < t / (2 * Real.pi) := div_pos ht hpi
  have h_sq := Real.sq_sqrt h_pos.le
  have h4 : (Real.sqrt (t / (2 * Real.pi)))^4 = (t / (2 * Real.pi))^2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h_sq]
  rw [h4]; field_simp; ring

/-- The quartic-to-quadratic ratio at the saddle: (π²/t)/(4π) = π/(4t).
    For t ≥ 2π, this is ≤ 1/8, ensuring the quartic correction is small. -/
theorem quartic_to_quadratic_ratio (t : ℝ) (ht : 0 < t) :
    Real.pi ^ 2 / t / (4 * Real.pi) = Real.pi / (4 * t) := by
  field_simp

/-- For t ≥ 2π, the quartic ratio π/(4t) ≤ 1/8. -/
theorem quartic_ratio_small (t : ℝ) (ht : 2 * Real.pi ≤ t) :
    Real.pi / (4 * t) ≤ 1 / 8 := by
  have ht_pos : 0 < t := by linarith [Real.pi_pos]
  rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 8)]
  nlinarith [Real.pi_gt_three]

/-! ## Part 2: Gaussian integral infrastructure -/

/-- Real Gaussian integral: ∫ exp(-b·x²) dx = √(π/b).
    This is the base case for the saddle-point evaluation. -/
theorem gaussian_integral_real (b : ℝ) :
    ∫ x : ℝ, Real.exp (-b * x ^ 2) = Real.sqrt (Real.pi / b) :=
  integral_gaussian b

/-- Complex Gaussian integral: ∫ exp(-b·x²) dx = (π/b)^{1/2} for Re(b) > 0.
    This handles oscillatory Gaussian integrals where b has an imaginary part
    (as in the Fresnel integral). -/
theorem gaussian_integral_complex (b : ℂ) (hb : 0 < b.re) :
    ∫ x : ℝ, Complex.exp (-b * x ^ 2) = (Complex.ofReal Real.pi / b) ^ (1/2 : ℂ) :=
  integral_gaussian_complex hb

/-- Simplified Gaussian: ∫ exp(-(a·π)·x²) dx = 1/√a for a > 0.
    This is the saddle-point evaluation with prefactor extracted. -/
theorem gaussian_simplified (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ, Real.exp (-(a * Real.pi) * x ^ 2) = 1 / Real.sqrt a := by
  rw [integral_gaussian (a * Real.pi)]
  rw [show Real.pi / (a * Real.pi) = 1 / a from by field_simp]
  rw [Real.sqrt_div' 1 (by positivity), Real.sqrt_one, one_div]

/-- For the Riemann-Siegel case with a = 2t:
    ∫ exp(-2tπx²) dx = 1/√(2t).
    This is the Gaussian integral at the Siegel saddle point. -/
theorem siegel_gaussian_eval (t : ℝ) (ht : 0 < t) :
    ∫ x : ℝ, Real.exp (-(2 * t * Real.pi) * x ^ 2) = 1 / Real.sqrt (2 * t) := by
  rw [show 2 * t * Real.pi = (2 * t) * Real.pi from by ring]
  exact gaussian_simplified (2 * t) (by positivity)

/-- The Fresnel amplitude factor: 1/√(2t) = (1/√2)·1/√t. -/
theorem fresnel_amplitude (t : ℝ) (ht : 0 < t) :
    1 / Real.sqrt (2 * t) = (1 / Real.sqrt 2) * (1 / Real.sqrt t) := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]; field_simp

/-- Combined: the Siegel Gaussian integral has amplitude (1/√2)·1/√t. -/
theorem siegel_gaussian_amplitude (t : ℝ) (ht : 0 < t) :
    ∫ x : ℝ, Real.exp (-(2 * t * Real.pi) * x ^ 2) =
    (1 / Real.sqrt 2) * (1 / Real.sqrt t) := by
  rw [siegel_gaussian_eval t ht, fresnel_amplitude t ht]

/-- The Fresnel parameter b = π(1-i) has Re(b) = π > 0, so the
    complex Gaussian integral applies to the Fresnel case. -/
theorem fresnel_parameter_re_pos :
    (Complex.ofReal Real.pi * (1 - Complex.I)).re = Real.pi := by
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]

/-! ## Part 3: rpow identities for the RS formula -/

/-- t^{-1/2} = 1/√t for t > 0. -/
theorem rpow_neg_half_eq_inv_sqrt (t : ℝ) (ht : 0 < t) :
    t ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt t := by
  rw [show -(1 : ℝ) / 2 = -(1/2 : ℝ) from by ring]
  rw [Real.rpow_neg ht.le]
  rw [show (1/2 : ℝ) = 2⁻¹ from by norm_num]
  rw [show (t ^ (2 : ℝ)⁻¹)⁻¹ = 1 / t ^ (2 : ℝ)⁻¹ from by ring]
  congr 1
  rw [show (2 : ℝ)⁻¹ = 1/2 from by norm_num]
  exact (Real.sqrt_eq_rpow t).symm

/-- t^{-1/4} · t^{-1/2} = t^{-3/4} for t > 0. -/
theorem rpow_neg_quarter_mul_neg_half (t : ℝ) (ht : 0 < t) :
    t ^ (-(1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 2) = t ^ (-(3 : ℝ) / 4) := by
  rw [← Real.rpow_add ht]; congr 1; norm_num

/-- t^{-3/4} / (2π/t)^{1/4} = t^{-1/2} / (2π)^{1/4}.
    KEY identity for converting the RS remainder bound. -/
theorem rpow_three_quarter_div_amp (t : ℝ) (ht : 0 < t) :
    t ^ (-(3:ℝ)/4) / ((2 * Real.pi / t) ^ ((1:ℝ)/4)) =
    t ^ (-(1:ℝ)/2) / (2 * Real.pi) ^ ((1:ℝ)/4) := by
  have h2pi_pos : (0:ℝ) < 2 * Real.pi := by positivity
  have h_amp_pos : 0 < (2 * Real.pi / t) ^ ((1:ℝ)/4) :=
    rpow_pos_of_pos (div_pos h2pi_pos ht) _
  have h_2pi14_pos : 0 < (2 * Real.pi) ^ ((1:ℝ)/4) := rpow_pos_of_pos h2pi_pos _
  have h_eq : t ^ (-(3:ℝ)/4) * (2 * Real.pi) ^ ((1:ℝ)/4) =
      t ^ (-(1:ℝ)/2) * (2 * Real.pi / t) ^ ((1:ℝ)/4) := by
    rw [Real.div_rpow (by positivity : (0:ℝ) ≤ 2 * Real.pi) ht.le]
    rw [show t ^ (-(1:ℝ)/2) * ((2 * Real.pi) ^ ((1:ℝ)/4) / t ^ ((1:ℝ)/4))
        = (2 * Real.pi) ^ ((1:ℝ)/4) * (t ^ (-(1:ℝ)/2) / t ^ ((1:ℝ)/4)) from by ring]
    rw [show t ^ (-(1:ℝ)/2) / t ^ ((1:ℝ)/4) = t ^ (-(1:ℝ)/2) * (t ^ ((1:ℝ)/4))⁻¹ from div_eq_mul_inv _ _]
    rw [show (t ^ ((1:ℝ)/4))⁻¹ = t ^ (-(1:ℝ)/4) from by
      rw [← Real.rpow_neg ht.le]; congr 1; ring]
    rw [← Real.rpow_add ht, show -(1:ℝ)/2 + -(1:ℝ)/4 = -(3:ℝ)/4 from by ring]
    ring
  exact div_eq_div_iff h_amp_pos.ne' h_2pi14_pos.ne' |>.mpr h_eq

/-! ## Part 4: Amplitude-division bound -/

/-- If |x| ≤ C · t^{-3/4}, then |x / amp| ≤ (C / (2π)^{1/4}) · t^{-1/2}
    where amp = (2π/t)^{1/4}.

    This converts the Riemann-Siegel remainder bound (in terms of t^{-3/4})
    into the normalized saddle-point remainder bound (in terms of t^{-1/2}). -/
theorem abs_div_amp_bound (x C t : ℝ) (ht : 0 < t)
    (hx : |x| ≤ C * t ^ (-(3:ℝ)/4)) :
    |x / (2 * Real.pi / t) ^ ((1:ℝ)/4)| ≤
    (C / (2 * Real.pi) ^ ((1:ℝ)/4)) * t ^ (-(1:ℝ)/2) := by
  have h_amp_pos : 0 < (2 * Real.pi / t) ^ ((1:ℝ)/4) :=
    rpow_pos_of_pos (div_pos (by positivity) ht) _
  rw [abs_div, abs_of_pos h_amp_pos]
  calc |x| / (2 * Real.pi / t) ^ ((1:ℝ)/4)
      ≤ C * t ^ (-(3:ℝ)/4) / (2 * Real.pi / t) ^ ((1:ℝ)/4) :=
        div_le_div_of_nonneg_right hx h_amp_pos.le
    _ = C * (t ^ (-(3:ℝ)/4) / (2 * Real.pi / t) ^ ((1:ℝ)/4)) := by ring
    _ = C * (t ^ (-(1:ℝ)/2) / (2 * Real.pi) ^ ((1:ℝ)/4)) := by
        rw [rpow_three_quarter_div_amp t ht]
    _ = C / (2 * Real.pi) ^ ((1:ℝ)/4) * t ^ (-(1:ℝ)/2) := by ring

/-- Specialization: for C = fresnelC1Bound · (2π)^{1/4}, the bound simplifies to
    fresnelC1Bound · t^{-1/2}. This is the exact form used in contour_saddle_bound. -/
theorem abs_div_amp_bound_specialized (x t : ℝ) (ht : 0 < t) (c : ℝ) (_hc : 0 < c)
    (hx : |x| ≤ (c * (2 * Real.pi) ^ ((1:ℝ)/4)) * t ^ (-(3:ℝ)/4)) :
    |x / (2 * Real.pi / t) ^ ((1:ℝ)/4)| ≤ c * t ^ (-(1:ℝ)/2) := by
  have h := abs_div_amp_bound x (c * (2 * Real.pi) ^ ((1:ℝ)/4)) t ht hx
  have h_2pi14_pos : 0 < (2 * Real.pi) ^ ((1:ℝ)/4) :=
    rpow_pos_of_pos (by positivity : (0:ℝ) < 2 * Real.pi) _
  rw [show c * (2 * Real.pi) ^ ((1:ℝ)/4) / (2 * Real.pi) ^ ((1:ℝ)/4) = c from
    mul_div_cancel_right₀ c (ne_of_gt h_2pi14_pos)] at h
  exact h

/-! ## Part 5: Saddle-point scale identities -/

/-- The saddle-point scale: (2π/t)^{1/4} = (2π)^{1/4} · t^{-1/4}. -/
theorem amp_factor_split (t : ℝ) (ht : 0 < t) :
    (2 * Real.pi / t) ^ ((1:ℝ)/4) =
    (2 * Real.pi) ^ ((1:ℝ)/4) * t ^ (-(1:ℝ)/4) := by
  rw [Real.div_rpow (by positivity : (0:ℝ) ≤ 2 * Real.pi) ht.le, div_eq_mul_inv,
      ← Real.rpow_neg ht.le, show -((1:ℝ)/4) = -(1:ℝ)/4 from by ring]

/-- (2π/t)^{1/4} ≤ 1 for t ≥ 2π. -/
theorem amp_factor_le_one (t : ℝ) (ht : 2 * Real.pi ≤ t) :
    (2 * Real.pi / t) ^ ((1:ℝ)/4) ≤ 1 := by
  have ht_pos : 0 < t := by linarith [Real.pi_pos]
  apply Real.rpow_le_one (div_nonneg (by positivity) ht_pos.le)
  · exact div_le_one_of_le₀ ht ht_pos.le
  · norm_num

/-- (2π/t)^{1/4} is positive for t > 0. -/
theorem amp_factor_pos (t : ℝ) (ht : 0 < t) :
    0 < (2 * Real.pi / t) ^ ((1:ℝ)/4) :=
  rpow_pos_of_pos (div_pos (by positivity) ht) _

end SaddlePointMethod
