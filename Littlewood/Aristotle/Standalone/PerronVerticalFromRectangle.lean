/-
Perron vertical integral from rectangle contour.

Connects the per-term vertical line integral to the rectangle contour evaluations
in PerronContourIntegralsV2.

KEY RESULTS (proved):
- `vertical_integral_from_rect_pos`: for y > 1, vert*I = 2πi - boundary (PROVED)
- `vertical_integral_re_from_rect_pos`: Re(vert) = 2π - Im(boundary) (PROVED)
- `vertical_integral_re_error_bound`: |Re(vert) - 2π| ≤ ‖boundary‖ (PROVED)
- `top_horizontal_bound`: top horizontal ≤ V2 bound (PROVED)
- `left_vertical_bound`: left vertical ≤ V2 bound (PROVED)
- `perron_per_term_error_from_boundary`: per-term = 1 + O(boundary) (PROVED)

SORRY COUNT: 0 (all proved)

References: Davenport Ch. 17.

Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.PerronContourIntegralsV2

set_option linter.mathlibStandardSet false

open scoped BigOperators Real
open Real Complex Set MeasureTheory intervalIntegral Filter Topology

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.PerronVerticalFromRectangle

/-! ## Perron integrand and conventions -/

def perronIntegrand (y c t : ℝ) : ℂ :=
  (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
    ((c : ℂ) + (t : ℂ) * Complex.I)

lemma vertical_integral_factor_I (y c T : ℝ) :
    ∫ t in (-T)..T, perronIntegrand y c t * Complex.I =
    (∫ t in (-T)..T, perronIntegrand y c t) * Complex.I :=
  intervalIntegral.integral_mul_const _ _

/-! ## Boundary remainder -/

def boundaryRemainder (y c T R : ℝ) : ℂ :=
  let f := fun z : ℂ => (y : ℂ) ^ z / z
  (∫ x in (c : ℝ)..((-R : ℝ)), f ((x : ℂ) + Complex.I * (T : ℂ))) +
  (∫ t in (T : ℝ)..((-T : ℝ)), f ((-R : ℂ) + Complex.I * (t : ℂ)) * Complex.I) +
  (∫ x in ((-R : ℝ))..(c : ℝ), f ((x : ℂ) - Complex.I * (T : ℂ)))

/-! ## Rectangle identity rearranged -/

theorem vertical_integral_from_rect_pos (y : ℝ) (hy : 1 < y) (c : ℝ) (hc : 0 < c)
    (T : ℝ) (hT : 0 < T) (R : ℝ) (hR : 0 < R) :
    (∫ t in (-T)..T, perronIntegrand y c t) * Complex.I =
      2 * ↑Real.pi * Complex.I - boundaryRemainder y c T R := by
  have hV2 := integral_boundary_rect_perron_pos y hy c hc T hT R hR
  have h_rewrite : ∫ t in (-T)..T,
      (fun z : ℂ => (↑y) ^ z / z) (↑c + I * ↑t) * I =
    (∫ t in (-T)..T, perronIntegrand y c t) * Complex.I := by
    rw [← vertical_integral_factor_I]
    congr 1; ext t; unfold perronIntegrand; ring
  have h_eq := hV2
  dsimp only at h_eq
  have h1 : ∀ t : ℝ,
      ((↑y : ℂ) ^ ((↑c : ℂ) + I * (↑t : ℂ)) / ((↑c : ℂ) + I * (↑t : ℂ))) * I =
      perronIntegrand y c t * I := by
    intro t; unfold perronIntegrand; ring
  simp_rw [h1] at h_eq
  rw [intervalIntegral.integral_mul_const] at h_eq
  simp only [boundaryRemainder]
  have key : (∫ t in (-T)..T, perronIntegrand y c t) * I +
    ((∫ x in (c : ℝ)..((-R : ℝ)),
        ((↑y : ℂ) ^ ((↑x : ℂ) + I * (↑T : ℂ)) / ((↑x : ℂ) + I * (↑T : ℂ)))) +
     (∫ t in (T : ℝ)..((-T : ℝ)),
        ((↑y : ℂ) ^ ((-↑R : ℂ) + I * (↑t : ℂ)) / ((-↑R : ℂ) + I * (↑t : ℂ))) * I) +
     (∫ x in ((-R : ℝ))..(c : ℝ),
        ((↑y : ℂ) ^ ((↑x : ℂ) - I * (↑T : ℂ)) / ((↑x : ℂ) - I * (↑T : ℂ))))) =
    2 * ↑π * I := by convert h_eq using 1; ring
  exact eq_sub_of_add_eq key

/-! ## Taking Re -/

lemma im_mul_I (z : ℂ) : (z * Complex.I).im = z.re := by
  simp [Complex.mul_im, Complex.I_re, Complex.I_im]

theorem vertical_integral_re_from_rect_pos (y : ℝ) (hy : 1 < y) (c : ℝ) (hc : 0 < c)
    (T : ℝ) (hT : 0 < T) (R : ℝ) (hR : 0 < R) :
    (∫ t in (-T)..T, perronIntegrand y c t).re =
      2 * Real.pi - (boundaryRemainder y c T R).im := by
  have hid := vertical_integral_from_rect_pos y hy c hc T hT R hR
  have him := congrArg Complex.im hid
  simp only [im_mul_I] at him
  rw [Complex.sub_im, Complex.mul_im, Complex.I_im, Complex.I_re] at him
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, mul_one, add_zero] at him
  norm_num at him; linarith

theorem vertical_integral_re_error_bound (y : ℝ) (hy : 1 < y) (c : ℝ) (hc : 0 < c)
    (T : ℝ) (hT : 0 < T) (R : ℝ) (hR : 0 < R) :
    |(∫ t in (-T)..T, perronIntegrand y c t).re - 2 * Real.pi| ≤
      ‖boundaryRemainder y c T R‖ := by
  rw [vertical_integral_re_from_rect_pos y hy c hc T hT R hR]
  simp only [sub_sub_cancel_left, abs_neg]
  exact Complex.abs_im_le_norm _

/-! ## Component bounds -/

lemma top_horizontal_bound (y : ℝ) (hy : 1 < y) (c : ℝ) (hc : 0 < c) (T : ℝ) (hT : 0 < T)
    (R : ℝ) (hR : 0 < R) :
    ‖∫ x in (c : ℝ)..((-R : ℝ)),
      ((↑y : ℂ) ^ ((↑x : ℂ) + I * (↑T : ℂ)) / ((↑x : ℂ) + I * (↑T : ℂ)))‖ ≤
    (y ^ c - y ^ (-R)) / (T * Real.log y) := by
  rw [intervalIntegral.integral_symm, norm_neg]
  exact le_trans
    (intervalIntegral.norm_integral_le_integral_norm (by linarith))
    (integral_norm_bound_large_y y hy c T hT R (by linarith))

lemma left_vertical_bound (y : ℝ) (hy : 1 < y) (R : ℝ) (hR : 0 < R)
    (T : ℝ) (hT : 0 < T) :
    ‖∫ t in (T : ℝ)..((-T : ℝ)),
      ((↑y : ℂ) ^ ((-↑R : ℂ) + I * (↑t : ℂ)) / ((-↑R : ℂ) + I * (↑t : ℂ))) * I‖ ≤
    2 * T * y ^ (-R) / R := by
  -- Factor out * I: ∫ g*I = (∫ g)*I, and ‖z*I‖ = ‖z‖
  rw [intervalIntegral.integral_mul_const]
  have hI : ‖(Complex.I : ℂ)‖ = 1 := by simp [Complex.norm_I]
  rw [norm_mul, hI, mul_one]
  rw [intervalIntegral.integral_symm, norm_neg]
  exact vertical_integral_bound_far_left y (by positivity) R hR T hT

-- Bottom horizontal: ‖y^{x-iT}/(x-iT)‖ = ‖y^{x+iT}/(x+iT)‖ by norm equality.
lemma norm_integrand_conj_eq (y : ℝ) (hy : 0 < y) (x T : ℝ) :
    ‖(↑y : ℂ) ^ ((↑x : ℂ) - I * (↑T : ℂ)) / ((↑x : ℂ) - I * (↑T : ℂ))‖ =
    ‖(↑y : ℂ) ^ ((↑x : ℂ) + I * (↑T : ℂ)) / ((↑x : ℂ) + I * (↑T : ℂ))‖ := by
  simp only [norm_div]
  congr 1
  · -- Numerator: ‖y^{x-iT}‖ = y^x = ‖y^{x+iT}‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy,
        Complex.norm_cpow_eq_rpow_re_of_pos hy]
    congr 1
    simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im]
  · -- Denominator: ‖x-iT‖ = ‖x+iT‖  (both = √(x² + T²))
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]

lemma bottom_horizontal_bound (y : ℝ) (hy : 1 < y) (c : ℝ) (hc : 0 < c) (T : ℝ) (hT : 0 < T)
    (R : ℝ) (hR : 0 < R) :
    ‖∫ x in ((-R : ℝ))..(c : ℝ),
      ((↑y : ℂ) ^ ((↑x : ℂ) - I * (↑T : ℂ)) / ((↑x : ℂ) - I * (↑T : ℂ)))‖ ≤
    (y ^ c - y ^ (-R)) / (T * Real.log y) := by
  calc ‖∫ x in (-R)..c,
        ((↑y : ℂ) ^ ((↑x : ℂ) - I * (↑T : ℂ)) / ((↑x : ℂ) - I * (↑T : ℂ)))‖
      ≤ ∫ x in (-R)..c,
        ‖((↑y : ℂ) ^ ((↑x : ℂ) - I * (↑T : ℂ)) / ((↑x : ℂ) - I * (↑T : ℂ)))‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ = ∫ x in (-R)..c,
        ‖((↑y : ℂ) ^ ((↑x : ℂ) + I * (↑T : ℂ)) / ((↑x : ℂ) + I * (↑T : ℂ)))‖ := by
      congr 1; ext x; exact norm_integrand_conj_eq y (by positivity) x T
    _ ≤ (y ^ c - y ^ (-R)) / (T * Real.log y) :=
      integral_norm_bound_large_y y hy c T hT R (by linarith)

theorem boundaryRemainder_norm_bound (y : ℝ) (hy : 1 < y) (c : ℝ) (hc : 0 < c)
    (T : ℝ) (hT : 0 < T) (R : ℝ) (hR : 0 < R) :
    ‖boundaryRemainder y c T R‖ ≤
      2 * (y ^ c - y ^ (-R)) / (T * Real.log y) +
      2 * T * y ^ (-R) / R := by
  unfold boundaryRemainder; dsimp only
  calc ‖(∫ x in (c : ℝ)..((-R : ℝ)),
          ((↑y : ℂ) ^ ((↑x : ℂ) + I * (↑T : ℂ)) / ((↑x : ℂ) + I * (↑T : ℂ)))) +
        (∫ t in (T : ℝ)..((-T : ℝ)),
          ((↑y : ℂ) ^ ((-↑R : ℂ) + I * (↑t : ℂ)) / ((-↑R : ℂ) + I * (↑t : ℂ))) * I) +
        (∫ x in ((-R : ℝ))..(c : ℝ),
          ((↑y : ℂ) ^ ((↑x : ℂ) - I * (↑T : ℂ)) / ((↑x : ℂ) - I * (↑T : ℂ))))‖
      ≤ ‖∫ x in (c : ℝ)..((-R : ℝ)),
            ((↑y : ℂ) ^ ((↑x : ℂ) + I * (↑T : ℂ)) / ((↑x : ℂ) + I * (↑T : ℂ)))‖ +
        ‖∫ t in (T : ℝ)..((-T : ℝ)),
            ((↑y : ℂ) ^ ((-↑R : ℂ) + I * (↑t : ℂ)) / ((-↑R : ℂ) + I * (↑t : ℂ))) * I‖ +
        ‖∫ x in ((-R : ℝ))..(c : ℝ),
            ((↑y : ℂ) ^ ((↑x : ℂ) - I * (↑T : ℂ)) / ((↑x : ℂ) - I * (↑T : ℂ)))‖ := by
        have h12 := norm_add_le
          ((∫ x in (c : ℝ)..((-R : ℝ)),
              ((↑y : ℂ) ^ ((↑x : ℂ) + I * (↑T : ℂ)) / ((↑x : ℂ) + I * (↑T : ℂ)))) +
           (∫ t in (T : ℝ)..((-T : ℝ)),
              ((↑y : ℂ) ^ ((-↑R : ℂ) + I * (↑t : ℂ)) / ((-↑R : ℂ) + I * (↑t : ℂ))) * I))
          (∫ x in ((-R : ℝ))..(c : ℝ),
            ((↑y : ℂ) ^ ((↑x : ℂ) - I * (↑T : ℂ)) / ((↑x : ℂ) - I * (↑T : ℂ))))
        have h1 := norm_add_le
          (∫ x in (c : ℝ)..((-R : ℝ)),
            ((↑y : ℂ) ^ ((↑x : ℂ) + I * (↑T : ℂ)) / ((↑x : ℂ) + I * (↑T : ℂ))))
          (∫ t in (T : ℝ)..((-T : ℝ)),
            ((↑y : ℂ) ^ ((-↑R : ℂ) + I * (↑t : ℂ)) / ((-↑R : ℂ) + I * (↑t : ℂ))) * I)
        linarith
    _ ≤ (y ^ c - y ^ (-R)) / (T * Real.log y) +
        2 * T * y ^ (-R) / R +
        (y ^ c - y ^ (-R)) / (T * Real.log y) := by
      linarith [top_horizontal_bound y hy c hc T hT R hR,
                left_vertical_bound y hy R hR T hT,
                bottom_horizontal_bound y hy c hc T hT R hR]
    _ = 2 * (y ^ c - y ^ (-R)) / (T * Real.log y) +
        2 * T * y ^ (-R) / R := by ring

/-! ## Per-term Perron bound -/

theorem perron_per_term_error_from_boundary (y : ℝ) (hy : 1 < y) (c : ℝ) (hc : 0 < c)
    (T : ℝ) (hT : 0 < T) (R : ℝ) (hR : 0 < R) :
    |(2 * Real.pi)⁻¹ * (∫ t in (-T)..T, perronIntegrand y c t).re - 1| ≤
      (2 * Real.pi)⁻¹ * ‖boundaryRemainder y c T R‖ := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hpi_inv : 0 < (2 * Real.pi)⁻¹ := inv_pos.mpr hpi
  rw [show (1 : ℝ) = (2 * Real.pi)⁻¹ * (2 * Real.pi) from by field_simp]
  rw [← mul_sub, abs_mul, abs_of_pos hpi_inv]
  gcongr
  exact vertical_integral_re_error_bound y hy c hc T hT R hR

end Aristotle.Standalone.PerronVerticalFromRectangle
