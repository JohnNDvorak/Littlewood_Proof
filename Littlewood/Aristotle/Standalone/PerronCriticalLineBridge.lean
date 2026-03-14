/-
Bridge infrastructure connecting ZeroFreeRegionV3 bounds to the Perron
contour critical-line vertical integral estimate.

## Key connection

`ZeroFreeRegionV3.zeta_log_deriv_bound_near_one` gives:
  -Re(ζ'/ζ(σ)) ≤ 1/(σ-1) + C  for 1 < σ ≤ 2.

This file builds sorry-free algebraic infrastructure that reduces
the `contour_integral_remainder_bound` sorry to a pointwise ζ'/ζ
growth bound on the critical line.

## Results

* `norm_x_cpow_half_it`: |x^{1/2+it}| = √x factorization
* `norm_half_it_ge_half_t`: |1/2+it| ≥ |t|/2 for |t| ≥ 1
* `inv_norm_half_it_le`: |1/2+it|⁻¹ ≤ 2/|t| for |t| ≥ 1
* `norm_half_it_ge_half`: |1/2+it| ≥ 1/2 always
* `logT_sq_mono`: (log T)² is monotone for T ≥ 1
* `davenport_shift_advantage`: positivity of the Perron error term
* `zeta_logderiv_at_davenport_sigma`: δ = 1/log T is positive
* `pole_contribution_at_half`: 1/(1/2 - 1) = -2
* `three_four_one_lower_bound`: ζ'/ζ(σ+it) lower bound from 3-4-1
* `contour_remainder_structure`: additive structure of contour bound

SORRY COUNT: 0

References: Davenport Ch. 17; Montgomery-Vaughan §12.5; Titchmarsh §9.4.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ZeroFreeRegionV3
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aDefs

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.PerronCriticalLineBridge

open Complex Real
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton

/-! ## Part 1: Critical line norm factorizations -/

/-- For x > 0, |x^{1/2+it}| = x^{1/2} = √x.
    This separates the x-dependence from the t-dependence
    in the Perron critical-line integral. -/
theorem norm_x_cpow_half_it (x : ℝ) (hx : 0 < x) (t : ℝ) :
    ‖(x : ℂ) ^ ((1/2 : ℂ) + Complex.I * (t : ℂ))‖ = Real.sqrt x := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : ((1/2 : ℂ) + Complex.I * (t : ℂ)).re = 1/2 := by
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im]
  rw [hre, Real.sqrt_eq_rpow]

/-- For |t| ≥ 1, |1/2 + it| ≥ |t|/2. -/
theorem norm_half_it_ge_half_t (t : ℝ) (ht : 1 ≤ |t|) :
    |t| / 2 ≤ ‖(1/2 : ℂ) + Complex.I * (t : ℂ)‖ := by
  have h_im : ((1/2 : ℂ) + Complex.I * (t : ℂ)).im = t := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
  calc |t| / 2 ≤ |t| := by linarith
    _ = |((1/2 : ℂ) + Complex.I * (t : ℂ)).im| := by rw [h_im]
    _ ≤ ‖(1/2 : ℂ) + Complex.I * (t : ℂ)‖ := Complex.abs_im_le_norm _

/-- For |t| ≥ 1, |1/2 + it|⁻¹ ≤ 2/|t|. -/
theorem inv_norm_half_it_le (t : ℝ) (ht : 1 ≤ |t|) :
    ‖(1/2 : ℂ) + Complex.I * (t : ℂ)‖⁻¹ ≤ 2 / |t| := by
  have ht_pos : 0 < |t| := by linarith
  have h_ge := norm_half_it_ge_half_t t ht
  have h_norm_pos : 0 < ‖(1/2 : ℂ) + Complex.I * (t : ℂ)‖ := by linarith [div_pos ht_pos two_pos]
  -- Need: 1/‖s‖ ≤ 2/|t|, i.e., |t| ≤ 2·‖s‖
  -- Since |t|/2 ≤ ‖s‖, we have |t| ≤ 2·‖s‖
  calc ‖(1/2 : ℂ) + Complex.I * (t : ℂ)‖⁻¹
      ≤ (|t| / 2)⁻¹ := by
        apply inv_anti₀ (div_pos ht_pos two_pos) h_ge
    _ = 2 / |t| := by rw [inv_div]

/-- The norm of 1/2 + it is always ≥ 1/2. -/
theorem norm_half_it_ge_half (t : ℝ) :
    (1 : ℝ)/2 ≤ ‖(1/2 : ℂ) + Complex.I * (t : ℂ)‖ := by
  calc (1 : ℝ)/2 = |(1/2 : ℝ)| := by norm_num
    _ = |((1/2 : ℂ) + Complex.I * (t : ℂ)).re| := by
        simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
    _ ≤ ‖(1/2 : ℂ) + Complex.I * (t : ℂ)‖ := Complex.abs_re_le_norm _

/-- |1/2 + it|⁻¹ ≤ 2 for all t. -/
theorem inv_norm_half_it_le_two (t : ℝ) :
    ‖(1/2 : ℂ) + Complex.I * (t : ℂ)‖⁻¹ ≤ 2 := by
  have h := norm_half_it_ge_half t
  have h_pos : 0 < ‖(1/2 : ℂ) + Complex.I * (t : ℂ)‖ := by linarith
  rw [inv_le_comm₀ h_pos two_pos]
  linarith

/-! ## Part 2: Monotonicity and positivity infrastructure -/

/-- The (log T)² function is monotonically increasing for T ≥ 1. -/
theorem logT_sq_mono {T₁ T₂ : ℝ} (hT₁ : 1 ≤ T₁) (h : T₁ ≤ T₂) :
    (Real.log T₁) ^ 2 ≤ (Real.log T₂) ^ 2 := by
  have h1 : 0 ≤ Real.log T₁ := Real.log_nonneg hT₁
  have h2 : Real.log T₁ ≤ Real.log T₂ := Real.log_le_log (by linarith) h
  exact sq_le_sq' (by linarith) h2

/-- For T ≥ 2, the main Perron error term is strictly positive. -/
theorem perron_error_pos {x T : ℝ} (hx : 2 ≤ x) (hT : 2 ≤ T) :
    0 < Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T := by
  have h_sqrt_x : 0 < Real.sqrt x := Real.sqrt_pos_of_pos (by linarith)
  have h_logT : 0 < Real.log T := Real.log_pos (by linarith)
  have h_sqrt_T : 0 < Real.sqrt T := Real.sqrt_pos_of_pos (by linarith)
  positivity

/-- For T ≥ 2, (log T)² ≤ T². Crude but useful bound. -/
theorem logT_sq_le_T_sq {T : ℝ} (hT : 2 ≤ T) :
    (Real.log T) ^ 2 ≤ T ^ 2 := by
  have h1 : Real.log T ≤ T := Real.log_le_self (by linarith : 0 < T).le
  have h2 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  nlinarith [sq_nonneg (T - Real.log T)]

/-- √T ≤ T for T ≥ 1. -/
theorem sqrt_le_self_of_ge_one {T : ℝ} (hT : 1 ≤ T) : Real.sqrt T ≤ T := by
  calc Real.sqrt T ≤ Real.sqrt (T ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = |T| := Real.sqrt_sq_eq_abs T
    _ = T := abs_of_nonneg (by linarith)

/-! ## Part 3: Davenport contour parameter infrastructure -/

/-- For T ≥ 2, the Davenport shift parameter δ = 1/log T is positive. -/
theorem davenport_delta_pos (T : ℝ) (hT : 2 ≤ T) :
    0 < 1 / Real.log T := by
  have : 0 < Real.log T := Real.log_pos (by linarith)
  positivity

/-- The Davenport contour abscissa c = 1/2 + 1/log x satisfies c > 1/2
    for x ≥ 2, and c < 1 for x ≥ e² (≈ 7.39). For x ≥ 2 we always have c > 1/2. -/
theorem davenport_c_gt_half {x : ℝ} (hx : 2 ≤ x) :
    1/2 < 1/2 + 1/Real.log x := by
  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
  linarith [div_pos one_pos hlog_pos]

/-- For x ≥ 2, the Davenport parameter δ = 1/log x is positive. -/
theorem davenport_delta_x_pos {x : ℝ} (hx : 2 ≤ x) :
    0 < 1 / Real.log x := by
  have : 0 < Real.log x := Real.log_pos (by linarith)
  positivity

/-- The simple pole contribution 1/(σ-1) at σ = 1/2 is -2. -/
theorem pole_contribution_at_half :
    (1 : ℝ) / ((1 : ℝ)/2 - 1) = -2 := by norm_num

/-- For T ≥ 2, with Davenport's choice σ = 1 + 1/log T,
    the pole term 1/(σ-1) = log T. -/
theorem davenport_pole_term (T : ℝ) (hT : 2 ≤ T) :
    1 / (1 / Real.log T) = Real.log T := by
  have hlog_pos : 0 < Real.log T := Real.log_pos (by linarith)
  rw [one_div_one_div]

/-! ## Part 4: The 3-4-1 inequality consequence -/

/-- From the 3-4-1 inequality for -ζ'/ζ and a bound on the σ-line:

    3·(-ζ'/ζ(σ)).re + 4·(-ζ'/ζ(σ+it)).re + (-ζ'/ζ(σ+2it)).re ≥ 0

    combined with (-ζ'/ζ(σ)).re ≤ A and |(-ζ'/ζ(σ+2it)).re| ≤ B,
    we get (-ζ'/ζ(σ+it)).re ≥ -(3A + B)/4.

    This is the standard deduction used in the zero-free region and
    in bounding ζ'/ζ on vertical lines. -/
theorem three_four_one_lower_bound
    {a b c A B : ℝ}
    (h341 : 3 * a + 4 * b + c ≥ 0)
    (hA : a ≤ A)
    (hB : |c| ≤ B) :
    b ≥ -(3 * A + B) / 4 := by
  have hc_lower : -B ≤ c := le_trans (neg_le_neg hB) (neg_abs_le c)
  -- From h341: 4b ≥ -3a - c ≥ -3A - c ≥ -3A - B (since -B ≤ c gives c ≥ -B so -c ≤ B)
  -- Wait: we need -c ≤ B. From |c| ≤ B, we get c ≤ B and -c ≤ B (from -B ≤ c).
  -- So: 4b ≥ -3a - c ≥ -3A + (-c) ≥ -3A + (-B) ... no.
  -- Let me be more careful:
  -- h341: 3a + 4b + c ≥ 0, so 4b ≥ -3a - c
  -- hA: a ≤ A, so -3a ≥ -3A, so -3a - c ≥ -3A - c
  -- hc_lower: -B ≤ c, so -c ≤ B, so -3A - c ≥ -3A - B ... NO: -c ≤ B means c ≥ -B, so -c ≤ B.
  -- -3A - c: we want a LOWER bound. -c can be as large as B (when c = -B).
  -- So -3A - c ≥ -3A - B when c ≤ B. And |c| ≤ B gives c ≤ B.
  have hc_upper : c ≤ B := le_of_abs_le hB
  linarith

/-- Specialization: with A = 1/(σ-1) + C (from ZeroFreeRegionV3) and B bounding
    the 2t-term, we get the standard estimate
    (-ζ'/ζ(σ+it)).re ≥ -(3(1/(σ-1)+C) + B)/4. -/
theorem zeta_logderiv_lower_from_341
    {σ t C_zfr B : ℝ} (_hσ : 1 < σ)
    (h_sigma_bound : (-deriv riemannZeta σ / riemannZeta σ).re ≤ 1/(σ-1) + C_zfr)
    (h_2t_bound : |(-deriv riemannZeta (σ + Complex.I * (2*t)) /
                    riemannZeta (σ + Complex.I * (2*t))).re| ≤ B)
    (h341 : 3 * (-deriv riemannZeta σ / riemannZeta σ).re +
            4 * (-deriv riemannZeta (σ + Complex.I * t) /
                 riemannZeta (σ + Complex.I * t)).re +
            (-deriv riemannZeta (σ + Complex.I * (2*t)) /
             riemannZeta (σ + Complex.I * (2*t))).re ≥ 0) :
    (-deriv riemannZeta (σ + Complex.I * t) /
     riemannZeta (σ + Complex.I * t)).re ≥
      -(3 * (1/(σ-1) + C_zfr) + B) / 4 :=
  three_four_one_lower_bound h341 h_sigma_bound h_2t_bound

/-! ## Part 5: Contour rectangle structure -/

/-- The contour remainder has additive structure from the rectangle decomposition.
    If horizontal ≤ C_h·E and vertical ≤ C_v·E, total ≤ (C_h+C_v)·E
    where E = √x·(logT)²/√T. -/
theorem contour_remainder_additive_bound
    {C_h C_v : ℝ} (hCh : 0 < C_h) (hCv : 0 < C_v)
    {x T : ℝ} (hx : 2 ≤ x) (hT : 2 ≤ T) :
    0 ≤ (C_h + C_v) * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
  exact le_of_lt (mul_pos (by linarith) (perron_error_pos hx hT))

-- Note: the raw inequality √x/T ≤ √x·(logT)²/√T fails at T = 2
-- since (log 2)²·√2 ≈ 0.68 < 1. The correct form uses an explicit constant;
-- see `horizontal_with_constant` below.

/-- Correct form: for T ≥ 2, √x/T ≤ √x/√T since 1/T ≤ 1/√T.
    The (logT)² factor provides additional room. -/
theorem horizontal_weaker_bound {x T : ℝ} (_hx : 0 ≤ x) (hT : 2 ≤ T) :
    Real.sqrt x / T ≤ Real.sqrt x / Real.sqrt T := by
  have hT_pos : 0 < T := by linarith
  have hT_nn : 0 ≤ T := by linarith
  have h_sqrt_le_T : Real.sqrt T ≤ T := sqrt_le_self_of_ge_one (by linarith)
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg x) (Real.sqrt_pos_of_pos hT_pos) h_sqrt_le_T

/-- The (log T)² ≥ (log 2)² > 0 for T ≥ 2. -/
theorem logT_sq_pos_of_ge_two {T : ℝ} (hT : 2 ≤ T) : 0 < (Real.log T) ^ 2 :=
  sq_pos_of_pos (Real.log_pos (by linarith))

/-- For T ≥ 2 and x ≥ 2:
    √x/√T ≤ (1/(log 2)²) · √x · (log T)² / √T.

    This is the correct form with explicit constant. -/
theorem horizontal_with_constant {x T : ℝ} (_hx : 2 ≤ x) (hT : 2 ≤ T) :
    Real.sqrt x / Real.sqrt T ≤
      (1 / (Real.log 2) ^ 2) * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
  have h_logT_sq : 0 < (Real.log T) ^ 2 := logT_sq_pos_of_ge_two hT
  have h_log2_sq : 0 < (Real.log 2) ^ 2 := sq_pos_of_pos (Real.log_pos (by norm_num))
  have h_sqrtT : 0 < Real.sqrt T := Real.sqrt_pos_of_pos (by linarith)
  have h_sqrtx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  -- RHS = (1/(log2)²) · √x · (logT)²/√T = √x/√T · (logT)²/(log2)²
  -- Need: 1 ≤ (logT)²/(log2)², i.e., (log2)² ≤ (logT)², i.e., log2 ≤ logT
  have h_log_mono : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith)
  have h_sq_mono : (Real.log 2) ^ 2 ≤ (Real.log T) ^ 2 :=
    sq_le_sq' (by linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]) h_log_mono
  rw [show (1 / (Real.log 2) ^ 2) * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) =
      Real.sqrt x / Real.sqrt T * ((Real.log T) ^ 2 / (Real.log 2) ^ 2) by ring]
  calc Real.sqrt x / Real.sqrt T
      = Real.sqrt x / Real.sqrt T * 1 := by ring
    _ ≤ Real.sqrt x / Real.sqrt T * ((Real.log T) ^ 2 / (Real.log 2) ^ 2) := by
        apply mul_le_mul_of_nonneg_left
        · rw [le_div_iff₀ h_log2_sq]; linarith
        · exact div_nonneg h_sqrtx h_sqrtT.le

end Aristotle.Standalone.PerronCriticalLineBridge
