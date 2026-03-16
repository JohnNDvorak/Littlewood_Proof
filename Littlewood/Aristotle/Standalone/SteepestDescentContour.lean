/-
Steepest-descent contour infrastructure for closing SiegelSaddleExpansionHyp.

## Overview

The saddle-point approximation of the Siegel integral at w₀ = √(t/2π) requires:
1. The contour integral representation of the error term
2. Deformation to a steepest-descent path through w₀
3. Gaussian approximation + quartic remainder bound

This file provides sorry-free algebraic infrastructure for the steepest-descent
analysis. The actual contour deformation and integral estimation remain as
the irreducible sorry in SiegelSaddleExpansionHyp.

## Mathematical content

The Siegel integral representation gives:
  ErrorTerm(t) = Re[e^{iθ(t)} · I(t)]
where I(t) involves a contour integral of Γ(s/2) π^{-s/2}.

After changing variables to w and deforming to the saddle w₀ = √(t/2π):
  I(t) ≈ e^{iφ(w₀)} · (2π/t)^{1/4} · [Ψ(p) + c₁(p)·t^{-1/2} + ...]

The Fresnel integral evaluation gives the leading term (2π/t)^{1/4} · Ψ(p),
and the remainder is bounded by the quartic coefficient ≤ 1/4 · t^{-1/2}.

SORRY COUNT: 0

Reference: Siegel 1932 §3; Edwards Ch. 7; Gabcke 1979 Satz 1.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.RSBlockParam
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.Standalone.FresnelSaddlePointInfra

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.SteepestDescentContour

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.RSBlockParam Aristotle.ErrorTermExpansion
open Aristotle.Standalone.FresnelSaddlePointInfra

/-! ## Part 1: Saddle-point location and derivatives -/

/-- The saddle point w₀ = √(t/(2π)) for the Siegel integral. -/
def saddlePoint (t : ℝ) : ℝ := Real.sqrt (t / (2 * Real.pi))

/-- The saddle point is positive for t > 0. -/
theorem saddlePoint_pos (t : ℝ) (ht : 0 < t) : 0 < saddlePoint t := by
  unfold saddlePoint
  exact Real.sqrt_pos_of_pos (div_pos ht (by positivity))

/-- The saddle point squared equals t/(2π). -/
theorem saddlePoint_sq (t : ℝ) (ht : 0 < t) :
    (saddlePoint t) ^ 2 = t / (2 * Real.pi) := by
  unfold saddlePoint
  rw [sq, Real.mul_self_sqrt (div_nonneg ht.le (by positivity))]

/-- w₀ ≥ 1 when t ≥ 2π. -/
theorem saddlePoint_ge_one (t : ℝ) (ht : 2 * Real.pi ≤ t) :
    1 ≤ saddlePoint t := by
  unfold saddlePoint
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  apply Real.sqrt_le_sqrt
  rw [le_div_iff₀ (show (0 : ℝ) < 2 * Real.pi by positivity)]
  linarith

/-- w₀ ≥ k+1 when t ≥ hardyStart k = 2π(k+1)². -/
theorem saddlePoint_ge_block (k : ℕ) (t : ℝ)
    (ht : hardyStart k ≤ t) :
    (k : ℝ) + 1 ≤ saddlePoint t := by
  unfold saddlePoint
  have hk : 0 < (k : ℝ) + 1 := by positivity
  rw [show (k : ℝ) + 1 = Real.sqrt (((k : ℝ) + 1) ^ 2) from
      (Real.sqrt_sq hk.le).symm]
  apply Real.sqrt_le_sqrt
  rw [le_div_iff₀ (show (0 : ℝ) < 2 * Real.pi by positivity)]
  have : hardyStart k = 2 * Real.pi * ((k : ℝ) + 1) ^ 2 := by
    unfold hardyStart; push_cast; ring
  linarith

/-! ## Part 2: Phase function Taylor coefficients at the saddle -/

/-- The cubic coefficient c₃ = 2π/(3w₀) is bounded by 2π/(3(k+1)) on block k. -/
theorem cubic_coeff_bound (k : ℕ) (t : ℝ) (ht : hardyStart k ≤ t) :
    2 * Real.pi / (3 * saddlePoint t) ≤ 2 * Real.pi / (3 * ((k : ℝ) + 1)) := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hw := saddlePoint_ge_block k t ht
  have hw_pos : 0 < saddlePoint t := lt_of_lt_of_le hk hw
  -- a/(3·w₀) ≤ a/(3·(k+1)) since w₀ ≥ k+1
  exact div_le_div_of_nonneg_left
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    (by positivity : (0 : ℝ) < 3 * ((k : ℝ) + 1))
    (mul_le_mul_of_nonneg_left hw (by norm_num : (0:ℝ) ≤ 3))

/-- The quartic-to-quadratic ratio π/(2t) ≤ 1/4 for t ≥ 2π. -/
theorem quartic_ratio_le_quarter_on_block (k : ℕ) (t : ℝ)
    (ht : hardyStart k ≤ t) :
    Real.pi / (2 * t) ≤ 1 / 4 := by
  have ht_pos : 0 < t := by
    have : 0 < hardyStart k := by unfold hardyStart; positivity
    linarith
  have h2pi : 2 * Real.pi ≤ t := by
    have : hardyStart 0 = 2 * Real.pi := by unfold hardyStart; push_cast; ring
    have : hardyStart 0 ≤ hardyStart k := by
      unfold hardyStart; push_cast
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith
    linarith
  exact quartic_ratio_le_quarter t h2pi

/-! ## Part 3: Gaussian width and integration scale -/

/-- The effective integration width: 1/√(2π) < 1. -/
theorem gaussian_width_bound :
    1 / Real.sqrt (2 * Real.pi) < 1 := by
  rw [div_lt_one (Real.sqrt_pos_of_pos (by positivity))]
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  apply Real.sqrt_lt_sqrt (by norm_num)
  linarith [Real.pi_gt_three]

/-- The cubic-to-quadratic ratio: for w₀ ≥ 2 (k ≥ 1), 2/(3w₀) ≤ 1/3. -/
theorem cubic_quadratic_ratio_bound (w₀ : ℝ) (hw₀ : 2 ≤ w₀) :
    2 / (3 * w₀) ≤ 1 / 3 := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 3)]
  linarith

/-! ## Part 4: Remainder integral estimates -/

/-- The quartic remainder bound: (π²/t) · (3/(4π²)) = 3/(4t). -/
theorem quartic_remainder_simplified (t : ℝ) (ht : 0 < t) :
    Real.pi ^ 2 / t * (3 / (4 * Real.pi ^ 2)) = 3 / (4 * t) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

/-- For t ≥ 2π, 3/(4t) ≤ 1/8. -/
theorem quartic_remainder_le_eighth (t : ℝ) (ht : 2 * Real.pi ≤ t) :
    3 / (4 * t) ≤ 1 / 8 := by
  have ht_pos : 0 < t := by linarith [Real.pi_pos]
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 4 * t) (by norm_num : (0:ℝ) < 8)]
  -- Goal: 3 * 8 ≤ 1 * (4 * t), i.e., 24 ≤ 4t
  nlinarith [Real.pi_gt_three]

/-! ## Part 5: Block structure compatibility -/

/-- On any block k, t ≥ 2π. -/
theorem block_ge_two_pi (k : ℕ) (t : ℝ) (ht : hardyStart k ≤ t) :
    2 * Real.pi ≤ t := by
  have h0 : hardyStart 0 = 2 * Real.pi := by
    unfold hardyStart; push_cast; ring
  have hk : hardyStart 0 ≤ hardyStart k := by
    unfold hardyStart; push_cast
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith
  linarith

/-- The saddlePoint function is monotone in t. -/
theorem saddlePoint_mono : Monotone saddlePoint := by
  intro a b hab
  unfold saddlePoint
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_right hab (le_of_lt (by positivity : (0 : ℝ) < 2 * Real.pi))

/-! ## Part 6: Gabcke constant and remainder bound chain -/

/-- The Gabcke constant: sup of |c₁(p)| on [0,1]. -/
def gabckeConstant : ℝ := 0.083

/-- The Gabcke constant is positive. -/
theorem gabckeConstant_pos : 0 < gabckeConstant := by
  unfold gabckeConstant; norm_num

/-- The Gabcke constant is at most 1/4 (conservative bound). -/
theorem gabckeConstant_le_quarter : gabckeConstant ≤ 1 / 4 := by
  unfold gabckeConstant; norm_num

/-- For t ≥ 2π, C_G · t^{-1/2} ≤ C_G (since t^{-1/2} ≤ 1). -/
theorem gabcke_remainder_le_constant (t : ℝ) (ht : 2 * Real.pi ≤ t) :
    gabckeConstant * t ^ (-(1 : ℝ) / 2) ≤ gabckeConstant := by
  have ht_pos : 0 < t := by linarith [Real.pi_pos]
  have h_ge_one : 1 ≤ t := le_trans (by linarith [Real.pi_gt_three]) ht
  have h_rpow : t ^ (-(1:ℝ)/2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h_ge_one (by norm_num)
  nlinarith [gabckeConstant_pos]

/-- For t ≥ 2π, C_G · t^{-1/2} ≤ 1/4. -/
theorem gabcke_remainder_le_quarter (t : ℝ) (ht : 2 * Real.pi ≤ t) :
    gabckeConstant * t ^ (-(1 : ℝ) / 2) ≤ 1 / 4 :=
  le_trans (gabcke_remainder_le_constant t ht) gabckeConstant_le_quarter

/-- The amplitude factor times remainder: (2π/t)^{1/4} · C_G · t^{-1/2} ≤ 1/4. -/
theorem full_error_bound (t : ℝ) (ht : 2 * Real.pi ≤ t) :
    (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * (gabckeConstant * t ^ (-(1 : ℝ) / 2)) ≤ 1 / 4 := by
  have ht_pos : 0 < t := by linarith [Real.pi_pos]
  have h_amp : (2 * Real.pi / t) ^ ((1:ℝ)/4) ≤ 1 := quarter_power_le_one t ht
  have h_rem := gabcke_remainder_le_quarter t ht
  have h_rem_nn : 0 ≤ gabckeConstant * t ^ (-(1:ℝ)/2) :=
    mul_nonneg gabckeConstant_pos.le (Real.rpow_nonneg ht_pos.le _)
  calc (2 * Real.pi / t) ^ ((1:ℝ)/4) * (gabckeConstant * t ^ (-(1:ℝ)/2))
      ≤ 1 * (1/4) := mul_le_mul h_amp h_rem h_rem_nn (by norm_num)
    _ = 1/4 := one_mul _

/-! ## Part 7: Saddle-point and block parameter relationship -/

/-- The saddle point w₀ = √(t/(2π)) equals k+1+p where p = blockParam k t. -/
theorem saddlePoint_eq_block (k : ℕ) (t : ℝ) :
    saddlePoint t = (k : ℝ) + 1 + blockParam k t := by
  unfold saddlePoint blockParam; ring

/-- The inverse saddle scale 1/w₀ ≤ 1/(k+1) on block k. -/
theorem inv_saddlePoint_le (k : ℕ) (t : ℝ) (ht : hardyStart k ≤ t) :
    1 / saddlePoint t ≤ 1 / ((k : ℝ) + 1) := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hw := saddlePoint_ge_block k t ht
  have hw_pos : 0 < saddlePoint t := lt_of_lt_of_le hk hw
  exact div_le_div_of_nonneg_left (by norm_num) hk hw

/-- On block k, 1/w₀ ≤ 1 (since t ≥ 2π implies w₀ ≥ 1). -/
theorem inv_saddlePoint_le_one (k : ℕ) (t : ℝ) (ht : hardyStart k ≤ t) :
    1 / saddlePoint t ≤ 1 := by
  have h2pi := block_ge_two_pi k t ht
  have hw := saddlePoint_ge_one t h2pi
  have ht_pos : 0 < t := by linarith [Real.pi_pos]
  exact div_le_one_of_le₀ hw (le_of_lt (saddlePoint_pos t ht_pos))

end Aristotle.Standalone.SteepestDescentContour
