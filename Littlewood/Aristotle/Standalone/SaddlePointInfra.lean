/-
Infrastructure for the pointwise saddle-point bound (siegel_expansion_core conjunct 1).

The saddle-point approximation on block k gives:
  ErrorTerm(t) ≈ (-1)^k · (2π/t)^{1/4} · Ψ(blockParam k t)
with error O(t^{-3/4}).

This file provides:
- rpow exponent arithmetic for combining (2π/t)^{1/4} · t^{-1/2} = (2π)^{1/4} · t^{-3/4}
- Block parameter bounds
- Absolute value through (-1)^k
- Remainder term structure lemmas

SORRY COUNT: 0

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace SaddlePointInfra

open Real

-- ============================================================
-- Part 1: rpow exponent arithmetic
-- ============================================================

/-- t^{-1/4} · t^{-1/2} = t^{-3/4} for t > 0. -/
theorem rpow_neg_quarter_neg_half (t : ℝ) (ht : 0 < t) :
    t ^ (-(1 : ℝ) / 4) * t ^ (-(1 : ℝ) / 2) = t ^ (-(3 : ℝ) / 4) := by
  rw [← rpow_add ht]; congr 1; norm_num

/-- t^{-1/2} · t^{-1/4} = t^{-3/4} for t > 0. -/
theorem rpow_neg_half_neg_quarter (t : ℝ) (ht : 0 < t) :
    t ^ (-(1 : ℝ) / 2) * t ^ (-(1 : ℝ) / 4) = t ^ (-(3 : ℝ) / 4) := by
  rw [mul_comm]; exact rpow_neg_quarter_neg_half t ht

/-- t^{-3/4} > 0 for t > 0. -/
theorem rpow_neg_three_quarter_pos (t : ℝ) (ht : 0 < t) :
    0 < t ^ (-(3 : ℝ) / 4) :=
  rpow_pos_of_pos ht _

/-- t^{-3/4} ≤ 1 for t ≥ 1. -/
theorem rpow_neg_three_quarter_le_one (t : ℝ) (ht : 1 ≤ t) :
    t ^ (-(3 : ℝ) / 4) ≤ 1 := by
  calc t ^ (-(3 : ℝ) / 4) ≤ 1 ^ (-(3 : ℝ) / 4) :=
    rpow_le_rpow_of_nonpos (by linarith) ht (by norm_num)
    _ = 1 := one_rpow _

/-- t^{-3/4} is antitone on (0, ∞): for a ≤ b with 0 < a,
    b^{-3/4} ≤ a^{-3/4}. -/
theorem rpow_neg_three_quarter_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b ^ (-(3 : ℝ) / 4) ≤ a ^ (-(3 : ℝ) / 4) := by
  exact rpow_le_rpow_of_nonpos (by linarith) hab (by norm_num)

-- ============================================================
-- Part 2: Absolute value through sign
-- ============================================================

/-- |(-1)^k · x| = |x| for any x. -/
theorem abs_neg_one_pow_mul_eq (k : ℕ) (x : ℝ) :
    |(-1 : ℝ) ^ k * x| = |x| := by
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- (-1)^k · (-1)^k = 1. -/
theorem neg_one_pow_sq_eq_one (k : ℕ) : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
  rw [← pow_add]; exact Even.neg_one_pow ⟨k, by omega⟩

/-- |A - B| ≤ |A - C| + |C - B|: triangle for differences. -/
theorem abs_diff_triangle (A B C : ℝ) :
    |A - B| ≤ |A - C| + |C - B| := by
  have h : A - B = (A - C) + (C - B) := by ring
  rw [h]; exact abs_add_le _ _

-- ============================================================
-- Part 3: Remainder absorbs into constant
-- ============================================================

/-- If |r₁| ≤ C₁·t^{-3/4} and |r₂| ≤ C₂·t^{-3/4},
    then |r₁ + r₂| ≤ (C₁+C₂)·t^{-3/4}. -/
theorem remainder_absorb_sum (C₁ C₂ t r₁ r₂ : ℝ) (ht : 0 < t)
    (h₁ : |r₁| ≤ C₁ * t ^ (-(3 : ℝ) / 4))
    (h₂ : |r₂| ≤ C₂ * t ^ (-(3 : ℝ) / 4)) :
    |r₁ + r₂| ≤ (C₁ + C₂) * t ^ (-(3 : ℝ) / 4) := by
  calc |r₁ + r₂| ≤ |r₁| + |r₂| := abs_add_le _ _
    _ ≤ C₁ * t ^ (-(3 : ℝ) / 4) + C₂ * t ^ (-(3 : ℝ) / 4) := add_le_add h₁ h₂
    _ = (C₁ + C₂) * t ^ (-(3 : ℝ) / 4) := by ring

/-- Scaling: if |r| ≤ C·t^{-3/4} and 0 ≤ A,
    then |A · r| ≤ (A · C)·t^{-3/4}. -/
theorem remainder_scale (A C t r : ℝ) (_ht : 0 < t) (hA : 0 ≤ A)
    (hr : |r| ≤ C * t ^ (-(3 : ℝ) / 4)) :
    |A * r| ≤ (A * C) * t ^ (-(3 : ℝ) / 4) := by
  rw [abs_mul, abs_of_nonneg hA]
  calc A * |r| ≤ A * (C * t ^ (-(3 : ℝ) / 4)) :=
    mul_le_mul_of_nonneg_left hr hA
    _ = (A * C) * t ^ (-(3 : ℝ) / 4) := by ring

-- ============================================================
-- Part 4: Amplitude bounds
-- ============================================================

/-- (2π/t)^{1/4} ≤ 1 for t ≥ 2π. -/
theorem quarter_pow_le_one (t : ℝ) (ht : 2 * Real.pi ≤ t) :
    (2 * Real.pi / t) ^ ((1 : ℝ) / 4) ≤ 1 := by
  have ht_pos : 0 < t := lt_of_lt_of_le (by positivity) ht
  have h_ratio : 2 * Real.pi / t ≤ 1 := by
    rw [div_le_one₀ ht_pos]; exact ht
  calc (2 * Real.pi / t) ^ ((1 : ℝ) / 4)
      ≤ 1 ^ ((1 : ℝ) / 4) :=
        rpow_le_rpow (div_nonneg (by positivity) ht_pos.le) h_ratio (by norm_num)
    _ = 1 := one_rpow _

/-- (2π/t)^{1/4} ≥ 0 for t > 0. -/
theorem quarter_pow_nonneg (t : ℝ) (ht : 0 < t) :
    0 ≤ (2 * Real.pi / t) ^ ((1 : ℝ) / 4) :=
  rpow_nonneg (div_nonneg (by positivity) ht.le) _

/-- cos perturbation: |cos(α+δ) - cos(α)| ≤ |δ|.
    Proof: cos is 1-Lipschitz. -/
theorem cos_perturb_bound (α δ : ℝ) :
    |Real.cos (α + δ) - Real.cos α| ≤ |δ| := by
  have h := @LipschitzWith.dist_le_mul ℝ ℝ _ _ 1 Real.cos Real.lipschitzWith_cos (α + δ) α
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
  rwa [show α + δ - α = δ from by ring] at h

end SaddlePointInfra
