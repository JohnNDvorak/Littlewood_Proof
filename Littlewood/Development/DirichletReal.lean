/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real Part Properties of Dirichlet Series

For real σ > 1, L-series with non-negative real coefficients have non-negative real part.
This is fundamental infrastructure for Landau's lemma and related results.

## Main Results

* `cpow_neg_real_im_zero` : n^(-σ) has zero imaginary part for positive n and real σ
* `cpow_neg_real_re_pos` : n^(-σ) has positive real part for n > 0 and σ > 0
* `cpow_neg_real_eq_rpow` : real part of n^(-σ) equals n^(-σ) as real power
* `lseries_nonneg_coeff_re_nonneg` : LSeries with non-negative coefficients has non-negative
  real part for real σ > 1
-/

open Complex Real

namespace Littlewood.Development.DirichletReal

/-! ## Supporting Lemmas -/

/-- For natural n > 0 and real σ, n^(-σ) as a complex power has zero imaginary part -/
theorem cpow_neg_real_im_zero (n : ℕ) (hn : n ≠ 0) (σ : ℝ) :
    ((n : ℂ) ^ (-(σ : ℂ))).im = 0 := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hne : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hn_pos)
  simp only [cpow_def_of_ne_zero hne]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := (ofReal_log hn_pos.le).symm
  rw [hlog]
  have h1 : (Real.log (n : ℝ) : ℂ) * (-(σ : ℂ)) = (-(Real.log n * σ) : ℝ) := by
    simp only [ofReal_neg, ofReal_mul]
    ring
  rw [h1]
  exact exp_ofReal_im _

/-- For natural n > 0 and real σ > 0, n^(-σ) as a complex power has positive real part -/
theorem cpow_neg_real_re_pos (n : ℕ) (hn : n ≠ 0) (σ : ℝ) (hσ : 0 < σ) :
    0 < ((n : ℂ) ^ (-(σ : ℂ))).re := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hne : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hn_pos)
  simp only [cpow_def_of_ne_zero hne]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := (ofReal_log hn_pos.le).symm
  rw [hlog]
  have h1 : (Real.log (n : ℝ) : ℂ) * (-(σ : ℂ)) = (-(Real.log n * σ) : ℝ) := by
    simp only [ofReal_neg, ofReal_mul]
    ring
  rw [h1]
  simp only [exp_ofReal_re]
  exact Real.exp_pos _

/-- The real part of n^(-σ) equals the real power for positive n -/
theorem cpow_neg_real_eq_rpow (n : ℕ) (hn : n ≠ 0) (σ : ℝ) :
    ((n : ℂ) ^ (-(σ : ℂ))).re = (n : ℝ) ^ (-σ) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hne : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hn_pos)
  simp only [cpow_def_of_ne_zero hne]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := (ofReal_log hn_pos.le).symm
  rw [hlog]
  have h1 : (Real.log (n : ℝ) : ℂ) * (-(σ : ℂ)) = (-(Real.log n * σ) : ℝ) := by
    simp only [ofReal_neg, ofReal_mul]
    ring
  rw [h1]
  simp only [exp_ofReal_re]
  rw [Real.rpow_def_of_pos hn_pos]
  ring_nf

/-! ## Main Theorem -/

/-- L-series with non-negative real coefficients has non-negative real part for real σ > 1 -/
theorem lseries_nonneg_coeff_re_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (σ : ℝ) (hσ : 1 < σ) :
    0 ≤ (LSeries (fun n => (a n : ℂ)) σ).re := by
  -- LSeries is ∑ a(n) * n^(-σ)
  -- Each term: a(n) * n^(-σ) is real and non-negative
  -- Sum of non-negatives is non-negative
  unfold LSeries
  -- Need: re of tsum = tsum of re when summable
  -- Then: each term's re is non-negative
  sorry

end Littlewood.Development.DirichletReal
