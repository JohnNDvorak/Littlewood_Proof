/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Littlewood.Development.PowerLemmas
import Littlewood.Development.SumLemmas
import Mathlib.NumberTheory.LSeries.Basic

/-!
# LSeries Term Properties

Properties of individual terms a(n) * n^(-s) in L-series for real s.

## Main Results

* `lseries_term_real` : Each term of LSeries with real coefficients has zero imaginary part for real s
* `lseries_term_nonneg` : Each term has non-negative real part when coefficient is non-negative
-/

open Complex Real

namespace Littlewood.Development.LSeriesTerms

/-- A single LSeries term a(n) * n^(-σ) is real when a is real and σ is real -/
theorem lseries_term_im_zero (a : ℝ) (n : ℕ) (hn : n ≠ 0) (σ : ℝ) :
    ((a : ℂ) * (n : ℂ) ^ (-(σ : ℂ))).im = 0 := by
  have him : ((n : ℂ) ^ (-(σ : ℂ))).im = 0 := PowerLemmas.cpow_neg_real_im_zero n hn σ
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, him, mul_zero, zero_mul, add_zero]

/-- A single LSeries term a(n) * n^(-σ) has non-negative real part when a ≥ 0, σ > 0 -/
theorem lseries_term_re_nonneg (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hn : n ≠ 0) (σ : ℝ) (_hσ : 0 < σ) :
    0 ≤ ((a : ℂ) * (n : ℂ) ^ (-(σ : ℂ))).re := by
  have hre : ((n : ℂ) ^ (-(σ : ℂ))).re = (n : ℝ) ^ (-σ) := PowerLemmas.cpow_neg_real_eq_rpow n hn σ
  have him : ((n : ℂ) ^ (-(σ : ℂ))).im = 0 := PowerLemmas.cpow_neg_real_im_zero n hn σ
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, him, mul_zero, sub_zero, hre]
  apply mul_nonneg ha
  exact le_of_lt (PowerLemmas.rpow_neg_real_pos n hn σ)

/-- The LSeries term function for real coefficients -/
noncomputable def lseriesTerm (a : ℕ → ℝ) (σ : ℝ) (n : ℕ) : ℂ :=
  (a n : ℂ) * (n : ℂ) ^ (-(σ : ℂ))

/-- Each term of the LSeries summand has zero imaginary part for real σ -/
theorem lseries_summand_im_zero (a : ℕ → ℝ) (σ : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (lseriesTerm a σ n).im = 0 := lseries_term_im_zero (a n) n hn σ

/-- Each term of the LSeries summand has non-negative real part when coefficients are non-negative -/
theorem lseries_summand_re_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : n ≠ 0) :
    0 ≤ (lseriesTerm a σ n).re := lseries_term_re_nonneg (a n) (ha n) n hn σ hσ

/-- The real part of an LSeries term equals a * n^(-σ) as real numbers -/
theorem lseries_term_re_eq (a : ℝ) (n : ℕ) (hn : n ≠ 0) (σ : ℝ) :
    ((a : ℂ) * (n : ℂ) ^ (-(σ : ℂ))).re = a * (n : ℝ) ^ (-σ) := by
  have hre : ((n : ℂ) ^ (-(σ : ℂ))).re = (n : ℝ) ^ (-σ) := PowerLemmas.cpow_neg_real_eq_rpow n hn σ
  have him : ((n : ℂ) ^ (-(σ : ℂ))).im = 0 := PowerLemmas.cpow_neg_real_im_zero n hn σ
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, him, mul_zero, sub_zero, hre]

/-- Norm bound: |a * n^(-σ)| = |a| * n^(-σ) for real σ and n > 0 -/
theorem lseries_term_norm (a : ℝ) (n : ℕ) (hn : n ≠ 0) (σ : ℝ) :
    ‖(a : ℂ) * (n : ℂ) ^ (-(σ : ℂ))‖ = |a| * (n : ℝ) ^ (-σ) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hpow : ‖(n : ℂ) ^ (-(σ : ℂ))‖ = (n : ℝ) ^ (-σ) := by
    -- Convert ℕ → ℂ to ℕ → ℝ → ℂ
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) from ofReal_natCast n]
    rw [norm_cpow_eq_rpow_re_of_pos hn_pos]
    simp only [neg_re, ofReal_re]
  rw [norm_mul, hpow, norm_real, Real.norm_eq_abs]

/-- For bounded coefficients |a(n)| ≤ M, term bound |a(n) * n^(-σ)| ≤ M * n^(-σ) -/
theorem lseries_term_bound (a : ℕ → ℝ) (M : ℝ) (hM : ∀ n, |a n| ≤ M)
    (n : ℕ) (hn : n ≠ 0) (σ : ℝ) :
    ‖(a n : ℂ) * (n : ℂ) ^ (-(σ : ℂ))‖ ≤ M * (n : ℝ) ^ (-σ) := by
  rw [lseries_term_norm (a n) n hn σ]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  apply mul_le_mul_of_nonneg_right (hM n)
  exact le_of_lt (Real.rpow_pos_of_pos hn_pos (-σ))

/-- For non-negative bounded coefficients, norm equals term value -/
theorem lseries_term_norm_nonneg (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hn : n ≠ 0) (σ : ℝ) :
    ‖(a : ℂ) * (n : ℂ) ^ (-(σ : ℂ))‖ = a * (n : ℝ) ^ (-σ) := by
  rw [lseries_term_norm a n hn σ, abs_of_nonneg ha]

/-- Term comparison: for σ₁ ≤ σ₂ and n ≥ 1, a * n^(-σ₂) ≤ a * n^(-σ₁) when a ≥ 0 -/
theorem lseries_term_antitone (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hn : 1 ≤ n)
    {σ₁ σ₂ : ℝ} (hσ : σ₁ ≤ σ₂) :
    a * (n : ℝ) ^ (-σ₂) ≤ a * (n : ℝ) ^ (-σ₁) := by
  apply mul_le_mul_of_nonneg_left _ ha
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact Real.rpow_le_rpow_of_exponent_le hn' (neg_le_neg hσ)

end Littlewood.Development.LSeriesTerms
