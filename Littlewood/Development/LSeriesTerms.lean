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

end Littlewood.Development.LSeriesTerms
