/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Littlewood.Development.PowerLemmas
import Littlewood.Development.SumLemmas

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

/-- Each term of LSeries.term has non-negative real part for non-negative real coefficients -/
theorem lseries_term_re_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (σ : ℝ) (_hσ : 0 < σ) (n : ℕ) :
    0 ≤ (LSeries.term (fun n => (a n : ℂ)) σ n).re := by
  simp only [LSeries.term]
  split_ifs with hn
  · simp
  · -- a(n) / n^σ for n ≠ 0
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hne : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hn_pos)
    -- Key: (n : ℂ)^(σ : ℂ) is a positive real for real n > 0 and real σ
    have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := (ofReal_log hn_pos.le).symm
    have hpow_real : (n : ℂ) ^ (σ : ℂ) = ((n : ℝ) ^ σ : ℝ) := by
      simp only [cpow_def_of_ne_zero hne, hlog]
      have h1 : (Real.log (n : ℝ) : ℂ) * (σ : ℂ) = ((Real.log n * σ) : ℝ) := by simp only [ofReal_mul]
      rw [h1, ← ofReal_exp, Real.rpow_def_of_pos hn_pos]
    rw [hpow_real]
    have hpow_pos : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hn_pos σ
    rw [div_ofReal (a n) ((n : ℝ) ^ σ)]
    simp only [ofReal_re]
    exact div_nonneg (ha n) (le_of_lt hpow_pos)

/-- L-series with non-negative real coefficients has non-negative real part for real σ > 1,
assuming the series is summable. -/
theorem lseries_nonneg_coeff_re_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (σ : ℝ) (hσ : 1 < σ)
    (hsumm : LSeriesSummable (fun n => (a n : ℂ)) σ) :
    0 ≤ (LSeries (fun n => (a n : ℂ)) σ).re := by
  unfold LSeries
  have h_re : ∀ n, 0 ≤ (LSeries.term (fun n => (a n : ℂ)) σ n).re :=
    lseries_term_re_nonneg a ha σ (by linarith : 0 < σ)
  rw [Complex.re_tsum]
  · exact tsum_nonneg h_re
  · -- Summability from hypothesis
    exact hsumm

end Littlewood.Development.DirichletReal
