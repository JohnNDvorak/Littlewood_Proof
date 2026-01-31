/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Littlewood.Development.PowerLemmas

/-!
# LSeries to Real Tsum Bridge

For real σ > 1 and real coefficients, the complex LSeries has
real part equal to the real tsum.

## Main Results

* `lseries_real_coeff_re` : Real part of LSeries equals real tsum

## Strategy

For real σ and real coefficients a(n):
- Each term a(n) / n^σ is real (both factors real)
- Use re_tsum to extract real parts
- Each term's real part equals the real expression
-/

open Complex Real

namespace Littlewood.Development.LSeriesRealBridge

/-- For n ≠ 0 and real σ, (n : ℂ)^(σ : ℂ) equals (n^σ : ℂ) -/
lemma nat_cpow_eq_rpow (n : ℕ) (hn : n ≠ 0) (σ : ℝ) :
    (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [← ofReal_natCast n, ← ofReal_cpow hn_pos.le σ]

/-- For n ≠ 0 and real σ, the imaginary part of the cpow is zero -/
lemma nat_cpow_im_zero (n : ℕ) (hn : n ≠ 0) (σ : ℝ) :
    ((n : ℂ) ^ (σ : ℂ)).im = 0 := by
  rw [nat_cpow_eq_rpow n hn σ, ofReal_im]

/-- For n ≠ 0 and real σ, the real part of the cpow equals the rpow -/
lemma nat_cpow_re (n : ℕ) (hn : n ≠ 0) (σ : ℝ) :
    ((n : ℂ) ^ (σ : ℂ)).re = (n : ℝ) ^ σ := by
  rw [nat_cpow_eq_rpow n hn σ, ofReal_re]

/-- LSeries.term real part for real coefficients -/
lemma lseries_term_re_real_coeff (a : ℕ → ℝ) (σ : ℝ) (n : ℕ) :
    (LSeries.term (fun k => (a k : ℂ)) (σ : ℂ) n).re =
      if n = 0 then 0 else a n / (n : ℝ) ^ σ := by
  simp only [LSeries.term]
  split_ifs with hn
  · simp
  · -- a(n) / n^σ where both are real
    have hpow := nat_cpow_eq_rpow n hn σ
    simp only [hpow]
    -- (a n : ℂ) / ((n : ℝ)^σ : ℂ) = ((a n / n^σ) : ℂ)
    rw [← ofReal_div, ofReal_re]

/-- The real part of LSeries with real coefficients equals real tsum -/
theorem lseries_real_coeff_re (a : ℕ → ℝ) (σ : ℝ) (hσ : 1 < σ)
    (hs : LSeriesSummable (fun n => (a n : ℂ)) (σ : ℂ)) :
    (LSeries (fun n => (a n : ℂ)) (σ : ℂ)).re = ∑' n, a n / (n : ℝ) ^ σ := by
  unfold LSeries
  rw [re_tsum hs]
  congr 1
  ext n
  rw [lseries_term_re_real_coeff]
  split_ifs with hn
  · simp only [hn, Nat.cast_zero]
    have h0pow : (0 : ℝ) ^ σ = 0 := Real.zero_rpow (by linarith : σ ≠ 0)
    rw [h0pow, div_zero]
  · rfl

/-- Multiplication form: real part of LSeries equals real tsum with negative exponent -/
theorem lseries_real_coeff_re' (a : ℕ → ℝ) (σ : ℝ) (hσ : 1 < σ)
    (hs : LSeriesSummable (fun n => (a n : ℂ)) (σ : ℂ)) :
    (LSeries (fun n => (a n : ℂ)) (σ : ℂ)).re = ∑' n, a n * (n : ℝ) ^ (-σ) := by
  rw [lseries_real_coeff_re a σ hσ hs]
  congr 1
  ext n
  by_cases hn : n = 0
  · simp only [hn, Nat.cast_zero]
    have h0pow : (0 : ℝ) ^ σ = 0 := Real.zero_rpow (by linarith : σ ≠ 0)
    have h0pow' : (0 : ℝ) ^ (-σ) = 0 := Real.zero_rpow (neg_ne_zero.mpr (by linarith : σ ≠ 0))
    rw [h0pow, h0pow', div_zero, mul_zero]
  · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [div_eq_mul_inv, Real.rpow_neg hn_pos.le, inv_eq_one_div]

end Littlewood.Development.LSeriesRealBridge
