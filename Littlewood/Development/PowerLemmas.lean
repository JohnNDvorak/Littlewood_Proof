/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Power Function Lemmas for Real Exponents

Properties of n^(-σ) for natural n and real σ, fundamental for Dirichlet series analysis.

## Main Results

* `rpow_neg_real_pos` : n^(-σ) > 0 for n ≠ 0
* `cpow_neg_real_eq_rpow` : complex power with real exponent equals real power
* `cpow_neg_real_im_zero` : imaginary part is zero
-/

open Complex Real

namespace Littlewood.Development.PowerLemmas

/-- For natural n > 0 and real σ, the real power n^(-σ) is positive -/
theorem rpow_neg_real_pos (n : ℕ) (hn : n ≠ 0) (σ : ℝ) : 0 < (n : ℝ) ^ (-σ) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  exact Real.rpow_pos_of_pos hn_pos (-σ)

/-- For natural n > 0 and real σ, the complex power n^(-σ) equals the real power -/
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

/-- For natural n > 0 and real σ, the imaginary part of n^(-σ) is zero -/
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

/-- Complex power with real base and exponent is real -/
theorem cpow_real_base_real_exp_is_real (x : ℝ) (hx : 0 < x) (y : ℝ) :
    ((x : ℂ) ^ (y : ℂ)).im = 0 := by
  have hne : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
  simp only [cpow_def_of_ne_zero hne]
  have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) := (ofReal_log hx.le).symm
  rw [hlog]
  have h1 : (Real.log x : ℂ) * (y : ℂ) = ((Real.log x * y) : ℝ) := by
    simp only [ofReal_mul]
  rw [h1]
  exact exp_ofReal_im _

/-- Complex power with real base and exponent equals real power -/
theorem cpow_real_base_real_exp_eq_rpow (x : ℝ) (hx : 0 < x) (y : ℝ) :
    ((x : ℂ) ^ (y : ℂ)).re = x ^ y := by
  have hne : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
  simp only [cpow_def_of_ne_zero hne]
  have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) := (ofReal_log hx.le).symm
  rw [hlog]
  have h1 : (Real.log x : ℂ) * (y : ℂ) = ((Real.log x * y) : ℝ) := by
    simp only [ofReal_mul]
  rw [h1]
  simp only [exp_ofReal_re]
  rw [Real.rpow_def_of_pos hx]

end Littlewood.Development.PowerLemmas
