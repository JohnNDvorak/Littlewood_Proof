/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Sum Lemmas for Non-negative Complex Numbers

Properties of infinite sums of complex numbers with non-negative real parts.

## Main Results

* `tsum_re_nonneg` : tsum of complex numbers with non-negative real parts has non-negative real part
* `tsum_re_eq_tsum_of_im_zero` : when all imaginary parts are zero, the real part of tsum is tsum of real parts
-/

open scoped ComplexOrder

namespace Littlewood.Development.SumLemmas

/-- The real part of a tsum of complex numbers with non-negative real parts is non-negative -/
theorem tsum_re_nonneg {f : ℕ → ℂ} (hf : ∀ n, 0 ≤ (f n).re) (hs : Summable f) :
    0 ≤ (∑' n, f n).re := by
  have hre : (∑' n, f n).re = ∑' n, (f n).re := Complex.re_tsum hs
  rw [hre]
  exact tsum_nonneg hf

/-- If all terms have zero imaginary part, the tsum's real part equals the tsum of real parts -/
theorem tsum_re_eq_tsum_re {f : ℕ → ℂ} (hs : Summable f) :
    (∑' n, f n).re = ∑' n, (f n).re := Complex.re_tsum hs

/-- The imaginary part of a tsum equals the tsum of imaginary parts -/
theorem tsum_im_eq_tsum_im {f : ℕ → ℂ} (hs : Summable f) :
    (∑' n, f n).im = ∑' n, (f n).im := Complex.im_tsum hs

/-- If all imaginary parts are zero, the tsum imaginary part is zero -/
theorem tsum_im_zero_of_all_im_zero {f : ℕ → ℂ} (hf : ∀ n, (f n).im = 0) (hs : Summable f) :
    (∑' n, f n).im = 0 := by
  rw [tsum_im_eq_tsum_im hs]
  simp only [hf, tsum_zero]

/-- Combined: tsum of reals (as complex) has non-negative real part when all terms non-negative -/
theorem tsum_real_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable (fun n => (a n : ℂ))) :
    0 ≤ (∑' n, (a n : ℂ)).re := by
  apply tsum_re_nonneg
  · intro n
    simp only [Complex.ofReal_re]
    exact ha n
  · exact hs

end Littlewood.Development.SumLemmas
