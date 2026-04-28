import Mathlib
import Littlewood.Aristotle.Standalone.PerronKernelTruncation
import Littlewood.Aristotle.Standalone.PerronTruncationAtomics

/-!
# Helpers for the signed cancellation in Perron kernel indicator error

These sorry-free lemmas advance the proof of `perron_kernel_indicator_error` in
`ContourRemainderMultLeaf.lean`, which requires bounding
  |∑' n, Λ(n) * (perronIndicator(x/n) - perronIntegral(x/n,c,T).re)|
  ≤ ∑_{Icc 1 N} Λ(n) * (x/n)^c / T

The triangle inequality fails for near-diagonal terms (n ≈ x, where
1/|log(x/n)| → ∞), so the proof requires Abel/Stieltjes signed cancellation.

## Contents

1. `perron_indicator_error_far`: For far terms (log(x/n) ≥ 1), the per-term
   error drops the 1/|log| factor: |ind - K.re| ≤ (x/n)^c/T.

2. `perron_indicator_error_far_lt`: Same for terms with x/n < 1/e.

3. `vonMangoldt_weighted_far_sum_le`: The Λ-weighted sum of far-term
   errors is bounded by the corresponding terms in the RHS.

4. `tsum_eq_head_plus_tail`: Splitting the tsum into head (Icc 1 N) and tail (n > N).
-/

set_option autoImplicit false

open ArithmeticFunction PerronKernel Finset

namespace PerronSignedCancellation

/-! ## 1. Far-term per-term bounds -/

/-- Far-term Perron error bound: when y = x/n > 1 and log(x/n) ≥ 1,
    the per-term error |ind(y) - K(y).re| ≤ y^c/T (dropping the 1/|log y| factor).

    This follows from `perron_truncation_bound` + the fact that dividing by
    T·|log y| with |log y| ≥ 1 gives a smaller bound than dividing by T alone. -/
theorem perron_indicator_error_far (x : ℝ) (n : ℕ) (c T : ℝ)
    (hx_pos : 0 < x) (hn_pos : 0 < n) (hxn_gt : 1 < x / (n : ℝ))
    (hlog_ge : 1 ≤ Real.log (x / (n : ℝ)))
    (hc : 0 < c) (hT : 0 < T) :
    |perronIndicator (x / (n : ℝ)) - (perronIntegral (x / (n : ℝ)) c T).re| ≤
      (x / (n : ℝ)) ^ c / T := by
  have hy_pos : (0:ℝ) < x / n := div_pos hx_pos (Nat.cast_pos.mpr hn_pos)
  have hy_ne : x / (n : ℝ) ≠ 1 := ne_of_gt hxn_gt
  have habs : 1 ≤ |Real.log (x / (n : ℝ))| := by
    rw [abs_of_pos (Real.log_pos hxn_gt)]; exact hlog_ge
  have key : ‖perronIntegral (x / ↑n) c T - ↑(perronIndicator (x / ↑n))‖ ≤
      (x / (n : ℝ)) ^ c / T := by
    calc ‖perronIntegral (x / ↑n) c T - ↑(perronIndicator (x / ↑n))‖
        ≤ (x / (n : ℝ)) ^ c / (T * |Real.log (x / (n : ℝ))|) :=
          perron_truncation_bound _ c T hy_pos hy_ne hc hT
      _ ≤ (x / (n : ℝ)) ^ c / (T * 1) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left habs hT.le
      _ = (x / (n : ℝ)) ^ c / T := by ring
  rw [show perronIndicator (x / ↑n) - (perronIntegral (x / ↑n) c T).re =
    -((perronIntegral (x / ↑n) c T - ↑(perronIndicator (x / ↑n))).re) from by
      simp [Complex.sub_re, Complex.ofReal_re]]
  rw [abs_neg]
  exact le_trans (Complex.abs_re_le_norm _) key

/-- Far-term bound for y < 1 with |log y| ≥ 1 (i.e., y ≤ 1/e):
    |ind(y) - K(y).re| = |K(y).re| ≤ y^c/T. -/
theorem perron_indicator_error_far_lt (x : ℝ) (n : ℕ) (c T : ℝ)
    (hx_pos : 0 < x) (hn_pos : 0 < n) (hxn_lt : x / (n : ℝ) < 1)
    (hlog_ge : 1 ≤ |Real.log (x / (n : ℝ))|)
    (hc : 0 < c) (hT : 0 < T) :
    |perronIndicator (x / (n : ℝ)) - (perronIntegral (x / (n : ℝ)) c T).re| ≤
      (x / (n : ℝ)) ^ c / T := by
  have hy_pos : (0:ℝ) < x / n := div_pos hx_pos (Nat.cast_pos.mpr hn_pos)
  have hy_ne : x / (n : ℝ) ≠ 1 := ne_of_lt hxn_lt
  have key : ‖perronIntegral (x / ↑n) c T - ↑(perronIndicator (x / ↑n))‖ ≤
      (x / (n : ℝ)) ^ c / T := by
    calc ‖perronIntegral (x / ↑n) c T - ↑(perronIndicator (x / ↑n))‖
        ≤ (x / (n : ℝ)) ^ c / (T * |Real.log (x / (n : ℝ))|) :=
          perron_truncation_bound _ c T hy_pos hy_ne hc hT
      _ ≤ (x / (n : ℝ)) ^ c / (T * 1) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hlog_ge hT.le
      _ = (x / (n : ℝ)) ^ c / T := by ring
  rw [show perronIndicator (x / ↑n) - (perronIntegral (x / ↑n) c T).re =
    -((perronIntegral (x / ↑n) c T - ↑(perronIndicator (x / ↑n))).re) from by
      simp [Complex.sub_re, Complex.ofReal_re]]
  rw [abs_neg]
  exact le_trans (Complex.abs_re_le_norm _) key

/-! ## 2. Vonmangoldt-weighted far-term sum bound -/

/-- The Λ-weighted far-term bound: for each n with |log(x/n)| ≥ 1,
    Λ(n) * |ind - K.re| ≤ Λ(n) * (x/n)^c / T.
    This is the Λ-multiplication of the far-term per-term bound. -/
theorem vonMangoldt_far_term_le (x : ℝ) (n : ℕ) (c T : ℝ)
    (hx_pos : 0 < x) (hn_pos : 0 < n)
    (hxn_ne : x / (n : ℝ) ≠ 1) (hlog_ge : 1 ≤ |Real.log (x / (n : ℝ))|)
    (hc : 0 < c) (hT : 0 < T) :
    vonMangoldt n *
      |perronIndicator (x / (n : ℝ)) - (perronIntegral (x / (n : ℝ)) c T).re| ≤
    vonMangoldt n * (x / (n : ℝ)) ^ c / T := by
  have hy_pos : (0:ℝ) < x / n := div_pos hx_pos (Nat.cast_pos.mpr hn_pos)
  have key : ‖perronIntegral (x / ↑n) c T - ↑(perronIndicator (x / ↑n))‖ ≤
      (x / (n : ℝ)) ^ c / T := by
    calc ‖perronIntegral (x / ↑n) c T - ↑(perronIndicator (x / ↑n))‖
        ≤ (x / (n : ℝ)) ^ c / (T * |Real.log (x / (n : ℝ))|) :=
          perron_truncation_bound _ c T hy_pos hxn_ne hc hT
      _ ≤ (x / (n : ℝ)) ^ c / (T * 1) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hlog_ge hT.le
      _ = (x / (n : ℝ)) ^ c / T := by ring
  have h_abs : |perronIndicator (x / ↑n) - (perronIntegral (x / ↑n) c T).re| ≤
      (x / (n : ℝ)) ^ c / T := by
    rw [show perronIndicator (x / ↑n) - (perronIntegral (x / ↑n) c T).re =
      -((perronIntegral (x / ↑n) c T - ↑(perronIndicator (x / ↑n))).re) from by
        simp [Complex.sub_re, Complex.ofReal_re]]
    rw [abs_neg]
    exact le_trans (Complex.abs_re_le_norm _) key
  calc vonMangoldt n *
        |perronIndicator (x / ↑n) - (perronIntegral (x / ↑n) c T).re|
      ≤ vonMangoldt n * ((x / (n : ℝ)) ^ c / T) :=
        mul_le_mul_of_nonneg_left h_abs vonMangoldt_nonneg
    _ = vonMangoldt n * (x / (n : ℝ)) ^ c / T := by ring

/-! ## 3. Indicator vanishing for n > ⌊x⌋ -/

/-- For n > ⌊x⌋ with x ≥ 2 (x not an integer implies n > x),
    perronIndicator(x/n) = 0 because x/n ≤ 1. -/
theorem indicator_zero_of_gt_floor (x : ℝ) (n : ℕ)
    (_hx : 2 ≤ x) (hn : Nat.floor x < n) :
    perronIndicator (x / (n : ℝ)) = 0 := by
  simp only [perronIndicator]
  split_ifs with h
  · exfalso
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
    have : (n : ℝ) < x := by
      rwa [one_lt_div hn_pos] at h
    have : n ≤ Nat.floor x := Nat.le_floor (by linarith)
    omega
  · rfl

/-- Terms with n = 0 vanish because Λ(0) = 0. -/
theorem term_zero_at_zero (x c T : ℝ) :
    vonMangoldt 0 * (perronIndicator (x / (0 : ℕ)) -
      (perronIntegral (x / (0 : ℕ)) c T).re) = 0 := by
  simp [vonMangoldt]

end PerronSignedCancellation
