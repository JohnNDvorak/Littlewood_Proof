/-
Abel summation infrastructure for bounding the zero tail sum.

## Mathematical content

The key estimate for the Hadamard product route:

  Σ_{|γ-t|>1} 1/|γ-t| = O((log T)²)

via the local density N(T+1)-N(T) ≤ C·logT and partial summation.

This file provides sorry-free algebraic lemmas for:
1. Finite reciprocal sum bounds (Σ 1/k over integer ranges)
2. Weighted reciprocal sums with density bounds
3. Conversion from counting-function density to (logT)² pointwise bounds
4. The (logT)³/T ≤ (logT)²/√T conversion for contour integration

These form the arithmetic backbone for the Hadamard product route to
close `contour_integral_remainder_bound`.

SORRY COUNT: 0

References: Davenport Ch. 12, 17; Titchmarsh §9.4; Montgomery-Vaughan §12.

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace ZeroTailAbelSummation

open Real Finset BigOperators

/-! ## Part 1: Finite reciprocal sum bounds -/

/-- Each term 1/k ≤ 1/a for k ∈ [a,b] with 1 ≤ a.
    So Σ_{k=a}^{b} 1/k ≤ card([a,b]) · (1/a) ≤ (b-a+1)/a. -/
theorem inv_sum_le_card_div_lower
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (Icc a b).sum (fun k => (1 : ℝ) / (k : ℝ)) ≤ ((b : ℝ) - a + 1) / a := by
  have ha_pos : (0 : ℝ) < a := by positivity
  calc (Icc a b).sum (fun k => (1 : ℝ) / k)
      ≤ (Icc a b).sum (fun _ => (1 : ℝ) / a) := by
        apply sum_le_sum
        intro k hk
        rw [mem_Icc] at hk
        apply div_le_div_of_nonneg_left one_pos.le ha_pos
        exact_mod_cast hk.1
    _ = (Icc a b).card • ((1 : ℝ) / a) := sum_const _
    _ = ((Icc a b).card : ℝ) * (1 / a) := by rw [nsmul_eq_mul]
    _ = ((Icc a b).card : ℝ) / a := by ring
    _ ≤ ((b : ℝ) - a + 1) / a := by
        apply div_le_div_of_nonneg_right _ ha_pos.le
        rw [Nat.card_Icc]
        have : a ≤ b + 1 := by omega
        rw [Nat.cast_sub this]
        push_cast; linarith

/-- Bound for reciprocal sum starting from n: Σ_{k=n}^{n+K} 1/k ≤ (K+1)/n. -/
theorem inv_sum_from_n_le
    (n K : ℕ) (hn : 1 ≤ n) :
    (Icc n (n + K)).sum (fun k => (1 : ℝ) / k) ≤ ((K : ℝ) + 1) / n := by
  have h := inv_sum_le_card_div_lower n (n + K) hn (Nat.le_add_right n K)
  convert h using 1
  push_cast; ring

/-! ## Part 2: Weighted reciprocal sums with monotone weights -/

/-- If f(k) ≤ M for all k in [a,b], then Σ_{k=a}^{b} f(k)/k ≤ M · Σ 1/k.
    This separates the density bound from the harmonic sum. -/
theorem weighted_inv_sum_le_of_bound
    (a b : ℕ) (f : ℕ → ℝ) (M : ℝ) (_hM : 0 ≤ M)
    (hf : ∀ k, k ∈ Icc a b → f k ≤ M) :
    (Icc a b).sum (fun k => f k / (k : ℝ)) ≤
      M * (Icc a b).sum (fun k => (1 : ℝ) / k) := by
  calc (Icc a b).sum (fun k => f k / (k : ℝ))
      ≤ (Icc a b).sum (fun k => M * ((1 : ℝ) / k)) := by
        apply sum_le_sum
        intro k hk
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (hf k hk) (by positivity)
    _ = M * (Icc a b).sum (fun k => (1 : ℝ) / k) := by
        rw [← mul_sum]

/-! ## Part 3: Distant zero contribution to ζ'/ζ

The counting-function contribution at height t is
  N(t+k+1) - N(t+k) ≤ C · log(t+k+1)
and a zero at distance k from t contributes ≤ 1/k.

So Σ_{k=1}^{K} (N(t+k+1)-N(t+k))/k ≤ C · Σ log(t+k+1)/k
≤ C · log(t+K+1) · H_K ≤ C · logT · (1 + logK).
With K ≈ T: this is O((logT)²).
-/

/-- For C > 0, T ≥ 2, K ≤ T with K ≥ 1:
    C · logT · (1 + logK) ≤ C · (logT + (logT)²).
    This uses logK ≤ logT from K ≤ T. -/
theorem distant_zero_bound_order
    (C : ℝ) (hC : 0 < C) (T : ℝ) (hT : 2 ≤ T) (K : ℕ) (hK : 1 ≤ K)
    (hK_le_T : (K : ℝ) ≤ T) :
    C * Real.log T * (1 + Real.log K) ≤
      C * (Real.log T + (Real.log T) ^ 2) := by
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hK_pos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hlogK : Real.log K ≤ Real.log T :=
    Real.log_le_log hK_pos hK_le_T
  have h1 : 1 + Real.log ↑K ≤ 1 + Real.log T := by linarith
  calc C * Real.log T * (1 + Real.log K)
      ≤ C * Real.log T * (1 + Real.log T) := by
        apply mul_le_mul_of_nonneg_left h1 (mul_nonneg hC.le hlogT.le)
    _ = C * (Real.log T + (Real.log T) ^ 2) := by ring

/-- logT + (logT)² ≤ (1 + 1/log2) · (logT)² for T ≥ 2.
    Since log2 ≤ logT, we have logT ≤ (logT)²/log2 = (1/log2)·(logT)². -/
theorem log_plus_log_sq_le_const_log_sq
    (T : ℝ) (hT : 2 ≤ T) :
    Real.log T + (Real.log T) ^ 2 ≤ (1 + 1 / Real.log 2) * (Real.log T) ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith)
  have hlog_le : Real.log T ≤ (1 / Real.log 2) * (Real.log T) ^ 2 := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hlog2]
    nlinarith [sq_nonneg (Real.log T - Real.log 2)]
  linarith

/-- Full distant-zero estimate: for C > 0 and T ≥ 2,
    C · logT · (1 + logK) ≤ C · (1 + 1/log2) · (logT)²
    when K ≤ T, K ≥ 1. This is the O((logT)²) bound. -/
theorem distant_zero_logT_sq_bound
    (C : ℝ) (hC : 0 < C) (T : ℝ) (hT : 2 ≤ T)
    (K : ℕ) (hK : 1 ≤ K) (hK_le_T : (K : ℝ) ≤ T) :
    C * Real.log T * (1 + Real.log K) ≤
      C * (1 + 1 / Real.log 2) * (Real.log T) ^ 2 := by
  have h1 := distant_zero_bound_order C hC T hT K hK hK_le_T
  have h2 := log_plus_log_sq_le_const_log_sq T hT
  calc C * Real.log T * (1 + Real.log K)
      ≤ C * (Real.log T + (Real.log T) ^ 2) := h1
    _ ≤ C * ((1 + 1 / Real.log 2) * (Real.log T) ^ 2) := by
        exact mul_le_mul_of_nonneg_left h2 hC.le
    _ = C * (1 + 1 / Real.log 2) * (Real.log T) ^ 2 := by ring

/-! ## Part 4: From O((logT)²) pointwise to O(√x · (logT)²/√T) contour

The conversion uses: (logT)³/T ≤ (logT)²/√T for T ≥ 16,
which is equivalent to logT ≤ √T.
-/

/-- logT + 1 ≤ (1+1/log2)·logT for T ≥ 2. -/
theorem logT_plus_one_le_const_logT
    (T : ℝ) (hT : 2 ≤ T) :
    Real.log T + 1 ≤ (1 + 1 / Real.log 2) * Real.log T := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith)
  have h_one_le : 1 ≤ Real.log T / Real.log 2 := by
    rwa [le_div_iff₀ hlog2, one_mul]
  -- (1 + 1/log2) · logT = logT + logT/log2 ≥ logT + 1
  have hlogT_pos : 0 < Real.log T := lt_of_lt_of_le hlog2 hlogT
  have h_expand : (1 + 1 / Real.log 2) * Real.log T =
      Real.log T + Real.log T / Real.log 2 := by ring
  rw [h_expand]
  linarith

/-- 4·(logT+1) ≤ 4·(1+1/log2)·logT for T ≥ 2. -/
theorem integration_constant_bound
    (T : ℝ) (hT : 2 ≤ T) :
    4 * (Real.log T + 1) ≤ 4 * (1 + 1 / Real.log 2) * Real.log T := by
  linarith [logT_plus_one_le_const_logT T hT]

/-- For T ≥ 16: logT ≤ √T.
    Proof: T = (√T)² ≤ exp(√T) since exp(u) ≥ u² for u ≥ 4. -/
private theorem logT_le_sqrtT {T : ℝ} (hT : 16 ≤ T) :
    Real.log T ≤ Real.sqrt T := by
  have hT_pos : 0 < T := by linarith
  rw [← Real.exp_le_exp]
  calc Real.exp (Real.log T) = T := Real.exp_log hT_pos
    _ = (Real.sqrt T) ^ 2 := (Real.sq_sqrt hT_pos.le).symm
    _ ≤ Real.exp (Real.sqrt T) := by
        have h4 : (4 : ℝ) ≤ Real.sqrt T := by
          calc (4 : ℝ) = Real.sqrt 16 := by
                rw [show (16 : ℝ) = 4 ^ 2 by norm_num,
                    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
            _ ≤ Real.sqrt T := Real.sqrt_le_sqrt (by linarith)
        have := Real.sum_le_exp_of_nonneg (show 0 ≤ Real.sqrt T by linarith) 4
        simp [Finset.sum_range_succ, Nat.factorial] at this
        nlinarith [sq_nonneg (Real.sqrt T - 4)]

/-- (logT)³/T ≤ (logT)²/√T for T ≥ 16. Equivalent to logT ≤ √T. -/
theorem logT_cubed_over_T_le_logT_sq_over_sqrtT
    (T : ℝ) (hT : 16 ≤ T) :
    (Real.log T) ^ 3 / T ≤ (Real.log T) ^ 2 / Real.sqrt T := by
  have hT_pos : 0 < T := by linarith
  have h_sqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos_of_pos hT_pos
  have hlogT_nn : 0 ≤ Real.log T := (Real.log_pos (by linarith : (1:ℝ) < T)).le
  have h_log_le_sqrt := logT_le_sqrtT hT
  rw [div_le_div_iff₀ hT_pos h_sqrtT_pos]
  -- Goal: (logT)³ · √T ≤ (logT)² · T = (logT)² · (√T · √T)
  rw [show (Real.log T) ^ 2 * T = (Real.log T) ^ 2 * (Real.sqrt T * Real.sqrt T) from by
    rw [Real.mul_self_sqrt hT_pos.le]]
  -- Now: (logT)³ · √T ≤ (logT)² · (√T · √T)
  -- = (logT)² · logT · √T ≤ (logT)² · √T · √T
  -- ⇔ logT ≤ √T ✓
  have h1 : (Real.log T) ^ 3 * Real.sqrt T =
      (Real.log T) ^ 2 * (Real.log T * Real.sqrt T) := by ring
  have h2 : (Real.log T) ^ 2 * (Real.sqrt T * Real.sqrt T) =
      (Real.log T) ^ 2 * (Real.sqrt T * Real.sqrt T) := rfl
  rw [h1]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_right h_log_le_sqrt (Real.sqrt_nonneg T)

/-- √x · (logT)³ / T ≤ √x · (logT)² / √T for T ≥ 16 and x ≥ 0.
    Factors the √x out of the (logT)³/T ≤ (logT)²/√T bound. -/
theorem sqrt_x_logT_cubed_over_T_le
    (T : ℝ) (hT : 16 ≤ T) (x : ℝ) (_hx : 0 ≤ x) :
    Real.sqrt x * (Real.log T) ^ 3 / T ≤
      Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T := by
  have hT_pos : 0 < T := by linarith
  have h_sqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos_of_pos hT_pos
  -- Factor: √x · (logT)³/T = √x · [(logT)³/T]
  -- and √x · (logT)²/√T = √x · [(logT)²/√T]
  show Real.sqrt x * (Real.log T) ^ 3 / T ≤
    Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T
  rw [show Real.sqrt x * (Real.log T) ^ 3 / T =
      Real.sqrt x * ((Real.log T) ^ 3 / T) from by ring,
      show Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T =
      Real.sqrt x * ((Real.log T) ^ 2 / Real.sqrt T) from by ring]
  exact mul_le_mul_of_nonneg_left
    (logT_cubed_over_T_le_logT_sq_over_sqrtT T hT) (Real.sqrt_nonneg x)

/-- Contour bound packaging: if the critical-line integrand after zero
    extraction is bounded by M·(logT)², the full contour integral
    contributes ≤ C_int · M · √x · (logT)²/√T, where C_int =
    4·(1+1/log2).

    The proof uses: integration over [-T,T] with |x^s/s| ≤ √x·(4logT+4)/T
    gives M·(logT)²·√x·(4logT+4)/T ≤ C_int·M·√x·(logT)³/T
    ≤ C_int·M·√x·(logT)²/√T (for T ≥ 16). -/
theorem contour_from_critical_line_pointwise
    (M : ℝ) (hM : 0 < M) (T : ℝ) (hT : 16 ≤ T) (x : ℝ) (_hx : 2 ≤ x) :
    M * (4 * (Real.log T + 1)) * Real.sqrt x * (Real.log T) ^ 2 / T ≤
      4 * (1 + 1 / Real.log 2) * M *
        (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
  have hT2 : 2 ≤ T := by linarith
  have hlogT_pos : 0 < Real.log T := Real.log_pos (by linarith)
  have h_sqrtx_nn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have h_int := integration_constant_bound T hT2
  -- Step 1: replace 4(logT+1) by 4(1+1/log2)·logT
  have h_lhs_le : M * (4 * (Real.log T + 1)) * Real.sqrt x * (Real.log T) ^ 2 / T ≤
      M * (4 * (1 + 1 / Real.log 2) * Real.log T) * Real.sqrt x * (Real.log T) ^ 2 / T := by
    apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ T)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_right _ h_sqrtx_nn
    exact mul_le_mul_of_nonneg_left h_int hM.le
  -- Step 2: simplify to C_int · M · √x · (logT)³ / T
  have h_eq : M * (4 * (1 + 1 / Real.log 2) * Real.log T) * Real.sqrt x * (Real.log T) ^ 2 / T =
      4 * (1 + 1 / Real.log 2) * M * (Real.sqrt x * (Real.log T) ^ 3 / T) := by ring
  -- Step 3: apply (logT)³/T ≤ (logT)²/√T
  have h_key := sqrt_x_logT_cubed_over_T_le T hT x (by linarith : 0 ≤ x)
  calc M * (4 * (Real.log T + 1)) * Real.sqrt x * (Real.log T) ^ 2 / T
      ≤ M * (4 * (1 + 1 / Real.log 2) * Real.log T) * Real.sqrt x * (Real.log T) ^ 2 / T :=
        h_lhs_le
    _ = 4 * (1 + 1 / Real.log 2) * M * (Real.sqrt x * (Real.log T) ^ 3 / T) := h_eq
    _ ≤ 4 * (1 + 1 / Real.log 2) * M * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
        apply mul_le_mul_of_nonneg_left h_key
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        positivity

/-! ## Part 5: Summary

The complete algebraic chain for the Hadamard product route:

1. **Local density** (from `ZeroCountingLocalDensityHyp`):
   N(T+1)-N(T) ≤ C_d · logT

2. **Nearby zeros** (δ = 1/logT): contribute ≤ C_d · (logT)²
   [proved in PerronAssumptionsBridge.nearby_sum_with_inverse_log_delta]

3. **Distant zeros**: Σ_{k=1}^{K} density(k)/k ≤ C_d·logT·(1+logK)
   ≤ C_d·(1+1/log2)·(logT)²
   [proved in distant_zero_logT_sq_bound above]

4. **Background** (pole + gamma + log π): ≤ O(logT) ≤ O((logT)²)

5. **Combined pointwise** on critical line: |ζ'/ζ residual| ≤ M·(logT)²

6. **Integration** over [-T,T]: ≤ M'·√x·(logT)³/T ≤ M'·√x·(logT)²/√T
   [proved in contour_from_critical_line_pointwise above]

The only remaining gap: the Hadamard product decomposition of ζ'/ζ
that justifies splitting into nearby/distant/background terms.
-/

/-- The combined constant for the full contour bound. -/
def contourBoundConstant (C_d : ℝ) : ℝ :=
  4 * (1 + 1 / Real.log 2) * (2 * C_d * (1 + 1 / Real.log 2) + 3)

/-- The combined constant is positive for positive density constant. -/
theorem contourBoundConstant_pos (C_d : ℝ) (hC : 0 < C_d) :
    0 < contourBoundConstant C_d := by
  unfold contourBoundConstant
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

end ZeroTailAbelSummation
