/-
B2 first moment bound from the RS expansion hypothesis.

SORRY COUNT: 0
WARNING COUNT: 0 (target — pending build verification)

Reference: Heath-Brown 1978; Titchmarsh §4.15, §7.6; Siegel 1932 §3.
Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.RSBlockParam
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyZFirstMomentIBP
import Littlewood.Aristotle.Standalone.OscPieceBigOAssembly
import Littlewood.Bridge.HardyZTransfer
import Littlewood.Aristotle.HardyZRealV2
import Littlewood.Aristotle.AbelSummation
import Littlewood.Aristotle.IntervalPartition
import Littlewood.Aristotle.Standalone.RSExpansionProof
import Littlewood.Aristotle.RSBlockDecomposition

set_option maxHeartbeats 3200000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.B2FirstMomentFromExpansion

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.ErrorTermExpansion Aristotle.RSBlockParam Aristotle.HardyNProperties

-- ============================================================
-- Step 1: ErrorTerm pointwise bound from RS expansion
-- ============================================================

private theorem errorTerm_pointwise_of_expansion
    (h_exp : ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4)) :
    ∃ C_et > (0 : ℝ), ∀ t : ℝ, t ≥ 1 →
      |ErrorTerm t| ≤ C_et * t ^ (-(1 : ℝ) / 4) := by
  obtain ⟨C_R, hCR_pos, h_expansion⟩ := h_exp
  have h_cont : Continuous hardyZ := by
    have h_eq : hardyZ = fun t => (hardyZV2 t).re :=
      funext HardyZTransfer.hardyZ_eq_hardyZV2_re
    rw [h_eq]; exact Complex.continuous_re.comp continuous_hardyZV2
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := hardyStart 0)).exists_bound_of_continuousOn
    h_cont.continuousOn
  set C_block := (2 * Real.pi) ^ ((1 : ℝ)/4) + C_R
  set C_compact := M₀ * (hardyStart 0) ^ ((1 : ℝ)/4)
  refine ⟨max C_block C_compact + 1, by positivity, fun t ht => ?_⟩
  by_cases h_large : hardyStart 0 ≤ t
  · obtain ⟨k, hk_lo, hk_hi⟩ :=
      Aristotle.Standalone.OscPieceBigOAssembly.exists_block_of_ge_hardyStart0 t h_large
    have ht_pos : (0 : ℝ) < t := by linarith
    have h_exp_k := h_expansion k t hk_lo hk_hi ht_pos
    have h_tri : |ErrorTerm t| ≤
        (2 * Real.pi / t) ^ ((1 : ℝ) / 4) + C_R * t ^ (-(3 : ℝ) / 4) := by
      have h1 := abs_add_le
        (ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t))
        ((-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) * rsPsi (blockParam k t))
      simp only [sub_add_cancel] at h1
      have h_lead_le : |(-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ (2 * Real.pi / t) ^ ((1 : ℝ) / 4) := by
        rw [abs_mul, abs_mul, show |(-1 : ℝ) ^ k| = 1 from by simp [abs_pow, abs_neg, abs_one]]
        rw [one_mul, abs_of_nonneg (rpow_nonneg (div_nonneg (by positivity) ht_pos.le) _)]
        exact mul_le_of_le_one_right (rpow_nonneg (div_nonneg (by positivity) ht_pos.le) _)
          (abs_cos_le_one _)
      linarith
    have h_factor : (2 * Real.pi / t) ^ ((1 : ℝ) / 4) =
        (2 * Real.pi) ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) := by
      rw [div_eq_mul_inv,
          Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (inv_nonneg.mpr ht_pos.le)]
      congr 1
      rw [show (-(1:ℝ)/4) = -((1:ℝ)/4) from by ring, rpow_neg ht_pos.le, Real.inv_rpow ht_pos.le]
    have h_rpow_mono : t ^ (-(3 : ℝ)/4) ≤ t ^ (-(1 : ℝ)/4) :=
      rpow_le_rpow_of_exponent_le ht (by norm_num)
    calc |ErrorTerm t|
        ≤ (2 * Real.pi) ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) + C_R * t ^ (-(1 : ℝ)/4) := by
          rw [h_factor] at h_tri
          linarith [mul_le_mul_of_nonneg_left h_rpow_mono hCR_pos.le]
      _ = C_block * t ^ (-(1 : ℝ)/4) := by simp only [C_block]; ring
      _ ≤ (max C_block C_compact + 1) * t ^ (-(1 : ℝ)/4) := by
          have : 0 ≤ t ^ (-(1 : ℝ)/4) := rpow_nonneg (by linarith) _
          nlinarith [le_max_left C_block C_compact]
  · push_neg at h_large
    have ht_in : t ∈ Icc (1 : ℝ) (hardyStart 0) := ⟨ht, le_of_lt h_large⟩
    have h_eq : ErrorTerm t = hardyZ t := by
      unfold ErrorTerm MainTerm
      have h_div : t / (2 * Real.pi) < 1 := by
        rw [div_lt_one (by positivity : (0 : ℝ) < 2 * Real.pi)]
        rw [hardyStart_formula] at h_large
        have : ((0 : ℕ) + 1 : ℝ) ^ 2 = 1 := by push_cast; norm_num
        rw [this] at h_large; linarith
      have h_sqrt_lt : Real.sqrt (t / (2 * Real.pi)) < 1 := by
        by_cases h_nn : 0 ≤ t / (2 * Real.pi)
        · calc Real.sqrt (t / (2 * Real.pi)) < Real.sqrt 1 := Real.sqrt_lt_sqrt h_nn h_div
            _ = 1 := Real.sqrt_one
        · push_neg at h_nn
          calc Real.sqrt (t / (2 * Real.pi)) = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_lt h_nn)
            _ < 1 := one_pos
      have h_floor : Nat.floor (Real.sqrt (t / (2 * Real.pi))) = 0 :=
        Nat.floor_eq_zero.mpr h_sqrt_lt
      simp [h_floor]
    have h_bound_Z : ‖hardyZ t‖ ≤ M₀ := hM₀ t ht_in
    rw [Real.norm_eq_abs] at h_bound_Z
    have h_bound : |ErrorTerm t| ≤ M₀ := by rw [h_eq]; exact h_bound_Z
    have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
    have h_rpow_inv : t ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) = 1 := by
      rw [show (-(1 : ℝ)/4) = -((1 : ℝ)/4) from by ring,
          ← rpow_add ht_pos, add_neg_cancel, rpow_zero]
    have h_t14_le : t ^ ((1 : ℝ)/4) ≤ (hardyStart 0) ^ ((1 : ℝ)/4) :=
      rpow_le_rpow (by linarith) (le_of_lt h_large) (by norm_num)
    calc |ErrorTerm t|
        ≤ M₀ := h_bound
      _ = M₀ * (t ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4)) := by rw [h_rpow_inv, mul_one]
      _ = M₀ * t ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) := by ring
      _ ≤ M₀ * (hardyStart 0) ^ ((1 : ℝ)/4) * t ^ (-(1 : ℝ)/4) := by
          have h_nn : 0 ≤ t ^ (-(1 : ℝ)/4) := rpow_nonneg (by linarith) _
          have hM₀_nn : 0 ≤ M₀ := le_trans (abs_nonneg _) h_bound
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h_t14_le hM₀_nn) h_nn
      _ = C_compact * t ^ (-(1 : ℝ)/4) := by simp only [C_compact]
      _ ≤ (max C_block C_compact + 1) * t ^ (-(1 : ℝ)/4) := by
          have : 0 ≤ t ^ (-(1 : ℝ)/4) := rpow_nonneg (by linarith) _
          nlinarith [le_max_right C_block C_compact]

-- ============================================================
-- Step 2: Signed integral of ErrorTerm from pointwise bound
-- ============================================================

private theorem errorTerm_signed_integral_bound
    (C_et : ℝ) (hC_pos : 0 < C_et)
    (h_bound : ∀ t : ℝ, t ≥ 1 → |ErrorTerm t| ≤ C_et * t ^ (-(1 : ℝ) / 4)) :
    ∀ T : ℝ, T ≥ 2 →
      |∫ t in Set.Ioc 1 T, ErrorTerm t| ≤ C_et * T := by
  intro T hT
  have h_ptwise : ∀ t ∈ Set.uIoc 1 T, ‖ErrorTerm t‖ ≤ C_et := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith : (1:ℝ) ≤ T)] at ht
    rw [Real.norm_eq_abs]
    have ht1 : t ≥ 1 := by linarith [ht.1]
    calc |ErrorTerm t| ≤ C_et * t ^ (-(1 : ℝ) / 4) := h_bound t ht1
      _ ≤ C_et * 1 := by
          exact mul_le_mul_of_nonneg_left
            (rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)) hC_pos.le
      _ = C_et := mul_one _
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const h_ptwise
  rw [show ∫ t in Set.Ioc 1 T, ErrorTerm t = ∫ t in (1:ℝ)..T, ErrorTerm t from by
    rw [intervalIntegral.integral_of_le (by linarith)]] at *
  calc |∫ t in (1:ℝ)..T, ErrorTerm t|
      ≤ C_et * |T - 1| := h1
    _ ≤ C_et * T := by
        rw [abs_of_nonneg (by linarith)]
        nlinarith

-- ============================================================
-- Step 3: ErrorTerm signed integral bound from h_exp
-- ============================================================

/-- Upper bound on a single block's integral:
    |∫_{block k} ErrorTerm| ≤ C_et · block_length.
    Uses |ErrorTerm(t)| ≤ C_et · t^{-1/4} ≤ C_et on [hs k, hs(k+1)] since t ≥ 1. -/
private theorem block_integral_le_length
    (C_et : ℝ) (hC_pos : 0 < C_et)
    (h_ptwise : ∀ t : ℝ, t ≥ 1 → |ErrorTerm t| ≤ C_et * t ^ (-(1 : ℝ) / 4))
    (k : ℕ) :
    |∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t| ≤
      C_et * (2 * Real.pi * (2 * (k : ℝ) + 3)) := by
  have hhs_gt_one : (1 : ℝ) < hardyStart k := by
    rw [hardyStart_formula]
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [Real.pi_gt_three]
  have h_intble : IntegrableOn ErrorTerm (Set.Ioc (hardyStart k) (hardyStart (k + 1))) :=
    (errorTerm_integrable (hardyStart (k + 1))).mono_set (fun t ht =>
      ⟨lt_trans hhs_gt_one ht.1, ht.2⟩)
  have h_hs_le : hardyStart k ≤ hardyStart (k + 1) :=
    Aristotle.Standalone.OscPieceBigOAssembly.hardyStart_mono (Nat.le_succ k)
  have h_const : ∀ t ∈ Set.uIoc (hardyStart k) (hardyStart (k + 1)),
      ‖ErrorTerm t‖ ≤ C_et := by
    intro t ht
    rw [Set.uIoc_of_le h_hs_le] at ht
    rw [Real.norm_eq_abs]
    have ht1 : t ≥ 1 := by linarith [ht.1]
    calc |ErrorTerm t| ≤ C_et * t ^ (-(1 : ℝ) / 4) := h_ptwise t ht1
      _ ≤ C_et * 1 := mul_le_mul_of_nonneg_left
          (rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)) hC_pos.le
      _ = C_et := mul_one _
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const h_const
  rw [show ∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t =
      ∫ t in (hardyStart k)..(hardyStart (k + 1)), ErrorTerm t from by
    rw [intervalIntegral.integral_of_le h_hs_le]] at *
  calc |∫ t in (hardyStart k)..(hardyStart (k + 1)), ErrorTerm t|
      ≤ C_et * |hardyStart (k + 1) - hardyStart k| := h1
    _ = C_et * (hardyStart (k + 1) - hardyStart k) := by
        rw [abs_of_nonneg (sub_nonneg.mpr h_hs_le)]
    _ = C_et * (2 * Real.pi * (2 * (k : ℝ) + 3)) := by
        rw [block_length]

/-- Alternating sum bound for approximately monotone sequences (Route C2).
    If M is monotone nonneg and |a(k) - M(k)| ≤ δ for all k, then
    |∑_{k<n+1} (-1)^k a(k)| ≤ M(n) + (n + 1) * δ. -/
private theorem alternating_sum_approx_monotone (a M_fn : ℕ → ℝ) (δ : ℝ) (_hδ : 0 ≤ δ)
    (hM_nonneg : ∀ k, 0 ≤ M_fn k)
    (hM_mono : Monotone M_fn)
    (h_approx : ∀ k, |a k - M_fn k| ≤ δ)
    (n : ℕ) :
    |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * a k| ≤ M_fn n + (↑n + 1) * δ := by
  have h_split : ∀ k, (-1 : ℝ) ^ k * a k =
      (-1 : ℝ) ^ k * M_fn k + (-1 : ℝ) ^ k * (a k - M_fn k) := by intro k; ring
  simp_rw [h_split, Finset.sum_add_distrib]
  calc |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * M_fn k +
        ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (a k - M_fn k)|
      ≤ |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * M_fn k| +
        |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (a k - M_fn k)| := abs_add_le _ _
    _ ≤ M_fn n + ∑ k ∈ Finset.range (n + 1), |(-1 : ℝ) ^ k * (a k - M_fn k)| := by
        gcongr
        · exact AbelSummation.alternating_sum_le_last M_fn hM_nonneg hM_mono n
        · exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ M_fn n + ∑ k ∈ Finset.range (n + 1), δ := by
        gcongr with k _
        rw [abs_mul, show |(-1 : ℝ) ^ k| = 1 from by simp [abs_pow, abs_neg, abs_one], one_mul]
        exact h_approx k
    _ = M_fn n + (↑n + 1) * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- BL(k) · hs(k)^{-3/4} ≤ 6π for all k : ℕ.
    Uses: hs(k) ≥ (k+1)², so hs(k)^{-3/4} ≤ ((k+1)²)^{-3/4} = (k+1)^{-3/2}.
    Then 2π(2k+3)·(k+1)^{-3/2} ≤ 2π·3·(k+1)^{-1/2} ≤ 6π. -/
private theorem block_remainder_uniform_bound (k : ℕ) :
    (hardyStart (k + 1) - hardyStart k) * (hardyStart k) ^ (-(3 : ℝ) / 4) ≤ 6 * Real.pi := by
  rw [block_length]
  -- Goal: 2π(2k+3) · hs(k)^{-3/4} ≤ 6π
  have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hhs_pos : (0 : ℝ) < hardyStart k := by
    rw [hardyStart_formula]; nlinarith [Real.pi_gt_three]
  -- hs(k)^{-3/4} ≤ 1 (since hs(k) ≥ 1 and exponent ≤ 0)
  have hhs_ge1 : (1 : ℝ) ≤ hardyStart k := by
    rw [hardyStart_formula]; nlinarith [Real.pi_gt_three]
  have hhs_rpow_le1 : (hardyStart k) ^ (-(3 : ℝ) / 4) ≤ 1 :=
    rpow_le_one_of_one_le_of_nonpos hhs_ge1 (by norm_num)
  -- 2k+3 ≤ 3(k+1)
  have h_lin : 2 * (k : ℝ) + 3 ≤ 3 * ((k : ℝ) + 1) := by linarith
  -- So 2π(2k+3) · hs(k)^{-3/4} ≤ 2π · 3(k+1) · 1 = 6π(k+1)
  -- But we need ≤ 6π, not 6π(k+1). Need the rpow decay.
  -- Better: hs(k)^{-3/4} ≤ (k+1)^{-3/2} ≤ (k+1)^{-1}
  -- Then 2π(2k+3)/(k+1) ≤ 6π.
  -- hs(k) ≥ (k+1)², so hs(k)^{-3/4} ≤ (k+1)^{-3/2} ≤ (k+1)^{-1}
  -- Then 2π(2k+3)/(k+1) ≤ 6π.
  -- Use rpow directly: hs(k)^{-3/4} ≤ hs(k)^{-1/2} since hs ≥ 1 and -3/4 ≤ -1/2
  -- hs(k)^{-1/2} = 1/√hs(k). √hs(k) = √(2π(k+1)²) ≥ √((k+1)²) = k+1.
  -- So hs(k)^{-1/2} ≤ 1/(k+1).
  -- Alternatively, just use: hs(k)^{-3/4} ≤ 1 and 2k+3 ≤ 3(k+1), but that gives ≤ 6π(k+1).
  -- We need the (k+1)^{-1} factor.
  -- Simplest: hs(k)^{-3/4} ≤ hs(k)^{-1/2} (exponent monotonicity for base ≥ 1)
  have h_rpow_exponent : (hardyStart k) ^ (-(3 : ℝ) / 4) ≤ (hardyStart k) ^ (-(1 : ℝ) / 2) :=
    rpow_le_rpow_of_exponent_le hhs_ge1 (by norm_num)
  -- hs(k)^{-1/2} = (√hs(k))⁻¹
  have h_rpow_sqrt : (hardyStart k) ^ (-(1 : ℝ) / 2) = (Real.sqrt (hardyStart k))⁻¹ := by
    rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) from by ring, rpow_neg (le_of_lt hhs_pos),
        Real.sqrt_eq_rpow, inv_eq_one_div]
  -- √hs(k) = √(2π) · (k+1) ≥ k+1
  have h_sqrt_ge : (k : ℝ) + 1 ≤ Real.sqrt (hardyStart k) := by
    rw [hardyStart_formula]
    rw [show 2 * Real.pi * ((k : ℝ) + 1) ^ 2 = (Real.sqrt (2 * Real.pi) * ((k : ℝ) + 1)) ^ 2 from by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]]
    rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) * ((k : ℝ) + 1))]
    have : 1 ≤ Real.sqrt (2 * Real.pi) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
    nlinarith
  -- (√hs(k))⁻¹ ≤ (k+1)⁻¹
  have h_inv_le : (Real.sqrt (hardyStart k))⁻¹ ≤ ((k : ℝ) + 1)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hk1_pos h_sqrt_ge
  -- Combine: hs(k)^{-3/4} ≤ (k+1)⁻¹
  have h_hs_rpow_le_inv : (hardyStart k) ^ (-(3 : ℝ) / 4) ≤ ((k : ℝ) + 1)⁻¹ := by
    linarith [h_rpow_exponent, h_rpow_sqrt, h_inv_le]
  -- Final: 2π(2k+3) · hs(k)^{-3/4} ≤ 2π(2k+3)/(k+1) ≤ 6π
  -- 2π(2k+3) · hs^{-3/4} ≤ 2π(2k+3)/(k+1) ≤ 6π
  have h_main : 2 * Real.pi * (2 * (k : ℝ) + 3) * ((k : ℝ) + 1)⁻¹ ≤ 6 * Real.pi := by
    rw [mul_assoc, mul_comm (2 * (k : ℝ) + 3) ((k : ℝ) + 1)⁻¹, ← mul_assoc,
        show 2 * Real.pi * ((k : ℝ) + 1)⁻¹ * (2 * (k : ℝ) + 3) =
          2 * Real.pi * ((2 * (k : ℝ) + 3) * ((k : ℝ) + 1)⁻¹) from by ring,
        ← div_eq_mul_inv]
    calc 2 * Real.pi * ((2 * (k : ℝ) + 3) / ((k : ℝ) + 1))
        ≤ 2 * Real.pi * 3 := by
          gcongr; rw [div_le_iff₀ hk1_pos]; nlinarith
      _ = 6 * Real.pi := by ring
  calc 2 * Real.pi * (2 * (k : ℝ) + 3) * (hardyStart k) ^ (-(3 : ℝ) / 4)
      ≤ 2 * Real.pi * (2 * (k : ℝ) + 3) * ((k : ℝ) + 1)⁻¹ := by
        apply mul_le_mul_of_nonneg_left h_hs_rpow_le_inv
        apply mul_nonneg (by positivity) (by linarith)
    _ ≤ 6 * Real.pi := h_main

/-- |∫₁ᵀ ErrorTerm(t) dt| ≤ C · T^{1/2+ε} for every ε > 0.
    Uses alternating block cancellation + block integral bound.

    Proof strategy:
    - ε ≥ 1/2: use linear bound h_linear (T ≤ T^{1/2+ε} for T ≥ 1).
    - ε < 1/2: prove √T bound via alternating cancellation:
      Split ∫₁ᵀ = head + middle_blocks + partial_tail.
      Middle blocks form alternating sum bounded by b(K-1) via alternating_sum_le_last.
      b(K-1) ≤ C·BL(K) = O(K) = O(√T). Then √T ≤ T^{1/2+ε}. -/
private theorem errorTerm_signed_integral_sublinear
    (h_exp : ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4)) :
    ∀ ε : ℝ, ε > 0 →
      ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
        |∫ t in Set.Ioc 1 T, ErrorTerm t| ≤ C * T ^ (1 / 2 + ε) := by
  intro ε hε
  obtain ⟨C_R, hCR_pos, h_rs⟩ := h_exp
  obtain ⟨C_et, hCet_pos, h_ptwise⟩ := errorTerm_pointwise_of_expansion ⟨C_R, hCR_pos, h_rs⟩
  have h_linear := errorTerm_signed_integral_bound C_et hCet_pos h_ptwise
  set b : ℕ → ℝ := fun k => (-1 : ℝ) ^ k *
    ∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t with hb_def
  have hb_nonneg : ∀ k, 0 ≤ b k := fun k => by
    simp only [hb_def]
    exact Aristotle.Standalone.RSExpansionProof.signed_block_integral_nonneg k
  -- M(k) = 4π · ∫₀¹ √(k+1+p) · Ψ(p) dp — the monotone leading term
  set M_fn : ℕ → ℝ := fun k => 4 * Real.pi *
    ∫ p in Set.Ioc (0 : ℝ) 1, Real.sqrt ((k : ℝ) + 1 + p) * rsPsi p with hM_def
  have hM_nonneg : ∀ k, 0 ≤ M_fn k := by
    intro k; simp only [hM_def]
    apply mul_nonneg (by positivity)
    apply setIntegral_nonneg measurableSet_Ioc
    intro p hp; exact mul_nonneg (Real.sqrt_nonneg _)
      (rsPsi_nonneg_on p (Set.Ioc_subset_Icc_self hp))
  have hM_mono : Monotone M_fn := by
    apply monotone_nat_of_le_succ; intro k; simp only [hM_def]
    apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
    have h := Aristotle.Standalone.RSExpansionProof.weighted_sqrt_monotone k
    convert h using 2
    push_cast; ring
  have hb_le : ∀ k : ℕ, b k ≤ C_et * (2 * Real.pi * (2 * (k : ℝ) + 3)) := by
    intro k
    have h_bk_eq_abs : b k =
        |∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t| := by
      have hnn := hb_nonneg k
      rw [hb_def] at hnn ⊢
      rw [← abs_of_nonneg hnn, abs_mul,
          show |(-1 : ℝ) ^ k| = 1 from by simp [abs_pow, abs_neg, abs_one], one_mul]
    rw [h_bk_eq_abs]
    exact block_integral_le_length C_et hCet_pos h_ptwise k
  have hhs_gt1 : ∀ k : ℕ, (1 : ℝ) < hardyStart k := by
    intro k
    have : hardyStart k = 2 * Real.pi * ((k : ℝ) + 1) ^ 2 := hardyStart_formula k
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hsq : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [Real.pi_gt_three]
  -- Split on ε: large ε uses linear bound, small ε needs alternating cancellation
  by_cases hε_half : (1 : ℝ) / 2 ≤ ε
  · -- Case ε ≥ 1/2: T^1 ≤ T^{1/2+ε} for T ≥ 1
    refine ⟨C_et, hCet_pos, fun T hT => ?_⟩
    calc |∫ t in Set.Ioc 1 T, ErrorTerm t|
        ≤ C_et * T := h_linear T hT
      _ = C_et * T ^ (1 : ℝ) := by rw [rpow_one]
      _ ≤ C_et * T ^ (1 / 2 + ε) := by gcongr <;> linarith
  · -- Case ε < 1/2: prove √T bound via alternating cancellation, then upgrade
    push_neg at hε_half
    -- Step 1: Prove ∃ C_sq, ∀ T ≥ 2, |∫₁ᵀ E| ≤ C_sq * √T
    suffices h_sqrt : ∃ C_sq > (0 : ℝ), ∀ T : ℝ, T ≥ 2 →
        |∫ t in Set.Ioc 1 T, ErrorTerm t| ≤ C_sq * Real.sqrt T by
      obtain ⟨C_sq, hCsq_pos, h_sq⟩ := h_sqrt
      refine ⟨C_sq, hCsq_pos, fun T hT => ?_⟩
      calc |∫ t in Set.Ioc 1 T, ErrorTerm t|
          ≤ C_sq * Real.sqrt T := h_sq T hT
        _ = C_sq * T ^ ((1 : ℝ) / 2) := by rw [Real.sqrt_eq_rpow]
        _ ≤ C_sq * T ^ (1 / 2 + ε) := by gcongr <;> linarith
    -- Step 2: Prove the √T bound using block decomposition + M+R alternating cancellation
    -- δ_rem covers the per-term approx error for alternating_sum_approx_monotone
    -- For k ≥ 1: |R(k)| ≤ (1/2) · 6π = 3π (from block_remainder_uniform_bound and C_R' ≤ 1/2)
    -- For k = 0: |b(0) - M_ext(0)| = M_fn(0) (handled by padding M_ext = M_fn + b(0))
    -- Set δ = M_fn 0 + 3π + b 0 (covers both cases)
    -- Constant absorbs head + middle (M_ext(K-1) + K·δ) + partial tail
    set C_sq := C_et * hardyStart 0 + C_et * 4 * Real.pi * 3 + C_et * 8 * Real.pi +
      (M_fn 0 + 4 * Real.pi + b 0) * 2 + 1
    have hC_sq_pos : 0 < C_sq := by
      simp only [C_sq]; nlinarith [Real.pi_pos, hhs_gt1 0, hb_nonneg 0, hM_nonneg 0]
    refine ⟨C_sq, hC_sq_pos, fun T hT => ?_⟩
    have h_sqrtT_ge1 : (1 : ℝ) ≤ Real.sqrt T := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
    by_cases hT_ge_hs0 : hardyStart 0 ≤ T
    · -- T ≥ hardyStart 0: use block decomposition + alternating cancellation
      obtain ⟨K, hK_le, hK_le'⟩ :=
        Aristotle.Standalone.OscPieceBigOAssembly.exists_block_of_ge_hardyStart0 T hT_ge_hs0
      -- (K+1)² ≤ T/(2π) ≤ T, so K+1 ≤ √T
      have hK1_le_sqrtT : (K : ℝ) + 1 ≤ Real.sqrt T := by
        have hK1_sq := Aristotle.Standalone.OscPieceBigOAssembly.block_index_sq_le K T hK_le
        rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (K : ℝ) + 1)]
        exact Real.sqrt_le_sqrt (le_trans hK1_sq (div_le_self (by linarith) (by nlinarith [Real.pi_gt_three])))
      -- 2K+3 ≤ 2√T + 1
      have h2K3_le : 2 * (K : ℝ) + 3 ≤ 2 * Real.sqrt T + 1 := by linarith
      -- Integrability setup
      have h_E_intble : IntegrableOn ErrorTerm (Set.Ioc 1 T) := errorTerm_integrable T
      have h_1_le_hs0 : (1 : ℝ) ≤ hardyStart 0 := le_of_lt (hhs_gt1 0)
      have h_hs0_le_hsK : hardyStart 0 ≤ hardyStart K :=
        Aristotle.Standalone.OscPieceBigOAssembly.hardyStart_mono (Nat.zero_le K)
      have h_E_head : IntegrableOn ErrorTerm (Set.Ioc 1 (hardyStart 0)) :=
        h_E_intble.mono_set (fun t ht => ⟨ht.1, le_trans ht.2 hT_ge_hs0⟩)
      have h_E_tail : IntegrableOn ErrorTerm (Set.Ioc (hardyStart 0) T) :=
        h_E_intble.mono_set (fun t ht => ⟨lt_of_lt_of_le (hhs_gt1 0) (le_of_lt ht.1), ht.2⟩)
      have h_E_mid : IntegrableOn ErrorTerm (Set.Ioc (hardyStart 0) (hardyStart K)) :=
        h_E_intble.mono_set (fun t ht => ⟨lt_of_lt_of_le (hhs_gt1 0) (le_of_lt ht.1),
          le_trans ht.2 hK_le⟩)
      have h_E_partial : IntegrableOn ErrorTerm (Set.Ioc (hardyStart K) T) :=
        h_E_intble.mono_set (fun t ht => ⟨lt_of_lt_of_le (hhs_gt1 0)
          (le_trans h_hs0_le_hsK (le_of_lt ht.1)), ht.2⟩)
      -- Split ∫₁ᵀ = ∫₁^{hs0} + ∫_{hs0}^T
      have h_split1 : ∫ t in Set.Ioc 1 T, ErrorTerm t =
          (∫ t in Set.Ioc 1 (hardyStart 0), ErrorTerm t) +
          (∫ t in Set.Ioc (hardyStart 0) T, ErrorTerm t) :=
        Aristotle.IntervalPartition.integral_split_at _ 1 (hardyStart 0) T
          h_1_le_hs0 hT_ge_hs0 h_E_head h_E_tail
      -- Split ∫_{hs0}^T = ∫_{hs0}^{hsK} + ∫_{hsK}^T
      have h_split2 : ∫ t in Set.Ioc (hardyStart 0) T, ErrorTerm t =
          (∫ t in Set.Ioc (hardyStart 0) (hardyStart K), ErrorTerm t) +
          (∫ t in Set.Ioc (hardyStart K) T, ErrorTerm t) :=
        Aristotle.IntervalPartition.integral_split_at _ (hardyStart 0) (hardyStart K) T
          h_hs0_le_hsK hK_le h_E_mid h_E_partial
      -- |head| ≤ C_et * hs0
      have h_head_le : |∫ t in Set.Ioc 1 (hardyStart 0), ErrorTerm t| ≤
          C_et * hardyStart 0 :=
        h_linear (hardyStart 0) (by
          have := hardyStart_formula 0; push_cast at this; nlinarith [Real.pi_gt_three])
      -- |partial tail| ≤ C_et * BL(K) = C_et * 2π(2K+3)
      have h_partial_le : |∫ t in Set.Ioc (hardyStart K) T, ErrorTerm t| ≤
          C_et * (2 * Real.pi * (2 * (K : ℝ) + 3)) := by
        have h_c : ∀ t ∈ Set.uIoc (hardyStart K) T, ‖ErrorTerm t‖ ≤ C_et := by
          intro t ht; rw [Set.uIoc_of_le hK_le] at ht; rw [Real.norm_eq_abs]
          calc |ErrorTerm t| ≤ C_et * t ^ (-(1 : ℝ) / 4) :=
                h_ptwise t (le_of_lt (lt_trans (hhs_gt1 K) ht.1))
            _ ≤ C_et * 1 := mul_le_mul_of_nonneg_left
                (rpow_le_one_of_one_le_of_nonpos
                  (le_of_lt (lt_trans (hhs_gt1 K) ht.1)) (by norm_num)) hCet_pos.le
            _ = C_et := mul_one _
        have h_ii := intervalIntegral.norm_integral_le_of_norm_le_const h_c
        rw [show ∫ t in Set.Ioc (hardyStart K) T, ErrorTerm t =
            ∫ t in (hardyStart K)..T, ErrorTerm t from by
          rw [intervalIntegral.integral_of_le hK_le]] at *
        calc |∫ t in (hardyStart K)..T, ErrorTerm t|
            ≤ C_et * |T - hardyStart K| := h_ii
          _ = C_et * (T - hardyStart K) := by rw [abs_of_nonneg (sub_nonneg.mpr hK_le)]
          _ ≤ C_et * (hardyStart (K + 1) - hardyStart K) := by gcongr
          _ = C_et * (2 * Real.pi * (2 * (K : ℝ) + 3)) := by rw [block_length]
      -- |middle| via M+R split + alternating_sum_approx_monotone
      -- M_ext(k) = M_fn(k) + b(0), δ = M_fn(0) + 3π + b(0)
      have h_mid_le : |∫ t in Set.Ioc (hardyStart 0) (hardyStart K), ErrorTerm t| ≤
          C_et * (2 * Real.pi * (2 * (K : ℝ) + 3)) +
          (M_fn 0 + 4 * Real.pi + b 0) * ((K : ℝ) + 1) := by
        rcases Nat.eq_zero_or_pos K with hK0 | hK_pos
        · subst hK0
          convert_to |((0 : ℝ))| ≤ _
          · congr 1
            have : Set.Ioc (hardyStart 0) (hardyStart 0) = ∅ := Set.Ioc_self _
            simp [this]
          · rw [abs_zero]; apply add_nonneg
            · exact mul_nonneg hCet_pos.le (by nlinarith [Real.pi_pos])
            · apply mul_nonneg _ (by positivity)
              nlinarith [hM_nonneg 0, Real.pi_pos, hb_nonneg 0]
        · -- K ≥ 1: block decomposition + M+R alternating cancellation
          have h_bp_mono : ∀ k, k < K → hardyStart k ≤ hardyStart (k + 1) :=
            fun k _ => Aristotle.Standalone.OscPieceBigOAssembly.hardyStart_mono (Nat.le_succ k)
          have h_bp_intble : ∀ k, k < K →
              IntegrableOn ErrorTerm (Set.Ioc (hardyStart k) (hardyStart (k + 1))) :=
            fun k _ => (errorTerm_integrable (hardyStart (k + 1))).mono_set
              (fun t ht => ⟨lt_trans (hhs_gt1 k) ht.1, ht.2⟩)
          have h_mid_split :
              ∫ t in Set.Ioc (hardyStart 0) (hardyStart K), ErrorTerm t =
                ∑ k ∈ Finset.range K,
                  ∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t :=
            Aristotle.IntervalPartition.integral_split_finitely ErrorTerm hardyStart K
              h_bp_mono h_bp_intble
          have h_block_eq : ∀ k : ℕ,
              ∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t =
                (-1 : ℝ) ^ k * b k := by
            intro k; simp only [hb_def]
            rw [← mul_assoc, ← pow_add, show k + k = 2 * k from by ring,
                pow_mul, neg_one_sq, one_pow, one_mul]
          have h_sum_eq : ∑ k ∈ Finset.range K,
              ∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t =
                ∑ k ∈ Finset.range K, (-1 : ℝ) ^ k * b k := by
            congr 1; ext k; exact h_block_eq k
          rw [h_mid_split, h_sum_eq]
          -- Define M_ext and δ for the approximately monotone bound
          set M_ext : ℕ → ℝ := fun k => M_fn k + b 0 with hMext_def
          have hMext_nonneg : ∀ k, 0 ≤ M_ext k := fun k => by
            simp only [hMext_def]; linarith [hM_nonneg k, hb_nonneg 0]
          have hMext_mono : Monotone M_ext := fun a₁ a₂ h => by
            simp only [hMext_def]; linarith [hM_mono h]
          set δ := M_fn 0 + 4 * Real.pi + b 0 with hδ_def
          have hδ_nonneg : (0 : ℝ) ≤ δ := by
            simp only [hδ_def]; nlinarith [hM_nonneg 0, Real.pi_pos, hb_nonneg 0]
          -- Per-term approximation: |b(k) - M_ext(k)| ≤ δ
          have h_approx : ∀ k, |b k - M_ext k| ≤ δ := by
            intro k; simp only [hMext_def, hδ_def]
            -- For k = 0: |b(0) - M(0) - b(0)| = M(0) ≤ M(0) + 4π + b(0) = δ
            -- For k ≥ 1: b(k) = M(k) + R(k), |R(k)| ≤ 3π
            -- |b(k) - M(k) - b(0)| = |R(k) - b(0)| ≤ |R(k)| + b(0) ≤ 3π + b(0) ≤ δ
            -- Unified: |b(k) - M_fn(k) - b(0)| ≤ M_fn(0) + 4π + b(0)
            rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
            · -- k = 0
              subst hk0
              rw [show b 0 - (M_fn 0 + b 0) = -(M_fn 0) from by ring, abs_neg]
              rw [abs_of_nonneg (hM_nonneg 0)]
              linarith [Real.pi_pos, hb_nonneg 0]
            · -- k ≥ 1: use signed_block_integral_expansion
              have hk1 : 1 ≤ k := hk_pos
              obtain ⟨R_k, h_bk_eq, C_R', hCR'_pos, hCR'_le, h_Rbd⟩ :=
                Aristotle.Standalone.RSExpansionProof.signed_block_integral_expansion k hk1
              -- h_bk_eq : b(k) = M_fn(k) + R_k (after unfolding)
              have h_bk_eq' : b k = M_fn k + R_k := by
                simp only [hb_def, hM_def] at h_bk_eq ⊢; linarith
              -- |R_k| ≤ C_R' · BL(k) · hs(k)^{-3/4} ≤ (1/2) · 6π = 3π
              have h_Rk_le : |R_k| ≤ 3 * Real.pi := by
                have h_bl_rpow := block_remainder_uniform_bound k
                have h_bl_nn : 0 ≤ (hardyStart (k + 1) - hardyStart k) *
                    (hardyStart k) ^ (-(3 : ℝ) / 4) :=
                  mul_nonneg (sub_nonneg.mpr (Aristotle.Standalone.OscPieceBigOAssembly.hardyStart_mono
                    (Nat.le_succ k)))
                    (rpow_nonneg (le_of_lt (by rw [hardyStart_formula]; positivity)) _)
                calc |R_k|
                    ≤ C_R' * (hardyStart (k + 1) - hardyStart k) *
                        (hardyStart k) ^ (-(3 : ℝ) / 4) := h_Rbd
                  _ = C_R' * ((hardyStart (k + 1) - hardyStart k) *
                        (hardyStart k) ^ (-(3 : ℝ) / 4)) := by ring
                  _ ≤ (1 / 2) * (6 * Real.pi) :=
                      mul_le_mul hCR'_le h_bl_rpow h_bl_nn (by linarith)
                  _ = 3 * Real.pi := by ring
              -- |b(k) - M(k) - b(0)| = |R_k - b(0)| ≤ |R_k| + b(0) ≤ 3π + b(0)
              rw [h_bk_eq', show M_fn k + R_k - (M_fn k + b 0) = R_k - b 0 from by ring]
              have h_tri : |R_k - b 0| ≤ |R_k| + |b 0| := by
                rw [show R_k - b 0 = R_k + (-b 0) from sub_eq_add_neg _ _]
                exact (abs_add_le R_k (-b 0)).trans (by rw [abs_neg])
              calc |R_k - b 0|
                  ≤ |R_k| + |b 0| := h_tri
                _ = |R_k| + b 0 := by rw [abs_of_nonneg (hb_nonneg 0)]
                _ ≤ 3 * Real.pi + b 0 := by linarith
                _ ≤ M_fn 0 + 4 * Real.pi + b 0 := by linarith [hM_nonneg 0, Real.pi_pos]
          -- Apply alternating_sum_approx_monotone
          have hK_eq : K = (K - 1) + 1 := by omega
          calc |∑ k ∈ Finset.range K, (-1 : ℝ) ^ k * b k|
              ≤ M_ext (K - 1) + (↑(K - 1) + 1) * δ := by
                rw [hK_eq]
                exact alternating_sum_approx_monotone b M_ext δ hδ_nonneg
                  hMext_nonneg hMext_mono h_approx (K - 1)
            _ ≤ C_et * (2 * Real.pi * (2 * (K : ℝ) + 3)) + δ * ((K : ℝ) + 1) := by
                simp only [hMext_def]
                -- M_ext(K-1) = M_fn(K-1) + b(0)
                -- M_fn(K-1) ≤ b(K-1) + |R(K-1)| ≤ hb_le(K-1) + 3π
                -- ≤ C_et · BL(K-1) + 3π ≤ C_et · BL(K) + 3π (BL increasing)
                -- Actually simpler: M_fn(K-1) ≤ M_fn(K-1). And b(K-1) = M_fn(K-1) + R.
                -- We need M_fn(K-1) + b(0) + (↑(K-1)+1)·δ ≤ C_et·BL(K) + δ·(K+1)
                -- M_fn(K-1) + b(0) ≤ hb_le(K-1) + 3π + b(0) ≤ C_et·BL(K) + 3π + b(0)
                -- And 3π + b(0) ≤ δ. So M_fn(K-1)+b(0) ≤ C_et·BL(K) + δ.
                -- And (↑(K-1)+1) = K, so total ≤ C_et·BL(K) + δ + K·δ = C_et·BL(K) + (K+1)·δ.
                -- Hmm need to be more precise.
                -- LHS = M_fn(K-1) + b(0) + K·δ
                -- RHS = C_et·2π(2K+3) + δ·(K+1) = C_et·BL(K) + K·δ + δ
                -- Need: M_fn(K-1) + b(0) ≤ C_et·BL(K) + δ
                -- M_fn(K-1) ≤ b(K-1) + 3π (from expansion)
                -- ≤ C_et·BL(K-1) + 3π ≤ C_et·BL(K) + 3π (BL increasing, 2K+1 ≤ 2K+3)
                -- b(0) ≤ C_et·BL(0) ≤ C_et·BL(K) (BL increasing)
                -- So M_fn(K-1)+b(0) ≤ 2·C_et·BL(K) + 3π ... that's > C_et·BL(K) + δ sometimes.
                -- Actually let me just bound M_fn(K-1) directly.
                -- M_fn(K-1) ≤ 4π·√(K+1)·1 (since |Ψ| ≤ 1, √(K+p) ≤ √(K+1) for p ∈ [0,1])
                -- 4π·√(K+1) ≤ 4π·√T^{1/2} ... this doesn't help for the immediate bound.
                -- Let me use: M_fn(K-1) + b(0) ≤ b(K-1) + 3π + b(0)
                -- (from b(K-1) = M_fn(K-1) + R, |R| ≤ 3π, so M_fn(K-1) ≤ b(K-1) + 3π)
                -- ≤ C_et·BL(K-1) + 3π + b(0) ≤ C_et·BL(K) + 4π + b(0)
                -- (since BL(K-1) ≤ BL(K) and 3π ≤ 4π)
                -- And δ = M_fn(0) + 4π + b(0) ≥ 4π + b(0) ≥ 0
                -- So C_et·BL(K) + 4π + b(0) ≤ C_et·BL(K) + δ. Almost!
                -- C_et·BL(K) + 4π + b(0) ≤ C_et·BL(K) + M_fn(0) + 4π + b(0) = C_et·BL(K) + δ. ✓
                -- (↑(K-1)+1)·δ = K·δ (as naturals, K-1+1=K)
                -- So LHS = M_fn(K-1)+b(0) + K·δ ≤ C_et·BL(K) + δ + K·δ = C_et·BL(K) + (K+1)·δ = RHS. ✓
                have hK_nat : (↑(K - 1) : ℝ) + 1 = (K : ℝ) := by
                  have hK_sub : K - 1 + 1 = K := Nat.sub_add_cancel hK_pos
                  have : (↑(K - 1 + 1) : ℝ) = (↑K : ℝ) := by rw [hK_sub]
                  push_cast at this; linarith
                rw [hK_nat]
                -- Need: M_fn(K-1) + b(0) + K·δ ≤ C_et·BL(K) + δ·(K+1)
                -- i.e., M_fn(K-1) + b(0) ≤ C_et·BL(K) + δ
                suffices h_Mext_le : M_fn (K - 1) + b 0 ≤
                    C_et * (2 * Real.pi * (2 * (K : ℝ) + 3)) + δ by linarith
                -- M_fn(K-1) ≤ b(K-1) + 3π
                rcases Nat.eq_zero_or_pos (K - 1) with hKm10 | hKm1_pos
                · -- K-1 = 0, so K = 1
                  have : K = 1 := by omega
                  subst this
                  simp only [Nat.sub_self]
                  -- M_fn(0) + b(0) ≤ C_et·BL(1) + δ
                  simp only [hδ_def]; push_cast
                  nlinarith [Real.pi_pos, hCet_pos]
                · have hKm1_ge1 : 1 ≤ K - 1 := hKm1_pos
                  obtain ⟨R_Km1, h_bKm1_eq, C_R'', _, hCR''_le, h_RKm1_bd⟩ :=
                    Aristotle.Standalone.RSExpansionProof.signed_block_integral_expansion
                      (K - 1) hKm1_ge1
                  have h_bKm1_eq' : b (K - 1) = M_fn (K - 1) + R_Km1 := by
                    simp only [hb_def, hM_def] at h_bKm1_eq ⊢; linarith
                  -- M_fn(K-1) = b(K-1) - R_Km1 ≤ b(K-1) + |R_Km1| ≤ b(K-1) + 3π
                  have h_Rk_le_Km1 : |R_Km1| ≤ 3 * Real.pi := by
                    have h_bl_rpow := block_remainder_uniform_bound (K - 1)
                    have h_bl_nn : 0 ≤ (hardyStart (K - 1 + 1) - hardyStart (K - 1)) *
                        (hardyStart (K - 1)) ^ (-(3 : ℝ) / 4) :=
                      mul_nonneg (sub_nonneg.mpr (Aristotle.Standalone.OscPieceBigOAssembly.hardyStart_mono
                        (Nat.le_succ (K - 1))))
                        (rpow_nonneg (le_of_lt (by rw [hardyStart_formula]; positivity)) _)
                    -- (h_reassoc removed, using `by ring` inline in calc)
                    calc |R_Km1|
                        ≤ C_R'' * (hardyStart (K - 1 + 1) - hardyStart (K - 1)) *
                            (hardyStart (K - 1)) ^ (-(3 : ℝ) / 4) := h_RKm1_bd
                      _ = C_R'' * ((hardyStart (K - 1 + 1) - hardyStart (K - 1)) *
                            (hardyStart (K - 1)) ^ (-(3 : ℝ) / 4)) := by ring
                      _ ≤ (1 / 2) * (6 * Real.pi) :=
                          mul_le_mul hCR''_le h_bl_rpow h_bl_nn (by linarith)
                      _ = 3 * Real.pi := by ring
                  have h_M_le_b : M_fn (K - 1) ≤ b (K - 1) + 3 * Real.pi := by
                    rw [h_bKm1_eq']; linarith [neg_abs_le R_Km1]
                  calc M_fn (K - 1) + b 0
                      ≤ b (K - 1) + 3 * Real.pi + b 0 := by linarith
                    _ ≤ C_et * (2 * Real.pi * (2 * ((K - 1 : ℕ) : ℝ) + 3)) + 3 * Real.pi + b 0 := by
                        linarith [hb_le (K - 1)]
                    _ ≤ C_et * (2 * Real.pi * (2 * (K : ℝ) + 3)) + 4 * Real.pi + b 0 := by
                        have : C_et * (2 * Real.pi * (2 * ((K - 1 : ℕ) : ℝ) + 3)) ≤
                            C_et * (2 * Real.pi * (2 * (K : ℝ) + 3)) := by
                          gcongr
                          exact_mod_cast Nat.sub_le K 1
                        linarith [Real.pi_pos]
                    _ ≤ C_et * (2 * Real.pi * (2 * (K : ℝ) + 3)) + δ := by
                        simp only [hδ_def]; linarith [hM_nonneg 0]
      -- Combine: |∫₁ᵀ E| ≤ head + mid + partial ≤ C_sq * √T
      -- K ≤ √T (for the δ · (K+1) term)
      have hK_le_sqrtT : (K : ℝ) ≤ Real.sqrt T := by linarith [hK1_le_sqrtT]
      calc |∫ t in Set.Ioc 1 T, ErrorTerm t|
          = |(∫ t in Set.Ioc 1 (hardyStart 0), ErrorTerm t) +
             (∫ t in Set.Ioc (hardyStart 0) T, ErrorTerm t)| := by rw [h_split1]
        _ ≤ |∫ t in Set.Ioc 1 (hardyStart 0), ErrorTerm t| +
             |∫ t in Set.Ioc (hardyStart 0) T, ErrorTerm t| := abs_add_le _ _
        _ = |∫ t in Set.Ioc 1 (hardyStart 0), ErrorTerm t| +
            |(∫ t in Set.Ioc (hardyStart 0) (hardyStart K), ErrorTerm t) +
             (∫ t in Set.Ioc (hardyStart K) T, ErrorTerm t)| := by rw [h_split2]
        _ ≤ |∫ t in Set.Ioc 1 (hardyStart 0), ErrorTerm t| +
            (|∫ t in Set.Ioc (hardyStart 0) (hardyStart K), ErrorTerm t| +
             |∫ t in Set.Ioc (hardyStart K) T, ErrorTerm t|) := by
            gcongr; exact abs_add_le _ _
        _ ≤ C_et * hardyStart 0 +
            ((C_et * (2 * Real.pi * (2 * ↑K + 3)) +
              (M_fn 0 + 4 * Real.pi + b 0) * (↑K + 1)) +
             C_et * (2 * Real.pi * (2 * ↑K + 3))) := by gcongr
        _ = C_et * hardyStart 0 + C_et * 4 * Real.pi * (2 * ↑K + 3) +
            (M_fn 0 + 4 * Real.pi + b 0) * (↑K + 1) := by ring
        _ ≤ C_et * hardyStart 0 + C_et * 4 * Real.pi * (2 * Real.sqrt T + 1) +
            (M_fn 0 + 4 * Real.pi + b 0) * (Real.sqrt T + 1) := by
            have h_d_nn : 0 ≤ M_fn 0 + 4 * Real.pi + b 0 := by
              nlinarith [hM_nonneg 0, Real.pi_pos, hb_nonneg 0]
            have h1 : C_et * 4 * Real.pi * (2 * ↑K + 3) ≤
                C_et * 4 * Real.pi * (2 * Real.sqrt T + 1) := by
              apply mul_le_mul_of_nonneg_left h2K3_le; nlinarith [Real.pi_pos]
            have h2 : (M_fn 0 + 4 * Real.pi + b 0) * (↑K + 1) ≤
                (M_fn 0 + 4 * Real.pi + b 0) * (Real.sqrt T + 1) := by
              apply mul_le_mul_of_nonneg_left _ h_d_nn; linarith [hK_le_sqrtT]
            linarith
        _ = (C_et * hardyStart 0 + C_et * 4 * Real.pi + (M_fn 0 + 4 * Real.pi + b 0)) +
            (C_et * 8 * Real.pi + (M_fn 0 + 4 * Real.pi + b 0)) * Real.sqrt T := by ring
        _ ≤ (C_et * hardyStart 0 + C_et * 4 * Real.pi + (M_fn 0 + 4 * Real.pi + b 0)) *
            Real.sqrt T +
            (C_et * 8 * Real.pi + (M_fn 0 + 4 * Real.pi + b 0)) * Real.sqrt T := by
            have h_nn : 0 ≤ C_et * hardyStart 0 + C_et * 4 * Real.pi +
                (M_fn 0 + 4 * Real.pi + b 0) := by
              nlinarith [hhs_gt1 0, Real.pi_pos, hM_nonneg 0, hb_nonneg 0]
            nlinarith [mul_le_mul_of_nonneg_left h_sqrtT_ge1 h_nn]
        _ = (C_et * hardyStart 0 + C_et * 4 * Real.pi + (M_fn 0 + 4 * Real.pi + b 0) +
            C_et * 8 * Real.pi + (M_fn 0 + 4 * Real.pi + b 0)) * Real.sqrt T := by ring
        _ ≤ C_sq * Real.sqrt T := by
            apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg T)
            simp only [C_sq]; nlinarith [Real.pi_pos, hM_nonneg 0, hb_nonneg 0]
    · -- T < hardyStart 0: constant bound absorbed into √T
      push_neg at hT_ge_hs0
      have hT_lt_hs0 := hT_ge_hs0
      calc |∫ t in Set.Ioc 1 T, ErrorTerm t|
          ≤ C_et * T := h_linear T hT
        _ ≤ C_et * hardyStart 0 := by
            have : T ≤ hardyStart 0 := le_of_lt hT_lt_hs0
            exact mul_le_mul_of_nonneg_left this hCet_pos.le
        _ ≤ C_et * hardyStart 0 * Real.sqrt T :=
            le_mul_of_one_le_right (mul_nonneg hCet_pos.le (by linarith [hhs_gt1 0])) h_sqrtT_ge1
        _ ≤ C_sq * Real.sqrt T := by
            apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg T)
            simp only [C_sq]; nlinarith [Real.pi_pos, hM_nonneg 0, hb_nonneg 0]

-- ============================================================
-- Step 4: Assembly via MainTerm = hardyZ - ErrorTerm
-- ============================================================

theorem b2_first_moment_core
    (h_exp : ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4)) :
    ∀ ε : ℝ, ε > 0 →
      ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
        |∫ t in Set.Ioc 1 T, MainTerm t| ≤ C * T ^ (1 / 2 + ε) := by
  intro ε hε
  obtain ⟨C₁, hC₁_pos, h_hardyZ⟩ :=
    HardyZFirstMomentIBP.hardyZ_first_moment_sublinear ε hε
  obtain ⟨C₂, hC₂_pos, h_et_sublinear⟩ :=
    errorTerm_signed_integral_sublinear h_exp ε hε
  refine ⟨C₁ + C₂, by positivity, fun T hT => ?_⟩
  have h_hardyZ_intble : IntegrableOn hardyZ (Set.Ioc 1 T) :=
    hardyZ_integrable T
  have h_error_intble : IntegrableOn ErrorTerm (Set.Ioc 1 T) :=
    errorTerm_integrable T
  have h_main_eq : ∀ t : ℝ,
      MainTerm t = hardyZ t - ErrorTerm t := fun t => by
    unfold ErrorTerm; ring
  have h_int_split :
      ∫ t in Set.Ioc 1 T, MainTerm t =
        (∫ t in Set.Ioc 1 T, hardyZ t) - (∫ t in Set.Ioc 1 T, ErrorTerm t) := by
    rw [show ∫ t in Set.Ioc 1 T, MainTerm t =
        ∫ t in Set.Ioc 1 T, (hardyZ t - ErrorTerm t) from by
      congr 1; ext t; exact h_main_eq t]
    exact MeasureTheory.integral_sub h_hardyZ_intble h_error_intble
  calc |∫ t in Set.Ioc 1 T, MainTerm t|
      = |(∫ t in Set.Ioc 1 T, hardyZ t) - (∫ t in Set.Ioc 1 T, ErrorTerm t)| := by
        rw [h_int_split]
    _ ≤ |∫ t in Set.Ioc 1 T, hardyZ t| + |∫ t in Set.Ioc 1 T, ErrorTerm t| := by
        have := norm_sub_le (∫ t in Set.Ioc 1 T, hardyZ t) (∫ t in Set.Ioc 1 T, ErrorTerm t)
        simp only [Real.norm_eq_abs] at this
        exact this
    _ ≤ C₁ * T ^ (1 / 2 + ε) + C₂ * T ^ (1 / 2 + ε) := by
        gcongr
        · exact h_hardyZ T hT
        · exact h_et_sublinear T hT
    _ = (C₁ + C₂) * T ^ (1 / 2 + ε) := by ring

end Aristotle.Standalone.B2FirstMomentFromExpansion
