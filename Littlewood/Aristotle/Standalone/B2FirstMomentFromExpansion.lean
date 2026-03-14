/-
B2 first moment bound from the RS expansion hypothesis.

SORRY COUNT: 1 (signed_block_integrals_monotone)
WARNING COUNT: 1

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

/-- Monotonicity of signed block integrals: b(k) := (-1)^k · ∫_{block k} ErrorTerm is
    nonneg and monotone increasing.

    SUB-SORRY: requires per-block analysis of the leading RS term integral.
    Reference: Siegel 1932 §3; Titchmarsh §4.16. -/
private theorem signed_block_integrals_monotone
    (h_exp : ∃ C_R > (0 : ℝ), ∀ k : ℕ, ∀ t : ℝ,
      hardyStart k ≤ t → t ≤ hardyStart (k + 1) → t > 0 →
        |ErrorTerm t - (-1 : ℝ) ^ k * (2 * Real.pi / t) ^ ((1 : ℝ) / 4) *
          rsPsi (blockParam k t)| ≤ C_R * t ^ (-(3 : ℝ) / 4)) :
    Monotone (fun k : ℕ => (-1 : ℝ) ^ k *
      ∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t) := by
  sorry

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
  have hb_mono : Monotone b := signed_block_integrals_monotone ⟨C_R, hCR_pos, h_rs⟩
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
    -- Step 2: Prove the √T bound using block decomposition + alternating cancellation
    -- Constant: absorbs head (C_et * hs0) + middle (C_et * 4π(2K+3)) via √T ≥ 1
    set C_sq := C_et * hardyStart 0 + C_et * 4 * Real.pi * 3 + C_et * 8 * Real.pi + 1
    refine ⟨C_sq, by positivity, fun T hT => ?_⟩
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
        exact Real.sqrt_le_sqrt (le_trans hK1_sq (div_le_self (by linarith) (by positivity)))
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
        h_E_intble.mono_set (fun t ht => ⟨lt_of_lt_of_le (hhs_gt1 0) ht.1, ht.2⟩)
      have h_E_mid : IntegrableOn ErrorTerm (Set.Ioc (hardyStart 0) (hardyStart K)) :=
        h_E_intble.mono_set (fun t ht => ⟨lt_of_lt_of_le (hhs_gt1 0) ht.1,
          le_trans ht.2 hK_le⟩)
      have h_E_partial : IntegrableOn ErrorTerm (Set.Ioc (hardyStart K) T) :=
        h_E_intble.mono_set (fun t ht => ⟨lt_of_lt_of_le (hhs_gt1 0)
          (lt_of_lt_of_le (hhs_gt1 K) ht.1), ht.2⟩)
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
        h_linear (hardyStart 0) (by rw [hardyStart_formula]; nlinarith [Real.pi_gt_three])
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
      -- |middle| ≤ C_et * 2π(2K+3) via alternating cancellation
      have h_mid_le : |∫ t in Set.Ioc (hardyStart 0) (hardyStart K), ErrorTerm t| ≤
          C_et * (2 * Real.pi * (2 * (K : ℝ) + 3)) := by
        rcases Nat.eq_zero_or_pos K with hK0 | hK_pos
        · subst hK0; simp [Set.Ioc_self]; exact mul_nonneg hCet_pos.le (by positivity)
        · -- K ≥ 1: block decomposition + alternating_sum_le_last
          have h_bp_mono : ∀ k, k < K → hardyStart k ≤ hardyStart (k + 1) :=
            fun k _ => Aristotle.Standalone.OscPieceBigOAssembly.hardyStart_mono (Nat.le_succ k)
          have h_bp_intble : ∀ k, k < K →
              IntegrableOn ErrorTerm (Set.Ioc (hardyStart k) (hardyStart (k + 1))) :=
            fun k _ => (errorTerm_integrable (hardyStart (k + 1))).mono_set
              (fun t ht => ⟨lt_trans (hhs_gt1 k) ht.1, ht.2⟩)
          -- ∫_{hs0}^{hsK} E = ∑_{k<K} ∫_{hsk}^{hsk+1} E
          have h_mid_split :
              ∫ t in Set.Ioc (hardyStart 0) (hardyStart K), ErrorTerm t =
                ∑ k ∈ Finset.range K,
                  ∫ t in Set.Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t :=
            Aristotle.IntervalPartition.integral_split_finitely ErrorTerm hardyStart K
              h_bp_mono h_bp_intble
          -- Each block integral = (-1)^k * b(k)
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
          -- Apply alternating_sum_le_last: |∑_{k<K} (-1)^k b(k)| ≤ b(K-1)
          rw [h_mid_split, h_sum_eq, show K = (K - 1) + 1 from by omega]
          calc |∑ k ∈ Finset.range ((K - 1) + 1), (-1 : ℝ) ^ k * b k|
              ≤ b (K - 1) :=
                AbelSummation.alternating_sum_le_last b hb_nonneg hb_mono (K - 1)
            _ ≤ C_et * (2 * Real.pi * (2 * ((K - 1 : ℕ) : ℝ) + 3)) := hb_le (K - 1)
            _ ≤ C_et * (2 * Real.pi * (2 * (K : ℝ) + 3)) := by
                gcongr; push_cast; omega
      -- Combine: |∫₁ᵀ E| ≤ head + mid + partial ≤ C_sq * √T
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
        _ ≤ C_et * hardyStart 0 + (C_et * (2 * Real.pi * (2 * ↑K + 3)) +
            C_et * (2 * Real.pi * (2 * ↑K + 3))) := by gcongr
        _ = C_et * hardyStart 0 + C_et * 4 * Real.pi * (2 * ↑K + 3) := by ring
        _ ≤ C_et * hardyStart 0 + C_et * 4 * Real.pi * (2 * Real.sqrt T + 1) := by
            gcongr; linarith [h2K3_le]
        _ = (C_et * hardyStart 0 + C_et * 4 * Real.pi) +
            C_et * 8 * Real.pi * Real.sqrt T := by ring
        _ ≤ (C_et * hardyStart 0 + C_et * 4 * Real.pi) * Real.sqrt T +
            C_et * 8 * Real.pi * Real.sqrt T := by
            gcongr
            · exact mul_nonneg (by positivity) (Real.sqrt_nonneg T)
            · exact h_sqrtT_ge1
        _ = (C_et * hardyStart 0 + C_et * 4 * Real.pi + C_et * 8 * Real.pi) *
            Real.sqrt T := by ring
        _ ≤ C_sq * Real.sqrt T := by
            gcongr; simp only [C_sq]; linarith [Real.pi_pos]
    · -- T < hardyStart 0: constant bound absorbed into √T
      push_neg at hT_ge_hs0
      calc |∫ t in Set.Ioc 1 T, ErrorTerm t|
          ≤ C_et * T := h_linear T hT
        _ ≤ C_et * hardyStart 0 := by gcongr; linarith
        _ ≤ C_et * hardyStart 0 * Real.sqrt T :=
            le_mul_of_one_le_right (by positivity) h_sqrtT_ge1
        _ ≤ C_sq * Real.sqrt T := by
            gcongr; simp only [C_sq]; linarith [hCet_pos, Real.pi_pos]

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
