/-
Off-resonance integral bounds via smooth complex VdC.

This file bridges the complex Van der Corput bound (ComplexVdC) with the
Hardy cosine smooth representation (HardyCosSmooth, HardyCosExpOmega) to
prove `off_resonance_integral_bound_smooth` without requiring global differentiability
of `hardyTheta`.

The key chain:
1. cos(θ(t) - t·log(n+1)) = Re(hardyCosExp n t)           [HardyCosSmooth]
2. hardyCosExp has angular velocity ω(t) = thetaDeriv(t) - log(n+1)  [HardyCosExpOmega]
3. ω ≥ m > 0 on block k (from monotonicity + lower bound, for large k)
4. ω' ≥ 0 (from thetaDeriv strictly increasing)
5. Complex VdC gives ‖∫ hardyCosExp‖ ≤ 3/m                [ComplexVdC]
6. |∫ cos(...)| = |∫ Re(hardyCosExp)| ≤ ‖∫ hardyCosExp‖ ≤ 3/m
7. For small k, use trivial bound |∫ cos| ≤ block length

Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.ComplexVdC
import Littlewood.Aristotle.HardyCosSmooth
import Littlewood.Aristotle.HardyCosExpOmega
import Littlewood.Aristotle.ThetaDerivMonotone
import Littlewood.Aristotle.ThetaDerivAsymptotic
import Littlewood.Aristotle.HardyNProperties

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.OffResonanceSmoothVdC

open MeasureTheory Set Real Filter Topology Complex
open HardyEstimatesPartial HardyCosSmooth
open Aristotle.HardyNProperties
open ThetaDerivAsymptotic ThetaDerivMonotone
open Aristotle.HardyCosExpOmega

-- ============================================================
-- Section 1: ω(t) = thetaDeriv(t) - log(n+1) infrastructure
-- ============================================================

/-- The instantaneous frequency of mode n. -/
def modeOmega (n : ℕ) (t : ℝ) : ℝ :=
  thetaDeriv t - Real.log (↑n + 1)

/-- modeOmega is differentiable (thetaDeriv has HasDerivAt everywhere). -/
lemma differentiable_modeOmega (n : ℕ) : Differentiable ℝ (modeOmega n) := by
  intro t
  exact ((thetaDeriv_hasDerivAt t).differentiableAt.sub
    (differentiableAt_const _))

/-- The derivative of modeOmega equals the derivative of thetaDeriv. -/
lemma deriv_modeOmega (n : ℕ) (t : ℝ) :
    deriv (modeOmega n) t = deriv thetaDeriv t := by
  have htd := thetaDeriv_hasDerivAt t
  have h : HasDerivAt (modeOmega n) (-(1 / 4) * (∑' n_1 : ℕ,
      1 / (sOfT t + (↑n_1 : ℂ)) ^ 2).im) t := by
    show HasDerivAt (fun t => thetaDeriv t - Real.log (↑n + 1)) _ t
    have := htd.sub (hasDerivAt_const t (Real.log (↑n + 1)))
    simp only [sub_zero] at this
    exact this
  rw [h.deriv, htd.deriv]

/-- deriv thetaDeriv is nonneg for t > 0 (thetaDeriv' > 0). -/
lemma deriv_thetaDeriv_nonneg (t : ℝ) (ht : 0 < t) :
    0 ≤ deriv thetaDeriv t := by
  obtain ⟨d, hd, hd_pos⟩ := thetaDeriv_deriv_pos t ht
  rw [hd.deriv]
  exact le_of_lt hd_pos

/-- deriv modeOmega is nonneg for t > 0. -/
lemma deriv_modeOmega_nonneg (n : ℕ) (t : ℝ) (ht : 0 < t) :
    0 ≤ deriv (modeOmega n) t := by
  rw [deriv_modeOmega]
  exact deriv_thetaDeriv_nonneg t ht

-- ============================================================
-- Section 2: ‖hardyCosExp‖ = 1
-- ============================================================

/-- hardyCosExp has unit norm (it equals exp(i·phase)). -/
lemma norm_hardyCosExp (n : ℕ) (t : ℝ) : ‖hardyCosExp n t‖ = 1 := by
  rw [hardyCosExp_eq_cexp_phaseArg, mul_comm]
  exact norm_exp_ofReal_mul_I _

-- ============================================================
-- Section 3: Lower bound on modeOmega (eventual version)
-- ============================================================

/-- hardyStart k is positive for k ≥ 0. -/
private lemma hardyStart_pos (k : ℕ) : 0 < hardyStart k := by
  rw [hardyStart_formula]
  positivity

/-- For sufficiently large k, with n < k, modeOmega n ≥ log((k+1)/(n+1))/2 on block k.

    Key idea: thetaDeriv(t) ≥ thetaDeriv(hardyStart k) ≥ log(k+1) - C/(k+1)²
    by monotonicity + theta_deriv_at_stationary_point. For large k the error is absorbed
    since log((k+1)/(n+1)) ≥ 1/(k+1) (from log(1+x) ≥ x/(1+x)). -/
lemma modeOmega_lower_bound_eventually :
    ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k → ∀ n : ℕ, n < k →
      ∀ t : ℝ, hardyStart k ≤ t → t ≤ hardyStart (k + 1) →
        Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) / 2 ≤ modeOmega n t := by
  obtain ⟨C, hC_pos, hC_bound⟩ := theta_deriv_at_stationary_point
  -- Pick K₀ so that 2C ≤ K₀ + 1, ensuring C/(k+1)² ≤ 1/(2(k+1)) ≤ log((k+1)/(n+1))/2
  obtain ⟨K₀, hK₀⟩ := exists_nat_ge (2 * C)
  refine ⟨K₀, fun k hk n hnk t ht_lo ht_hi => ?_⟩
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hkn_succ : (n : ℝ) + 1 < (k : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ hnk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := Nat.pos_of_ne_zero (by omega)
    exact_mod_cast this
  have ha_pos : 0 < hardyStart k := hardyStart_pos k
  -- thetaDeriv is increasing: thetaDeriv(t) ≥ thetaDeriv(hardyStart k)
  have h_mono : thetaDeriv (hardyStart k) ≤ thetaDeriv t := by
    rcases eq_or_lt_of_le ht_lo with h_eq | h_lt
    · rw [← h_eq]
    · exact le_of_lt (thetaDeriv_strictMonoOn (mem_Ioi.mpr ha_pos)
        (mem_Ioi.mpr (lt_of_lt_of_le ha_pos ht_lo)) h_lt)
  -- hardyStart k = 2π(k+1)²
  have h_hs_eq : hardyStart k = 2 * Real.pi * ((k : ℝ) + 1) ^ 2 := by
    unfold hardyStart; ring
  -- |thetaDeriv(2π(k+1)²) - log(k+1)| ≤ C/(k+1)²
  have h_sp := hC_bound k
  -- thetaDeriv(hardyStart k) ≥ log(k+1) - C/(k+1)²
  have h_td_lower : Real.log ((k : ℝ) + 1) - C / ((k : ℝ) + 1) ^ 2
      ≤ thetaDeriv (hardyStart k) := by
    rw [h_hs_eq]
    linarith [neg_abs_le (thetaDeriv (2 * Real.pi * (↑k + 1) ^ 2) - Real.log (↑k + 1))]
  -- modeOmega n t ≥ log((k+1)/(n+1)) - C/(k+1)²
  have h_omega_lower : Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) - C / ((k : ℝ) + 1) ^ 2
      ≤ modeOmega n t := by
    show _ ≤ thetaDeriv t - Real.log (↑n + 1)
    rw [Real.log_div (ne_of_gt hk1_pos) (ne_of_gt hn1_pos)]
    linarith
  -- Suffices: C/(k+1)² ≤ log((k+1)/(n+1))/2
  suffices h_suff : C / ((k : ℝ) + 1) ^ 2 ≤
      Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) / 2 by linarith
  -- Lower bound: log((k+1)/(n+1)) ≥ log((k+1)/k) ≥ 1/(k+1)
  -- since (k+1)/(n+1) ≥ (k+1)/k (as n+1 ≤ k)
  have hn1_le_k : (n : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hnk
  have h_ratio_lower : ((k : ℝ) + 1) / (k : ℝ) ≤ ((k : ℝ) + 1) / ((n : ℝ) + 1) :=
    div_le_div_of_nonneg_left hk1_pos.le (by positivity) hn1_le_k
  have h_log_mono : Real.log (((k : ℝ) + 1) / (k : ℝ)) ≤
      Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) :=
    Real.log_le_log (by positivity) h_ratio_lower
  -- log((k+1)/k) ≥ 1/(k+1) via one_sub_inv_le_log_of_pos
  have h_log_ge : 1 / ((k : ℝ) + 1) ≤ Real.log (((k : ℝ) + 1) / (k : ℝ)) := by
    have hy_pos : (0 : ℝ) < ((k : ℝ) + 1) / (k : ℝ) := by positivity
    -- one_sub_inv_le_log_of_pos: 1 - y⁻¹ ≤ log(y) for y > 0
    have h := Real.one_sub_inv_le_log_of_pos hy_pos
    -- 1 - ((k+1)/k)⁻¹ = 1 - k/(k+1) = 1/(k+1)
    have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
    have hk1_ne : (k : ℝ) + 1 ≠ 0 := ne_of_gt hk1_pos
    calc 1 / ((k : ℝ) + 1) = 1 - (((k : ℝ) + 1) / (k : ℝ))⁻¹ := by field_simp; ring
      _ ≤ Real.log (((k : ℝ) + 1) / (k : ℝ)) := h
  -- Combine: log((k+1)/(n+1)) ≥ 1/(k+1), so log(…)/2 ≥ 1/(2(k+1))
  -- Need: C/(k+1)² ≤ 1/(2(k+1)), i.e., 2C ≤ k+1
  have h_2C_le : 2 * C ≤ (k : ℝ) + 1 := by
    calc 2 * C ≤ (K₀ : ℝ) := hK₀
      _ ≤ (k : ℝ) := Nat.cast_le.mpr hk
      _ ≤ (k : ℝ) + 1 := le_add_of_nonneg_right (by norm_num)
  -- C/(k+1)² ≤ log((k+1)/(n+1))/2 via chain of inequalities
  -- Step: C/(k+1)² ≤ 1/(2(k+1)) since 2C ≤ k+1
  -- Step: 1/(2(k+1)) = (1/(k+1))/2 ≤ log((k+1)/k)/2 ≤ log((k+1)/(n+1))/2
  have h_step1 : C / ((k : ℝ) + 1) ^ 2 ≤ 1 / (2 * ((k : ℝ) + 1)) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < ((k : ℝ) + 1) ^ 2)
        (by positivity : (0 : ℝ) < 2 * ((k : ℝ) + 1))]
    nlinarith [sq_nonneg ((k : ℝ) + 1)]
  have h_step2 : 1 / (2 * ((k : ℝ) + 1)) ≤ Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) / 2 := by
    have h1 : 1 / ((k : ℝ) + 1) ≤ Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) :=
      le_trans h_log_ge h_log_mono
    have h2 : 1 / (2 * ((k : ℝ) + 1)) = 1 / ((k : ℝ) + 1) / 2 := by field_simp
    linarith
  linarith

-- ============================================================
-- Section 4: Continuity of deriv modeOmega
-- ============================================================

/-- Summability of 16/(n+1)² (reproduced from ThetaDerivMonotone). -/
private lemma summable_sixteen_div_sq :
    Summable (fun n : ℕ => 16 / ((↑n : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (↑n : ℝ) ^ 2) 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  simp only [Nat.cast_add, Nat.cast_one] at h
  exact (h.mul_left 16).congr (fun n => by ring)

/-- Uniform norm bound: ‖1/(sOfT t + n)²‖ ≤ 16/(n+1)² for all t. -/
private lemma norm_inv_sq_sOfT_le (t : ℝ) (n : ℕ) :
    ‖(1 : ℂ) / (sOfT t + (↑n : ℂ)) ^ 2‖ ≤ 16 / ((↑n : ℝ) + 1) ^ 2 := by
  have h14 := norm_sOfT_add_nat_ge t n
  have h14_pos : (0 : ℝ) < ↑n + 1/4 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have h1_pos : (0 : ℝ) < ↑n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hstep1 : ‖(1 : ℂ) / (sOfT t + (↑n : ℂ)) ^ 2‖ ≤ 1 / ((↑n : ℝ) + 1/4) ^ 2 := by
    rw [one_div, norm_inv, norm_pow, one_div]
    apply inv_anti₀ (by positivity)
    exact sq_le_sq' (by linarith [norm_nonneg (sOfT t + (↑n : ℂ))]) h14
  have hstep2 : 1 / ((↑n : ℝ) + 1/4) ^ 2 ≤ 16 / ((↑n : ℝ) + 1) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  linarith

/-- Each summand of the trigamma series is continuous in t. -/
private lemma continuous_inv_sq_summand (n : ℕ) :
    Continuous (fun t : ℝ => (1 : ℂ) / (sOfT t + (↑n : ℂ)) ^ 2) := by
  apply Continuous.div continuous_const
  · apply Continuous.pow
    apply Continuous.add _ continuous_const
    show Continuous fun t => sOfT t
    exact continuous_const.add (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_id |>.div_const 2))
  · intro t; exact pow_ne_zero 2 (sOfT_add_nat_ne_zero t n)

/-- The derivative of thetaDeriv is continuous. -/
lemma continuous_deriv_thetaDeriv : Continuous (deriv thetaDeriv) := by
  have h_eq : deriv thetaDeriv = fun t =>
      -(1 / 4) * (∑' n : ℕ, 1 / (sOfT t + (↑n : ℂ)) ^ 2).im := by
    ext t; exact (thetaDeriv_hasDerivAt t).deriv
  rw [h_eq]
  apply Continuous.mul continuous_const
  exact Complex.continuous_im.comp
    (continuous_tsum (fun n => continuous_inv_sq_summand n)
      summable_sixteen_div_sq (fun n t => norm_inv_sq_sOfT_le t n))

/-- The derivative of modeOmega is continuous. -/
lemma continuous_deriv_modeOmega (n : ℕ) : Continuous (deriv (modeOmega n)) := by
  have h : deriv (modeOmega n) = deriv thetaDeriv := by
    ext t; exact deriv_modeOmega n t
  rw [h]
  exact continuous_deriv_thetaDeriv

-- ============================================================
-- Section 5: Block length bound
-- ============================================================

/-- Block length: hardyStart(k+1) - hardyStart(k) = 2π(2k+3). -/
private lemma block_length (k : ℕ) :
    hardyStart (k + 1) - hardyStart k = 2 * Real.pi * (2 * (k : ℝ) + 3) := by
  rw [hardyStart_formula, hardyStart_formula]
  push_cast; ring

/-- Block length is positive. -/
private lemma block_length_pos (k : ℕ) :
    0 < hardyStart (k + 1) - hardyStart k := by
  rw [block_length]; positivity

-- ============================================================
-- Section 6: Main theorem — existential constant version
-- ============================================================

/-- Off-resonance integral bound via smooth complex VdC, with existential constant.

    For large k: apply complex_vdc_angular_re with ω lower bound from modeOmega_lower_bound_eventually.
    For small k (< K₀): trivially bound |∫ cos| ≤ block_length ≤ C_small/log(...). -/
theorem off_resonance_integral_bound_smooth :
    ∃ C_vdc > 0, ∀ k : ℕ, ∀ n : ℕ, n < k → 1 ≤ k →
      |∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
        Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))|
          ≤ C_vdc / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
  obtain ⟨K₀, hK₀⟩ := modeOmega_lower_bound_eventually
  -- For small k: |∫ cos| ≤ block_length ≤ 2π(2K₀+1) (since k < K₀ means 2k+3 ≤ 2K₀+1)
  -- And 1/log((k+1)/(n+1)) ≥ 1/log(K₀+1) (since k < K₀ means (k+1)/(n+1) ≤ K₀+1)
  -- So |∫ cos| ≤ 2π(2K₀+1) = 2π(2K₀+1) · (log(K₀+1)/log(K₀+1))
  --            ≤ [2π(2K₀+1)·log(K₀+1)] / log((k+1)/(n+1))
  set C_small := 2 * Real.pi * (2 * (K₀ : ℝ) + 3) * Real.log ((K₀ : ℝ) + 2) with hC_small_def
  refine ⟨max 6 C_small, by positivity, fun k n hnk hk => ?_⟩
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hkn : (n : ℝ) + 1 < (k : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ hnk
  have hratio_gt : 1 < ((k : ℝ) + 1) / ((n : ℝ) + 1) := by rw [one_lt_div hn1_pos]; linarith
  have hlog_pos : 0 < Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := Real.log_pos hratio_gt
  have hab : hardyStart k ≤ hardyStart (k + 1) := by
    rw [hardyStart_formula, hardyStart_formula]; gcongr; linarith
  by_cases hk_large : K₀ ≤ k
  · -- Case 1: k ≥ K₀ — use VdC
    set m := Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) / 2 with hm_def
    have hm_pos : 0 < m := by positivity
    set a := hardyStart k with ha_def
    set b := hardyStart (k + 1) with hb_def
    have ha_pos : 0 < a := hardyStart_pos k
    have h_cos_eq : (fun t => Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1)))
        = (fun t => (hardyCosExp n t).re) := funext (fun t => hardyCos_eq_re_hardyCosExp n t)
    rw [h_cos_eq, ← intervalIntegral.integral_of_le hab]
    have h_bound := Aristotle.ComplexVdC.complex_vdc_angular_re
      (fun t => hardyCosExp n t) (modeOmega n) a b m hab hm_pos
      (fun t _ht => by
        have h := hardyCosExp_angular_velocity n t
        simp only [modeOmega, Nat.cast_succ] at h ⊢
        exact h)
      (fun t _ht => le_of_eq (norm_hardyCosExp n t))
      (differentiable_modeOmega n)
      (continuous_deriv_modeOmega n)
      (fun t ht => hK₀ k hk_large n hnk t ht.1 ht.2)
      (fun t ht => deriv_modeOmega_nonneg n t (lt_of_lt_of_le ha_pos ht.1))
    calc |∫ t in a..b, (hardyCosExp n t).re|
        ≤ 3 / m := h_bound
      _ = 6 / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by rw [hm_def]; ring
      _ ≤ max 6 C_small / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
          apply div_le_div_of_nonneg_right (le_max_left _ _) (by linarith)
  · -- Case 2: k < K₀ — trivial bound
    push_neg at hk_large
    -- Bound |∫ cos| ≤ block_length via norm_setIntegral_le_of_norm_le_const
    have h_vol_finite : volume (Ioc (hardyStart k) (hardyStart (k + 1))) < ⊤ := by
      rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    have h_trivial : ‖∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
        Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))‖
        ≤ 1 * volume.real (Ioc (hardyStart k) (hardyStart (k + 1))) :=
      norm_setIntegral_le_of_norm_le_const h_vol_finite (fun t _ => by
        rw [Real.norm_eq_abs]; exact abs_cos_le_one _)
    rw [one_mul, measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (le_of_lt (block_length_pos k)),
        Real.norm_eq_abs] at h_trivial
    -- Block length ≤ 2π(2K₀+3) since k ≤ K₀-1
    have hk_le_K₀ : (k : ℝ) + 1 ≤ (K₀ : ℝ) := by exact_mod_cast hk_large
    have h_bl_bound : hardyStart (k + 1) - hardyStart k ≤ 2 * Real.pi * (2 * (K₀ : ℝ) + 3) := by
      rw [block_length]; nlinarith [hk_le_K₀, Real.pi_pos]
    -- (k+1)/(n+1) ≤ k+1 ≤ K₀ ≤ K₀+2
    have h_ratio_upper : ((k : ℝ) + 1) / ((n : ℝ) + 1) ≤ (K₀ : ℝ) + 2 := by
      calc ((k : ℝ) + 1) / ((n : ℝ) + 1)
          ≤ (k : ℝ) + 1 := by rw [div_le_iff₀ hn1_pos]; nlinarith
        _ ≤ (K₀ : ℝ) := hk_le_K₀
        _ ≤ (K₀ : ℝ) + 2 := by linarith
    have hK02_gt : (1 : ℝ) < (K₀ : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) K₀]
    have h_log_upper : Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) ≤
        Real.log ((K₀ : ℝ) + 2) :=
      Real.log_le_log (by positivity) h_ratio_upper
    have hlogK_pos : 0 < Real.log ((K₀ : ℝ) + 2) := Real.log_pos hK02_gt
    calc |∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
            Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))|
        ≤ hardyStart (k + 1) - hardyStart k := h_trivial
      _ ≤ 2 * Real.pi * (2 * (K₀ : ℝ) + 3) := h_bl_bound
      _ = C_small / Real.log ((K₀ : ℝ) + 2) := by
          rw [hC_small_def, mul_div_cancel_right₀ _ (ne_of_gt hlogK_pos)]
      _ ≤ C_small / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
          apply div_le_div_of_nonneg_left (by rw [hC_small_def]; positivity) hlog_pos h_log_upper
      _ ≤ max 6 C_small / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
          apply div_le_div_of_nonneg_right (le_max_right _ _) (by linarith)

end Aristotle.OffResonanceSmoothVdC
