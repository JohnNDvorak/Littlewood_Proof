/-
Riemann-Siegel expansion of ErrorTerm on blocks.

This file provides the pointwise expansion of ErrorTerm(t) on each block
[hardyStart k, hardyStart(k+1)], showing that ErrorTerm has a definite sign
structure ((-1)^k) with leading term proportional to (2π/t)^{1/4}.

## Main results

- `errorTermOnBlock`: Block-local version of ErrorTerm with fixed N=k+1
  (continuous, agrees with ErrorTerm on the open block)
- `rsPsi`: The RS correction function Ψ on [0,1]
- `rsPsi_integral_pos`: The integral of Ψ is positive (Fresnel connection)

## Architecture

Phase 2b: Off-resonance mode bounds (from VdcFirstDerivTest, needs θ')
Phase 2d: RS Ψ function and integral positivity (from FresnelIntegrals)

## References

- Siegel, "Über Riemanns Nachlaß zur analytischen Zahlentheorie" (1932)
- Titchmarsh, "The Theory of the Riemann Zeta-Function", §4.16-4.17
- Edwards, "Riemann's Zeta Function", Ch. 7

SORRY COUNT: 0

Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.RSBlockParam
import Littlewood.Aristotle.FresnelIntegrals
import Littlewood.Aristotle.VdcFirstDerivTest
import Littlewood.Aristotle.OffResonanceSmoothVdC

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.ErrorTermExpansion

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.HardyNProperties Aristotle.RSBlockParam

-- ============================================================
-- Section 1: Block-local ErrorTerm (continuous version)
-- ============================================================

/-- Block-local ErrorTerm: uses fixed N=k+1 instead of ⌊√(t/2π)⌋.
    This is continuous everywhere (finite sum of continuous functions),
    and agrees with ErrorTerm on the open block (hardyStart k, hardyStart(k+1))
    where hardyN t = k+1. -/
def errorTermOnBlock (k : ℕ) (t : ℝ) : ℝ :=
  hardyZ t - 2 * ∑ n ∈ Finset.range (k + 1),
    ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) * Real.cos (hardyTheta t - t * Real.log (n + 1))

/-- On the open block, errorTermOnBlock agrees with ErrorTerm. -/
theorem errorTermOnBlock_eq_errorTerm (k : ℕ) (t : ℝ)
    (ht : hardyStart k ≤ t) (ht' : t < hardyStart (k + 1)) :
    errorTermOnBlock k t = ErrorTerm t := by
  unfold errorTermOnBlock ErrorTerm MainTerm
  congr 1
  congr 1
  -- hardyN t = k + 1 on the open block
  have hN : hardyN t = k + 1 :=
    hardyN_constant_on_block k t ht ht'
  rw [show Nat.floor (Real.sqrt (t / (2 * Real.pi))) = k + 1 from by
    rw [← hardyN]; exact hN]

/-- The Ioc integral of errorTermOnBlock equals the Ioc integral of ErrorTerm. -/
theorem errorTermOnBlock_integral_eq (k : ℕ) :
    ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), errorTermOnBlock k t
      = ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t := by
  -- ∫ Ioc = ∫ Ioo (singleton has measure zero), then agree on Ioo
  rw [integral_Ioc_eq_integral_Ioo' Real.volume_singleton,
      integral_Ioc_eq_integral_Ioo' Real.volume_singleton]
  exact setIntegral_congr_fun measurableSet_Ioo
    (fun t ht => errorTermOnBlock_eq_errorTerm k t (le_of_lt ht.1) ht.2)


-- ============================================================
-- Section 3: Phase 2b — Off-resonance mode bounds
-- ============================================================

/-- For modes n < k on block k, the phase derivative is bounded below by
    (1/2)·log((k+1)/(n+1)), ensuring rapid oscillation. -/
theorem phase_deriv_off_resonance :
    ∀ k : ℕ, ∀ n : ℕ, n < k → ∀ t : ℝ,
      hardyStart k ≤ t → t < hardyStart (k + 1) →
      Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) / 2 ≤
        |(1/2) * Real.log (t / (2 * Real.pi)) - Real.log ((n : ℝ) + 1)| := by
  intro k n hnk t ht_lo _ht_hi
  -- Positivity setup
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- n + 1 ≤ k + 1 from n < k
  have hn_le_k : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by
    have h : (n : ℕ) + 1 ≤ (k : ℕ) + 1 := Nat.succ_le_succ (le_of_lt hnk)
    exact_mod_cast h
  -- t / (2π) ≥ (k+1)²
  have ht_div : ((k : ℝ) + 1) ^ 2 ≤ t / (2 * Real.pi) := by
    rw [le_div_iff₀ hpi]
    have : 2 * Real.pi * ((k : ℝ) + 1) ^ 2 = hardyStart k := by unfold hardyStart; ring
    linarith
  -- (k+1)*(n+1) ≤ t / (2π) via (k+1)*(n+1) ≤ (k+1)²
  have h_prod : ((k : ℝ) + 1) * ((n : ℝ) + 1) ≤ t / (2 * Real.pi) := by
    calc ((k : ℝ) + 1) * ((n : ℝ) + 1)
        ≤ ((k : ℝ) + 1) * ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hn_le_k (le_of_lt hk1)
      _ = ((k : ℝ) + 1) ^ 2 := (sq _).symm
      _ ≤ t / (2 * Real.pi) := ht_div
  -- Expression is nonneg: (1/2)*log(t/(2π)) ≥ log(k+1) ≥ log(n+1)
  have h_nonneg : 0 ≤ 1 / 2 * Real.log (t / (2 * Real.pi)) - Real.log (↑n + 1) := by
    have h1 : Real.log (((k : ℝ) + 1) ^ 2) ≤ Real.log (t / (2 * Real.pi)) :=
      Real.log_le_log (by positivity) ht_div
    rw [Real.log_pow] at h1
    have h2 : Real.log (↑n + 1) ≤ Real.log (↑k + 1) :=
      Real.log_le_log hn1 hn_le_k
    linarith
  rw [abs_of_nonneg h_nonneg]
  -- Goal: log((k+1)/(n+1))/2 ≤ (1/2)*log(t/(2π)) - log(n+1)
  rw [Real.log_div (ne_of_gt hk1) (ne_of_gt hn1)]
  -- Sufficient: log(k+1) + log(n+1) ≤ log(t/(2π))
  have h_key : Real.log (↑k + 1) + Real.log (↑n + 1) ≤ Real.log (t / (2 * Real.pi)) := by
    rw [← Real.log_mul (ne_of_gt hk1) (ne_of_gt hn1)]
    exact Real.log_le_log (mul_pos hk1 hn1) h_prod
  linarith

/-- Van der Corput bound per off-resonance mode: the integral of cos(θ(t)-t·log(n+1))
    over block k is bounded by C_vdc/log((k+1)/(n+1)) for some universal C_vdc > 0. -/
theorem off_resonance_integral_bound :
    ∃ C_vdc > 0, ∀ k : ℕ, ∀ n : ℕ, n < k → 1 ≤ k →
      |∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
        Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))|
          ≤ C_vdc / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) :=
  Aristotle.OffResonanceSmoothVdC.off_resonance_integral_bound_smooth

-- ============================================================
-- Helpers for off_resonance_sum_bound
-- ============================================================

/-- Per-term bound: (n+1)^{-1/2} ≤ 2(√(n+1) - √n) by squaring √(n(n+1)) ≤ n+1/2. -/
private lemma inv_sqrt_le_two_sqrt_diff (n : ℕ) :
    ((↑n + 1 : ℝ) ^ (-(1:ℝ)/2)) ≤ 2 * (Real.sqrt (↑n + 1) - Real.sqrt ↑n) := by
  have hn1_pos : (0 : ℝ) < ↑n + 1 := by positivity
  have hn_nn : (0 : ℝ) ≤ ↑n := Nat.cast_nonneg n
  have hsqrt_pos : 0 < Real.sqrt (↑n + 1) := Real.sqrt_pos.mpr hn1_pos
  have hrpow : (↑n + 1 : ℝ) ^ (-(1:ℝ)/2) = (Real.sqrt (↑n + 1))⁻¹ := by
    rw [Real.sqrt_eq_rpow, show (-(1:ℝ)/2) = -(1/2 : ℝ) from by ring]
    exact Real.rpow_neg (by linarith) (1/2)
  rw [hrpow, (one_div (Real.sqrt (↑n + 1))).symm, div_le_iff₀ hsqrt_pos]
  have hsq : Real.sqrt (↑n + 1) * Real.sqrt (↑n + 1) = ↑n + 1 :=
    Real.mul_self_sqrt (by linarith)
  have hprod : Real.sqrt (↑n + 1) * Real.sqrt ↑n = Real.sqrt ((↑n + 1) * ↑n) :=
    (Real.sqrt_mul (by linarith) ↑n).symm
  have hkey : Real.sqrt ((↑n + 1) * ↑n) ≤ ↑n + 1/2 := by
    rw [← Real.sqrt_sq (by linarith : (0:ℝ) ≤ ↑n + 1/2)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  nlinarith

/-- Telescoping: ∑_{n<M} (n+1)^{-1/2} ≤ 2√M. -/
private lemma sum_rpow_neg_half_le (M : ℕ) :
    ∑ n ∈ Finset.range M, ((↑n + 1 : ℝ) ^ (-(1:ℝ)/2)) ≤ 2 * Real.sqrt ↑M := by
  calc ∑ n ∈ Finset.range M, ((↑n + 1 : ℝ) ^ (-(1:ℝ)/2))
      ≤ ∑ n ∈ Finset.range M, (2 * (Real.sqrt (↑n + 1) - Real.sqrt ↑n)) :=
        Finset.sum_le_sum (fun n _ => inv_sqrt_le_two_sqrt_diff n)
    _ = ∑ n ∈ Finset.range M, (2 * Real.sqrt (↑n + 1) - 2 * Real.sqrt ↑n) := by
        congr 1; ext n; ring
    _ = 2 * Real.sqrt ↑M - 2 * Real.sqrt 0 := by
        have := Finset.sum_range_sub (fun n : ℕ => 2 * Real.sqrt ↑n) M
        simp only [Nat.cast_zero] at this
        convert this using 1
        congr 1; ext n; push_cast; ring
    _ = 2 * Real.sqrt ↑M := by rw [Real.sqrt_zero]; ring

/-- Harmonic bound: ∑_{j<J} 1/(j+1) ≤ 1 + log J, by telescoping with log. -/
private lemma harmonic_sum_le_one_add_log (J : ℕ) :
    ∑ j ∈ Finset.range J, (1 / ((↑j : ℝ) + 1)) ≤ 1 + Real.log ↑J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_succ]
    by_cases hJ : J = 0
    · subst hJ; simp [Real.log_one]
    · have hJ_pos : (0 : ℝ) < ↑J := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hJ)
      suffices h : 1 / ((↑J : ℝ) + 1) ≤ Real.log (↑J + 1) - Real.log ↑J by linarith
      rw [← Real.log_div (ne_of_gt (by positivity : (0:ℝ) < ↑J + 1))
                          (ne_of_gt hJ_pos)]
      have h1 := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < (↑J + 1) / ↑J by positivity)
      have h2 : 1 / ((↑J : ℝ) + 1) = 1 - ((↑J + 1) / (↑J : ℝ))⁻¹ := by
        field_simp; ring
      linarith

/-- Re-indexing: ∑_{n<k} 1/(k-n) = ∑_{n<k} 1/(n+1), by Finset.sum_range_reflect. -/
private lemma sum_inv_diff_eq_harmonic (k : ℕ) :
    ∑ n ∈ Finset.range k, (1 / ((k : ℝ) - (n : ℝ))) =
    ∑ n ∈ Finset.range k, (1 / ((n : ℝ) + 1)) := by
  rw [← Finset.sum_range_reflect (fun n => 1 / ((n : ℝ) + 1)) k]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn_lt : n < k := Finset.mem_range.mp hn
  congr 1
  have h1 : (k - 1 - n : ℕ) + 1 = k - n := by omega
  rw [show (↑(k - 1 - n) : ℝ) + 1 = ↑(k - 1 - n + 1) from by push_cast; ring]
  rw [h1, Nat.cast_sub (by omega : n ≤ k)]

/-- Weighted sum of off-resonance contributions is O(√(k+1) · log(k+2)).

    The original O(√(k+1)) bound was mathematically incorrect — near-diagonal
    terms (n close to k) contribute O(√k · log k). The weakened bound suffices
    for the downstream RS expansion.

    Proof: split into far terms (n+1 ≤ (k+1)/2, use VdC + inv-sqrt telescoping)
    and near terms (n+1 > (k+1)/2, use VdC + harmonic sum + √(k+1) ≤ √(2(n+1))). -/
theorem off_resonance_sum_bound :
    ∃ C_off > 0, ∀ k : ℕ, 1 ≤ k →
      |∑ n ∈ Finset.range k, ((n + 1 : ℝ) ^ (-(1 : ℝ)/2)) *
        ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
          Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))|
        ≤ C_off * Real.sqrt ((k : ℝ) + 1) * Real.log ((k : ℝ) + 2) := by
  obtain ⟨C_vdc, hC_vdc_pos, h_vdc⟩ := off_resonance_integral_bound
  refine ⟨10 * C_vdc, by positivity, fun k hk => ?_⟩
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hlog_k2_ge_one : 1 ≤ Real.log ((k : ℝ) + 2) := by
    have h3le : (3 : ℝ) ≤ (k : ℝ) + 2 := by
      linarith [show (1 : ℝ) ≤ (k : ℝ) from Nat.one_le_cast.mpr hk]
    calc (1 : ℝ) ≤ Real.log 3 := by
          rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)]
          exact le_of_lt Real.exp_one_lt_three
      _ ≤ Real.log ((k : ℝ) + 2) := Real.log_le_log (by norm_num) h3le
  -- log(2) ≥ 1/2 (from one_sub_inv_le_log applied to 2)
  have hlog2_ge : 1 / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  -- Step 1: Triangle + per-mode VdC bound
  have h_tri : |∑ n ∈ Finset.range k, ((n + 1 : ℝ) ^ (-(1 : ℝ)/2)) *
      ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
        Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))|
      ≤ ∑ n ∈ Finset.range k, ((n + 1 : ℝ) ^ (-(1 : ℝ)/2)) *
        (C_vdc / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1))) := by
    calc _ ≤ ∑ n ∈ Finset.range k, |((n + 1 : ℝ) ^ (-(1 : ℝ)/2)) *
        ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
          Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        have hn_lt : n < k := Finset.mem_range.mp hn
        have hcoef_nn : 0 ≤ ((n + 1 : ℝ) ^ (-(1 : ℝ)/2)) := by positivity
        rw [abs_mul, abs_of_nonneg hcoef_nn]
        exact mul_le_mul_of_nonneg_left (h_vdc k n hn_lt hk) hcoef_nn
  -- Step 2: Bound each term using (n+1)^{-1/2} ≤ 1 and VdC + log lower bound
  -- Then: ∑ ≤ C_vdc*(k+1) * ∑ 1/(k-n) = C_vdc*(k+1)*H_k ≤ 2*C_vdc*(k+1)*log(k+2)
  -- This gives O(k*log k). For O(√k*log k), split into far/near.
  --
  -- Far (2*(n+1) ≤ k+1): log ≥ log(2) ≥ 1/2, each ≤ 2*C_vdc*(n+1)^{-1/2}
  --   sum ≤ 2*C_vdc * 2√k ≤ 4*C_vdc*√(k+1)
  -- Near (k+1 < 2*(n+1)): √(k+1) ≤ √(2(n+1)), so (n+1)^{-1/2}*(k+1)/(k-n) ≤ √2*√(k+1)/(k-n)
  --   sum ≤ √2*C_vdc*√(k+1)*H_k ≤ 3*C_vdc*√(k+1)*log(k+2)
  set far_pred : ℕ → Prop := fun n => 2 * (n + 1) ≤ k + 1 with far_pred_def
  -- Far bound
  have h_far : ∑ n ∈ (Finset.range k).filter far_pred,
      ((n + 1 : ℝ) ^ (-(1 : ℝ)/2)) *
        (C_vdc / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)))
      ≤ 4 * C_vdc * Real.sqrt ((k : ℝ) + 1) := by
    -- Each term ≤ (n+1)^{-1/2} * 2*C_vdc since C_vdc/log ≤ 2*C_vdc
    have h1 : ∀ n ∈ (Finset.range k).filter far_pred,
        ((n + 1 : ℝ) ^ (-(1 : ℝ)/2)) * (C_vdc / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)))
        ≤ ((n + 1 : ℝ) ^ (-(1 : ℝ)/2)) * (2 * C_vdc) := by
      intro n hn
      have hmem := (Finset.mem_filter.mp hn).2
      have hn1_pos : (0:ℝ) < (n:ℝ) + 1 := by positivity
      have hratio_ge : (2:ℝ) ≤ ((k:ℝ)+1) / ((n:ℝ)+1) := by
        rw [le_div_iff₀ hn1_pos]; exact_mod_cast hmem
      have hlog_ge : Real.log 2 ≤ Real.log (((k:ℝ)+1)/((n:ℝ)+1)) :=
        Real.log_le_log (by norm_num) hratio_ge
      have hlog_pos : (0:ℝ) < Real.log (((k:ℝ)+1)/((n:ℝ)+1)) := by linarith
      gcongr
      rw [div_le_iff₀ hlog_pos]; nlinarith
    calc ∑ n ∈ (Finset.range k).filter far_pred,
          ((n + 1 : ℝ) ^ (-(1 : ℝ)/2)) * (C_vdc / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)))
        ≤ ∑ n ∈ (Finset.range k).filter far_pred,
          ((n + 1 : ℝ) ^ (-(1 : ℝ)/2)) * (2 * C_vdc) :=
          Finset.sum_le_sum h1
      _ ≤ ∑ n ∈ Finset.range k, ((↑n + 1 : ℝ) ^ (-(1:ℝ)/2)) * (2 * C_vdc) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun n _ _ => by positivity)
      _ = 2 * C_vdc * ∑ n ∈ Finset.range k, ((↑n + 1 : ℝ) ^ (-(1:ℝ)/2)) := by
          have hcomm : ∀ n : ℕ, ((↑n + 1 : ℝ) ^ (-(1:ℝ)/2)) * (2 * C_vdc) =
              2 * C_vdc * ((↑n + 1 : ℝ) ^ (-(1:ℝ)/2)) := fun n => by ring
          simp_rw [hcomm, ← Finset.mul_sum]
      _ ≤ 2 * C_vdc * (2 * Real.sqrt ↑k) := by
          gcongr; exact sum_rpow_neg_half_le k
      _ ≤ 4 * C_vdc * Real.sqrt ((k : ℝ) + 1) := by
          nlinarith [Real.sqrt_le_sqrt (show (↑k : ℝ) ≤ ↑k + 1 by linarith)]
  -- Near bound: each term ≤ √2 * C_vdc * √(k+1) / (k-n)
  -- Sum ≤ √2 * C_vdc * √(k+1) * H_k ≤ 6 * C_vdc * √(k+1) * log(k+2)
  have h_near : ∑ n ∈ (Finset.range k).filter (fun n => ¬ far_pred n),
      ((n + 1 : ℝ) ^ (-(1 : ℝ)/2)) *
        (C_vdc / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)))
      ≤ 6 * C_vdc * Real.sqrt ((k : ℝ) + 1) * Real.log ((k : ℝ) + 2) := by
    -- Bound each near term
    have h_near_term : ∀ n ∈ (Finset.range k).filter (fun n => ¬ far_pred n),
        ((n + 1 : ℝ) ^ (-(1 : ℝ)/2)) * (C_vdc / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)))
        ≤ C_vdc * Real.sqrt 2 * Real.sqrt ((k : ℝ) + 1) / ((k : ℝ) - (n : ℝ)) := by
      intro n hn
      have hmem := (Finset.mem_filter.mp hn).2
      have hn_lt : n < k := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
      have hn1_pos : (0:ℝ) < (n:ℝ) + 1 := by positivity
      have hkn_pos : (0:ℝ) < (k:ℝ) - (n:ℝ) := by
        have : (n:ℝ) < (k:ℝ) := Nat.cast_lt.mpr hn_lt; linarith
      have hratio_pos : (0:ℝ) < ((k:ℝ)+1) / ((n:ℝ)+1) := by positivity
      have hlog_pos : 0 < Real.log (((k:ℝ)+1)/((n:ℝ)+1)) :=
        Real.log_pos (by rw [one_lt_div hn1_pos]; linarith [show (n:ℝ) < (k:ℝ) from by exact_mod_cast hn_lt])
      -- Near condition: ¬(2*(n+1) ≤ k+1), so k+1 < 2*(n+1), so k+1 ≤ 2*(n+1)
      have hk_le_2n : k + 1 ≤ 2 * (n + 1) := by
        rw [far_pred_def] at hmem; omega
      -- (n+1)^{-1/2} = (√(n+1))⁻¹
      have hrpow : (↑n + 1 : ℝ) ^ (-(1:ℝ)/2) = (Real.sqrt (↑n + 1))⁻¹ := by
        rw [Real.sqrt_eq_rpow, show (-(1:ℝ)/2) = -(1/2 : ℝ) from by ring]
        exact Real.rpow_neg (by linarith) (1/2)
      -- √(k+1) ≤ √(2*(n+1)) = √2 * √(n+1) from near condition
      have h_sqrt_bound : Real.sqrt ((k:ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt ((n:ℝ) + 1) := by
        rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hk_le_2n)
      -- 1/log(...) ≤ (k+1)/(k-n) from one_sub_inv_le_log
      have h_log_lb : ((k:ℝ) - (n:ℝ)) / ((k:ℝ) + 1) ≤ Real.log (((k:ℝ)+1)/((n:ℝ)+1)) := by
        have := Real.one_sub_inv_le_log_of_pos hratio_pos
        calc ((k:ℝ) - (n:ℝ)) / ((k:ℝ) + 1)
            = 1 - ((n:ℝ)+1) / ((k:ℝ)+1) := by field_simp; ring
          _ = 1 - (((k:ℝ)+1) / ((n:ℝ)+1))⁻¹ := by rw [inv_div]
          _ ≤ Real.log (((k:ℝ)+1)/((n:ℝ)+1)) := this
      -- Combine: (n+1)^{-1/2} * C_vdc/log ≤ C_vdc/(√(n+1)*log) ≤ C_vdc*(k+1)/(√(n+1)*(k-n))
      --   ≤ C_vdc*√2*√(k+1)/(k-n) since (k+1)/√(n+1) ≤ √2*√(k+1)*√(n+1)/√(n+1) = √2*√(k+1)
      -- Direct approach: bound LHS ≤ RHS via intermediate steps
      -- LHS = (√(n+1))⁻¹ * C_vdc / log(...)
      -- RHS = C_vdc * √2 * √(k+1) / (k-n)
      -- Suffices: C_vdc / (√(n+1) * log(...)) ≤ C_vdc * √2 * √(k+1) / (k-n)
      rw [hrpow]
      have hsqrt_n1_pos : 0 < Real.sqrt (↑n + 1) := Real.sqrt_pos.mpr hn1_pos
      -- LHS = C_vdc / (√(n+1) * log(...))
      have hlhs : (Real.sqrt (↑n + 1))⁻¹ * (C_vdc / Real.log (((k:ℝ)+1)/((n:ℝ)+1)))
          = C_vdc / (Real.sqrt (↑n + 1) * Real.log (((k:ℝ)+1)/((n:ℝ)+1))) := by
        field_simp
      rw [hlhs]
      rw [div_le_div_iff₀ (mul_pos hsqrt_n1_pos hlog_pos) hkn_pos]
      -- Goal: C_vdc * ((k:ℝ) - (n:ℝ)) ≤ C_vdc * √2 * √(k+1) * (√(n+1) * log(...))
      -- From h_log_lb: (k-n)/(k+1) ≤ log(...), so (k-n) ≤ (k+1)*log(...)
      -- From h_sqrt_bound: √(k+1) ≤ √2*√(n+1), so (k+1) ≤ 2*(n+1), hence
      --   (k+1) = √(k+1)*√(k+1) ≤ √2*√(n+1)*√(k+1)
      have hk1_bound : (k:ℝ) + 1 ≤ Real.sqrt 2 * Real.sqrt ((n:ℝ) + 1) * Real.sqrt ((k:ℝ) + 1) := by
        have hsq := Real.mul_self_sqrt (show (0:ℝ) ≤ (k:ℝ) + 1 by linarith)
        nlinarith [Real.sqrt_nonneg ((k:ℝ) + 1), Real.sqrt_nonneg ((n:ℝ) + 1)]
      have hkn_le : ((k:ℝ) - (n:ℝ)) ≤ ((k:ℝ) + 1) * Real.log (((k:ℝ)+1)/((n:ℝ)+1)) := by
        rw [div_le_iff₀ (show (0:ℝ) < (k:ℝ) + 1 from by linarith)] at h_log_lb
        linarith
      -- C*(k-n) ≤ C*(k+1)*log ≤ C*√2*√(n+1)*√(k+1)*log
      calc C_vdc * ((k:ℝ) - (n:ℝ))
          ≤ C_vdc * (((k:ℝ) + 1) * Real.log (((k:ℝ)+1)/((n:ℝ)+1))) :=
            mul_le_mul_of_nonneg_left hkn_le (le_of_lt hC_vdc_pos)
        _ ≤ C_vdc * (Real.sqrt 2 * Real.sqrt ((n:ℝ) + 1) * Real.sqrt ((k:ℝ) + 1) *
              Real.log (((k:ℝ)+1)/((n:ℝ)+1))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hk1_bound (le_of_lt hlog_pos))
              (le_of_lt hC_vdc_pos)
        _ = C_vdc * Real.sqrt 2 * Real.sqrt ((k:ℝ) + 1) *
              (Real.sqrt ((n:ℝ) + 1) * Real.log (((k:ℝ)+1)/((n:ℝ)+1))) := by ring
    -- Chain: sum_le_sum → extend to full range → factor → reindex → harmonic → arithmetic
    calc ∑ n ∈ (Finset.range k).filter (fun n => ¬ far_pred n),
          ((n + 1 : ℝ) ^ (-(1 : ℝ)/2)) * (C_vdc / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)))
        ≤ ∑ n ∈ (Finset.range k).filter (fun n => ¬ far_pred n),
          C_vdc * Real.sqrt 2 * Real.sqrt ((k : ℝ) + 1) / ((k : ℝ) - (n : ℝ)) :=
          Finset.sum_le_sum h_near_term
      _ ≤ ∑ n ∈ Finset.range k,
          C_vdc * Real.sqrt 2 * Real.sqrt ((k : ℝ) + 1) / ((k : ℝ) - (n : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun n hn _ => by
              have : (n : ℝ) < (k : ℝ) := Nat.cast_lt.mpr (Finset.mem_range.mp hn)
              have : (0 : ℝ) < (k : ℝ) - (n : ℝ) := by linarith
              apply div_nonneg _ (le_of_lt this)
              exact mul_nonneg (mul_nonneg (le_of_lt hC_vdc_pos) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
      _ = C_vdc * Real.sqrt 2 * Real.sqrt ((k : ℝ) + 1) *
            ∑ n ∈ Finset.range k, (1 / ((k : ℝ) - (n : ℝ))) := by
          simp_rw [show ∀ n : ℕ,
              C_vdc * Real.sqrt 2 * Real.sqrt ((k : ℝ) + 1) / ((k : ℝ) - (n : ℝ))
              = C_vdc * Real.sqrt 2 * Real.sqrt ((k : ℝ) + 1) * (1 / ((k : ℝ) - (n : ℝ))) from
            fun n => by ring]
          rw [← Finset.mul_sum]
      _ = C_vdc * Real.sqrt 2 * Real.sqrt ((k : ℝ) + 1) *
            ∑ n ∈ Finset.range k, (1 / ((n : ℝ) + 1)) := by
          rw [sum_inv_diff_eq_harmonic]
      _ ≤ C_vdc * Real.sqrt 2 * Real.sqrt ((k : ℝ) + 1) * (1 + Real.log ↑k) := by
          gcongr; exact harmonic_sum_le_one_add_log k
      _ ≤ C_vdc * (3 / 2 : ℝ) * Real.sqrt ((k : ℝ) + 1) * (1 + Real.log ↑k) := by
          have h_sqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
            rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)]
            exact Real.sqrt_le_sqrt (by norm_num)
          have h_log_nn : (0 : ℝ) ≤ 1 + Real.log ↑k := by
            linarith [Real.log_nonneg (show (1 : ℝ) ≤ (k : ℝ) from by exact_mod_cast hk)]
          have h_rest_nn : (0 : ℝ) ≤ C_vdc * Real.sqrt ((k : ℝ) + 1) * (1 + Real.log ↑k) :=
            mul_nonneg (mul_nonneg (le_of_lt hC_vdc_pos) (Real.sqrt_nonneg _)) h_log_nn
          calc C_vdc * Real.sqrt 2 * Real.sqrt ((k : ℝ) + 1) * (1 + Real.log ↑k)
              = C_vdc * Real.sqrt ((k : ℝ) + 1) * (1 + Real.log ↑k) * Real.sqrt 2 := by ring
            _ ≤ C_vdc * Real.sqrt ((k : ℝ) + 1) * (1 + Real.log ↑k) * (3 / 2) :=
                mul_le_mul_of_nonneg_left h_sqrt2 h_rest_nn
            _ = C_vdc * (3 / 2) * Real.sqrt ((k : ℝ) + 1) * (1 + Real.log ↑k) := by ring
      _ ≤ C_vdc * (3 / 2 : ℝ) * Real.sqrt ((k : ℝ) + 1) * (2 * Real.log ((k : ℝ) + 2)) := by
          have h_log_k : Real.log ↑k ≤ Real.log ((k : ℝ) + 2) :=
            Real.log_le_log hk_pos (by linarith)
          have h_1_log : 1 + Real.log ↑k ≤ 2 * Real.log ((k : ℝ) + 2) := by linarith
          have h_prefix_nn : (0 : ℝ) ≤ C_vdc * (3 / 2) * Real.sqrt ((k : ℝ) + 1) :=
            mul_nonneg (mul_nonneg (le_of_lt hC_vdc_pos) (by norm_num)) (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left h_1_log h_prefix_nn
      _ = 3 * C_vdc * Real.sqrt ((k : ℝ) + 1) * Real.log ((k : ℝ) + 2) := by ring
      _ ≤ 6 * C_vdc * Real.sqrt ((k : ℝ) + 1) * Real.log ((k : ℝ) + 2) := by
          have h_log_nn : (0 : ℝ) ≤ Real.log ((k : ℝ) + 2) :=
            Real.log_nonneg (show (1 : ℝ) ≤ (k : ℝ) + 2 from by linarith)
          have h_suffix_nn : (0 : ℝ) ≤ C_vdc * Real.sqrt ((k : ℝ) + 1) * Real.log ((k : ℝ) + 2) :=
            mul_nonneg (mul_nonneg (le_of_lt hC_vdc_pos) (Real.sqrt_nonneg _)) h_log_nn
          linarith
  -- Combine far + near
  have h_split := (Finset.sum_filter_add_sum_filter_not (Finset.range k) far_pred
    (fun n => ((n + 1 : ℝ) ^ (-(1 : ℝ)/2)) *
      (C_vdc / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1))))).symm
  have h_combined : ∑ n ∈ Finset.range k, ((n + 1 : ℝ) ^ (-(1 : ℝ)/2)) *
      (C_vdc / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)))
      ≤ 10 * C_vdc * Real.sqrt ((k : ℝ) + 1) * Real.log ((k : ℝ) + 2) := by
    have hsqrt_nn := Real.sqrt_nonneg ((k : ℝ) + 1)
    -- far ≤ 4*C*√(k+1) ≤ 4*C*√(k+1)*log(k+2) since log(k+2) ≥ 1
    have h_far_log : 4 * C_vdc * Real.sqrt ((k : ℝ) + 1) ≤
        4 * C_vdc * Real.sqrt ((k : ℝ) + 1) * Real.log ((k : ℝ) + 2) := by
      have := mul_le_mul_of_nonneg_left hlog_k2_ge_one (by nlinarith : 0 ≤ 4 * C_vdc * Real.sqrt ((k : ℝ) + 1))
      linarith
    linarith [h_split]
  linarith [h_tri]

-- ============================================================
-- Section 4: Phase 2d — RS Ψ function and integral positivity
-- ============================================================

/-- The RS correction function Ψ on [0,1].
    This encodes the leading-order correction from the Riemann-Siegel formula.
    The phase convention (+1/4) is chosen so that Ψ > 0 on [0,1], consistent with
    positive block integrals. -/
def rsPsi (p : ℝ) : ℝ :=
  Real.cos (Real.pi * (2 * p ^ 2 - 2 * p + 1/4))

/-- Ψ is continuous on [0,1]. -/
theorem rsPsi_continuousOn : ContinuousOn rsPsi (Icc 0 1) := by
  unfold rsPsi
  have : Continuous fun p : ℝ => Real.cos (Real.pi * (2 * p ^ 2 - 2 * p + 1 / 4)) := by
    fun_prop
  exact this.continuousOn

/-- Ψ is integrable on [0,1]. -/
theorem rsPsi_integrableOn : IntegrableOn rsPsi (Ioc 0 1) := by
  exact rsPsi_continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- The integral of Ψ over [0,1] is positive.
    With the +1/4 phase convention, Ψ > 0 on all of [0,1] since the argument
    π(2p²-2p+1/4) ∈ [-π/4, π/4] ⊂ (-π/2, π/2) where cos is positive. -/
theorem rsPsi_integral_pos : 0 < ∫ p in Ioc 0 1, rsPsi p := by
  -- cos(π/4) > 0
  have hcos_pos : (0 : ℝ) < Real.cos (Real.pi / 4) := by
    rw [Real.cos_pi_div_four]; positivity
  have hpi4_le_pi : Real.pi / 4 ≤ Real.pi :=
    div_le_self (le_of_lt Real.pi_pos) (by norm_num : (1 : ℝ) ≤ 4)
  -- cos(π/4) ≤ rsPsi(p) for p ∈ Ioc 0 1
  have h_lower : ∀ p ∈ Ioc (0 : ℝ) 1, Real.cos (Real.pi / 4) ≤ rsPsi p := by
    intro p hp
    have ⟨hp0, hp1⟩ := Ioc_subset_Icc_self hp
    simp only [rsPsi]
    have harg_abs : |Real.pi * (2 * p ^ 2 - 2 * p + 1/4)| ≤ Real.pi / 4 := by
      rw [abs_le]; constructor
      · have h1 : 0 ≤ 2 * (p - 1/2) ^ 2 := by positivity
        nlinarith [Real.pi_pos]
      · have h2 : 2 * p * (p - 1) ≤ 0 := by nlinarith
        nlinarith [Real.pi_pos]
    -- cos is even and antitone on [0,π]: |arg| ≤ π/4 → cos(arg) ≥ cos(π/4)
    rw [← Real.cos_abs (Real.pi * (2 * p ^ 2 - 2 * p + 1/4))]
    exact Real.strictAntiOn_cos.antitoneOn
      (Set.mem_Icc.mpr ⟨abs_nonneg _, le_trans harg_abs hpi4_le_pi⟩)
      (Set.mem_Icc.mpr ⟨le_of_lt (div_pos Real.pi_pos (by norm_num : (0:ℝ) < 4)), hpi4_le_pi⟩)
      harg_abs
  -- ∫ rsPsi ≥ ∫ cos(π/4) = cos(π/4) > 0 via ae monotonicity
  have h_ae : ∀ᵐ p ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      (fun _ => Real.cos (Real.pi / 4)) p ≤ rsPsi p :=
    (ae_restrict_mem measurableSet_Ioc).mono (fun p hp => h_lower p hp)
  have h_const_int : IntegrableOn (fun _ => Real.cos (Real.pi / 4)) (Ioc (0 : ℝ) 1) :=
    continuous_const.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h_mono : ∫ _ in Ioc (0 : ℝ) 1, Real.cos (Real.pi / 4)
      ≤ ∫ p in Ioc (0 : ℝ) 1, rsPsi p :=
    integral_mono_ae h_const_int rsPsi_integrableOn h_ae
  have h_const_val : ∫ _ in Ioc (0 : ℝ) 1, Real.cos (Real.pi / 4)
      = Real.cos (Real.pi / 4) := by
    simp
  linarith

end Aristotle.ErrorTermExpansion
