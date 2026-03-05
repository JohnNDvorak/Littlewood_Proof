/-
Block parametrization for the Riemann-Siegel block analysis.

Defines the change of variables between block parameter p ∈ [0,1] and height t
in the k-th block [hardyStart k, hardyStart (k+1)].

Key results:
- blockCoord / blockParam: forward and inverse maps
- blockCoord_zero/one: match hardyStart endpoints
- blockCoord_hasDerivAt: derivative = 4π(k+1+p) > 0
- blockCoord_strictMonoOn: strict monotonicity on [0,1]
- block_integral_cov: change of variables for block integrals

SORRY COUNT: 0
-/

import Mathlib
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.HardyZMeasurability

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.RSBlockParam

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.HardyNProperties
open intervalIntegral

-- ============================================================
-- Definitions
-- ============================================================

/-- Block coordinate: t(k,p) = 2π(k+1+p)². Maps p ∈ [0,1] to t in block k. -/
def blockCoord (k : ℕ) (p : ℝ) : ℝ :=
  2 * Real.pi * ((k : ℝ) + 1 + p) ^ 2

/-- Block parameter: p(t) = √(t/(2π)) - (k+1). Inverse of blockCoord on block k. -/
def blockParam (k : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (t / (2 * Real.pi)) - ((k : ℝ) + 1)

/-- Jacobian of the block coordinate map: d/dp blockCoord(k,p) = 4π(k+1+p). -/
def blockJacobian (k : ℕ) (p : ℝ) : ℝ :=
  4 * Real.pi * ((k : ℝ) + 1 + p)

-- ============================================================
-- Section 1: Endpoint identities
-- ============================================================

theorem blockCoord_zero (k : ℕ) : blockCoord k 0 = hardyStart k := by
  unfold blockCoord hardyStart; ring

theorem blockCoord_one (k : ℕ) : blockCoord k 1 = hardyStart (k + 1) := by
  unfold blockCoord hardyStart; push_cast; ring

theorem hardyStart_le_succ' (k : ℕ) : hardyStart k ≤ hardyStart (k + 1) := by
  rw [← blockCoord_zero k, ← blockCoord_one k, blockCoord, blockCoord]
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  apply sq_le_sq'
  · linarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]
  · linarith

theorem hardyStart_nonneg (k : ℕ) : 0 ≤ hardyStart k := by
  simp [hardyStart]; positivity

-- ============================================================
-- Section 2: Derivative and monotonicity
-- ============================================================

theorem blockCoord_hasDerivAt (k : ℕ) (p : ℝ) :
    HasDerivAt (blockCoord k) (blockJacobian k p) p := by
  unfold blockCoord blockJacobian
  exact (((hasDerivAt_id p).const_add ((k : ℝ) + 1)).pow 2
    |>.const_mul (2 * Real.pi)).congr_deriv (by simp only [id]; ring)

theorem blockJacobian_pos (k : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 < blockJacobian k p := by
  unfold blockJacobian; positivity

theorem blockCoord_continuous (k : ℕ) : Continuous (blockCoord k) := by
  unfold blockCoord; fun_prop

theorem blockJacobian_continuous (k : ℕ) : Continuous (blockJacobian k) := by
  unfold blockJacobian; fun_prop

theorem blockCoord_strictMonoOn (k : ℕ) :
    StrictMonoOn (blockCoord k) (Icc 0 1) :=
  strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1)
    (blockCoord_continuous k).continuousOn
    (fun p hp => by
      rw [interior_Icc] at hp
      rw [(blockCoord_hasDerivAt k p).deriv]
      exact blockJacobian_pos k (le_of_lt hp.1))

theorem blockCoord_strictMonoOn_nonneg (k : ℕ) :
    StrictMonoOn (blockCoord k) (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
    (blockCoord_continuous k).continuousOn
    (fun p hp => by
      rw [interior_Ici] at hp
      rw [(blockCoord_hasDerivAt k p).deriv]
      exact blockJacobian_pos k (le_of_lt hp))

theorem blockCoord_injOn (k : ℕ) : InjOn (blockCoord k) (Icc 0 1) :=
  (blockCoord_strictMonoOn k).injOn

-- ============================================================
-- Section 3: Block parameter properties
-- ============================================================

theorem blockParam_nonneg (k : ℕ) (t : ℝ) (ht : hardyStart k ≤ t) :
    0 ≤ blockParam k t := by
  simp only [blockParam]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have ht_nn : 0 ≤ t := le_trans (hardyStart_nonneg k) ht
  suffices h : (k : ℝ) + 1 ≤ Real.sqrt (t / (2 * Real.pi)) by linarith
  calc (k : ℝ) + 1
      = Real.sqrt (((k : ℝ) + 1) ^ 2) := (Real.sqrt_sq hk1).symm
    _ ≤ Real.sqrt (t / (2 * Real.pi)) := by
        apply Real.sqrt_le_sqrt
        rw [le_div_iff₀ hpi]
        have : hardyStart k = 2 * Real.pi * ((k : ℝ) + 1) ^ 2 := by
          unfold hardyStart; ring
        linarith

theorem blockParam_lt_one (k : ℕ) (t : ℝ) (ht : t < hardyStart (k + 1)) :
    blockParam k t < 1 := by
  simp only [blockParam]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  suffices h : Real.sqrt (t / (2 * Real.pi)) < (k : ℝ) + 2 by linarith
  have h_sq : t / (2 * Real.pi) < ((k : ℝ) + 2) ^ 2 := by
    rw [div_lt_iff₀ hpi]
    have : hardyStart (k + 1) = 2 * Real.pi * ((k : ℝ) + 2) ^ 2 := by
      unfold hardyStart; push_cast; ring
    linarith
  by_cases ht_nn : 0 ≤ t
  · exact lt_of_lt_of_eq
      (Real.sqrt_lt_sqrt (div_nonneg ht_nn (le_of_lt hpi)) h_sq)
      (Real.sqrt_sq (le_of_lt hk2))
  · push_neg at ht_nn
    calc Real.sqrt (t / (2 * Real.pi))
        = 0 := Real.sqrt_eq_zero'.mpr (le_of_lt (div_neg_of_neg_of_pos ht_nn hpi))
      _ < (k : ℝ) + 2 := hk2

theorem blockParam_mem_Ico (k : ℕ) (t : ℝ)
    (ht_lo : hardyStart k ≤ t) (ht_hi : t < hardyStart (k + 1)) :
    blockParam k t ∈ Ico 0 1 :=
  ⟨blockParam_nonneg k t ht_lo, blockParam_lt_one k t ht_hi⟩

-- ============================================================
-- Section 4: Inverse relationship
-- ============================================================

theorem blockParam_blockCoord (k : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    blockParam k (blockCoord k p) = p := by
  simp only [blockParam, blockCoord]
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.pi)
  have hkp : (0 : ℝ) ≤ (k : ℝ) + 1 + p := by positivity
  rw [mul_div_cancel_left₀ _ hpi, Real.sqrt_sq hkp]
  ring

theorem blockCoord_blockParam (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    blockCoord k (blockParam k t) = t := by
  simp only [blockCoord, blockParam]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_ring : (↑k + 1 + (Real.sqrt (t / (2 * Real.pi)) - (↑k + 1)))
      = Real.sqrt (t / (2 * Real.pi)) := by ring
  rw [h_ring, Real.sq_sqrt (div_nonneg ht (le_of_lt hpi))]
  field_simp

-- ============================================================
-- Section 5: Image characterization
-- ============================================================

theorem blockCoord_mem_Icc (k : ℕ) {p : ℝ} (hp : p ∈ Icc 0 1) :
    blockCoord k p ∈ Icc (hardyStart k) (hardyStart (k + 1)) := by
  rw [← blockCoord_zero k, ← blockCoord_one k]
  have hm := (blockCoord_strictMonoOn k).monotoneOn
  exact ⟨hm (left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)) hp hp.1,
         hm hp (right_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)) hp.2⟩

theorem blockCoord_image_uIcc_subset (k : ℕ) :
    blockCoord k '' uIcc 0 1 ⊆ Icc (hardyStart k) (hardyStart (k + 1)) := by
  intro t ht
  obtain ⟨p, hp, hpt⟩ := ht
  have hp' : p ∈ Icc 0 1 := by rwa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hp
  rw [← hpt]
  exact blockCoord_mem_Icc k hp'

-- ============================================================
-- Section 6: Change of variables for block integrals
-- ============================================================

/-- Change of variables for block integrals: transforms an integral over a
Hardy block into an integral over the unit interval with the appropriate
Jacobian factor.

    ∫ t in block k, g(t) dt = ∫ p in (0,1], g(blockCoord k p) · blockJacobian(k,p) dp
-/
theorem block_integral_cov (k : ℕ) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc (hardyStart k) (hardyStart (k + 1)))) :
    ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), g t
      = ∫ p in Ioc 0 1, g (blockCoord k p) * blockJacobian k p := by
  -- Convert set integrals (Ioc) to interval integrals (a..b)
  rw [← integral_of_le (hardyStart_le_succ' k),
      ← integral_of_le (show (0 : ℝ) ≤ 1 from by norm_num)]
  -- Rewrite LHS endpoints as blockCoord values
  rw [← blockCoord_zero k, ← blockCoord_one k]
  -- Apply Mathlib substitution rule (reversed)
  exact (integral_comp_mul_deriv'
    (f := blockCoord k) (f' := blockJacobian k)
    (fun x _ => blockCoord_hasDerivAt k x)
    ((blockJacobian_continuous k).continuousOn)
    (hg.mono (blockCoord_image_uIcc_subset k))).symm

end Aristotle.RSBlockParam
