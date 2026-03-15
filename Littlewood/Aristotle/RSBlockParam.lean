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

-- ============================================================
-- Section 7: Block coordinate monotonicity across blocks
-- ============================================================

/-- blockCoord(k,p) < blockCoord(k+1,p) for p ∈ [0,1]. -/
theorem blockCoord_lt_succ (k : ℕ) {p : ℝ} (hp : 0 ≤ p) (_hp1 : p ≤ 1) :
    blockCoord k p < blockCoord (k + 1) p := by
  unfold blockCoord
  apply mul_lt_mul_of_pos_left _ (by positivity : (0 : ℝ) < 2 * Real.pi)
  exact pow_lt_pow_left₀ (by push_cast; linarith) (by positivity) two_ne_zero

/-- blockCoord is monotone in the block index at each fixed parameter. -/
theorem blockCoord_mono_block {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) (p : ℝ) (hp : 0 ≤ p) :
    blockCoord k₁ p ≤ blockCoord k₂ p := by
  unfold blockCoord
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  apply pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ _) _ 2
  have : (k₁ : ℝ) ≤ (k₂ : ℝ) := Nat.cast_le.mpr hk
  linarith

-- ============================================================
-- Section 8: Block integral signed structure (CoV with explicit Jacobian)
-- ============================================================

/-- Block integral via CoV with explicit Jacobian 4π(k+1+p). -/
theorem block_integral_cov_jacobian (k : ℕ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (hardyStart k) (hardyStart (k + 1)))) :
    ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), f t
      = ∫ p in Ioc 0 1, f (blockCoord k p) * (4 * Real.pi * ((k : ℝ) + 1 + p)) := by
  have h_jac : ∀ p, blockJacobian k p = 4 * Real.pi * ((k : ℝ) + 1 + p) := by
    intro p; unfold blockJacobian; ring
  simp_rw [← h_jac]
  exact block_integral_cov k f hf

-- ============================================================
-- Section 9: √(k+1) concavity — decrement bounds
-- ============================================================

/-- √(k+2) - √(k+1) ≤ √(k+1) - √(k): square root has decreasing increments. -/
theorem sqrt_decrement_antitone (k : ℕ) (_hk : 1 ≤ k) :
    Real.sqrt ((k : ℝ) + 2) - Real.sqrt ((k : ℝ) + 1)
      ≤ Real.sqrt ((k : ℝ) + 1) - Real.sqrt (k : ℝ) := by
  have hk_nn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have sq_k := Real.sq_sqrt hk_nn
  have sq_k1 := Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ) + 1 by linarith)
  have sq_k2 := Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ) + 2 by linarith)
  have prod_le : Real.sqrt (k : ℝ) * Real.sqrt ((k : ℝ) + 2) ≤ (k : ℝ) + 1 := by
    rw [← Real.sqrt_mul hk_nn]
    calc Real.sqrt ((k : ℝ) * ((k : ℝ) + 2))
        ≤ Real.sqrt (((k : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = (k : ℝ) + 1 := Real.sqrt_sq (by linarith)
  suffices h : 0 ≤ 2 * Real.sqrt ((k : ℝ) + 1) - Real.sqrt ((k : ℝ) + 2)
      - Real.sqrt (k : ℝ) by linarith
  have hS_pos : (0 : ℝ) < 2 * Real.sqrt ((k : ℝ) + 1) + Real.sqrt ((k : ℝ) + 2)
      + Real.sqrt (k : ℝ) := by positivity
  have h_ds_nn : 0 ≤ (2 * Real.sqrt ((k : ℝ) + 1) - Real.sqrt ((k : ℝ) + 2)
      - Real.sqrt (k : ℝ))
      * (2 * Real.sqrt ((k : ℝ) + 1) + Real.sqrt ((k : ℝ) + 2) + Real.sqrt (k : ℝ)) := by
    nlinarith [sq_k, sq_k1, sq_k2, prod_le,
               Real.sqrt_nonneg (k : ℝ), Real.sqrt_nonneg ((k : ℝ) + 2)]
  exact nonneg_of_mul_nonneg_left h_ds_nn hS_pos

/-- The square root increment √(k+1) - √k is positive for k ≥ 0. -/
theorem sqrt_increment_pos (k : ℕ) :
    0 < Real.sqrt ((k : ℝ) + 1) - Real.sqrt (k : ℝ) := by
  have : Real.sqrt (k : ℝ) < Real.sqrt ((k : ℝ) + 1) :=
    Real.sqrt_lt_sqrt (Nat.cast_nonneg k) (by linarith)
  linarith

/-- Upper bound on √(k+1)-√k: at most 1/(2√k) for k ≥ 1. -/
theorem sqrt_increment_le_inv (k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt ((k : ℝ) + 1) - Real.sqrt (k : ℝ) ≤ 1 / (2 * Real.sqrt (k : ℝ)) := by
  have hk_nn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have _hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have h2sk_pos : (0 : ℝ) < 2 * Real.sqrt (k : ℝ) := by positivity
  rw [le_div_iff₀ h2sk_pos]
  have sq_k := Real.sq_sqrt hk_nn
  have sq_k1 := Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ) + 1 by linarith)
  nlinarith [sq_nonneg (Real.sqrt (k : ℝ) - Real.sqrt ((k : ℝ) + 1))]

-- ============================================================
-- Section 10: Consecutive block difference infrastructure
-- ============================================================

/-- Difference of consecutive block integrals expressed via CoV. -/
theorem consecutive_block_diff_cov (k : ℕ) (f : ℝ → ℝ)
    (hf_k : ContinuousOn f (Icc (hardyStart k) (hardyStart (k + 1))))
    (hf_k1 : ContinuousOn f (Icc (hardyStart (k + 1)) (hardyStart (k + 2)))) :
    (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), f t)
      - (∫ t in Ioc (hardyStart (k + 1)) (hardyStart (k + 2)), f t)
    = (∫ p in Ioc 0 1, f (blockCoord k p) * blockJacobian k p)
      - (∫ p in Ioc 0 1, f (blockCoord (k + 1) p) * blockJacobian (k + 1) p) := by
  rw [block_integral_cov k f hf_k, block_integral_cov (k + 1) f hf_k1]

-- ============================================================
-- Section 11: Jacobian monotonicity
-- ============================================================

/-- Jacobian is monotone in block index: 4π(k+1+p) ≤ 4π(k+2+p). -/
theorem blockJacobian_mono_block (k : ℕ) (p : ℝ) :
    blockJacobian k p ≤ blockJacobian (k + 1) p := by
  unfold blockJacobian; push_cast; nlinarith [Real.pi_pos]

/-- Jacobian at p=0 in block k is 4π(k+1). -/
theorem blockJacobian_at_zero (k : ℕ) : blockJacobian k 0 = 4 * Real.pi * ((k : ℝ) + 1) := by
  unfold blockJacobian; ring

/-- Jacobian at p=1 in block k is 4π(k+2). -/
theorem blockJacobian_at_one (k : ℕ) : blockJacobian k 1 = 4 * Real.pi * ((k : ℝ) + 2) := by
  unfold blockJacobian; ring

end Aristotle.RSBlockParam
