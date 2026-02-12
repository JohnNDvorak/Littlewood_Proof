/- 
Crude amplitude bounds for Riemann-Siegel remainder blocks.

This is auxiliary infrastructure for the block decomposition route:
- per-block absolute integral bounds from a pointwise RS remainder decay input
- a global crude first-moment bound `O(T^(3/4))` from the same input
-/

import Mathlib
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyNProperties

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.RSBlockAmplitude

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

private lemma hardyStart_le_succ (k : ℕ) :
    hardyStart k ≤ hardyStart (k + 1) := by
  have hlen := Aristotle.HardyNProperties.block_length k
  have hnonneg : 0 ≤ 2 * Real.pi * (2 * (k : ℝ) + 3) := by positivity
  linarith

private lemma hardyStart_ge_one (k : ℕ) : (1 : ℝ) ≤ hardyStart k := by
  rw [Aristotle.HardyNProperties.hardyStart_formula]
  have hk1 : (1 : ℝ) ≤ (k + 1 : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
  have hsq : (1 : ℝ) ≤ ((k + 1 : ℝ) ^ 2) := by nlinarith [hk1]
  have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  nlinarith

/-- Crude per-block bound from a pointwise RS remainder input.

The hypothesis is the standard RS-size control `|ErrorTerm t| ≤ C_rs * t^(-1/4)` on `t ≥ 1`.
On each block, this implies `|ErrorTerm t| ≤ C_rs`, so the block integral is bounded by
`C_rs * block_length`.
-/
theorem per_block_crude_bound
    (C_rs : ℝ)
    (hC_nonneg : 0 ≤ C_rs)
    (hpoint : ∀ t : ℝ, t ≥ 1 →
      |ErrorTerm t| ≤ C_rs * t ^ (-(1 / 4 : ℝ)))
    (T : ℝ) (hT : T ≥ 2) (k : ℕ) (hk : k < hardyN T) :
    |∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t|
      ≤ C_rs * (hardyStart (k + 1) - hardyStart k) := by
  let a : ℝ := min T (hardyStart k)
  let b : ℝ := min T (hardyStart (k + 1))
  have hT_nonneg : 0 ≤ T := by linarith
  have hstart_le_T : hardyStart k ≤ T := (hardyN_lt_iff k T hT_nonneg).1 hk
  have ha_eq : a = hardyStart k := by
    dsimp [a]
    exact min_eq_right hstart_le_T
  have hab : a ≤ b := by
    dsimp [a, b]
    exact min_le_min_left T (hardyStart_le_succ k)
  have h_bound_const : ∀ x ∈ Ioc a b, ‖ErrorTerm x‖ ≤ C_rs := by
    intro x hx
    have hxa : a < x := hx.1
    have hx_ge_one : (1 : ℝ) ≤ x := by
      have hage : (1 : ℝ) ≤ a := by
        rw [ha_eq]
        exact hardyStart_ge_one k
      linarith
    have hpow_le_one : x ^ (-(1 / 4 : ℝ)) ≤ 1 := by
      have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx_ge_one
      have hpow_ge_one : 1 ≤ x ^ (1 / 4 : ℝ) := by
        exact Real.one_le_rpow hx_ge_one (by norm_num)
      have hpow_pos : 0 < x ^ (1 / 4 : ℝ) := by
        exact Real.rpow_pos_of_pos hx_pos (1 / 4 : ℝ)
      calc
        x ^ (-(1 / 4 : ℝ)) = (x ^ (1 / 4 : ℝ))⁻¹ := by
          rw [Real.rpow_neg (le_of_lt hx_pos)]
        _ ≤ (1 : ℝ)⁻¹ := by
          exact (inv_le_inv₀ hpow_pos (by norm_num)).2 hpow_ge_one
        _ = 1 := by norm_num
    have hpointx : |ErrorTerm x| ≤ C_rs * x ^ (-(1 / 4 : ℝ)) := hpoint x hx_ge_one
    calc
      ‖ErrorTerm x‖ = |ErrorTerm x| := by simp
      _ ≤ C_rs * x ^ (-(1 / 4 : ℝ)) := hpointx
      _ ≤ C_rs * 1 := by
            exact mul_le_mul_of_nonneg_left hpow_le_one hC_nonneg
      _ = C_rs := by ring
  have h_fin : volume (Ioc a b) < ⊤ := by simp
  have h_int_len :
      |∫ t in Ioc a b, ErrorTerm t|
        ≤ C_rs * (volume.real (Ioc a b)) := by
    simpa [Real.norm_eq_abs] using
      (MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (f := ErrorTerm) (s := Ioc a b) (μ := volume) h_fin h_bound_const)
  have h_len_real : (volume.real (Ioc a b)) = b - a := by
    rw [MeasureTheory.Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal]
    exact sub_nonneg.mpr hab
  have h_b_sub_a :
      b - a ≤ hardyStart (k + 1) - hardyStart k := by
    have hb_le : b ≤ hardyStart (k + 1) := by
      dsimp [b]
      exact min_le_right T (hardyStart (k + 1))
    calc
      b - a ≤ hardyStart (k + 1) - a := sub_le_sub_right hb_le a
      _ = hardyStart (k + 1) - hardyStart k := by rw [ha_eq]
  calc
    |∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t|
        = |∫ t in Ioc a b, ErrorTerm t| := by simp [a, b]
    _ ≤ C_rs * (volume.real (Ioc a b)) := h_int_len
    _ = C_rs * (b - a) := by rw [h_len_real]
    _ ≤ C_rs * (hardyStart (k + 1) - hardyStart k) := by
          exact mul_le_mul_of_nonneg_left h_b_sub_a hC_nonneg

/-- Crude global first-moment bound from the pointwise RS-size input
`|ErrorTerm t| ≤ C_rs * t^(-1/4)` on `t ≥ 1`.

This yields `|∫_1^T ErrorTerm| ≤ (4/3) * C_rs * T^(3/4)` for `T ≥ 2`. -/
theorem errorTerm_first_moment_crude
    (C_rs : ℝ)
    (hC_nonneg : 0 ≤ C_rs)
    (hpoint : ∀ t : ℝ, t ≥ 1 →
      |ErrorTerm t| ≤ C_rs * t ^ (-(1 / 4 : ℝ))) :
    ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, ErrorTerm t| ≤ ((4 / 3 : ℝ) * C_rs) * T ^ (3 / 4 : ℝ) := by
  intro T hT
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hErrInt :
      IntervalIntegrable ErrorTerm volume 1 T := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT1).2
      (errorTerm_integrable T)
  have hQuarterInt :
      IntervalIntegrable (fun t : ℝ => C_rs * t ^ (-(1 / 4 : ℝ))) volume 1 T := by
    refine (intervalIntegral.intervalIntegrable_rpow' (a := 1) (b := T)
      (r := (-(1 / 4 : ℝ))) (by norm_num)).const_mul C_rs
  have hMono :
      ∫ t in 1..T, |ErrorTerm t|
        ≤ ∫ t in 1..T, C_rs * t ^ (-(1 / 4 : ℝ)) := by
    refine intervalIntegral.integral_mono_on hT1 hErrInt.norm hQuarterInt ?_
    intro t ht
    have htIcc : t ∈ Set.Icc (1 : ℝ) T := by
      simpa [Set.uIcc_of_le hT1] using ht
    exact hpoint t htIcc.1
  have hAbsInt :
      |∫ t in 1..T, ErrorTerm t|
        ≤ ∫ t in 1..T, |ErrorTerm t| := by
    simpa [Real.norm_eq_abs] using
      (intervalIntegral.norm_integral_le_integral_norm
        (f := ErrorTerm) hT1)
  have hRpowRaw :
      ∫ t in 1..T, t ^ (-(1 / 4 : ℝ))
        = (T ^ ((-(1 / 4 : ℝ)) + 1) - (1 : ℝ) ^ ((-(1 / 4 : ℝ)) + 1))
            / ((-(1 / 4 : ℝ)) + 1) := by
    simpa using (integral_rpow (a := 1) (b := T) (r := (-(1 / 4 : ℝ)))
      (Or.inl (by norm_num : (-1 : ℝ) < (-(1 / 4 : ℝ)))))
  have hConstMul :
      ∫ t in 1..T, C_rs * t ^ (-(1 / 4 : ℝ))
        = C_rs * ∫ t in 1..T, t ^ (-(1 / 4 : ℝ)) := by
    simpa using
      (intervalIntegral.integral_const_mul (a := 1) (b := T) (μ := volume)
        C_rs (fun t : ℝ => t ^ (-(1 / 4 : ℝ))))
  have hRpowLe :
      ∫ t in 1..T, t ^ (-(1 / 4 : ℝ))
        ≤ (4 / 3 : ℝ) * T ^ (3 / 4 : ℝ) := by
    have hTpow_nonneg : 0 ≤ T ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
    have hRpowRaw' :
        ∫ t in 1..T, t ^ (-(1 / 4 : ℝ))
          = (T ^ (3 / 4 : ℝ) - 1) / (3 / 4 : ℝ) := by
      have h34 : ((-(1 / 4 : ℝ)) + 1) = (3 / 4 : ℝ) := by norm_num
      have htmp := hRpowRaw
      rw [h34, Real.one_rpow] at htmp
      simpa using htmp
    calc
      ∫ t in 1..T, t ^ (-(1 / 4 : ℝ))
          = (T ^ (3 / 4 : ℝ) - 1) / (3 / 4 : ℝ) := hRpowRaw'
      _ ≤ (T ^ (3 / 4 : ℝ)) / (3 / 4 : ℝ) := by
            have hden : (0 : ℝ) < (3 / 4 : ℝ) := by norm_num
            exact (div_le_iff₀ hden).2 (by linarith)
      _ = (4 / 3 : ℝ) * T ^ (3 / 4 : ℝ) := by
            ring
  have hScale :
      ∫ t in 1..T, C_rs * t ^ (-(1 / 4 : ℝ))
        ≤ ((4 / 3 : ℝ) * C_rs) * T ^ (3 / 4 : ℝ) := by
    calc
      ∫ t in 1..T, C_rs * t ^ (-(1 / 4 : ℝ))
          = C_rs * ∫ t in 1..T, t ^ (-(1 / 4 : ℝ)) := hConstMul
      _ ≤ C_rs * ((4 / 3 : ℝ) * T ^ (3 / 4 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hRpowLe hC_nonneg
      _ = ((4 / 3 : ℝ) * C_rs) * T ^ (3 / 4 : ℝ) := by ring
  calc
    |∫ t in Ioc 1 T, ErrorTerm t|
        = |∫ t in 1..T, ErrorTerm t| := by
            rw [← intervalIntegral.integral_of_le hT1]
    _ ≤ ∫ t in 1..T, |ErrorTerm t| := hAbsInt
    _ ≤ ∫ t in 1..T, C_rs * t ^ (-(1 / 4 : ℝ)) := hMono
    _ ≤ ((4 / 3 : ℝ) * C_rs) * T ^ (3 / 4 : ℝ) := hScale

/-- Existential form of the crude global first-moment bound from
pointwise RS-size control. -/
theorem errorTerm_first_moment_crude_exists
    (hpoint : ∃ C_rs > 0, ∀ t : ℝ, t ≥ 1 →
      |ErrorTerm t| ≤ C_rs * t ^ (-(1 / 4 : ℝ))) :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, ErrorTerm t| ≤ C * T ^ (3 / 4 : ℝ) := by
  rcases hpoint with ⟨C_rs, hC_pos, hC_point⟩
  refine ⟨(4 / 3 : ℝ) * C_rs, by positivity, ?_⟩
  intro T hT
  simpa [mul_assoc] using
    errorTerm_first_moment_crude C_rs (le_of_lt hC_pos) hC_point T hT

end Aristotle.RSBlockAmplitude
