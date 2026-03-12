/-
Partial zeta mean square coefficient: ∫₁ᵀ |S_N(½+it)|² = ½·T·log T + O(T).

Extracted from HardyMeanSquareAsymptoticFromZetaMoment to a cycle-free location.
This file depends only on MeanSquare + HarmonicSumIntegral (Mathlib-only imports),
enabling use in CombinedB1B3DeepLeaf without the circular dependency through
HardyAfeSignedGapAtomic → afe_mean_square_bridge.

Proof outline:
  1. normSq decomposition: |S_N|² = H_{N(t)} + offDiag(t).re
  2. ∫(H_N − ½ log) = O(T) from integral_harmonicSum_sub_half_log_isBigO
  3. ∫ ½·log t = ½(T log T − T + 1)  [exact formula]
  4. |∫ offDiag| ≤ 8N² ≤ 8T  [off-diagonal bound]
  5. Combine: ∫|S_N|² = ½T log T + O(T)

Reference: Montgomery-Vaughan 2007, Theorem 9.1.

SORRY COUNT: 0

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.PartialZetaMeanSquareCoeff

open Filter Asymptotics MeasureTheory Set Real
open Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra

/-- Exact formula: ∫₁ᵀ log t = T·log T − T + 1 (integration by parts / FTC). -/
private lemma integral_log_exact (T : ℝ) (_hT : 1 ≤ T) :
    ∫ t in (1:ℝ)..T, Real.log t = T * Real.log T - T + 1 := by
  aesop

/-- **Partial zeta mean square coefficient**: ∫₁ᵀ |S_N(½+it)|² = ½·T·log T + O(T).

    Uses the Montgomery-Vaughan mean value theorem for Dirichlet polynomials:
    the diagonal terms give the harmonicSum integral and the off-diagonal terms
    are bounded by 8·N² = O(T). -/
theorem partial_zeta_mean_square_half_coeff :
    (fun T => (∫ t in (1:ℝ)..T, partialMsIntegrand t)
      - 2⁻¹ * T * Real.log T)
    =O[atTop] (fun T => T) := by
  -- Extract BigO witness from harmonicSum integral
  obtain ⟨C₁, hC₁_nn, hC₁⟩ := integral_harmonicSum_sub_half_log_isBigO.exists_nonneg
  rw [IsBigOWith] at hC₁
  -- Integrability: diagonal (monotone) and off-diagonal (piecewise continuous)
  have h_diag_int : ∀ T : ℝ, IntervalIntegrable
      (fun t => ∑ n ∈ Finset.Icc 1 (N_t t), (1:ℝ)/n) MeasureTheory.volume 1 T := by
    intro T; apply MonotoneOn.intervalIntegrable
    intro t _ u _ htu
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right (Nat.floor_mono (Real.sqrt_le_sqrt
        (div_le_div_of_nonneg_right htu (by positivity)))))
      (fun _ _ _ => by positivity)
  have h_offdiag_int : ∀ T : ℝ, IntervalIntegrable
      (fun t => (offDiagSsq t).re) MeasureTheory.volume 1 T := by
    intro T
    exact ⟨Complex.reCLM.integrable_comp (offDiagSsq_intervalIntegrable 1 T).1,
           Complex.reCLM.integrable_comp (offDiagSsq_intervalIntegrable 1 T).2⟩
  have h_half_log_int : ∀ T : ℝ, 1 ≤ T → IntervalIntegrable
      (fun t => 2⁻¹ * Real.log t) MeasureTheory.volume 1 T := by
    intro T hT
    exact (continuousOn_const.mul (Real.continuousOn_log.mono (fun t ht => by
      rw [Set.uIcc_of_le hT] at ht; exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
    )).intervalIntegrable
  -- Build pointwise bound
  refine .of_bound (C₁ + 1/2 + 8) ?_
  filter_upwards [hC₁, eventually_ge_atTop 1] with T hHS hT1
  -- Step 1: Rewrite integrand via normSq decomposition + harmonicSum bridge
  have h_eq : ∀ t, partialMsIntegrand t =
    harmonicSum (N_truncation t) + (offDiagSsq t).re := by
    intro t
    unfold partialMsIntegrand
    have := normSq_partialZeta_eq t
    rw [sum_Icc_eq_harmonicSum, N_t_eq_N_truncation] at this
    exact this
  -- Use integral_congr to rewrite integrand (keeps subtraction outside)
  have h_int_eq : ∫ t in (1:ℝ)..T, partialMsIntegrand t =
      ∫ t in (1:ℝ)..T, (harmonicSum (N_truncation t) + (offDiagSsq t).re) :=
    intervalIntegral.integral_congr (fun t _ => h_eq t)
  rw [h_int_eq]
  change ‖(∫ t in (1:ℝ)..T, (harmonicSum (N_truncation t) + (offDiagSsq t).re)) -
      2⁻¹ * T * Real.log T‖ ≤ (C₁ + 1 / 2 + 8) * ‖T‖
  have h_harm : ∀ t, (∑ n ∈ Finset.Icc 1 (N_t t), (1:ℝ)/n) = harmonicSum (N_truncation t) := by
    intro t; rw [sum_Icc_eq_harmonicSum, N_t_eq_N_truncation]
  -- Integrability in harmonicSum form
  have h1' : IntervalIntegrable
      (fun t => harmonicSum (N_truncation t)) MeasureTheory.volume 1 T := by
    have h1 := h_diag_int T; simp_rw [h_harm] at h1; exact h1
  have h3 := h_half_log_int T hT1
  have h2 := h_offdiag_int T
  have h_sub_int : IntervalIntegrable
      (fun t => harmonicSum (N_truncation t) - 2⁻¹ * Real.log t) MeasureTheory.volume 1 T :=
    h1'.sub h3
  -- Step 3: Split ∫(harm + offDiag) into three pieces
  have step1 := intervalIntegral.integral_add h1' h2
  have step2 := intervalIntegral.integral_add h_sub_int h3
  have h_congr : ∫ t in (1:ℝ)..T, harmonicSum (N_truncation t) =
      ∫ t in (1:ℝ)..T, ((harmonicSum (N_truncation t) - 2⁻¹ * Real.log t) + 2⁻¹ * Real.log t) :=
    intervalIntegral.integral_congr (fun t _ => (sub_add_cancel _ _).symm)
  -- Step 4: Exact formula for ∫ ½·log t
  have h_log : ∫ t in (1:ℝ)..T, (2⁻¹ * Real.log t) = 2⁻¹ * (T * Real.log T - T + 1) := by
    conv_lhs => rw [show (fun t => 2⁻¹ * Real.log t) = (fun t => (2:ℝ)⁻¹ * Real.log t) from rfl]
    rw [intervalIntegral.integral_const_mul, integral_log_exact T hT1]
  -- Normalize bound-variable names
  have step1' : ∫ t in (1:ℝ)..T, (harmonicSum (N_truncation t) + (offDiagSsq t).re) =
      (∫ t in (1:ℝ)..T, harmonicSum (N_truncation t)) +
      ∫ t in (1:ℝ)..T, (offDiagSsq t).re := step1
  have step2' : ∫ t in (1:ℝ)..T,
      ((harmonicSum (N_truncation t) - 2⁻¹ * Real.log t) + 2⁻¹ * Real.log t) =
      (∫ t in (1:ℝ)..T, (harmonicSum (N_truncation t) - 2⁻¹ * Real.log t)) +
      ∫ t in (1:ℝ)..T, (2⁻¹ * Real.log t) := step2
  -- Combine via rw chain
  have h_rw : (∫ t in (1:ℝ)..T, (harmonicSum (N_truncation t) + (offDiagSsq t).re)) -
      2⁻¹ * T * Real.log T =
    (∫ t in (1:ℝ)..T, (harmonicSum (N_truncation t) - 2⁻¹ * Real.log t)) +
    2⁻¹ * (1 - T) +
    (∫ t in (1:ℝ)..T, (offDiagSsq t).re) := by
    rw [step1', h_congr, step2', h_log]; ring
  rw [h_rw]
  -- Step 6: Triangle inequality and bound each piece
  have hT_nn : (0:ℝ) ≤ T := by linarith
  -- Bound 1: harmonicSum integral
  have hA : |∫ t in (1:ℝ)..T, (harmonicSum (N_truncation t) - 2⁻¹ * Real.log t)| ≤
      C₁ * |T| := by simpa only [Real.norm_eq_abs] using hHS
  -- Bound 2: ½·(1-T)
  have hB : |2⁻¹ * (1 - T)| ≤ (1/2) * |T| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2⁻¹)]
    have : |1 - T| ≤ |T| := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_of_nonneg hT_nn]; linarith
    linarith
  -- Bound 3: off-diagonal integral
  have hC : |∫ t in (1:ℝ)..T, (offDiagSsq t).re| ≤ 8 * |T| := by
    have h_int := offDiagSsq_intervalIntegrable 1 T
    have h_re_eq : ∫ t in (1:ℝ)..T, (offDiagSsq t).re =
        (∫ t in (1:ℝ)..T, offDiagSsq t).re :=
      Complex.reCLM.intervalIntegral_comp_comm h_int
    have h_N_sq : (N_t T : ℝ)^2 ≤ T := by
      have h1 : (N_t T : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) :=
        Nat.floor_le (Real.sqrt_nonneg _)
      have h4 : (N_t T : ℝ)^2 ≤ Real.sqrt (T / (2 * Real.pi)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
      linarith [Real.sq_sqrt (show (0:ℝ) ≤ T / (2 * Real.pi) by positivity),
        show T / (2 * Real.pi) ≤ T from div_le_self (by linarith) (by nlinarith [Real.pi_gt_three])]
    rw [h_re_eq]
    calc |(∫ t in (1:ℝ)..T, offDiagSsq t).re|
        ≤ ‖∫ t in (1:ℝ)..T, offDiagSsq t‖ := Complex.abs_re_le_norm _
      _ ≤ 8 * (N_t T : ℝ)^2 := norm_integral_offDiagSsq_le T hT1
      _ ≤ 8 * |T| := by nlinarith [abs_of_nonneg hT_nn]
  -- Combine via triangle inequality
  have tri1 := abs_add_le
    ((∫ t in (1:ℝ)..T, (harmonicSum (N_truncation t) - 2⁻¹ * Real.log t)) + 2⁻¹ * (1 - T))
    (∫ t in (1:ℝ)..T, (offDiagSsq t).re)
  have tri2 := abs_add_le
    (∫ t in (1:ℝ)..T, (harmonicSum (N_truncation t) - 2⁻¹ * Real.log t))
    (2⁻¹ * (1 - T))
  simp only [Real.norm_eq_abs] at *
  linarith

end Aristotle.Standalone.PartialZetaMeanSquareCoeff
