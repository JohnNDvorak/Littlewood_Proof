import Littlewood.Aristotle.HarmonicSumIntegral
import Littlewood.Aristotle.MeanSquare
import Littlewood.Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra
import Littlewood.Aristotle.Standalone.HardyAfeSignedGapScaffold

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.HardyAfeSignedGapRootInfra

open Filter Asymptotics MeasureTheory Set Real
open Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra
open Aristotle.Standalone.HardyAfeSignedGapScaffold

/-- Bundled root payload for the B1 signed AFE gap leaf. -/
class HardyAfeSignedGapRootPayload : Prop where
  signedGap :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
      =O[atTop] (fun T : ℝ => T)

/-- Canonical extraction of the signed AFE gap from the bundled root payload. -/
theorem signed_gap_isBigO_of_rootPayload
    [HardyAfeSignedGapRootPayload] :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
      =O[atTop] (fun T : ℝ => T) :=
  HardyAfeSignedGapRootPayload.signedGap

/-- Exact formula: `∫_1^T log t dt = T log T - T + 1`. -/
private lemma integral_log_exact (T : ℝ) (_hT : 1 ≤ T) :
    ∫ t in (1 : ℝ)..T, Real.log t = T * Real.log T - T + 1 := by
  aesop

/-- Coefficient extraction for the partial-zeta channel:
`∫₁ᵀ |S_N|² = (1/2) * T * log T + O(T)`. -/
private lemma partial_zeta_normSq_half_coeff :
    (fun T => (∫ t in (1 : ℝ)..T,
        Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1 / 2 + Complex.I * t)))
      - 2⁻¹ * T * Real.log T)
    =O[atTop] (fun T => T) := by
  obtain ⟨C₁, hC₁_nn, hC₁⟩ := integral_harmonicSum_sub_half_log_isBigO.exists_nonneg
  rw [IsBigOWith] at hC₁
  have h_diag_int : ∀ T : ℝ, IntervalIntegrable
      (fun t => ∑ n ∈ Finset.Icc 1 (N_t t), (1 : ℝ) / n) MeasureTheory.volume 1 T := by
    intro T
    apply MonotoneOn.intervalIntegrable
    intro t _ u _ htu
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right (Nat.floor_mono (Real.sqrt_le_sqrt
        (div_le_div_of_nonneg_right htu (by positivity)))))
      (fun _ _ _ => by positivity)
  have h_offdiag_int : ∀ T : ℝ, IntervalIntegrable
      (fun t => (offDiagSsq t).re) MeasureTheory.volume 1 T := by
    intro T
    exact
      ⟨Complex.reCLM.integrable_comp (offDiagSsq_intervalIntegrable 1 T).1,
       Complex.reCLM.integrable_comp (offDiagSsq_intervalIntegrable 1 T).2⟩
  have h_half_log_int : ∀ T : ℝ, 1 ≤ T → IntervalIntegrable
      (fun t => 2⁻¹ * Real.log t) MeasureTheory.volume 1 T := by
    intro T hT
    exact (continuousOn_const.mul (Real.continuousOn_log.mono (fun t ht => by
      rw [Set.uIcc_of_le hT] at ht
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))).intervalIntegrable
  refine .of_bound (C₁ + 1 / 2 + 8) ?_
  filter_upwards [hC₁, eventually_ge_atTop (1 : ℝ)] with T hHS hT1
  have h_eq : ∀ t,
      Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1 / 2 + Complex.I * t)) =
      harmonicSum (N_truncation t) + (offDiagSsq t).re := by
    intro t
    have := normSq_partialZeta_eq t
    rw [sum_Icc_eq_harmonicSum, N_t_eq_N_truncation] at this
    exact this
  have h_int_eq : ∫ t in (1 : ℝ)..T,
      Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1 / 2 + Complex.I * t)) =
      ∫ t in (1 : ℝ)..T, (harmonicSum (N_truncation t) + (offDiagSsq t).re) :=
    intervalIntegral.integral_congr (fun t _ => h_eq t)
  rw [h_int_eq]
  change ‖(∫ t in (1 : ℝ)..T, (harmonicSum (N_truncation t) + (offDiagSsq t).re)) -
      2⁻¹ * T * Real.log T‖ ≤ (C₁ + 1 / 2 + 8) * ‖T‖
  have h_harm : ∀ t, (∑ n ∈ Finset.Icc 1 (N_t t), (1 : ℝ) / n) = harmonicSum (N_truncation t) := by
    intro t
    rw [sum_Icc_eq_harmonicSum, N_t_eq_N_truncation]
  have h1' : IntervalIntegrable
      (fun t => harmonicSum (N_truncation t)) MeasureTheory.volume 1 T := by
    have h1 := h_diag_int T
    simp_rw [h_harm] at h1
    exact h1
  have h3 := h_half_log_int T hT1
  have h2 := h_offdiag_int T
  have h_sub_int : IntervalIntegrable
      (fun t => harmonicSum (N_truncation t) - 2⁻¹ * Real.log t) MeasureTheory.volume 1 T :=
    h1'.sub h3
  have step1 := intervalIntegral.integral_add h1' h2
  have step2 := intervalIntegral.integral_add h_sub_int h3
  have h_congr : ∫ t in (1 : ℝ)..T, harmonicSum (N_truncation t) =
      ∫ t in (1 : ℝ)..T, ((harmonicSum (N_truncation t) - 2⁻¹ * Real.log t) + 2⁻¹ * Real.log t) :=
    intervalIntegral.integral_congr (fun t _ => (sub_add_cancel _ _).symm)
  have h_log : ∫ t in (1 : ℝ)..T, (2⁻¹ * Real.log t) = 2⁻¹ * (T * Real.log T - T + 1) := by
    conv_lhs => rw [show (fun t => 2⁻¹ * Real.log t) = (fun t => (2 : ℝ)⁻¹ * Real.log t) from rfl]
    rw [intervalIntegral.integral_const_mul, integral_log_exact T hT1]
  have step1' : ∫ t in (1 : ℝ)..T, (harmonicSum (N_truncation t) + (offDiagSsq t).re) =
      (∫ t in (1 : ℝ)..T, harmonicSum (N_truncation t)) +
      ∫ t in (1 : ℝ)..T, (offDiagSsq t).re := step1
  have step2' : ∫ t in (1 : ℝ)..T,
      ((harmonicSum (N_truncation t) - 2⁻¹ * Real.log t) + 2⁻¹ * Real.log t) =
      (∫ t in (1 : ℝ)..T, (harmonicSum (N_truncation t) - 2⁻¹ * Real.log t)) +
      ∫ t in (1 : ℝ)..T, (2⁻¹ * Real.log t) := step2
  have h_rw : (∫ t in (1 : ℝ)..T, (harmonicSum (N_truncation t) + (offDiagSsq t).re)) -
      2⁻¹ * T * Real.log T =
    (∫ t in (1 : ℝ)..T, (harmonicSum (N_truncation t) - 2⁻¹ * Real.log t)) +
    2⁻¹ * (1 - T) +
    (∫ t in (1 : ℝ)..T, (offDiagSsq t).re) := by
    rw [step1', h_congr, step2', h_log]
    ring
  rw [h_rw]
  have hT_nn : (0 : ℝ) ≤ T := by linarith
  have hA : |∫ t in (1 : ℝ)..T, (harmonicSum (N_truncation t) - 2⁻¹ * Real.log t)| ≤ C₁ * |T| := by
    simpa only [Real.norm_eq_abs] using hHS
  have hB : |2⁻¹ * (1 - T)| ≤ (1 / 2) * |T| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
    have : |1 - T| ≤ |T| := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_of_nonneg hT_nn]
      linarith
    linarith
  have hC : |∫ t in (1 : ℝ)..T, (offDiagSsq t).re| ≤ 8 * |T| := by
    have h_int := offDiagSsq_intervalIntegrable 1 T
    have h_re_eq : ∫ t in (1 : ℝ)..T, (offDiagSsq t).re =
        (∫ t in (1 : ℝ)..T, offDiagSsq t).re :=
      Complex.reCLM.intervalIntegral_comp_comm h_int
    have h_N_sq : (N_t T : ℝ) ^ 2 ≤ T := by
      have h1 : (N_t T : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) :=
        Nat.floor_le (Real.sqrt_nonneg _)
      have h4 : (N_t T : ℝ) ^ 2 ≤ Real.sqrt (T / (2 * Real.pi)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
      linarith [Real.sq_sqrt (show (0 : ℝ) ≤ T / (2 * Real.pi) by positivity),
        show T / (2 * Real.pi) ≤ T from div_le_self (by linarith)
          (by nlinarith [Real.pi_gt_three])]
    rw [h_re_eq]
    calc |(∫ t in (1 : ℝ)..T, offDiagSsq t).re|
        ≤ ‖∫ t in (1 : ℝ)..T, offDiagSsq t‖ := Complex.abs_re_le_norm _
      _ ≤ 8 * (N_t T : ℝ) ^ 2 := norm_integral_offDiagSsq_le T hT1
      _ ≤ 8 * |T| := by nlinarith [abs_of_nonneg hT_nn]
  have tri1 := abs_add_le
    ((∫ t in (1 : ℝ)..T, (harmonicSum (N_truncation t) - 2⁻¹ * Real.log t)) + 2⁻¹ * (1 - T))
    (∫ t in (1 : ℝ)..T, (offDiagSsq t).re)
  have tri2 := abs_add_le
    (∫ t in (1 : ℝ)..T, (harmonicSum (N_truncation t) - 2⁻¹ * Real.log t))
    (2⁻¹ * (1 - T))
  simp only [Real.norm_eq_abs] at *
  linarith

/-- Partial channel asymptotic for the AFE bridge:
`∫₁ᵀ partialMsIntegrand = (1/2) * T * log T + O(T)`. -/
theorem partial_channel_main_term_isBigO :
    (fun T => (∫ t in (1 : ℝ)..T, partialMsIntegrand t) -
      (1 / 2 : ℝ) * T * Real.log T)
    =O[atTop] (fun T => T) := by
  simpa [partialMsIntegrand, one_div] using partial_zeta_normSq_half_coeff

/-- Root route to the signed AFE gap bound from the classical half-line
mean-square class plus the proved partial-channel asymptotic. -/
theorem signed_gap_isBigO_of_halfBound
    [ZetaMeanSquareHalfBound] :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
      =O[atTop] (fun T => T) := by
  exact signed_gap_isBigO_of_halfBound_and_partial_asymptotic
    partial_channel_main_term_isBigO

/-- Root route from a signed AFE gap bound to the zeta `1..T` channel:
`∫₁ᵀ |ζ|² - T log T = O(T)`. -/
theorem zeta_channel_main_term_isBigO_of_signed_gap
    (hSigned :
      (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
        =O[atTop] (fun T => T)) :
    (fun T => (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) - T * Real.log T)
      =O[atTop] (fun T => T) := by
  let bridge : ℝ → ℝ := fun T =>
    (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) -
      2 * (∫ t in (1 : ℝ)..T, partialMsIntegrand t)
  let partialErr : ℝ → ℝ := fun T =>
    (∫ t in (1 : ℝ)..T, partialMsIntegrand t) -
      (1 / 2 : ℝ) * T * Real.log T
  have hBridge : bridge =O[atTop] (fun T => T) := by
    simpa [bridge] using mean_square_bridge_of_signed_remainder hSigned
  have hPartial : partialErr =O[atTop] (fun T => T) := by
    simpa [partialErr] using partial_channel_main_term_isBigO
  have hAsymp :
      (fun T => bridge T + 2 * partialErr T) =O[atTop] (fun T => T) := by
    simpa using hBridge.add (hPartial.const_mul_left 2)
  have hEq :
      (fun T => bridge T + 2 * partialErr T) =
        (fun T => (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) - T * Real.log T) := by
    funext T
    dsimp [bridge, partialErr]
    ring
  simpa [hEq] using hAsymp

/-- Root route from a signed AFE gap bound to the standard critical-line
mean-square asymptotic:
`mean_square_zeta (1/2) T - T log T = O(T)`. -/
theorem mean_square_zeta_half_asymp_of_signed_gap
    (hSigned :
      (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
        =O[atTop] (fun T => T)) :
    (fun T : ℝ => mean_square_zeta (1 / 2) T - T * Real.log T)
      =O[atTop] (fun T : ℝ => T) := by
  have hzeta : (fun T => (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) - T * Real.log T)
      =O[atTop] (fun T => T) :=
    zeta_channel_main_term_isBigO_of_signed_gap hSigned
  have hshift :
      (fun T => (mean_square_zeta (1 / 2) T - T * Real.log T) -
        mean_square_zeta (1 / 2) 1)
      =O[atTop] (fun T => T) := by
    refine IsBigO.congr' hzeta ?_ (Eventually.of_forall (fun _ => rfl))
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    rw [integral_zetaMs_from_one_to_T_eq_mean_square_sub T hT]
    ring
  have hconst : (fun _ : ℝ => mean_square_zeta (1 / 2) 1) =O[atTop] (fun T => T) := by
    refine IsBigO.of_bound (|mean_square_zeta (1 / 2) 1| + 1) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hT0 : (0 : ℝ) ≤ T := by linarith
    have hTnorm : (1 : ℝ) ≤ ‖T‖ := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hT0] using hT
    have hcoef_nonneg : 0 ≤ |mean_square_zeta (1 / 2) 1| + 1 := by positivity
    calc
      ‖mean_square_zeta (1 / 2) 1‖
          = |mean_square_zeta (1 / 2) 1| := by
            simpa using (Real.norm_eq_abs (mean_square_zeta (1 / 2) 1))
      _ ≤ |mean_square_zeta (1 / 2) 1| + 1 := by
            exact le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)
      _ ≤ (|mean_square_zeta (1 / 2) 1| + 1) * ‖T‖ := by
            calc
              |mean_square_zeta (1 / 2) 1| + 1
                  = (|mean_square_zeta (1 / 2) 1| + 1) * 1 := by ring
              _ ≤ (|mean_square_zeta (1 / 2) 1| + 1) * ‖T‖ := by
                    exact mul_le_mul_of_nonneg_left hTnorm hcoef_nonneg
  have hsum :
      (fun T => ((mean_square_zeta (1 / 2) T - T * Real.log T) -
        mean_square_zeta (1 / 2) 1) + mean_square_zeta (1 / 2) 1)
      =O[atTop] (fun T => T) := by
    simpa using hshift.add hconst
  simpa [sub_eq_add_neg, add_assoc] using hsum

/-- Root-payload endpoint for the critical-line mean-square asymptotic. -/
theorem mean_square_zeta_half_asymp_of_rootPayload
    [HardyAfeSignedGapRootPayload] :
    (fun T : ℝ => mean_square_zeta (1 / 2) T - T * Real.log T)
      =O[atTop] (fun T : ℝ => T) := by
  exact mean_square_zeta_half_asymp_of_signed_gap signed_gap_isBigO_of_rootPayload

/-- Root route with an explicit (non-typeclass) zeta mean-square input:
if `mean_square_zeta (1/2) T - T log T = O(T)` is supplied directly, then the
signed AFE gap bound follows. -/
theorem signed_gap_isBigO_of_explicit_halfBound
    (hhalf :
      (fun T : ℝ => mean_square_zeta (1 / 2) T - T * Real.log T)
        =O[atTop] (fun T => T)) :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
      =O[atTop] (fun T => T) := by
  letI : ZetaMeanSquareHalfBound := ⟨hhalf⟩
  exact signed_gap_isBigO_of_halfBound

end Aristotle.Standalone.HardyAfeSignedGapRootInfra
