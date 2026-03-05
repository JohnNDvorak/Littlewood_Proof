import Littlewood.Aristotle.HardyMeanSquareAsymptoticLeaf
import Littlewood.Bridge.HardyZTransfer
import Littlewood.Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp
import Littlewood.Aristotle.Standalone.HardyAfeSignedGapRootInfra

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.HardyAfeZetaChannelFromAsymptotic

open Filter Asymptotics MeasureTheory Set
open Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra
open Aristotle.Standalone.HardyAfeSignedGapRootInfra

private lemma ep_sq_eq_decomp_sq (t : ℝ) :
    (HardyEstimatesPartial.hardyZ t) ^ 2 =
      (Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp.hardyZ t) ^ 2 := by
  have h_re := HardyZTransfer.hardyZ_eq_hardyZV2_re t
  have h_im := hardyZV2_real t
  have h_norm := hardyZV2_abs_eq_zeta_abs t
  have h_ep_sq : (HardyEstimatesPartial.hardyZ t) ^ 2 = ‖hardyZV2 t‖ ^ 2 := by
    rw [h_re]
    have h_eq : hardyZV2 t = ((hardyZV2 t).re : ℂ) :=
      Complex.ext rfl (by simp [h_im])
    conv_rhs => rw [h_eq, Complex.norm_real]
    exact (sq_abs _).symm
  have h_decomp_sq :
      (Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp.hardyZ t) ^ 2 =
        ‖hardyZV2 t‖ ^ 2 := by
    unfold Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp.hardyZ
    rw [← h_norm]
  rw [h_ep_sq, h_decomp_sq]

private lemma integral_ep_hardyZ_sq (T : ℝ) (hT : 1 ≤ T) :
    ∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t) ^ 2 =
      mean_square_zeta (1 / 2) T - mean_square_zeta (1 / 2) 1 := by
  have h_congr :
      ∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t) ^ 2 =
        ∫ t in Ioc 1 T,
          (Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp.hardyZ t) ^ 2 :=
    setIntegral_congr_fun measurableSet_Ioc (fun t _ => ep_sq_eq_decomp_sq t)
  rw [h_congr]
  exact
    Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp.integral_Ioc_one_eq_mean_square_sub
      T hT

/-- Extract the critical-line second moment asymptotic from the packaged
`HardyMeanSquareAsymptoticHyp` class. -/
theorem mean_square_zeta_half_asymp_of_hardyMeanSquareAsymptoticHyp
    [Aristotle.HardyMeanSquareAsymptoticLeaf.HardyMeanSquareAsymptoticHyp] :
    (fun T : ℝ => mean_square_zeta (1 / 2) T - T * Real.log T)
      =O[atTop] (fun T : ℝ => T) := by
  have h_asymp :
      (fun T : ℝ =>
        (∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t) ^ 2) - T * Real.log T)
        =O[atTop] (fun T : ℝ => T) :=
    Aristotle.HardyMeanSquareAsymptoticLeaf.HardyMeanSquareAsymptoticHyp.bound
  have h_shift :
      (fun T : ℝ =>
        ((mean_square_zeta (1 / 2) T - mean_square_zeta (1 / 2) 1) -
          T * Real.log T))
        =O[atTop] (fun T : ℝ => T) := by
    refine IsBigO.congr' h_asymp ?_ (Eventually.of_forall (fun _ => rfl))
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    rw [integral_ep_hardyZ_sq T hT]
  have h_const : (fun _ : ℝ => mean_square_zeta (1 / 2) 1) =O[atTop] (fun T => T) := by
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
  have h_sum :
      (fun T : ℝ =>
        (((mean_square_zeta (1 / 2) T - mean_square_zeta (1 / 2) 1) -
            T * Real.log T) + mean_square_zeta (1 / 2) 1))
        =O[atTop] (fun T : ℝ => T) := by
    simpa using h_shift.add h_const
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h_sum

/-- Recover the `1..T` zeta channel asymptotic from
`HardyMeanSquareAsymptoticHyp`. -/
theorem zeta_channel_main_term_isBigO_of_hardyMeanSquareAsymptoticHyp
    [Aristotle.HardyMeanSquareAsymptoticLeaf.HardyMeanSquareAsymptoticHyp] :
    (fun T => (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) - T * Real.log T)
      =O[atTop] (fun T : ℝ => T) := by
  letI : ZetaMeanSquareHalfBound :=
    ⟨mean_square_zeta_half_asymp_of_hardyMeanSquareAsymptoticHyp⟩
  exact Aristotle.Standalone.HardyAfeSignedGapScaffold.zeta_channel_main_term_isBigO_of_halfBound

/-- Exact pointwise bridge (for `T ≥ 1`) between the Hardy-Z channel and the
`zetaMsIntegrand` channel on `1..T`. -/
theorem integral_zetaMs_eq_integral_hardyZ_sq
    (T : ℝ) (hT : 1 ≤ T) :
    ∫ t in (1 : ℝ)..T, zetaMsIntegrand t =
      ∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t) ^ 2 := by
  calc
    ∫ t in (1 : ℝ)..T, zetaMsIntegrand t
        = mean_square_zeta (1 / 2) T - mean_square_zeta (1 / 2) 1 := by
            exact
              Aristotle.Standalone.HardyAfeSignedGapScaffold.integral_zetaMs_from_one_to_T_eq_mean_square_sub
                T hT
    _ = ∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t) ^ 2 := by
          rw [integral_ep_hardyZ_sq T hT]

/-- Non-circular route to the exact zeta-channel theorem from an explicit
Hardy-Z mean-square asymptotic on `Ioc 1 T`. -/
theorem zeta_channel_main_term_isBigO_of_hardyZ_ioc_main_term
    (hHardy :
      (fun T : ℝ =>
        (∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t) ^ 2) - T * Real.log T)
        =O[atTop] (fun T : ℝ => T)) :
    (fun T => (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) - T * Real.log T)
      =O[atTop] (fun T : ℝ => T) := by
  refine IsBigO.congr' hHardy ?_ (Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  rw [integral_zetaMs_eq_integral_hardyZ_sq T hT]

/-- Converse conversion: the exact zeta-channel theorem implies the Hardy-Z
`Ioc 1 T` main-term asymptotic. -/
theorem hardyZ_ioc_main_term_isBigO_of_zeta_channel_main_term
    (hzeta :
      (fun T => (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) - T * Real.log T)
        =O[atTop] (fun T : ℝ => T)) :
    (fun T : ℝ =>
      (∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t) ^ 2) - T * Real.log T)
      =O[atTop] (fun T : ℝ => T) := by
  refine IsBigO.congr' hzeta ?_ (Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  rw [integral_zetaMs_eq_integral_hardyZ_sq T hT]

/-- Exact equivalence between the two formulations of the Hardy mean-square
main term used in B1 root construction. -/
theorem zeta_channel_main_term_iff_hardyZ_ioc_main_term :
    ((fun T => (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) - T * Real.log T)
      =O[atTop] (fun T : ℝ => T)) ↔
    ((fun T : ℝ =>
      (∫ t in Ioc 1 T, (HardyEstimatesPartial.hardyZ t) ^ 2) - T * Real.log T)
      =O[atTop] (fun T : ℝ => T)) := by
  constructor
  · intro hzeta
    exact hardyZ_ioc_main_term_isBigO_of_zeta_channel_main_term hzeta
  · intro hHardy
    exact zeta_channel_main_term_isBigO_of_hardyZ_ioc_main_term hHardy

/-- Recover the signed AFE gap endpoint from
`HardyMeanSquareAsymptoticHyp`. -/
theorem signed_gap_isBigO_of_hardyMeanSquareAsymptoticHyp
    [Aristotle.HardyMeanSquareAsymptoticLeaf.HardyMeanSquareAsymptoticHyp] :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
      =O[atTop] (fun T : ℝ => T) := by
  exact signed_gap_isBigO_of_explicit_halfBound
    mean_square_zeta_half_asymp_of_hardyMeanSquareAsymptoticHyp

end Aristotle.Standalone.HardyAfeZetaChannelFromAsymptotic
