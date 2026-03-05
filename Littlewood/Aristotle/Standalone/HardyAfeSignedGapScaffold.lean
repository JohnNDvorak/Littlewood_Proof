import Littlewood.Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.HardyAfeSignedGapScaffold

open Filter Asymptotics MeasureTheory Set
open Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra

/-- Rewrite the `1..T` zeta mean-square channel via `mean_square_zeta (1/2)` and a
constant basepoint subtraction. -/
lemma integral_zetaMs_from_one_to_T_eq_mean_square_sub
    (T : ℝ) (hT : 1 ≤ T) :
    ∫ t in (1 : ℝ)..T, zetaMsIntegrand t =
      mean_square_zeta (1 / 2) T - mean_square_zeta (1 / 2) 1 := by
  let A : ℝ := ∫ t in (0 : ℝ)..T, zetaMsIntegrand t
  let B : ℝ := ∫ t in (0 : ℝ)..1, zetaMsIntegrand t
  let C : ℝ := ∫ t in (1 : ℝ)..T, zetaMsIntegrand t
  have hsplit :
      A = B + C := by
    dsimp [A, B, C]
    exact
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_zetaMsIntegrand_any 0 1)
        (intervalIntegrable_zetaMsIntegrand_any 1 T) |>.symm
  have hstep :
      C = A - B := by
    refine (eq_sub_iff_add_eq).2 ?_
    calc
      C + B = B + C := by ring
      _ = A := by simpa [add_comm] using hsplit.symm
  simpa [A, B, C, mean_square_zeta, zetaMsIntegrand] using hstep

/-- The zeta `1..T` channel is `T log T + O(T)` if the standard critical-line
mean-square class is available. -/
theorem zeta_channel_main_term_isBigO_of_halfBound
    [ZetaMeanSquareHalfBound] :
    (fun T => (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) - T * Real.log T)
      =O[atTop] (fun T => T) := by
  have hMs : (fun T => mean_square_zeta (1 / 2) T - T * Real.log T)
      =O[atTop] (fun T => T) := mean_square_zeta_half_asymp
  have hConst : (fun _ : ℝ => mean_square_zeta (1 / 2) 1) =O[atTop] (fun T => T) := by
    refine IsBigO.of_bound (|mean_square_zeta (1 / 2) 1| + 1) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hT0 : 0 ≤ T := le_trans (by norm_num) hT
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
  have hShift :
      (fun T => (mean_square_zeta (1 / 2) T - T * Real.log T)
          - mean_square_zeta (1 / 2) 1)
      =O[atTop] (fun T => T) := by
    simpa using hMs.sub hConst
  refine IsBigO.congr' hShift ?_ (Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  rw [integral_zetaMs_from_one_to_T_eq_mean_square_sub T hT]
  ring

/-- Exact integral identity for the signed AFE mean-square gap integrand. -/
lemma integral_afeGap_eq_zeta_minus_two_partial (T : ℝ) :
    ∫ t in (1 : ℝ)..T, afeGapIntegrand t =
      (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) -
        2 * (∫ t in (1 : ℝ)..T, partialMsIntegrand t) := by
  have hz : IntervalIntegrable zetaMsIntegrand volume 1 T :=
    intervalIntegrable_zetaMsIntegrand T
  have hp : IntervalIntegrable partialMsIntegrand volume 1 T :=
    intervalIntegrable_partialMsIntegrand T
  unfold afeGapIntegrand
  rw [← intervalIntegral.integral_const_mul 2]
  rw [← intervalIntegral.integral_sub hz (hp.const_mul 2)]

/-- Route lemma for B1:
if both mean-square channels have the expected main terms with `O(T)` errors,
then the signed AFE gap integral is `O(T)`. -/
theorem signed_gap_isBigO_of_main_term_asymptotics
    (hzeta :
      (fun T => (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) - T * Real.log T)
        =O[atTop] (fun T => T))
    (hpartial :
      (fun T => (∫ t in (1 : ℝ)..T, partialMsIntegrand t) -
          (1 / 2 : ℝ) * T * Real.log T)
        =O[atTop] (fun T => T)) :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
      =O[atTop] (fun T => T) := by
  let f : ℝ → ℝ := fun T =>
    (∫ t in (1 : ℝ)..T, zetaMsIntegrand t) - T * Real.log T
  let g : ℝ → ℝ := fun T =>
    (∫ t in (1 : ℝ)..T, partialMsIntegrand t) -
      (1 / 2 : ℝ) * T * Real.log T
  have hf : f =O[atTop] (fun T => T) := by
    simpa [f] using hzeta
  have hg : g =O[atTop] (fun T => T) := by
    simpa [g] using hpartial
  have hfg : (fun T => f T - 2 * g T) =O[atTop] (fun T => T) := by
    simpa [sub_eq_add_neg] using hf.sub (hg.const_mul_left 2)
  have hEq :
      (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t) =
        (fun T => f T - 2 * g T) := by
    funext T
    dsimp [f, g]
    rw [integral_afeGap_eq_zeta_minus_two_partial]
    ring
  simpa [hEq] using hfg

/-- Route lemma for B1 with a standard class + partial-channel asymptotic:
if the critical-line zeta mean-square class is available and the partial-zeta
channel has `1/2 * T log T + O(T)`, then the signed AFE gap integral is `O(T)`. -/
theorem signed_gap_isBigO_of_halfBound_and_partial_asymptotic
    [ZetaMeanSquareHalfBound]
    (hpartial :
      (fun T => (∫ t in (1 : ℝ)..T, partialMsIntegrand t) -
          (1 / 2 : ℝ) * T * Real.log T)
        =O[atTop] (fun T => T)) :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
      =O[atTop] (fun T => T) := by
  exact
    signed_gap_isBigO_of_main_term_asymptotics
      zeta_channel_main_term_isBigO_of_halfBound
      hpartial

end Aristotle.Standalone.HardyAfeSignedGapScaffold
