/-
Bridge: provide `OmegaThetaToPiLiHyp` from a focused bridge module.

This isolates the remaining theta-to-(pi-li) transfer gap from
`CriticalAssumptions.lean`, matching the pattern used for other
bridge-owned critical assumptions.

Mathematical content:
  If theta(x) - x = Omega+-(f(x)) and f eventually dominates sqrt(x), then
  pi(x) - li(x) = Omega+-(f(x) / log x).

Status: 1 sorry.
  The transfer plumbing is now proved in
  `Aristotle/ThetaToPiLiTransferInfra.lean`.
  Completed in this file:
  1. `psiThetaCorrection =o(√x/log x)` (instance provided)
  2. `psiPiLiRemainder =o(√x/log x)` from the mean-square input
     `PsiRemainderMeanSquareHyp`
  The remaining sorry is only the global instance of
  `OmegaThetaToPiLiHyp`, i.e. a source for that mean-square input.

Consumed by:
  - Bridge/PsiToPiLiOscillation.lean
  - CriticalAssumptions.lean (imported bridge instance)
-/

import Littlewood.Aristotle.ThetaToPiLiTransferInfra
import Littlewood.Aristotle.PsiThetaCanonicalBound
import Littlewood.Aristotle.RemainderTermAnalysis
import Littlewood.ExplicitFormulas.ConversionFormulas

noncomputable section

open Conversion
open Real MeasureTheory Asymptotics Filter
open scoped Chebyshev

namespace OmegaThetaToPiLiWiring

open Aristotle.ThetaToPiLiTransferInfra
open Aristotle.PsiThetaCanonicalBound

/-- Remaining analytic blocker for the θ→(π-li) transfer:
the decomposition remainder must be little-o at the canonical `√x/log x` scale. -/
class ThetaPiLiRemainderSmallHyp : Prop where
  bound :
    Aristotle.ThetaToPiLiTransferInfra.thetaPiLiRemainder =o[Filter.atTop]
      (fun x => Real.sqrt x / Real.log x)

/-- First analytic sub-goal for the theta→(pi-li) bridge:
psi-based remainder is little-o at `√x/log x`. -/
class PsiPiLiRemainderSmallHyp : Prop where
  bound :
    Aristotle.ThetaToPiLiTransferInfra.psiPiLiRemainder =o[Filter.atTop]
      (fun x => Real.sqrt x / Real.log x)

/-- Second analytic sub-goal for the theta→(pi-li) bridge:
the psi/theta correction is little-o at `√x/log x`. -/
class PsiThetaCorrectionSmallHyp : Prop where
  bound :
    Aristotle.ThetaToPiLiTransferInfra.psiThetaCorrection =o[Filter.atTop]
      (fun x => Real.sqrt x / Real.log x)

lemma inv_weight_continuousOn_uIcc (x : ℝ) (hx : 2 ≤ x) :
    ContinuousOn (fun t : ℝ => (1 : ℝ) / (t * (Real.log t)^2)) (Set.uIcc 2 x) := by
  refine continuousOn_of_forall_continuousAt ?_
  intro t ht
  have ht' : t ∈ Set.Icc 2 x := by simpa [Set.uIcc_of_le hx] using ht
  have ht_pos : 0 < t := by linarith [ht'.1]
  have hlog_pos : 0 < Real.log t := Real.log_pos (lt_of_lt_of_le (by norm_num) ht'.1)
  have hden_ne : t * (Real.log t)^2 ≠ 0 := by
    exact mul_ne_zero (ne_of_gt ht_pos) (pow_ne_zero _ (ne_of_gt hlog_pos))
  exact ContinuousAt.div continuousAt_const
    (ContinuousAt.mul continuousAt_id (ContinuousAt.pow (Real.continuousAt_log (ne_of_gt ht_pos)) _))
    hden_ne

lemma psiThetaCorrection_eq_integral_diff (x : ℝ) (hx : 2 ≤ x) :
    psiThetaCorrection x =
      ∫ t in Set.Icc 2 x, (chebyshevPsi t - chebyshevTheta t) / (t * (Real.log t)^2) := by
  let w : ℝ → ℝ := fun t => (1 : ℝ) / (t * (Real.log t)^2)
  have hwcont : ContinuousOn w (Set.uIcc 2 x) := inv_weight_continuousOn_uIcc x hx

  have hpsi_int : IntervalIntegrable (fun t => chebyshevPsi t / (t * (Real.log t)^2)) volume 2 x := by
    have hpsi_base : IntervalIntegrable (fun t => chebyshevPsi t * w t) volume 2 x :=
      (Chebyshev.psi_mono.intervalIntegrable).mul_continuousOn hwcont
    simpa [w, div_eq_mul_inv, mul_assoc] using hpsi_base

  have htheta_int : IntervalIntegrable (fun t => chebyshevTheta t / (t * (Real.log t)^2)) volume 2 x := by
    have htheta_base : IntervalIntegrable (fun t => chebyshevTheta t * w t) volume 2 x :=
      (Chebyshev.theta_mono.intervalIntegrable).mul_continuousOn hwcont
    simpa [w, div_eq_mul_inv, mul_assoc] using htheta_base

  have hpsi_on : IntegrableOn (fun t => chebyshevPsi t / (t * (Real.log t)^2)) (Set.Icc 2 x) volume := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx).1 hpsi_int
  have htheta_on : IntegrableOn (fun t => chebyshevTheta t / (t * (Real.log t)^2)) (Set.Icc 2 x) volume := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx).1 htheta_int

  have hsub := MeasureTheory.integral_sub hpsi_on htheta_on
  unfold psiThetaCorrection
  rw [← hsub]
  congr
  ext t
  ring

lemma first_integral_isBigO_log :
    (fun x : ℝ => ∫ t in (2 : ℝ)..x, |(chebyshevPsi t - chebyshevTheta t)|^2 / t^2)
      =O[atTop] Real.log := by
  obtain ⟨C, hCpos, hbound⟩ := abs_chebyshevPsi_sub_chebyshevTheta_le_const_sqrt
  refine Asymptotics.IsBigO.of_bound (C^2) ?_
  refine (Filter.eventually_ge_atTop (2 : ℝ)).mono ?_
  intro x hx
  have hpoint :
      ∀ t ∈ Set.Ioc (2 : ℝ) x,
        |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2 ≤ C^2 / t := by
    intro t ht
    have ht2 : 2 ≤ t := le_of_lt ht.1
    have ht0 : 0 < t := by linarith
    have hbt : |chebyshevPsi t - chebyshevTheta t| ≤ C * Real.sqrt t := hbound t ht2
    have hsq : |chebyshevPsi t - chebyshevTheta t|^2 ≤ (C * Real.sqrt t)^2 := by
      nlinarith [hbt, abs_nonneg (chebyshevPsi t - chebyshevTheta t)]
    have ht_ne : t ≠ 0 := ne_of_gt ht0
    have ht2_ne : t^2 ≠ 0 := pow_ne_zero _ ht_ne
    have hsqrt_sq : (Real.sqrt t)^2 = t := by
      exact Real.sq_sqrt (le_of_lt ht0)
    calc
      |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2
          ≤ (C * Real.sqrt t)^2 / t^2 := by
              exact div_le_div_of_nonneg_right hsq (sq_nonneg t)
      _ = (C^2 * t) / t^2 := by
            rw [mul_pow, hsqrt_sq]
      _ = C^2 / t := by
            field_simp [ht2_ne]
  have h_rhs_interval : IntervalIntegrable (fun t : ℝ => C^2 / t) volume 2 x := by
    refine (continuousOn_of_forall_continuousAt ?_).intervalIntegrable
    intro t ht
    have ht' : t ∈ Set.Icc 2 x := by
      have hu : t ∈ Set.uIcc 2 x := ht
      simpa [Set.uIcc_of_le hx] using hu
    have ht0 : (t:ℝ) ≠ 0 := by linarith [ht'.1]
    exact (continuousAt_const.div continuousAt_id ht0)
  have h_rhs_int : IntegrableOn (fun t : ℝ => C^2 / t) (Set.Ioc 2 x) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).1 h_rhs_interval
  have h_lhs_meas : AEStronglyMeasurable
      (fun t : ℝ => |chebyshevPsi t - chebyshevTheta t|^2 / t^2)
      (volume.restrict (Set.Ioc 2 x)) := by
    have hpsi_meas : Measurable chebyshevPsi := Chebyshev.psi_mono.measurable
    have htheta_meas : Measurable chebyshevTheta := Chebyshev.theta_mono.measurable
    exact (((hpsi_meas.sub htheta_meas).abs.pow_const 2).div (measurable_id.pow_const 2)).aestronglyMeasurable
  have h_lhs_int : IntegrableOn
      (fun t : ℝ => |chebyshevPsi t - chebyshevTheta t|^2 / t^2)
      (Set.Ioc 2 x) volume := by
    refine MeasureTheory.Integrable.mono' h_rhs_int h_lhs_meas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have hpt := hpoint t ht
    have hnonneg : 0 ≤ |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2 := by
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hpt
  have hmono := MeasureTheory.setIntegral_mono_on h_lhs_int h_rhs_int measurableSet_Ioc hpoint
  have hrhs_eval : ∫ t in Set.Ioc (2 : ℝ) x, C^2 / t = C^2 * Real.log (x / 2) := by
    rw [← intervalIntegral.integral_of_le hx]
    have hconst :
        ∫ t in (2 : ℝ)..x, C^2 / t = C^2 * ∫ t in (2 : ℝ)..x, (1 / t) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (intervalIntegral.integral_const_mul (C^2) (fun t : ℝ => t⁻¹) (a := 2) (b := x))
    have h_nozero : (0 : ℝ) ∉ Set.uIcc (2 : ℝ) x := by
      simp [Set.uIcc_of_le hx]
    rw [hconst, integral_one_div h_nozero]
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith : 1 ≤ x)
  have hlog_div_le : Real.log (x / 2) ≤ Real.log x := by
    rw [Real.log_div (by positivity) (by positivity)]
    linarith [Real.log_pos one_lt_two]
  have h_bound' :
      ∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2 ≤ C^2 * Real.log x := by
    calc
      ∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2
          = ∫ t in Set.Ioc (2 : ℝ) x, |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2 := by
              rw [intervalIntegral.integral_of_le hx]
      _ ≤ ∫ t in Set.Ioc (2 : ℝ) x, C^2 / t := hmono
      _ = C^2 * Real.log (x / 2) := hrhs_eval
      _ ≤ C^2 * Real.log x := by
          exact mul_le_mul_of_nonneg_left hlog_div_le (sq_nonneg C)
  have hnorm : ‖Real.log x‖ = Real.log x := Real.norm_of_nonneg hlog_nonneg
  calc
    ‖∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2‖
        = |∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2| := by simp [Real.norm_eq_abs]
    _ = ∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2 := by
          rw [abs_of_nonneg]
          exact intervalIntegral.integral_nonneg (by linarith) (fun t ht => div_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ C^2 * Real.log x := h_bound'
    _ = C^2 * ‖Real.log x‖ := by rw [hnorm]

lemma correction_sq_le_product_bound (x : ℝ) (hx : 2 ≤ x) :
    |psiThetaCorrection x| ^ 2 ≤
      (∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2) *
      (∫ t in (2 : ℝ)..x, 1 / (Real.log t)^4) := by
  have hrepr :
      psiThetaCorrection x =
        ∫ t in Set.Ioc 2 x,
          ((chebyshevPsi t - chebyshevTheta t) / t) * (1 / (Real.log t)^2) := by
    have h' := psiThetaCorrection_eq_integral_diff x hx
    rw [h']
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    congr
    ext t
    ring

  have hf_meas : AEStronglyMeasurable
      (fun t : ℝ => (chebyshevPsi t - chebyshevTheta t) / t)
      (volume.restrict (Set.Ioc 2 x)) := by
    have hpsi_meas : Measurable chebyshevPsi := Chebyshev.psi_mono.measurable
    have htheta_meas : Measurable chebyshevTheta := Chebyshev.theta_mono.measurable
    exact (hpsi_meas.sub htheta_meas).div measurable_id |>.aestronglyMeasurable
  have hg_meas : AEStronglyMeasurable
      (fun t : ℝ => 1 / (Real.log t)^2)
      (volume.restrict (Set.Ioc 2 x)) := by
    exact (measurable_const.div (Real.measurable_log.pow_const 2)).aestronglyMeasurable

  have hf_int : IntegrableOn
      (fun t : ℝ => ((chebyshevPsi t - chebyshevTheta t) / t)^2)
      (Set.Ioc 2 x) volume := by
    obtain ⟨C, hCpos, hbound⟩ := abs_chebyshevPsi_sub_chebyshevTheta_le_const_sqrt
    have hpoint :
      ∀ t ∈ Set.Ioc (2 : ℝ) x,
        ((chebyshevPsi t - chebyshevTheta t) / t)^2 ≤ C^2 / t := by
      intro t ht
      have ht2 : 2 ≤ t := le_of_lt ht.1
      have ht0 : 0 < t := by linarith
      have hbt : |chebyshevPsi t - chebyshevTheta t| ≤ C * Real.sqrt t := hbound t ht2
      have hsqabs : |chebyshevPsi t - chebyshevTheta t|^2 ≤ (C * Real.sqrt t)^2 := by
        nlinarith [hbt, abs_nonneg (chebyshevPsi t - chebyshevTheta t)]
      have hsq : (chebyshevPsi t - chebyshevTheta t)^2 ≤ (C * Real.sqrt t)^2 := by
        simpa [sq_abs] using hsqabs
      have ht_ne : t ≠ 0 := ne_of_gt ht0
      have ht2_ne : t^2 ≠ 0 := pow_ne_zero _ ht_ne
      have hsqrt_sq : (Real.sqrt t)^2 = t := Real.sq_sqrt (le_of_lt ht0)
      calc
        ((chebyshevPsi t - chebyshevTheta t) / t)^2
            = (chebyshevPsi t - chebyshevTheta t)^2 / t^2 := by field_simp [ht2_ne]
        _ ≤ (C * Real.sqrt t)^2 / t^2 := by exact div_le_div_of_nonneg_right hsq (sq_nonneg t)
        _ = (C^2 * t) / t^2 := by rw [mul_pow, hsqrt_sq]
        _ = C^2 / t := by field_simp [ht2_ne]

    have h_rhs_interval : IntervalIntegrable (fun t : ℝ => C^2 / t) volume 2 x := by
      refine (continuousOn_of_forall_continuousAt ?_).intervalIntegrable
      intro t ht
      have ht' : t ∈ Set.Icc 2 x := by
        have hu : t ∈ Set.uIcc 2 x := ht
        simpa [Set.uIcc_of_le hx] using hu
      have ht0 : (t:ℝ) ≠ 0 := by linarith [ht'.1]
      exact (continuousAt_const.div continuousAt_id ht0)
    have h_rhs_int : IntegrableOn (fun t : ℝ => C^2 / t) (Set.Ioc 2 x) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).1 h_rhs_interval
    have h_lhs_meas : AEStronglyMeasurable
        (fun t : ℝ => ((chebyshevPsi t - chebyshevTheta t) / t)^2)
        (volume.restrict (Set.Ioc 2 x)) := by
      exact (((Chebyshev.psi_mono.measurable.sub Chebyshev.theta_mono.measurable).div measurable_id).pow_const 2).aestronglyMeasurable
    refine MeasureTheory.Integrable.mono' h_rhs_int h_lhs_meas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have hpt := hpoint t ht
    have hnonneg : 0 ≤ ((chebyshevPsi t - chebyshevTheta t) / t)^2 := sq_nonneg _
    calc
      ‖((chebyshevPsi t - chebyshevTheta t) / t)^2‖
          = ((chebyshevPsi t - chebyshevTheta t) / t)^2 := Real.norm_of_nonneg hnonneg
      _ ≤ C^2 / t := hpt

  have hg_int : IntegrableOn
      (fun t : ℝ => (1 / (Real.log t)^2)^2)
      (Set.Ioc 2 x) volume := by
    have h_cont : ContinuousOn (fun t : ℝ => (1 / (Real.log t)^2)^2) (Set.uIcc 2 x) := by
      refine continuousOn_of_forall_continuousAt ?_
      intro t ht
      have ht' : t ∈ Set.Icc 2 x := by
        have hu : t ∈ Set.uIcc 2 x := ht
        simpa [Set.uIcc_of_le hx] using hu
      have ht_pos : 0 < t := by linarith [ht'.1]
      have ht1 : 1 < t := lt_of_lt_of_le (by norm_num) ht'.1
      have hlog_pos : 0 < Real.log t := Real.log_pos ht1
      have hlog_ne : Real.log t ≠ 0 := ne_of_gt hlog_pos
      have hden_ne : (Real.log t)^2 ≠ 0 := pow_ne_zero _ hlog_ne
      exact (ContinuousAt.pow (ContinuousAt.div continuousAt_const
        (ContinuousAt.pow (Real.continuousAt_log (ne_of_gt ht_pos)) 2) hden_ne) 2)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).1 h_cont.intervalIntegrable

  have hcs := Aristotle.RemainderTermAnalysis.integral_Ioc_cauchy_schwarz (a := 2) (b := x) hx
      (f := fun t => (chebyshevPsi t - chebyshevTheta t) / t)
      (g := fun t => 1 / (Real.log t)^2)
      hf_meas hg_meas hf_int hg_int

  have hcs' :
      (∫ t in Set.Ioc 2 x,
          ((chebyshevPsi t - chebyshevTheta t) / t) * (1 / (Real.log t)^2))^2
      ≤
      (∫ t in Set.Ioc 2 x, ((chebyshevPsi t - chebyshevTheta t) / t)^2) *
      (∫ t in Set.Ioc 2 x, (1 / (Real.log t)^2)^2) := hcs
  have hrewrite1 :
      (∫ t in Set.Ioc 2 x, ((chebyshevPsi t - chebyshevTheta t) / t)^2)
        = ∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t|^2 / t^2 := by
    rw [← intervalIntegral.integral_of_le hx]
    congr
    ext t
    by_cases ht : t = 0
    · simp [ht]
    · field_simp [ht]
      rw [sq_abs]
  have hrewrite2 :
      (∫ t in Set.Ioc 2 x, (1 / (Real.log t)^2)^2)
        = ∫ t in (2 : ℝ)..x, 1 / (Real.log t)^4 := by
    rw [← intervalIntegral.integral_of_le hx]
    congr
    ext t
    ring

  rw [hrepr]
  calc
    |∫ t in Set.Ioc 2 x,
        ((chebyshevPsi t - chebyshevTheta t) / t) * (1 / (Real.log t)^2)|^2
      = (∫ t in Set.Ioc 2 x,
          ((chebyshevPsi t - chebyshevTheta t) / t) * (1 / (Real.log t)^2))^2 := by rw [sq_abs]
    _ ≤ (∫ t in Set.Ioc 2 x, ((chebyshevPsi t - chebyshevTheta t) / t)^2) *
          (∫ t in Set.Ioc 2 x, (1 / (Real.log t)^2)^2) := hcs'
    _ = (∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t|^2 / t^2) *
          (∫ t in (2 : ℝ)..x, 1 / (Real.log t)^4) := by rw [hrewrite1, hrewrite2]

/-- The psi/theta correction term is little-o at scale `√x/log x`. -/
theorem psiThetaCorrection_isLittleO :
    psiThetaCorrection =o[atTop] (fun x => Real.sqrt x / Real.log x) := by
  have h_prod :
      (fun x => |psiThetaCorrection x|^2)
        =O[atTop]
          (fun x =>
            (∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2) *
            (∫ t in (2 : ℝ)..x, 1 / (Real.log t)^4)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
    have hsq := correction_sq_le_product_bound x hx
    have hnonneg1 : 0 ≤ ∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t ht => div_nonneg (sq_nonneg _) (sq_nonneg _))
    have hnonneg2 : 0 ≤ ∫ t in (2 : ℝ)..x, 1 / (Real.log t)^4 :=
      intervalIntegral.integral_nonneg (by linarith) (fun t ht => one_div_nonneg.mpr (pow_nonneg (Real.log_nonneg (by linarith [ht.1])) _))
    calc
      ‖|psiThetaCorrection x|^2‖ = |psiThetaCorrection x|^2 := Real.norm_of_nonneg (sq_nonneg _)
      _ ≤ (∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2) *
            (∫ t in (2 : ℝ)..x, 1 / (Real.log t)^4) := hsq
      _ = ‖(∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2) *
            (∫ t in (2 : ℝ)..x, 1 / (Real.log t)^4)‖ := by
            rw [Real.norm_of_nonneg (mul_nonneg hnonneg1 hnonneg2)]
      _ = (1 : ℝ) * ‖(∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2) *
            (∫ t in (2 : ℝ)..x, 1 / (Real.log t)^4)‖ := by ring

  have h_sq :
      (fun x => |psiThetaCorrection x|^2)
        =O[atTop] (fun x => x / (Real.log x)^3) := by
    refine (h_prod.trans ?_).trans Aristotle.RemainderTermAnalysis.asymptotic_algebra_1
    exact first_integral_isBigO_log.mul Aristotle.RemainderTermAnalysis.integral_inv_log_pow_four_bound

  have h_sqrt :
      (fun x => |psiThetaCorrection x|)
        =O[atTop] (fun x => Real.sqrt (x / (Real.log x)^3)) := by
    rw [Asymptotics.isBigO_iff] at *
    obtain ⟨c, hc⟩ := h_sq
    refine ⟨Real.sqrt c, ?_⟩
    filter_upwards [hc, Filter.eventually_gt_atTop (1 : ℝ)] with x hx₁ hx₂
    norm_num [abs_of_nonneg, Real.sqrt_nonneg] at *
    rw [← Real.sqrt_mul']
    · convert Real.abs_le_sqrt hx₁ using 1
      have hx_nonneg : 0 ≤ x := by linarith
      have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx₂.le
      rw [abs_of_nonneg hx_nonneg, abs_of_nonneg hlog_nonneg]
    · exact div_nonneg (by positivity) (pow_nonneg (Real.log_nonneg hx₂.le) _)

  have h_final :
      (fun x => |psiThetaCorrection x|)
        =o[atTop] (fun x => Real.sqrt x / Real.log x) := by
    exact h_sqrt.trans_isLittleO Aristotle.RemainderTermAnalysis.asymptotic_algebra_2

  simpa [Real.norm_eq_abs] using Asymptotics.IsLittleO.of_norm_left h_final

instance : PsiThetaCorrectionSmallHyp :=
  ⟨psiThetaCorrection_isLittleO⟩

/-- The `psi` used in `RemainderTermAnalysis` matches the canonical
`chebyshevPsi`. -/
lemma remainderTermPsi_eq_chebyshevPsi (x : ℝ) :
    Aristotle.RemainderTermAnalysis.psi x = chebyshevPsi x := by
  unfold Aristotle.RemainderTermAnalysis.psi chebyshevPsi
  rw [Chebyshev.psi_eq_sum_Icc]
  have hIcc :
      Finset.Icc (0 : ℕ) ⌊x⌋₊ = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_Icc.mp hn with ⟨hn0, hnle⟩
      by_cases h0 : n = 0
      · exact Finset.mem_insert.mpr (Or.inl h0)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_Icc.mpr ⟨Nat.pos_iff_ne_zero.mpr h0, hnle⟩))
    · intro hn
      rcases Finset.mem_insert.mp hn with h0 | hn'
      · subst h0
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩
      · rcases Finset.mem_Icc.mp hn' with ⟨hn1, hnle⟩
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hnle⟩
  rw [hIcc, Finset.sum_insert]
  · simp [ArithmeticFunction.vonMangoldt.map_zero']
  · simp

/-- For `x ≥ 2`, the psi-based transfer remainder is a constant plus the
`RemainderTermAnalysis` remainder term. -/
lemma psiPiLiRemainder_eq_const_add_remainder_term (x : ℝ) (hx : 2 ≤ x) :
    psiPiLiRemainder x =
      (2 / Real.log 2) + Aristotle.RemainderTermAnalysis.remainder_term x := by
  let w : ℝ → ℝ := fun t => (1 : ℝ) / (t * (Real.log t)^2)
  have hwcont : ContinuousOn w (Set.uIcc 2 x) := inv_weight_continuousOn_uIcc x hx
  have hpsi_int : IntervalIntegrable (fun t => chebyshevPsi t * w t) volume 2 x :=
    (Chebyshev.psi_mono.intervalIntegrable).mul_continuousOn hwcont
  have hone_int : IntervalIntegrable (fun t => (1 : ℝ) / (Real.log t)^2) volume 2 x := by
    refine (continuousOn_of_forall_continuousAt ?_).intervalIntegrable
    intro t ht
    have ht' : t ∈ Set.Icc 2 x := by
      have hu : t ∈ Set.uIcc 2 x := ht
      simpa [Set.uIcc_of_le hx] using hu
    have ht_pos : 0 < t := by linarith [ht'.1]
    have hlog_pos : 0 < Real.log t := Real.log_pos (lt_of_lt_of_le (by norm_num) ht'.1)
    have hden_ne : (Real.log t)^2 ≠ 0 := pow_ne_zero _ (ne_of_gt hlog_pos)
    exact ContinuousAt.div continuousAt_const
      (ContinuousAt.pow (Real.continuousAt_log (ne_of_gt ht_pos)) _) hden_ne
  have hsub' :
      (∫ t in (2 : ℝ)..x, chebyshevPsi t / (t * (Real.log t)^2))
        - (∫ t in (2 : ℝ)..x, 1 / (Real.log t)^2)
      = ∫ t in (2 : ℝ)..x, (chebyshevPsi t - t) / (t * (Real.log t)^2) := by
    calc
      (∫ t in (2 : ℝ)..x, chebyshevPsi t / (t * (Real.log t)^2))
          - (∫ t in (2 : ℝ)..x, 1 / (Real.log t)^2)
          = ∫ t in (2 : ℝ)..x, chebyshevPsi t * w t - (1 : ℝ) / (Real.log t)^2 := by
            rw [intervalIntegral.integral_sub]
            · simp [w, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
            · simpa [w, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hpsi_int
            · exact hone_int
      _ = ∫ t in (2 : ℝ)..x, (chebyshevPsi t - t) / (t * (Real.log t)^2) := by
            refine intervalIntegral.integral_congr_ae ?_
            filter_upwards [Filter.Eventually.of_forall (fun t : ℝ => True.intro)] with t _
            intro ht
            by_cases hlog : Real.log t = 0
            · simp [w, hlog]
            · have ht_ne : t ≠ 0 := by
                intro ht0
                apply hlog
                simp [ht0]
              field_simp [w, hlog, ht_ne, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
              have hw :
                  w t * (Real.log t)^2 * t = 1 := by
                unfold w
                field_simp [hlog, ht_ne, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
              calc
                (chebyshevPsi t * w t * (Real.log t)^2 - 1) * t
                    = chebyshevPsi t * (w t * (Real.log t)^2 * t) - t := by ring
                _ = chebyshevPsi t * 1 - t := by rw [hw]
                _ = chebyshevPsi t - t := by ring
  unfold psiPiLiRemainder Aristotle.RemainderTermAnalysis.remainder_term
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hx, ← intervalIntegral.integral_of_le hx]
  calc
    (2 / Real.log 2 + ∫ t in (2 : ℝ)..x, chebyshevPsi t / (t * (Real.log t)^2))
        - ∫ t in (2 : ℝ)..x, 1 / (Real.log t)^2
        = (2 / Real.log 2) +
            ((∫ t in (2 : ℝ)..x, chebyshevPsi t / (t * (Real.log t)^2))
              - (∫ t in (2 : ℝ)..x, 1 / (Real.log t)^2)) := by ring
    _ = (2 / Real.log 2) +
        ∫ t in (2 : ℝ)..x, (chebyshevPsi t - t) / (t * (Real.log t)^2) := by
          rw [hsub']
    _ = (2 / Real.log 2) + ∫ t in (2 : ℝ)..x,
          (Aristotle.RemainderTermAnalysis.psi t - t) / (t * (Real.log t)^2) := by
          have hpsi_eq :
              (fun t : ℝ => (chebyshevPsi t - t) / (t * (Real.log t)^2))
                = (fun t : ℝ =>
                    (Aristotle.RemainderTermAnalysis.psi t - t) / (t * (Real.log t)^2)) := by
            funext t
            rw [remainderTermPsi_eq_chebyshevPsi t]
          simp [hpsi_eq]

/-- If the mean-square input required by `RemainderTermAnalysis` is available,
then the psi-based transfer remainder is little-o at `√x/log x`. -/
theorem psiPiLiRemainder_isLittleO_of_meanSquare
    (h_mean_sq :
      (fun x : ℝ =>
        ∫ t in (2 : ℝ)..x, |Aristotle.RemainderTermAnalysis.psi t - t|^2 / t^2)
        =O[atTop] Real.log) :
    psiPiLiRemainder =o[atTop] (fun x => Real.sqrt x / Real.log x) := by
  have hrem :
      Aristotle.RemainderTermAnalysis.remainder_term =o[atTop]
        (fun x => Real.sqrt x / Real.log x) :=
    Aristotle.RemainderTermAnalysis.integral_remainder_small_proven h_mean_sq
  have hlog_div_zero :
      Tendsto (fun x : ℝ => Real.log x / (x ^ (1 / 2 : ℝ))) atTop (nhds 0) := by
    exact
      (isLittleO_log_rpow_atTop (by positivity : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hlog_div_pos :
      ∀ᶠ x in atTop, 0 < Real.log x / (x ^ (1 / 2 : ℝ)) := by
    refine (Filter.eventually_gt_atTop (1 : ℝ)).mono ?_
    intro x hx
    exact div_pos (Real.log_pos hx) (Real.rpow_pos_of_pos (by linarith) _)
  have hlog_div_within :
      Tendsto (fun x : ℝ => Real.log x / (x ^ (1 / 2 : ℝ)))
        atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    exact (tendsto_nhdsWithin_iff).2 ⟨hlog_div_zero, hlog_div_pos⟩
  have hscale_atTop :
      Tendsto (fun x : ℝ => Real.sqrt x / Real.log x) atTop atTop := by
    have hinv :
        Tendsto (fun x : ℝ => (Real.log x / (x ^ (1 / 2 : ℝ)))⁻¹) atTop atTop :=
      tendsto_inv_nhdsGT_zero.comp hlog_div_within
    refine hinv.congr' ?_
    refine (Filter.eventually_gt_atTop (1 : ℝ)).mono ?_
    intro x hx
    have hlog_ne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
    have hxpow_ne : x ^ (1 / 2 : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)
    calc
      (Real.log x / (x ^ (1 / 2 : ℝ)))⁻¹ = x ^ (1 / 2 : ℝ) / Real.log x := by
        field_simp [hlog_ne, hxpow_ne]
      _ = Real.sqrt x / Real.log x := by rw [Real.sqrt_eq_rpow]
  have hscale_pos :
      ∀ᶠ x in atTop, 0 < Real.sqrt x / Real.log x := by
    refine (Filter.eventually_gt_atTop (1 : ℝ)).mono ?_
    intro x hx
    exact div_pos (Real.sqrt_pos.2 (by linarith)) (Real.log_pos hx)
  have hnorm_eq :
      (fun x : ℝ => ‖Real.sqrt x / Real.log x‖)
        =ᶠ[atTop] (fun x => Real.sqrt x / Real.log x) :=
    hscale_pos.mono (fun _ hx => by simp [Real.norm_of_nonneg (le_of_lt hx)])
  have hnorm_atTop :
      Tendsto (fun x : ℝ => ‖Real.sqrt x / Real.log x‖) atTop atTop :=
    hscale_atTop.congr' hnorm_eq.symm
  have hconst :
      (fun _ : ℝ => (2 / Real.log 2))
        =o[atTop] (fun x => Real.sqrt x / Real.log x) := by
    exact Asymptotics.isLittleO_const_left.2 (Or.inr hnorm_atTop)
  have hsum :
      (fun x : ℝ => (2 / Real.log 2) + Aristotle.RemainderTermAnalysis.remainder_term x)
        =o[atTop] (fun x => Real.sqrt x / Real.log x) :=
    hconst.add hrem
  have hEq :
      psiPiLiRemainder =ᶠ[atTop]
        (fun x => (2 / Real.log 2) + Aristotle.RemainderTermAnalysis.remainder_term x) := by
    refine (Filter.eventually_ge_atTop (2 : ℝ)).mono ?_
    intro x hx
    exact psiPiLiRemainder_eq_const_add_remainder_term x hx
  exact hsum.congr' hEq.symm EventuallyEq.rfl

/-- Mean-square input needed by `RemainderTermAnalysis` to control the
`psi`-based remainder. -/
class PsiRemainderMeanSquareHyp : Prop where
  bound :
    (fun x : ℝ =>
      ∫ t in (2 : ℝ)..x, |Aristotle.RemainderTermAnalysis.psi t - t|^2 / t^2)
      =O[atTop] Real.log

/-- Optional stronger input: a square-root pointwise bound for `psi - id`.
This is sufficient to derive `PsiRemainderMeanSquareHyp`. -/
class PsiPointwiseSqrtBoundHyp : Prop where
  bound :
    ∃ C > 0, ∀ x ≥ 2, |Aristotle.RemainderTermAnalysis.psi x - x| ≤ C * Real.sqrt x

theorem psiRemainderMeanSquare_of_pointwiseSqrt
    (hbound :
      ∃ C > 0, ∀ x ≥ 2, |Aristotle.RemainderTermAnalysis.psi x - x| ≤ C * Real.sqrt x) :
    (fun x : ℝ =>
      ∫ t in (2 : ℝ)..x, |Aristotle.RemainderTermAnalysis.psi t - t|^2 / t^2)
      =O[atTop] Real.log := by
  obtain ⟨C, hCpos, hpsi_bound⟩ := hbound
  refine Asymptotics.IsBigO.of_bound (C^2) ?_
  refine (Filter.eventually_ge_atTop (2 : ℝ)).mono ?_
  intro x hx
  have hpoint :
      ∀ t ∈ Set.Ioc (2 : ℝ) x,
        |Aristotle.RemainderTermAnalysis.psi t - t| ^ 2 / t ^ 2 ≤ C^2 / t := by
    intro t ht
    have ht2 : 2 ≤ t := le_of_lt ht.1
    have ht0 : 0 < t := by linarith
    have hbt : |Aristotle.RemainderTermAnalysis.psi t - t| ≤ C * Real.sqrt t :=
      hpsi_bound t ht2
    have hsq : |Aristotle.RemainderTermAnalysis.psi t - t|^2 ≤ (C * Real.sqrt t)^2 := by
      nlinarith [hbt, abs_nonneg (Aristotle.RemainderTermAnalysis.psi t - t)]
    have ht_ne : t ≠ 0 := ne_of_gt ht0
    have ht2_ne : t^2 ≠ 0 := pow_ne_zero _ ht_ne
    have hsqrt_sq : (Real.sqrt t)^2 = t := Real.sq_sqrt (le_of_lt ht0)
    calc
      |Aristotle.RemainderTermAnalysis.psi t - t| ^ 2 / t ^ 2
          ≤ (C * Real.sqrt t)^2 / t^2 := by
              exact div_le_div_of_nonneg_right hsq (sq_nonneg t)
      _ = (C^2 * t) / t^2 := by rw [mul_pow, hsqrt_sq]
      _ = C^2 / t := by field_simp [ht2_ne]
  have h_rhs_interval : IntervalIntegrable (fun t : ℝ => C^2 / t) volume 2 x := by
    refine (continuousOn_of_forall_continuousAt ?_).intervalIntegrable
    intro t ht
    have ht' : t ∈ Set.Icc 2 x := by
      have hu : t ∈ Set.uIcc 2 x := ht
      simpa [Set.uIcc_of_le hx] using hu
    have ht0 : (t : ℝ) ≠ 0 := by linarith [ht'.1]
    exact continuousAt_const.div continuousAt_id ht0
  have h_rhs_int : IntegrableOn (fun t : ℝ => C^2 / t) (Set.Ioc 2 x) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).1 h_rhs_interval
  have hpsi_meas : Measurable Aristotle.RemainderTermAnalysis.psi := by
    have hEq : Aristotle.RemainderTermAnalysis.psi = chebyshevPsi := by
      funext t
      exact remainderTermPsi_eq_chebyshevPsi t
    simpa [hEq] using (Chebyshev.psi_mono.measurable)
  have h_lhs_meas : AEStronglyMeasurable
      (fun t : ℝ => |Aristotle.RemainderTermAnalysis.psi t - t|^2 / t^2)
      (volume.restrict (Set.Ioc 2 x)) := by
    exact (((hpsi_meas.sub measurable_id).abs.pow_const 2).div
      (measurable_id.pow_const 2)).aestronglyMeasurable
  have h_lhs_int : IntegrableOn
      (fun t : ℝ => |Aristotle.RemainderTermAnalysis.psi t - t|^2 / t^2)
      (Set.Ioc 2 x) volume := by
    refine MeasureTheory.Integrable.mono' h_rhs_int h_lhs_meas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have hpt := hpoint t ht
    have hnonneg : 0 ≤ |Aristotle.RemainderTermAnalysis.psi t - t| ^ 2 / t ^ 2 := by
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hpt
  have hmono := MeasureTheory.setIntegral_mono_on h_lhs_int h_rhs_int measurableSet_Ioc hpoint
  have hrhs_eval : ∫ t in Set.Ioc (2 : ℝ) x, C^2 / t = C^2 * Real.log (x / 2) := by
    rw [← intervalIntegral.integral_of_le hx]
    have hconst :
        ∫ t in (2 : ℝ)..x, C^2 / t = C^2 * ∫ t in (2 : ℝ)..x, (1 / t) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (intervalIntegral.integral_const_mul (C^2) (fun t : ℝ => t⁻¹) (a := 2) (b := x))
    have h_nozero : (0 : ℝ) ∉ Set.uIcc (2 : ℝ) x := by
      simp [Set.uIcc_of_le hx]
    rw [hconst, integral_one_div h_nozero]
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith : 1 ≤ x)
  have hlog_div_le : Real.log (x / 2) ≤ Real.log x := by
    rw [Real.log_div (by positivity) (by positivity)]
    linarith [Real.log_pos one_lt_two]
  have h_bound' :
      ∫ t in (2 : ℝ)..x, |Aristotle.RemainderTermAnalysis.psi t - t| ^ 2 / t ^ 2
        ≤ C^2 * Real.log x := by
    calc
      ∫ t in (2 : ℝ)..x, |Aristotle.RemainderTermAnalysis.psi t - t| ^ 2 / t ^ 2
          = ∫ t in Set.Ioc (2 : ℝ) x, |Aristotle.RemainderTermAnalysis.psi t - t| ^ 2 / t ^ 2 := by
              rw [intervalIntegral.integral_of_le hx]
      _ ≤ ∫ t in Set.Ioc (2 : ℝ) x, C^2 / t := hmono
      _ = C^2 * Real.log (x / 2) := hrhs_eval
      _ ≤ C^2 * Real.log x := mul_le_mul_of_nonneg_left hlog_div_le (sq_nonneg C)
  have hnorm : ‖Real.log x‖ = Real.log x := Real.norm_of_nonneg hlog_nonneg
  calc
    ‖∫ t in (2 : ℝ)..x, |Aristotle.RemainderTermAnalysis.psi t - t| ^ 2 / t ^ 2‖
        = |∫ t in (2 : ℝ)..x, |Aristotle.RemainderTermAnalysis.psi t - t| ^ 2 / t ^ 2| := by
            simp [Real.norm_eq_abs]
    _ = ∫ t in (2 : ℝ)..x, |Aristotle.RemainderTermAnalysis.psi t - t| ^ 2 / t ^ 2 := by
          rw [abs_of_nonneg]
          exact intervalIntegral.integral_nonneg (by linarith)
            (fun t ht => div_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ C^2 * Real.log x := h_bound'
    _ = C^2 * ‖Real.log x‖ := by rw [hnorm]

instance [PsiPointwiseSqrtBoundHyp] : PsiRemainderMeanSquareHyp := by
  refine ⟨psiRemainderMeanSquare_of_pointwiseSqrt PsiPointwiseSqrtBoundHyp.bound⟩

theorem psiPiLiRemainderSmallHyp_of_meanSquare
    (h_mean_sq :
      (fun x : ℝ =>
        ∫ t in (2 : ℝ)..x, |Aristotle.RemainderTermAnalysis.psi t - t|^2 / t^2)
        =O[atTop] Real.log) :
    PsiPiLiRemainderSmallHyp := by
  refine ⟨?_⟩
  exact psiPiLiRemainder_isLittleO_of_meanSquare h_mean_sq

instance [PsiRemainderMeanSquareHyp] : PsiPiLiRemainderSmallHyp := by
  exact psiPiLiRemainderSmallHyp_of_meanSquare PsiRemainderMeanSquareHyp.bound

/-- Plumbing theorem: the two sub-goals imply the canonical theta remainder bound. -/
theorem theta_remainder_small_from_psi_split
    [PsiPiLiRemainderSmallHyp] [PsiThetaCorrectionSmallHyp] :
    ThetaPiLiRemainderSmallHyp := by
  refine ⟨?_⟩
  exact Aristotle.ThetaToPiLiTransferInfra.thetaPiLiRemainder_isLittleO_of_psi_split
    PsiPiLiRemainderSmallHyp.bound
    PsiThetaCorrectionSmallHyp.bound

/-- If the remainder is negligible at scale `f/log`, the transfer is automatic. -/
theorem omegaThetaToPiLi_from_remainder_small [ThetaPiLiRemainderSmallHyp] :
    OmegaThetaToPiLiHyp := by
  refine OmegaThetaToPiLiHyp.mk ?_
  intro f hf hθ
  have hrem :
      Aristotle.ThetaToPiLiTransferInfra.thetaPiLiRemainder =o[Filter.atTop]
        (fun x => f x / Real.log x) :=
    Aristotle.ThetaToPiLiTransferInfra.remainder_isLittleO_of_sqrt
      ThetaPiLiRemainderSmallHyp.bound hf
  exact Aristotle.ThetaToPiLiTransferInfra.omega_theta_to_pi_li_of_remainder_isLittleO
    f hf hθ hrem

/-- No-sorry transfer: once the two split remainders are controlled, the
theta→(pi-li) omega transfer follows automatically. -/
theorem omegaThetaToPiLi_from_psi_split
    [PsiPiLiRemainderSmallHyp] [PsiThetaCorrectionSmallHyp] :
    OmegaThetaToPiLiHyp := by
  let _ : ThetaPiLiRemainderSmallHyp := theta_remainder_small_from_psi_split
  exact omegaThetaToPiLi_from_remainder_small

/-- Placeholder bridge instance for the theta-to-(pi-li) oscillation transfer.
The remaining missing analytic input is `PsiRemainderMeanSquareHyp`. -/
instance : OmegaThetaToPiLiHyp := by
  refine OmegaThetaToPiLiHyp.mk ?_
  intro f hf h
  sorry

end OmegaThetaToPiLiWiring
