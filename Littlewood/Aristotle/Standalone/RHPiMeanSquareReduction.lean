import Littlewood.Aristotle.ThetaToPiLiTransferInfra
import Littlewood.Aristotle.PsiThetaCanonicalBound
import Littlewood.Aristotle.RemainderTermAnalysis

noncomputable section

open Real MeasureTheory Asymptotics Filter
open scoped Chebyshev

namespace Aristotle.Standalone.RHPiMeanSquareReduction

open Aristotle.ThetaToPiLiTransferInfra
open Aristotle.PsiThetaCanonicalBound

/-- Continuity of the standard Step 5 weight on compact intervals away from `0`. -/
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
    (ContinuousAt.mul continuousAt_id
      (ContinuousAt.pow (Real.continuousAt_log (ne_of_gt ht_pos)) _))
    hden_ne

/-- Rewrite the `ψ-θ` correction term as a single weighted integral of the
difference `ψ-θ`. -/
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

  have hpsi_on : IntegrableOn
      (fun t => chebyshevPsi t / (t * (Real.log t)^2)) (Set.Icc 2 x) volume := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx).1 hpsi_int
  have htheta_on : IntegrableOn
      (fun t => chebyshevTheta t / (t * (Real.log t)^2)) (Set.Icc 2 x) volume := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx).1 htheta_int

  have hsub := MeasureTheory.integral_sub hpsi_on htheta_on
  unfold psiThetaCorrection
  rw [← hsub]
  congr
  ext t
  ring

/-- Mean-square control of the `ψ-θ` difference after dividing by `t`. -/
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
    have hsqrt_sq : (Real.sqrt t)^2 = t := Real.sq_sqrt (le_of_lt ht0)
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
    have ht0 : (t : ℝ) ≠ 0 := by linarith [ht'.1]
    exact continuousAt_const.div continuousAt_id ht0
  have h_rhs_int : IntegrableOn (fun t : ℝ => C^2 / t) (Set.Ioc 2 x) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).1 h_rhs_interval
  have h_lhs_meas : AEStronglyMeasurable
      (fun t : ℝ => |chebyshevPsi t - chebyshevTheta t|^2 / t^2)
      (volume.restrict (Set.Ioc 2 x)) := by
    have hpsi_meas : Measurable chebyshevPsi := Chebyshev.psi_mono.measurable
    have htheta_meas : Measurable chebyshevTheta := Chebyshev.theta_mono.measurable
    exact (((hpsi_meas.sub htheta_meas).abs.pow_const 2).div
      (measurable_id.pow_const 2)).aestronglyMeasurable
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
        = |∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2| := by
            simp [Real.norm_eq_abs]
    _ = ∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2 := by
          rw [abs_of_nonneg]
          exact intervalIntegral.integral_nonneg (by linarith)
            (fun t ht => div_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ C^2 * Real.log x := h_bound'
    _ = C^2 * ‖Real.log x‖ := by rw [hnorm]

/-- Cauchy-Schwarz bound for the `ψ-θ` correction term. -/
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
            = (chebyshevPsi t - chebyshevTheta t)^2 / t^2 := by
                field_simp [ht2_ne]
        _ ≤ (C * Real.sqrt t)^2 / t^2 := by
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
    have h_lhs_meas : AEStronglyMeasurable
        (fun t : ℝ => ((chebyshevPsi t - chebyshevTheta t) / t)^2)
        (volume.restrict (Set.Ioc 2 x)) := by
      exact (((Chebyshev.psi_mono.measurable.sub Chebyshev.theta_mono.measurable).div
        measurable_id).pow_const 2).aestronglyMeasurable
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
      exact ContinuousAt.pow (ContinuousAt.div continuousAt_const
        (ContinuousAt.pow (Real.continuousAt_log (ne_of_gt ht_pos)) 2) hden_ne) 2
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
          ((chebyshevPsi t - chebyshevTheta t) / t) * (1 / (Real.log t)^2))^2 := by
            rw [sq_abs]
    _ ≤ (∫ t in Set.Ioc 2 x, ((chebyshevPsi t - chebyshevTheta t) / t)^2) *
          (∫ t in Set.Ioc 2 x, (1 / (Real.log t)^2)^2) := hcs'
    _ = (∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t|^2 / t^2) *
          (∫ t in (2 : ℝ)..x, 1 / (Real.log t)^4) := by
            rw [hrewrite1, hrewrite2]

/-- The `ψ-θ` correction is already negligible at the canonical `√x/log x` scale. -/
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
    have hnonneg1 :
        0 ≤ ∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith)
        (fun t ht => div_nonneg (sq_nonneg _) (sq_nonneg _))
    have hnonneg2 :
        0 ≤ ∫ t in (2 : ℝ)..x, 1 / (Real.log t)^4 :=
      intervalIntegral.integral_nonneg (by linarith)
        (fun t ht => one_div_nonneg.mpr (pow_nonneg (Real.log_nonneg (by linarith [ht.1])) _))
    calc
      ‖|psiThetaCorrection x|^2‖ = |psiThetaCorrection x|^2 := Real.norm_of_nonneg (sq_nonneg _)
      _ ≤ (∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2) *
            (∫ t in (2 : ℝ)..x, 1 / (Real.log t)^4) := hsq
      _ = ‖(∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2) *
            (∫ t in (2 : ℝ)..x, 1 / (Real.log t)^4)‖ := by
            rw [Real.norm_of_nonneg (mul_nonneg hnonneg1 hnonneg2)]
      _ = (1 : ℝ) *
            ‖(∫ t in (2 : ℝ)..x, |chebyshevPsi t - chebyshevTheta t| ^ 2 / t ^ 2) *
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

/-- The `ψ` in `RemainderTermAnalysis` is definitionally the canonical `ψ`. -/
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
      · exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_Icc.mpr ⟨Nat.pos_iff_ne_zero.mpr h0, hnle⟩))
    · intro hn
      rcases Finset.mem_insert.mp hn with h0 | hn'
      · subst h0
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩
      · rcases Finset.mem_Icc.mp hn' with ⟨hn1, hnle⟩
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hnle⟩
  rw [hIcc, Finset.sum_insert]
  · simp [ArithmeticFunction.vonMangoldt.map_zero']
  · simp

/-- For `x ≥ 2`, the `ψ`-based remainder is a constant plus the
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
            filter_upwards [Filter.Eventually.of_forall (fun _ : ℝ => True.intro)] with t _
            intro _
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
then the `ψ`-based Step 5 remainder is negligible at scale `√x/log x`. -/
theorem psiPiLiRemainder_isLittleO_of_remainder_term
    (hrem :
      Aristotle.RemainderTermAnalysis.remainder_term =o[atTop]
        (fun x => Real.sqrt x / Real.log x)) :
    psiPiLiRemainder =o[atTop] (fun x => Real.sqrt x / Real.log x) := by
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
  have hnorm_atTop :
      Tendsto (fun x : ℝ => ‖Real.sqrt x / Real.log x‖) atTop atTop := by
    have hscale_pos :
        ∀ᶠ x in atTop, 0 < Real.sqrt x / Real.log x := by
      refine (Filter.eventually_gt_atTop (1 : ℝ)).mono ?_
      intro x hx
      exact div_pos (Real.sqrt_pos.2 (by linarith)) (Real.log_pos hx)
    have hnorm_eq :
        (fun x : ℝ => ‖Real.sqrt x / Real.log x‖)
          =ᶠ[atTop] (fun x => Real.sqrt x / Real.log x) :=
      hscale_pos.mono (fun _ hx => by simp [Real.norm_of_nonneg (le_of_lt hx)])
    exact hscale_atTop.congr' hnorm_eq.symm
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

/-- If the mean-square input required by `RemainderTermAnalysis` is available,
then the `ψ`-based Step 5 remainder is negligible at scale `√x/log x`. -/
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
  exact psiPiLiRemainder_isLittleO_of_remainder_term hrem

/-- Exact reduction of the honest Step 5 theorem to the `ψ` remainder term
plus the already-proved `ψ-θ` correction estimate. -/
theorem thetaPiLiRemainder_isLittleO_of_remainder_term
    (hrem :
      Aristotle.RemainderTermAnalysis.remainder_term =o[atTop]
        (fun x => Real.sqrt x / Real.log x)) :
    thetaPiLiRemainder =o[atTop] (fun x => Real.sqrt x / Real.log x) := by
  have hpsi :
      psiPiLiRemainder =o[atTop] (fun x => Real.sqrt x / Real.log x) :=
    psiPiLiRemainder_isLittleO_of_remainder_term hrem
  exact Aristotle.ThetaToPiLiTransferInfra.thetaPiLiRemainder_isLittleO_of_psi_split
    hpsi
    psiThetaCorrection_isLittleO

/-- Exact reduction of the canonical Step 5 blocker to the mean-square `ψ`
remainder input plus the already-proved `ψ-θ` correction estimate. -/
theorem thetaPiLiRemainder_isLittleO_of_meanSquare
    (h_mean_sq :
      (fun x : ℝ =>
        ∫ t in (2 : ℝ)..x, |Aristotle.RemainderTermAnalysis.psi t - t|^2 / t^2)
        =O[atTop] Real.log) :
    thetaPiLiRemainder =o[atTop] (fun x => Real.sqrt x / Real.log x) := by
  have hrem :
      Aristotle.RemainderTermAnalysis.remainder_term =o[atTop]
        (fun x => Real.sqrt x / Real.log x) :=
    Aristotle.RemainderTermAnalysis.integral_remainder_small_proven h_mean_sq
  exact thetaPiLiRemainder_isLittleO_of_remainder_term hrem

end Aristotle.Standalone.RHPiMeanSquareReduction
