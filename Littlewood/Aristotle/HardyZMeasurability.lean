/-
Integrated from Aristotle output af770898-b0c2-4f99-8c30-d87eb4516b46.
Hardy Z measurability, integrability, and integral decomposition infrastructure.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

KEY RESULTS:
- hardyN: approximate functional equation truncation point
- hardySum: main sum in the approximate functional equation for Z(t)
- hardyN_measurable, hardyTheta_measurable, hardyTerm_measurable, hardySum_measurable
- hardySum_bounded, hardySum_integrable, hardyZ_integrable, hardyRemainder_integrable
- hardySum_integral_eq: interchange of integral and sum for ∫Z
- hardyPhase_continuous: continuity of the Hardy phase factor
-/

import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZCauchySchwarz

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Complex Real Set Filter MeasureTheory
open scoped Topology

namespace HardyEstimatesPartial

/-
The truncation point for the approximate functional equation: N(t) = ⌊√(t/2π)⌋.
-/
noncomputable def hardyN (t : ℝ) : ℕ := Nat.floor (Real.sqrt (t / (2 * Real.pi)))

/-
The main sum in the approximate functional equation for Z(t).
-/
noncomputable def hardySum (t : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.range (hardyN t), ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) * Real.cos (hardyTheta t - t * Real.log (n + 1))

/-
The remainder term: Z(t) - main sum.
-/
noncomputable def hardyRemainder (t : ℝ) : ℝ := hardyZ t - hardySum t

lemma hardyZ_split (t : ℝ) : hardyZ t = hardySum t + hardyRemainder t := by
  simp [hardyRemainder]

/-
Individual term in the main sum.
-/
noncomputable def hardyTerm (n : ℕ) (t : ℝ) : ℝ :=
  ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) * Real.cos (hardyTheta t - t * Real.log (n + 1))

lemma hardyN_measurable : Measurable hardyN := by
  convert Measurable.comp ( show Measurable ( fun t => Nat.floor t ) from _ ) ( show Measurable ( fun t => Real.sqrt ( t / ( 2 * Real.pi ) ) ) from _ ) using 1;
  · exact measurable_id'.nat_floor;
  · exact Measurable.sqrt ( measurable_id'.div_const _ )

lemma hardyTheta_measurable : Measurable hardyTheta := by
  apply_rules [ Measurable.sub, Measurable.mul, measurable_id, measurable_const ];
  have h_arg_measurable : Measurable (fun a : ℝ => Complex.Gamma (1 / 4 + Complex.I * (a / 2))) := by
    refine' Continuous.measurable _;
    refine' continuous_iff_continuousAt.mpr _;
    intro x;
    refine' ( Complex.differentiableAt_Gamma _ _ |> DifferentiableAt.continuousAt ) |> ContinuousAt.comp <| Continuous.continuousAt <| by continuity;
    norm_num [ Complex.ext_iff ];
    exact fun m hm => by linarith;
  exact Measurable.comp ( Complex.measurable_im ) ( Complex.measurable_log.comp h_arg_measurable )

lemma hardyTerm_measurable (n : ℕ) : Measurable (fun t => hardyTerm n t) := by
  apply_rules [ Measurable.mul, Measurable.cos, measurableSet_Iic ];
  · exact measurable_const;
  · exact Measurable.sub ( hardyTheta_measurable ) ( measurable_id.mul_const _ )

lemma hardySum_measurable : Measurable hardySum := by
  refine' measurable_of_tendsto_metrizable ( fun n => _ ) _;
  exact fun n t => ∑ i ∈ Finset.range n, ( if i < Nat.floor ( Real.sqrt ( t / ( 2 * Real.pi ) ) ) then 2 * ( ( i + 1 : ℝ ) ^ ( - ( 1 / 2 : ℝ ) ) ) * Real.cos ( hardyTheta t - t * Real.log ( i + 1 ) ) else 0 );
  · refine' Finset.measurable_sum _ fun i _ => _;
    exact Measurable.ite ( measurableSet_lt measurable_const <| by exact Measurable.nat_floor <| by exact Measurable.sqrt <| by exact measurable_id'.div_const _ ) ( by exact Measurable.mul ( by exact measurable_const ) <| Real.continuous_cos.measurable.comp <| by exact Measurable.sub ( hardyTheta_measurable ) <| by exact measurable_id'.mul <| by exact measurable_const ) measurable_const;
  · refine' tendsto_pi_nhds.mpr _;
    intro x;
    convert Summable.hasSum _ |> HasSum.tendsto_sum_nat using 1;
    rw [ tsum_eq_sum ];
    any_goals exact Finset.range ⌊Real.sqrt ( x / ( 2 * Real.pi ) ) ⌋₊;
    · rw [ Finset.sum_congr rfl fun i hi => if_pos <| Finset.mem_range.mp hi ];
      unfold hardySum;
      unfold hardyN; norm_num [ mul_assoc, Finset.mul_sum _ _ _ ] ;
    · grind;
    · refine' summable_of_ne_finset_zero _;
      exacts [ Finset.range ⌊Real.sqrt ( x / ( 2 * Real.pi ) ) ⌋₊, fun n hn => if_neg <| by simpa using hn ]

lemma hardySum_bounded (T : ℝ) : ∃ M : ℝ, ∀ t ∈ Set.Ioc 1 T, |hardySum t| ≤ M := by
  use 2 * ∑ n ∈ Finset.range (Nat.floor (Real.sqrt (T / (2 * Real.pi)))), ((n + 1 : ℝ) ^ (-(1/2 : ℝ)));
  intros t ht
  have hN_bound : hardyN t ≤ Nat.floor (Real.sqrt (T / (2 * Real.pi))) := by
    exact Nat.floor_mono <| Real.sqrt_le_sqrt <| div_le_div_of_nonneg_right ht.2 <| by positivity;
  rw [ abs_le ];
  constructor <;> rw [ hardySum ];
  · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun i hi => show ( ( i : ℝ ) + 1 ) ^ ( - ( 1 / 2 : ℝ ) ) * Real.cos ( hardyTheta t - t * Real.log ( i + 1 ) ) ≥ - ( ( i : ℝ ) + 1 ) ^ ( - ( 1 / 2 : ℝ ) ) from _ ) zero_le_two );
    · norm_num [ Finset.sum_neg_distrib ];
      exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono hN_bound ) fun _ _ _ => by positivity;
    · nlinarith [ Real.neg_one_le_cos ( hardyTheta t - t * Real.log ( i + 1 ) ), Real.rpow_pos_of_pos ( by linarith : 0 < ( i : ℝ ) + 1 ) ( - ( 1 / 2 ) ) ];
  · exact mul_le_mul_of_nonneg_left ( le_trans ( Finset.sum_le_sum fun _ _ => mul_le_of_le_one_right ( by positivity ) ( Real.cos_le_one _ ) ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono hN_bound ) fun _ _ _ => by positivity ) ) zero_le_two

lemma hardySum_integrable (T : ℝ) : MeasureTheory.IntegrableOn hardySum (Set.Ioc 1 T) MeasureTheory.volume := by
  have h_integrable : MeasureTheory.IntegrableOn (fun t => hardySum t) (Set.Ioc 1 T) := by
    have h_bounded : ∃ M : ℝ, ∀ t ∈ Set.Ioc 1 T, |hardySum t| ≤ M :=
      hardySum_bounded T
    refine' MeasureTheory.Integrable.mono' _ _ _;
    exacts [ fun _ => h_bounded.choose, Continuous.integrableOn_Ioc ( by continuity ), ( hardySum_measurable.aestronglyMeasurable ), Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioc ) fun x hx => h_bounded.choose_spec x hx ];
  convert h_integrable using 1

/-
exp(i · Im(log z)) = z / ‖z‖ for z ≠ 0.
-/
lemma exp_im_log_eq_div_norm (z : ℂ) (hz : z ≠ 0) :
  Complex.exp (Complex.I * (Complex.log z).im) = z / ↑‖z‖ := by
  simp +decide [ Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im ];
  simp +decide [ mul_div_mul_right, hz, Complex.cos_arg, Complex.sin_arg ]

/-
The Hardy phase factor Γ(s)/|Γ(s)| · exp(-it/2 · log π).
-/
noncomputable def hardyPhase (t : ℝ) : ℂ :=
  let s := 1/4 + Complex.I * (t/2)
  (Complex.Gamma s / ↑‖Complex.Gamma s‖) * Complex.exp (-Complex.I * (t/2) * Real.log Real.pi)

/-
Alternative formula for Z(t) using the phase factor.
-/
noncomputable def hardyZ_alt (t : ℝ) : ℝ :=
  let s := 1/4 + Complex.I * (t/2)
  let G := Complex.Gamma s
  let phase := (G / ↑‖G‖) * Complex.exp (-Complex.I * (t/2) * Real.log Real.pi)
  (phase * riemannZeta (1/2 + Complex.I * t)).re

lemma hardyZ_eq_hardyZ_alt (t : ℝ) : hardyZ t = hardyZ_alt t := by
  have h_exp : Complex.exp (Complex.I * hardyTheta t) = (Complex.Gamma (1/4 + Complex.I * (t/2)) / ↑‖Complex.Gamma (1/4 + Complex.I * (t/2))‖) * Complex.exp (-Complex.I * (t/2) * Real.log Real.pi) := by
    have h_exp : Complex.exp (Complex.I * (Complex.log (Complex.Gamma (1 / 4 + Complex.I * (t / 2)))).im) = Complex.Gamma (1 / 4 + Complex.I * (t / 2)) / ↑‖Complex.Gamma (1 / 4 + Complex.I * (t / 2))‖ := by
      convert exp_im_log_eq_div_norm _ _ using 1;
      exact Complex.Gamma_ne_zero_of_re_pos ( by norm_num [ Complex.add_re, Complex.div_re, Complex.mul_re ] );
    convert congr_arg ( fun x : ℂ => x * Complex.exp ( - ( Complex.I * t * Real.log Real.pi / 2 ) ) ) h_exp using 1 <;> ring;
    rw [ ← Complex.exp_add ] ; norm_cast ; norm_num [ mul_assoc, mul_comm, mul_left_comm, hardyTheta ] ; ring;
    norm_num [ Rat.divInt_eq_div ];
  convert congr_arg Complex.re ( congrArg ( fun x => x * riemannZeta ( 1 / 2 + Complex.I * t ) ) h_exp ) using 1

/-
The starting point where term n enters the sum: t₀(n) = 2π(n+1)².
-/
noncomputable def hardyStart (n : ℕ) : ℝ := 2 * Real.pi * (n + 1)^2

lemma hardyN_lt_iff (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
  n < hardyN t ↔ hardyStart n ≤ t := by
  rw [ show hardyN t = Nat.floor ( Real.sqrt ( t / ( 2 * Real.pi ) ) ) by rfl ];
  rw [ Nat.lt_iff_add_one_le, Nat.le_floor_iff ( by positivity ), Real.le_sqrt ] <;> norm_num [ ht, Real.pi_pos.le ];
  · rw [ le_div_iff₀ ( by positivity ), mul_comm ] ; norm_cast ; aesop;
  · positivity;
  · positivity

noncomputable def hardyCos (n : ℕ) (t : ℝ) : ℝ := Real.cos (hardyTheta t - t * Real.log (n + 1))

noncomputable def hardySumInt (T : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.range (hardyN T), ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) * ∫ t in Set.Ioc (hardyStart n) T, hardyCos n t

lemma hardyPhase_continuous : Continuous hardyPhase := by
  refine' Continuous.mul _ _;
  · refine' Continuous.div _ _ _;
    · refine' continuous_iff_continuousAt.mpr _;
      intro x;
      refine' Complex.differentiableAt_Gamma _ _ |> DifferentiableAt.continuousAt |> ContinuousAt.comp <| Continuous.continuousAt <| by continuity;
      norm_num [ Complex.ext_iff ];
      exact fun m hm => by linarith;
    · refine' Complex.continuous_ofReal.comp _;
      refine' Continuous.norm _;
      refine' continuous_iff_continuousAt.mpr fun x => _;
      refine' ( Complex.differentiableAt_Gamma _ _ |> DifferentiableAt.continuousAt ) |> ContinuousAt.comp <| Continuous.continuousAt <| by continuity;
      norm_num [ Complex.ext_iff ];
      exact fun m hm => by linarith;
    · norm_num [ Complex.Gamma_ne_zero ];
      exact fun x => Complex.Gamma_ne_zero_of_re_pos ( by norm_num [ Complex.add_re, Complex.mul_re, Complex.div_re ] );
  · fun_prop

/-
Indicator version of hardyTerm: nonzero only when n < hardyN(t).
-/
noncomputable def hardyTermIndicator (n : ℕ) (t : ℝ) : ℝ :=
  if n < hardyN t then hardyTerm n t else 0

lemma hardySum_eq_sum_indicator (t : ℝ) :
  hardySum t = 2 * ∑' n : ℕ, hardyTermIndicator n t := by
  rw [ tsum_eq_sum ];
  any_goals exact Finset.range ( hardyN t );
  · unfold hardySum hardyTermIndicator; ring;
    exact congrArg₂ _ ( Finset.sum_congr rfl fun x hx => by rw [ if_pos ( Finset.mem_range.mp hx ) ] ; unfold hardyTerm; ring ) rfl;
  · unfold hardyTermIndicator; aesop

lemma hardySum_eq_finite_sum_indicator (T : ℝ) (t : ℝ) (ht : t ∈ Set.Ioc 1 T) :
  hardySum t = 2 * ∑ n ∈ Finset.range (hardyN T), hardyTermIndicator n t := by
  have hN : hardyN t ≤ hardyN T := by
    exact Nat.floor_mono <| Real.sqrt_le_sqrt <| div_le_div_of_nonneg_right ht.2 <| by positivity;
  have h_sum_eq : ∑ n ∈ Finset.range (hardyN T), hardyTermIndicator n t = ∑ n ∈ Finset.range (hardyN t), hardyTermIndicator n t := by
    rw [ ← Finset.sum_subset ( Finset.range_mono hN ) ];
    unfold hardyTermIndicator; aesop;
  rw [ h_sum_eq, ← Finset.sum_congr rfl fun n hn => ?_ ];
  convert hardySum_eq_sum_indicator t using 1;
  rw [ tsum_eq_sum ];
  · unfold hardyTermIndicator; aesop;
  · rfl

lemma hardyTermIndicator_zero_of_ge (n : ℕ) (T : ℝ) (hn : hardyN T ≤ n) :
  ∀ t ∈ Set.Ioc 1 T, hardyTermIndicator n t = 0 := by
  have h_le : ∀ t ∈ Set.Ioc 1 T, hardyN t ≤ hardyN T := by
    exact fun t ht => Nat.floor_mono <| Real.sqrt_le_sqrt <| div_le_div_of_nonneg_right ht.2 <| by positivity;
  exact fun t ht => if_neg <| not_lt_of_ge <| le_trans ( h_le t ht ) hn

lemma hardyTermIndicator_eq_of_lt (n : ℕ) (T : ℝ) (hn : n < hardyN T) :
  ∀ t ∈ Set.Ioc 1 T, hardyTermIndicator n t = if hardyStart n ≤ t then hardyTerm n t else 0 := by
  have h_indicator_eq : ∀ t ∈ Set.Ioc (1 : ℝ) T, n < hardyN t ↔ hardyStart n ≤ t := by
    intros t ht
    have h_indicator_eq : n < hardyN t ↔ hardyStart n ≤ t := by
      convert hardyN_lt_iff n t ( by linarith [ ht.1 ] ) using 1
    exact h_indicator_eq;
  unfold hardyTermIndicator; aesop;

lemma hardyTermIndicator_integral_of_ge (n : ℕ) (T : ℝ) (hT : 1 ≤ T) (hn : hardyN T ≤ n) :
  ∫ t in Set.Ioc 1 T, hardyTermIndicator n t = 0 := by
  have h_zero : ∀ t ∈ Set.Ioc 1 T, hardyTermIndicator n t = 0 :=
    hardyTermIndicator_zero_of_ge n T hn
  exact MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero h_zero

lemma hardyTermIndicator_integral_of_lt (n : ℕ) (T : ℝ) (hT : 1 ≤ T) (hn : n < hardyN T) :
  ∫ t in Set.Ioc 1 T, hardyTermIndicator n t = ∫ t in Set.Ioc (hardyStart n) T, hardyTerm n t := by
  have h_integral_support : ∫ t in Set.Ioc 1 T, hardyTermIndicator n t = ∫ t in Set.Ioc (hardyStart n) T ∩ Set.Ioc 1 T, hardyTerm n t := by
    have h_indicator_eq : ∀ t ∈ Set.Ioc 1 T, hardyTermIndicator n t = if hardyStart n ≤ t then hardyTerm n t else 0 :=
      hardyTermIndicator_eq_of_lt n T hn
    rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
    rw [ ← MeasureTheory.integral_congr_ae ];
    filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.1 ( MeasureTheory.measure_singleton ( hardyStart n ) ) ] with x hxop;
    grind;
  rw [ h_integral_support, Set.inter_eq_left.mpr ];
  refine' Set.Ioc_subset_Ioc _ le_rfl;
  exact one_le_mul_of_one_le_of_one_le ( by linarith [ Real.pi_gt_three ] ) ( by ring_nf; nlinarith [ Real.pi_gt_three ] )

/-
Key theorem: the integral of hardySum equals the sum of individual term integrals.
∫₁ᵀ hardySum(t) dt = 2 Σₙ (n+1)^{-1/2} ∫_{t₀(n)}^T cos(θ(t) - t log(n+1)) dt
-/
lemma hardySum_integral_eq (T : ℝ) (hT : 1 ≤ T) :
  ∫ t in Set.Ioc 1 T, hardySum t = hardySumInt T := by
  have h_sum_eq : ∫ t in Set.Ioc 1 T, hardySum t = ∫ t in Set.Ioc 1 T, 2 * ∑ n ∈ Finset.range (hardyN T), hardyTermIndicator n t := by
    refine' MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => hardySum_eq_finite_sum_indicator T t ht ▸ rfl;
  rw [ h_sum_eq, MeasureTheory.integral_const_mul, MeasureTheory.integral_finset_sum ];
  · rw [ Finset.sum_congr rfl fun i hi => ?_ ];
    rotate_left;
    use fun n => ∫ t in Set.Ioc ( hardyStart n ) T, hardyTerm n t;
    · rw [ ← hardyTermIndicator_integral_of_lt i T hT ];
      exact Finset.mem_range.mp hi;
    · unfold hardyTerm; norm_num [ mul_assoc, MeasureTheory.integral_const_mul ] ;
      rfl;
  · intro n hn;
    refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun t => ( n + 1 : ℝ ) ^ ( - ( 1 / 2 : ℝ ) );
    · norm_num;
    · refine' Measurable.aestronglyMeasurable _;
      refine' Measurable.ite _ _ _;
      · exact measurableSet_lt measurable_const ( hardyN_measurable );
      · exact hardyTerm_measurable n;
      · exact measurable_const;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht;
      unfold hardyTermIndicator;
      unfold hardyTerm;
      split_ifs <;> norm_num;
      · rw [ abs_of_nonneg ( by positivity ) ] ; exact mul_le_of_le_one_right ( by positivity ) ( Real.abs_cos_le_one _ );
      · positivity

/-
Z(t) is integrable on (1, T].
-/
lemma hardyZ_integrable (T : ℝ) : MeasureTheory.IntegrableOn hardyZ (Set.Ioc 1 T) MeasureTheory.volume := by
  have h_cont : Continuous (fun t => hardyZ t) := by
    have h_simplified : ∀ t, hardyZ t = (hardyPhase t * riemannZeta (1 / 2 + Complex.I * t)).re := by
      convert hardyZ_eq_hardyZ_alt using 1;
    simp +decide only [h_simplified];
    refine' Complex.continuous_re.comp _;
    refine' Continuous.mul _ _;
    · exact hardyPhase_continuous;
    · refine' continuous_iff_continuousAt.mpr _;
      intro t;
      refine' ContinuousAt.comp ( show ContinuousAt ( fun s : ℂ => riemannZeta s ) _ from _ ) _;
      · refine' ( differentiableAt_riemannZeta _ ).continuousAt;
        norm_num [ Complex.ext_iff ];
      · exact Continuous.continuousAt ( by continuity );
  exact h_cont.integrableOn_Ioc

/-
The remainder Z(t) - hardySum(t) is integrable on (1, T].
-/
lemma hardyRemainder_integrable (T : ℝ) : MeasureTheory.IntegrableOn hardyRemainder (Set.Ioc 1 T) MeasureTheory.volume := by
  exact MeasureTheory.Integrable.sub ( hardyZ_integrable T ) ( hardySum_integrable T )

/-
The cosine integral for term n.
-/
noncomputable def hardyCosIntegral (n : ℕ) (T : ℝ) : ℝ := ∫ t in Set.Ioc (hardyStart n) T, hardyCos n t

end HardyEstimatesPartial
