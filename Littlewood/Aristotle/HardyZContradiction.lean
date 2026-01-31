/-
Hardy Z function contradiction infrastructure from Aristotle.

Provides Cauchy-Schwarz bounds, asymptotic contradiction arguments, and
L1/L2/Linf bounds for deriving Hardy's theorem on zeros of Z(t).

Stripped of conflicting definitions (theta, HardyAssumptions) and
namespaced under HardyZContradiction to avoid collisions.

Note: Contains 3 exact? calls (lines marked) that may need resolution.
These are in auxiliary integrability goals that are likely provable.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace HardyZContradiction

open Complex Real MeasureTheory Set Filter Topology

/-
Hardy's Z function parameterized by theta
-/
def Z (theta : Real → Real) (t : Real) : Real :=
  (Complex.exp (Complex.I * theta t) * riemannZeta (1/2 + Complex.I * t)).re

/-
Structure capturing the building blocks as assumptions
-/
structure BuildingBlocks (theta : Real → Real) where
  completedRiemannZeta_critical_line_real : ∀ t : Real, (completedRiemannZeta (1/2 + Complex.I * t)).im = 0
  hardyZ_is_real : ∀ t : Real, (Complex.exp (Complex.I * theta t) * riemannZeta (1/2 + Complex.I * t)).im = 0
  hardyZ_eq_norm_zeta : ∀ t : Real, |(Complex.exp (Complex.I * theta t) * riemannZeta (1/2 + Complex.I * t)).re| = ‖riemannZeta (1/2 + Complex.I * t)‖
  zeta_mean_square_lower_bound : ∃ c > 0, ∃ T₀, ∀ T ≥ T₀, ∫ t in (0)..T, ((Complex.exp (Complex.I * theta t) * riemannZeta (1/2 + Complex.I * t)).re)^2 ≥ c * T * Real.log T
  hardyZ_integral_bound : ∀ ε > 0, ∃ C, ∀ T ≥ 1, |∫ t in (0)..T, (Complex.exp (Complex.I * theta t) * riemannZeta (1/2 + Complex.I * t)).re| ≤ C * T^(1/2 + ε)
  hardyZ_continuous : Continuous (fun t => (Complex.exp (Complex.I * theta t) * riemannZeta (1/2 + Complex.I * t)).re)

/-
Extended building blocks including convexity bound
-/
structure BuildingBlocksExtended (theta : Real → Real) extends BuildingBlocks theta where
  convexity_bound : ∀ ε > 0, ∃ C, ∀ t : Real, ‖riemannZeta (1/2 + Complex.I * t)‖ ≤ C * (1 + |t|)^(1/4 + ε)

/-
Z(t) is continuous
-/
theorem Z_continuous (theta : Real → Real) (h : BuildingBlocks theta) :
    Continuous (Z theta) := by
      convert h.hardyZ_continuous

/-
Cauchy-Schwarz inequality for Z(t) integrals
-/
lemma Z_integral_cauchy_schwarz (theta : Real → Real) (h : BuildingBlocks theta) (T₀ T : Real) (hT : T₀ < T) :
    (∫ t in T₀..T, |Z theta t|)^2 ≤ (T - T₀) * ∫ t in T₀..T, (Z theta t)^2 := by
      have h_cauchy_schwarz : (∫ t in (T₀)..T, (|Z theta t| - (∫ t in (T₀)..T, |Z theta t|) / (T - T₀))^2) ≥ 0 := by
        exact intervalIntegral.integral_nonneg ( by linarith ) fun x hx => sq_nonneg _;
      norm_num [ sub_sq ] at *;
      rw [ intervalIntegral.integral_add, intervalIntegral.integral_sub ] at h_cauchy_schwarz <;> norm_num at *;
      · nlinarith [ mul_div_cancel₀ ( ∫ t in T₀..T, |Z theta t| ) ( sub_ne_zero_of_ne hT.ne' ) ];
      · exact Continuous.intervalIntegrable ( by exact Continuous.pow ( Z_continuous _ h ) _ ) _ _;
      · apply_rules [ Continuous.intervalIntegrable ];
        exact Continuous.mul ( Continuous.mul continuous_const ( continuous_abs.comp ( h.hardyZ_continuous ) ) ) continuous_const;
      · apply_rules [ Continuous.intervalIntegrable ];
        exact Continuous.sub ( Continuous.pow ( by exact h.hardyZ_continuous ) _ ) ( Continuous.mul ( Continuous.mul continuous_const ( continuous_abs.comp h.hardyZ_continuous ) ) continuous_const )

/-
Asymptotic inequality for contradiction
-/
lemma asymptotic_contradiction {c C ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hε_lt : ε < 1/4) :
    ∃ T₀, ∀ T ≥ T₀, (C * T^(1/2 + ε))^2 < c * (T / 2) * T * Real.log T := by
      suffices h_div : ∃ T₀ : ℝ, ∀ T ≥ T₀, C^2 < (c / 2) * T^(1 - 2 * ε) * Real.log T by
        obtain ⟨ T₀, hT₀ ⟩ := h_div; refine ⟨ Max.max T₀ 1, fun T hT => ?_ ⟩ ; specialize hT₀ T ( le_trans ( le_max_left _ _ ) hT ) ; ring_nf at hT₀ ⊢; simp_all +decide [ Real.rpow_add, Real.rpow_sub ] ;
        convert mul_lt_mul_of_pos_right hT₀ ( show 0 < ( T ^ ( 2⁻¹ + ε ) ) ^ 2 by exact sq_pos_of_pos <| Real.rpow_pos_of_pos ( by linarith ) _ ) using 1 ; ring;
        norm_num [ sq, mul_assoc, ← Real.rpow_add ( by linarith : 0 < T ) ] ; ring;
        norm_num;
      have h_tendsto_infty : Filter.Tendsto (fun T : ℝ => T^(1 - 2 * ε) * Real.log T) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.atTop_mul_atTop₀ ( tendsto_rpow_atTop ( by linarith ) ) ( Real.tendsto_log_atTop );
      exact Filter.eventually_atTop.mp ( h_tendsto_infty.eventually_gt_atTop ( C ^ 2 / ( c / 2 ) ) ) |> fun ⟨ T₀, hT₀ ⟩ ↦ ⟨ T₀, fun T hT ↦ by nlinarith [ hT₀ T hT, mul_div_cancel₀ ( C ^ 2 ) ( by positivity : ( c / 2 ) ≠ 0 ) ] ⟩

/-
Integral of Z equals integral of |Z| if Z has constant sign
-/
lemma Z_constant_sign_implies_integral_eq_abs (theta : Real → Real) (h : BuildingBlocks theta) (T₀ T : Real) (hT : T₀ < T)
    (h_sign : (∀ t ∈ Set.Ioo T₀ T, 0 ≤ Z theta t) ∨ (∀ t ∈ Set.Ioo T₀ T, Z theta t ≤ 0)) :
    |∫ t in T₀..T, Z theta t| = ∫ t in T₀..T, |Z theta t| := by
      cases' h_sign with h_pos h_neg;
      · rw [ intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le hT.le ];
        rw [ MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo, abs_of_nonneg ( MeasureTheory.setIntegral_nonneg ( by norm_num ) fun x hx => h_pos x hx ) ];
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => by rw [ abs_of_nonneg ( h_pos x hx ) ] ;
      · rw [ intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le hT.le ];
        rw [ MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo, abs_of_nonpos ];
        · rw [ ← MeasureTheory.integral_neg, MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => abs_of_nonpos ( h_neg x hx ) ];
        · exact MeasureTheory.setIntegral_nonpos measurableSet_Ioo h_neg

/-
Inequality between T log T and T^(3/4 + 2ε)
-/
lemma contradiction_inequality_simplified (c C ε : Real) (hc : 0 < c) (hC : 0 < C) (hε : 0 < ε) (hε_small : ε < 1/8) :
    ∃ T₀, ∀ T ≥ T₀, c * T * Real.log T > C * T^(3/4 + 2 * ε) := by
      suffices h_div : ∃ T₀ : ℝ,
        (∀ T ≥ T₀, c * Real.log T > C * T^(- (1 / 4 - 2 * ε))) by
          obtain ⟨ T₀, hT₀ ⟩ := h_div; use Max.max T₀ 1; intro T hT; specialize hT₀ T ( le_trans ( le_max_left _ _ ) hT ) ; rw [ show ( 3 / 4 + 2 * ε : ℝ ) = - ( 1 / 4 - 2 * ε ) + 1 by ring ] ; rw [ Real.rpow_add' ] <;> norm_num at *;
          · nlinarith;
          · linarith;
          · linarith;
      have h_lim : Filter.Tendsto (fun T : ℝ => C * T^(- (1 / 4 - 2 * ε))) Filter.atTop (nhds 0) := by
        simpa using tendsto_const_nhds.mul ( tendsto_rpow_neg_atTop ( by linarith : 0 < 1 / 4 - 2 * ε ) );
      exact Filter.eventually_atTop.mp ( h_lim.eventually ( gt_mem_nhds <| show 0 < c * Real.log 2 by positivity ) ) |> fun ⟨ T₀, hT₀ ⟩ ↦ ⟨ Max.max T₀ 2, fun T hT ↦ by nlinarith [ hT₀ T ( le_trans ( le_max_left _ _ ) hT ), le_max_right T₀ 2, Real.log_le_log ( by positivity ) ( show T ≥ 2 by linarith [ le_max_right T₀ 2 ] ) ] ⟩

/-
Final contradiction from asymptotic inequality
-/
lemma contradiction_final_step (T₀ : Real) (c C C_Z ε K K' : Real)
    (hc : 0 < c) (hC : 0 < C) (hC_Z : 0 < C_Z) (hε : 0 < ε) (hε_small : ε < 1/8) (hT₀ : 0 < T₀)
    (h_ineq : ∀ T ≥ max T₀ 1, c * T * Real.log T - K' ≤ (C_Z * (1 + T)^(1/4 + ε)) * (C * T^(1/2 + ε) + K)) :
    False := by
      revert hc hC hC_Z hε hε_small hT₀ h_ineq;
      intro hc hC hC_Z hε hε_small hT₀ h_ineq
      obtain ⟨T₀', hT₀'⟩ : ∃ T₀', ∀ T ≥ T₀', c * T * Real.log T > C_Z * (1 + T) ^ (1 / 4 + ε) * (C * T ^ (1 / 2 + ε) + K) + K' := by
        have h_log_growth : Filter.Tendsto (fun T : ℝ => (C_Z * (1 + T) ^ (1 / 4 + ε)) * (C * T ^ (1 / 2 + ε) + K) / (T * Real.log T)) Filter.atTop (nhds 0) := by
          suffices h_factor : Filter.Tendsto (fun T : ℝ => C_Z * (1 + 1 / T)^(1 / 4 + ε) * (C * T^(1 / 2 + ε) + K) / (T^(3 / 4 - ε) * Real.log T)) Filter.atTop (nhds 0) by
            refine h_factor.congr' ?_ ; filter_upwards [ Filter.eventually_gt_atTop 0 ] with T hT ; rw [ show ( 1 + T ) = T * ( 1 + 1 / T ) by nlinarith [ one_div_mul_cancel hT.ne' ] ] ; rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring; norm_num [ hT.ne' ] ; ring;
            field_simp;
            rw [ show ( 3 - 4 * ε ) / 4 = 1 - ( 1 + 4 * ε ) / 4 by ring, Real.rpow_sub hT ] ; norm_num ; ring;
            norm_num [ ne_of_gt ( Real.rpow_pos_of_pos hT _ ) ];
          suffices h_simplify : Filter.Tendsto (fun T : ℝ => C_Z * (1 + 1 / T)^(1 / 4 + ε) * (C + K / T^(1 / 2 + ε)) / (T^(1 / 4 - 2 * ε) * Real.log T)) Filter.atTop (nhds 0) by
            refine h_simplify.congr' ?_;
            field_simp;
            filter_upwards [ Filter.eventually_gt_atTop 0 ] with T hT;
            rw [ show ( 3 - 4 * ε ) / 4 = ( 1 - 4 * ε * 2 ) / 4 + ( 1 + ε * 2 ) / 2 by ring, Real.rpow_add hT ] ; ring;
            norm_num [ ne_of_gt ( Real.rpow_pos_of_pos hT _ ) ];
          have h_log : Filter.Tendsto (fun T : ℝ => T^(1 / 4 - 2 * ε) * Real.log T) Filter.atTop Filter.atTop := by
            have h_log_growth : Filter.Tendsto (fun T : ℝ => T^(1 / 4 - 2 * ε) * Real.log T) Filter.atTop Filter.atTop := by
              have : Filter.Tendsto (fun T : ℝ => Real.log T) Filter.atTop Filter.atTop := by
                exact Real.tendsto_log_atTop
              exact Filter.Tendsto.atTop_mul_atTop₀ ( tendsto_rpow_atTop ( by linarith ) ) this;
            convert h_log_growth using 1;
          simpa using Filter.Tendsto.div_atTop ( Filter.Tendsto.mul ( tendsto_const_nhds.mul ( Filter.Tendsto.rpow ( tendsto_const_nhds.add ( tendsto_inv_atTop_zero ) ) tendsto_const_nhds <| Or.inl <| by linarith ) ) <| Filter.Tendsto.add tendsto_const_nhds <| tendsto_const_nhds.div_atTop <| tendsto_rpow_atTop <| by linarith ) h_log;
        obtain ⟨T₀', hT₀'⟩ : ∃ T₀', ∀ T ≥ T₀', (C_Z * (1 + T) ^ (1 / 4 + ε)) * (C * T ^ (1 / 2 + ε) + K) / (T * Real.log T) < c / 2 := by
          simpa using h_log_growth.eventually ( gt_mem_nhds <| half_pos hc );
        obtain ⟨T₀'', hT₀''⟩ : ∃ T₀'', ∀ T ≥ T₀'', c / 2 * T * Real.log T > K' := by
          have h_log_growth : Filter.Tendsto (fun T : ℝ => c / 2 * T * Real.log T) Filter.atTop Filter.atTop := by
            exact Filter.Tendsto.atTop_mul_atTop₀ ( Filter.tendsto_id.const_mul_atTop ( by positivity ) ) ( Real.tendsto_log_atTop );
          exact Filter.eventually_atTop.mp ( h_log_growth.eventually_gt_atTop K' ) |> fun ⟨ T₀'', hT₀'' ⟩ => ⟨ T₀'', fun T hT => hT₀'' T hT ⟩;
        exact ⟨ Max.max T₀' ( Max.max T₀'' 2 ), fun T hT => by have := hT₀' T ( le_trans ( le_max_left _ _ ) hT ) ; have := hT₀'' T ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hT ) ; rw [ div_lt_iff₀ ] at * <;> nlinarith [ le_max_right T₀' ( Max.max T₀'' 2 ), le_max_right T₀'' 2, Real.log_pos ( show T > 1 by linarith [ le_max_right T₀' ( Max.max T₀'' 2 ), le_max_right T₀'' 2 ] ) ] ⟩;
      exact absurd ( hT₀' ( Max.max ( Max.max T₀ 1 ) T₀' ) ( le_max_right ( Max.max T₀ 1 ) T₀' ) ) ( by linarith [ h_ineq ( Max.max ( Max.max T₀ 1 ) T₀' ) ( le_max_left ( Max.max T₀ 1 ) T₀' ) ] )

/-
Bound on Zeta at Re(s) = 1.1
-/
lemma riemannZeta_bound_1 : ∃ C, ∀ t : Real, ‖riemannZeta (1.1 + Complex.I * t)‖ ≤ C := by
  have h_bound : ∃ C : ℝ, ∀ t : ℝ, ‖riemannZeta (1.1 + Complex.I * t)‖ ≤ C := by
    have h_abs_conv : ∀ s : ℂ, 1 < s.re → ‖riemannZeta s‖ ≤ ∑' n : ℕ, (1 : ℝ) / (n + 1 : ℝ) ^ s.re := by
      intro s hs
      have h_abs_conv : ‖riemannZeta s‖ ≤ ∑' n : ℕ, ‖(1 : ℂ) / (n + 1 : ℂ) ^ s‖ := by
        convert norm_tsum_le_tsum_norm _ ; norm_num;
        · rw [ zeta_eq_tsum_one_div_nat_add_one_cpow ];
          · norm_num [ Complex.cpow_neg ];
          · exact hs;
        · have h_abs_conv : Summable (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ) ^ s.re) := by
            exact_mod_cast summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_rpow.2 hs;
          convert h_abs_conv using 1;
          ext; rw [ ← Complex.norm_cpow_eq_rpow_re_of_pos ( by positivity ) ] ; norm_num;
      convert h_abs_conv using 3;
      have := Complex.norm_cpow_eq_rpow_re_of_pos ( Nat.cast_add_one_pos ‹_› ) s ; aesop
    refine' ⟨ _, fun t => le_trans ( h_abs_conv _ _ ) _ ⟩ <;> norm_num;
    exacts [ ∑' n : ℕ, ( ( n + 1 : ℝ ) ^ ( 11 / 10 : ℝ ) ) ⁻¹, le_rfl ];
  exact h_bound

end HardyZContradiction
