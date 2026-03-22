/-
Right-Edge Gamma Main-Term Computation for RvM Formula

This file proves that the right-edge Γᵣ integral contribution to the
Riemann-von Mangoldt formula has the expected Stirling main term, up to
O(log T) error.
-/

import Mathlib
import Littlewood.Aristotle.DigammaAsymptotic
import Littlewood.ZetaZeros.RvMRightEdge

set_option maxHeartbeats 3200000
set_option autoImplicit false

noncomputable section

open Complex Real Filter Asymptotics Topology MeasureTheory Set
open scoped Real

namespace RightEdgeGammaMainTerm

-- Abbreviation for the integrand
private def integrand (y : ℝ) : ℝ :=
  ((-(1 / 2 : ℂ) * Complex.log (↑Real.pi)) +
    (1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2)).re

private def comparison (y : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log Real.pi + (1 / 2) * Real.log (y / 2)

/-! ## Step 1: Integral of the comparison function -/

/-
PROBLEM
The integral of log(y/2) from 1 to T.

PROVIDED SOLUTION
Split log(y/2) = log(y) - log(2) using Real.log_div. Then ∫₁ᵀ log(y/2) dy = ∫₁ᵀ log(y) dy - (T-1)·log(2). Use integral_log for the first part: ∫₁ᵀ log(y) dy = T·log(T) - 1·log(1) - T + 1 = T·log(T) - T + 1. So total = T·log(T) - T + 1 - (T-1)·log(2) = T·log(T) - T·log(2) + log(2) - T + 1 = T·log(T/2) - T + log(2) + 1.
-/
lemma integral_log_half (T : ℝ) (hT : 1 ≤ T) :
    ∫ y in (1 : ℝ)..T, Real.log (y / 2) =
      T * Real.log (T / 2) - T + Real.log 2 + 1 := by
  simpa [ Real.log_mul, show T ≠ 0 by linarith ] using by ring;

/-
PROBLEM
The integral of the comparison function from 1 to T.

PROVIDED SOLUTION
Unfold comparison and split ∫₁ᵀ [-(1/2)·log(π) + (1/2)·log(y/2)] dy into ∫₁ᵀ -(1/2)·log(π) dy + ∫₁ᵀ (1/2)·log(y/2) dy. The first integral is -(T-1)/2·log(π). The second is (1/2)·(T·log(T/2) - T + log(2) + 1) by integral_log_half. Sum: -(T-1)/2·log(π) + (T/2)·log(T/2) - T/2 + (log(2)+1)/2 which matches the RHS.
-/
lemma integral_comparison (T : ℝ) (hT : 1 ≤ T) :
    ∫ y in (1 : ℝ)..T, comparison y =
      (T / 2) * Real.log (T / 2) - T / 2 - ((T - 1) / 2) * Real.log Real.pi +
        (Real.log 2 + 1) / 2 := by
  unfold comparison; norm_num [ mul_div ] ; ring;
  rw [ intervalIntegral.integral_add ] <;> norm_num ; ring;
  · simpa using by ring;
  · exact Continuous.intervalIntegrable ( by continuity ) _ _;
  · apply_rules [ ContinuousOn.intervalIntegrable ] ; exact ContinuousOn.mul ( ContinuousOn.log ( continuousOn_id.mul continuousOn_const ) fun x hx => by linarith [ Set.mem_Icc.mp ( by simpa [ hT ] using hx ) ] ) continuousOn_const;

/-! ## Step 2: Digamma-log bound on the right edge -/

/-
PROBLEM
At s = 1 + iy/2 with y ≥ 2, |Re(ψ(s)) - Re(log(s))| ≤ C/y.

PROVIDED SOLUTION
Use DigammaAsymptotic.digamma_log_bound to get C > 0 and the bound. At s := (1 : ℂ) + (↑y : ℂ) / 2 * I:
- s.re = 1 (compute using add_re, mul_re, ofReal_re, I_re, I_im, ofReal_im)
- s.im = y/2 (similar)
- s.re ≥ 1/4: since s.re = 1
- |s.im| ≥ 1: since s.im = y/2 and y ≥ 2
- Gamma s ≠ 0: since s.re = 1 > 0, use Gamma_ne_zero_of_re_pos

Then ‖deriv Gamma s / Gamma s - log s‖ ≤ C / ‖s‖.
Since logDeriv Gamma s = deriv Gamma s / Gamma s (unfold logDeriv), and |z.re| ≤ ‖z‖ (abs_re_le_norm):
|(logDeriv Gamma s - log s).re| ≤ ‖logDeriv Gamma s - log s‖ ≤ C / ‖s‖.

For ‖s‖: ‖s‖ = sqrt(1 + y²/4) ≥ y/2 (since 1 + y²/4 ≥ y²/4).
So C / ‖s‖ ≤ C / (y/2) = 2C/y.

Use sub_re to rewrite (logDeriv Gamma s).re - (log s).re = (logDeriv Gamma s - log s).re.
-/
lemma digamma_re_error_bound_right_edge :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 2 ≤ y →
      |(logDeriv Complex.Gamma ((1 : ℂ) + (↑y : ℂ) / 2 * I)).re -
        (Complex.log ((1 : ℂ) + (↑y : ℂ) / 2 * I)).re| ≤ C / y := by
  -- Let's choose any $C > 0$ from the excavated DigammaAsymptotic theorem.
  obtain ⟨C, hCpos, hC⟩ : ∃ C > 0, ∀ s : ℂ, s.re ≥ 1/4 → |s.im| ≥ 1 → Complex.Gamma s ≠ 0 → ‖deriv Complex.Gamma s / Complex.Gamma s - Complex.log s‖ ≤ C / ‖s‖ := by
    exact?;
  refine' ⟨ C * 2 + 1, by positivity, fun y hy => _ ⟩ ; specialize hC ( 1 + ( y : ℂ ) / 2 * Complex.I ) _ _ _ <;> norm_num at *;
  · rw [ abs_of_nonneg ] <;> linarith;
  · exact Complex.Gamma_ne_zero_of_re_pos ( by norm_num [ Complex.normSq ] );
  · refine' le_trans ( _ : _ ≤ _ ) ( le_trans hC _ ) <;> norm_num [ Complex.normSq, Complex.norm_def ] at *;
    · exact Real.abs_le_sqrt ( by nlinarith! );
    · rw [ div_le_div_iff₀ ] <;> nlinarith [ sq_nonneg ( y - 2 ), Real.sqrt_nonneg ( 1 + y / 2 * ( y / 2 ) ), Real.mul_self_sqrt ( by positivity : 0 ≤ 1 + y / 2 * ( y / 2 ) ) ]

/-! ## Step 3: Re(log(1+iy/2)) computation -/

/-
PROBLEM
Re[log(1 + iy/2)] = (1/2)·log(1 + y²/4).

PROVIDED SOLUTION
Complex.log_re says (Complex.log z).re = Real.log ‖z‖ = Real.log (Complex.abs z). For z = 1 + (y/2)·I, we have Complex.abs z = Real.sqrt(1 + y²/4). So (Complex.log z).re = Real.log(sqrt(1+y²/4)) = (1/2)·log(1+y²/4). Use Real.log_sqrt for the last step.
-/
lemma re_log_one_plus_half_iy (y : ℝ) (hy : 0 < y) :
    (Complex.log ((1 : ℂ) + (↑y : ℂ) / 2 * I)).re =
      (1 / 2 : ℝ) * Real.log (1 + y ^ 2 / 4) := by
  rw [ Complex.log_re ] ; norm_num [ Complex.normSq, Complex.norm_def ] ; ring;
  rw [ Real.sqrt_eq_rpow, Real.log_rpow ( by positivity ) ] ; ring

/-
PROBLEM
|(1/2)·log(1+y²/4) - log(y/2)| ≤ 2/y for y ≥ 1.

PROVIDED SOLUTION
We have 1 + y^2/4 = (y/2)^2 * (1 + 4/y^2). So (1/2)*log(1+y^2/4) = (1/2)*log((y/2)^2) + (1/2)*log(1+4/y^2) = log(y/2) + (1/2)*log(1+4/y^2). The absolute value of the difference is (1/2)*log(1+4/y^2) which is nonneg. By log(1+x) ≤ x (from Real.add_one_le_exp, or Real.log_le_sub_one_of_pos applied as log(1+t) ≤ t), this is ≤ (1/2)*(4/y^2) = 2/y^2 ≤ 2/y for y ≥ 1.
-/
lemma half_log_vs_log_half (y : ℝ) (hy : 1 ≤ y) :
    |(1 / 2 : ℝ) * Real.log (1 + y ^ 2 / 4) - Real.log (y / 2)| ≤ 2 / y := by
  -- We'll use that $Real.log (1 + y ^ 2 / 4) - 2 * Real.log (y / 2) = Real.log (1 + 4 / y ^ 2)$.
  suffices h_suff' : Real.log (1 + 4 / y ^ 2) / 2 ≤ 2 / y by
    convert h_suff' using 1 ; rw [ show ( 1 + y ^ 2 / 4 ) = ( y / 2 ) ^ 2 * ( 1 + 4 / y ^ 2 ) by nlinarith [ div_mul_cancel₀ 4 ( show y ^ 2 ≠ 0 by positivity ) ] ] ; rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow ] ; ring;
    exact abs_of_nonneg ( mul_nonneg ( Real.log_nonneg ( by nlinarith ) ) ( by norm_num ) );
  exact le_trans ( div_le_div_of_nonneg_right ( Real.log_le_sub_one_of_pos ( by positivity ) ) zero_le_two ) ( by ring_nf; nlinarith [ mul_inv_cancel₀ ( by positivity : y ≠ 0 ) ] )

/-! ## Step 4: The integrand matches comparison up to O(1/y) -/

/-
PROBLEM
The integrand differs from the comparison by at most C/y for y ≥ 2.

PROVIDED SOLUTION
The integrand is Re[-(1/2)·log(π) + (1/2)·ψ((2+iy)/2)]. Note (2+iy)/2 = 1+iy/2 as complex numbers.

The comparison is -(1/2)·log(π) + (1/2)·log(y/2).

First show the real parts: Re[-(1/2)·log(π)] = -(1/2)·Real.log(π) since π > 0 so Complex.log(↑π) is real. And Re[(1/2)·ψ(z)] = (1/2)·Re[ψ(z)].

So integrand - comparison = (1/2)·(Re[ψ(1+iy/2)] - log(y/2)).

By triangle inequality:
|Re[ψ(1+iy/2)] - log(y/2)|
≤ |Re[ψ(1+iy/2)] - Re[log(1+iy/2)]| + |Re[log(1+iy/2)] - log(y/2)|

First term ≤ C₁/y by digamma_re_error_bound_right_edge.
Second term: Re[log(1+iy/2)] = (1/2)·log(1+y²/4) by re_log_one_plus_half_iy (y > 0 since y ≥ 2).
And |(1/2)·log(1+y²/4) - log(y/2)| ≤ 2/y by half_log_vs_log_half (y ≥ 2 ≥ 1).

So |integrand - comparison| ≤ (1/2)·(C₁/y + 2/y) = (C₁+2)/(2y). Take C = (C₁+2)/2 + 1.
-/
lemma integrand_vs_comparison :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 2 ≤ y →
      |integrand y - comparison y| ≤ C / y := by
  have := @digamma_re_error_bound_right_edge;
  obtain ⟨ C, hC₀, hC ⟩ := this;
  refine' ⟨ C + 2 + 1, by positivity, fun y hy => _ ⟩ ; unfold integrand comparison ; norm_num [ Complex.log_re ] at *;
  have h_log_bound : |Real.log ‖1 + y / 2 * Complex.I‖ - Real.log (y / 2)| ≤ 2 / y := by
    convert half_log_vs_log_half y ( by linarith ) using 1 ; norm_num [ Complex.normSq, Complex.norm_def ] ; ring;
    rw [ Real.log_sqrt ( by positivity ) ] ; ring;
  grind

/-! ## Step 5: Bound on the [1,2] and [2,T] contributions -/

/-- The integral of the error on [1,2] is a bounded constant. -/
lemma integral_error_one_two_bounded :
    ∃ M : ℝ, |∫ y in (1 : ℝ)..2, (integrand y - comparison y)| ≤ M := by
  exact ⟨_, le_refl _⟩

/-
PROBLEM
The integral of C/y on [2,T] is at most C·log(T).

PROVIDED SOLUTION
∫₂ᵀ C/y dy = C * ∫₂ᵀ 1/y dy = C * log(T/2) (by integral_one_div_of_pos). Since T ≥ 2 implies T/2 ≤ T, we have log(T/2) ≤ log(T). So result ≤ C * log(T).
-/
lemma integral_inv_le_log (C : ℝ) (hC : 0 ≤ C) (T : ℝ) (hT : 2 ≤ T) :
    ∫ y in (2 : ℝ)..T, C / y ≤ C * Real.log T := by
  norm_num [ div_eq_mul_inv ];
  rw [ integral_inv_of_pos ] <;> try linarith;
  exact mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) ( by linarith ) ) hC

/-
PROBLEM
The integrand error integral on [2,T] is bounded by C·log(T).

PROVIDED SOLUTION
Get C from integrand_vs_comparison. Use ⟨C, fun T hT => ...⟩. The key is: |∫₂ᵀ f| ≤ ∫₂ᵀ |f| ≤ ∫₂ᵀ C/y ≤ C·log(T). For the first inequality, use norm_integral_le_integral_norm or intervalIntegral.norm_integral_le_of_norm_le. For the second, use intervalIntegral.integral_mono_on with the pointwise bound. For the third, use integral_inv_le_log.
-/
lemma integral_error_two_T_bounded :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
      |∫ y in (2 : ℝ)..T, (integrand y - comparison y)| ≤ C * Real.log T := by
  obtain ⟨ C, hC₀, hC ⟩ := integrand_vs_comparison;
  use C;
  intro T hT
  have h_integral_le : |∫ y in (2 : ℝ)..T, integrand y - comparison y| ≤ ∫ y in (2 : ℝ)..T, C / y := by
    rw [ intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT ];
    refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( MeasureTheory.integral_mono_of_nonneg _ _ _ );
    · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
    · exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const continuousAt_id <| by linarith [ hx.1 ] ) |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with y hy using hC y hy.1.le;
  simp_all +decide [ division_def ];
  exact h_integral_le.trans ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) ( by linarith ) ) hC₀.le )

/-! ## Step 6: Full integral bound -/

/-
PROBLEM
The full integral error is O(log T).

PROVIDED SOLUTION
Split ∫₁ᵀ = ∫₁² + ∫₂ᵀ using intervalIntegral.integral_add_adjacent_intervals.
So |∫₁ᵀ (integrand - comparison)| = |∫₁² + ∫₂ᵀ| ≤ |∫₁²| + |∫₂ᵀ|.
From integral_error_one_two_bounded: |∫₁²| ≤ M for some constant M.
From integral_error_two_T_bounded: |∫₂ᵀ| ≤ C₂ · log T for some C₂.
So total ≤ M + C₂ · log T.
For T ≥ 14: log(14) > 0, so M ≤ M/log(14) · log T.
Thus total ≤ (M/log(14) + C₂) · log T. Take C = M/log(14) + C₂.
-/
lemma integral_error_full :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |∫ y in (1 : ℝ)..T, (integrand y - comparison y)| ≤ C * Real.log T := by
  by_contra h_contra;
  -- Split the integral into two parts: from 1 to 2 and from 2 to T.
  have h_split : ∀ T : ℝ, 14 ≤ T → ∫ y in (1 : ℝ)..T, (integrand y - comparison y) = (∫ y in (1 : ℝ)..2, (integrand y - comparison y)) + (∫ y in (2 : ℝ)..T, (integrand y - comparison y)) := by
    intro T hT;
    -- Since the integrand and comparison functions are continuous on [1, T], their difference is also continuous on [1, T].
    have h_cont : ContinuousOn (fun y : ℝ => integrand y - comparison y) (Set.Icc 1 T) := by
      refine' ContinuousOn.sub _ _;
      · refine' ContinuousOn.add _ _ <;> norm_num [ integrand ];
        · exact continuousOn_const;
        · -- The logarithmic derivative of the Gamma function is continuous on the interval [1, T].
          have h_log_deriv_cont : ContinuousOn (fun y : ℝ => logDeriv Complex.Gamma ((2 + y * Complex.I) / 2)) (Set.Icc 1 T) := by
            refine' ContinuousOn.div _ _ _;
            · refine' ContinuousOn.comp ( show ContinuousOn ( deriv Complex.Gamma ) ( { z : ℂ | 0 < z.re } ) from _ ) _ _;
              · have h_cont : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ Complex.Gamma z := by
                  intro z hz; exact Complex.differentiableAt_Gamma _ ( by contrapose! hz; aesop ) ;
                have h_cont : ∀ z : ℂ, 0 < z.re → AnalyticAt ℂ Complex.Gamma z := by
                  exact fun z hz => DifferentiableOn.analyticAt ( fun w hw => DifferentiableAt.differentiableWithinAt ( h_cont w hw ) ) ( IsOpen.mem_nhds ( isOpen_lt continuous_const Complex.continuous_re ) hz )
                generalize_proofs at *; (
                exact fun z hz => ( h_cont z hz |> AnalyticAt.deriv |> AnalyticAt.continuousAt |> ContinuousAt.continuousWithinAt ) |> ContinuousWithinAt.mono <| Set.Subset.refl _;);
              · exact Continuous.continuousOn ( by continuity );
              · norm_num [ MapsTo ];
            · refine' continuousOn_of_forall_continuousAt fun y hy => Complex.differentiableAt_Gamma _ _ |> DifferentiableAt.continuousAt |> ContinuousAt.comp <| Continuous.continuousAt <| by continuity;
              norm_num [ Complex.ext_iff ] ; intros ; linarith [ hy.1, hy.2 ] ;
            · intro x hx; exact Complex.Gamma_ne_zero_of_re_pos ( by norm_num [ Complex.div_re ] ) ;
          exact ContinuousOn.mul continuousOn_const ( Complex.continuous_re.comp_continuousOn h_log_deriv_cont );
      · exact ContinuousOn.add ( continuousOn_const ) ( ContinuousOn.mul continuousOn_const <| ContinuousOn.log ( continuousOn_id.div_const _ ) fun x hx => by linarith [ hx.1 ] );
    rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ ContinuousOn.intervalIntegrable, h_cont ];
    · exact h_cont.mono ( by rw [ Set.uIcc_of_le ( by norm_num ) ] ; exact Set.Icc_subset_Icc_right ( by linarith ) );
    · exact h_cont.mono ( by rw [ uIcc_of_le ( by linarith ) ] ; exact Set.Icc_subset_Icc ( by linarith ) le_rfl );
  -- Use the bounds from the lemmas to derive the contradiction.
  obtain ⟨M, hM⟩ := integral_error_one_two_bounded
  obtain ⟨C, hC⟩ := integral_error_two_T_bounded
  have h_bound : ∀ T : ℝ, 14 ≤ T → |∫ y in (1 : ℝ)..T, (integrand y - comparison y)| ≤ M + C * Real.log T := by
    grind;
  refine' h_contra ⟨ M / Real.log 14 + C, fun T hT => le_trans ( h_bound T hT ) _ ⟩;
  rw [ add_mul, div_mul_eq_mul_div, div_add', le_div_iff₀ ] <;> nlinarith [ Real.log_pos ( show 14 > 1 by norm_num ), Real.log_le_log ( by norm_num ) hT, abs_le.mp hM, abs_le.mp ( hC 2 ( by norm_num ) ) ]

/-
PROBLEM
The full right-edge integral differs from its main term by O(log T).

PROVIDED SOLUTION
From integral_error_full, get C such that |∫₁ᵀ (integrand - comparison)| ≤ C · log T. From integral_comparison, ∫₁ᵀ comparison = main_term. So |∫₁ᵀ integrand - main_term| = |∫₁ᵀ (integrand - comparison) + ∫₁ᵀ comparison - main_term| = |∫₁ᵀ (integrand - comparison)| (since ∫ comparison = main_term). Need to show the integral of integrand minus comparison equals the integral of (integrand - comparison). Use linearity of integral. Then the result follows from integral_error_full.
-/
theorem rightEdge_gamma_integral_main_term :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(∫ y in (1 : ℝ)..T, integrand y) -
        ((T / 2) * Real.log (T / 2) - T / 2 - ((T - 1) / 2) * Real.log Real.pi +
          (Real.log 2 + 1) / 2)| ≤ C * Real.log T := by
  convert integral_error_full using 3;
  congr! 2;
  rw [ intervalIntegral.integral_sub ];
  · rw [ integral_comparison _ ( by linarith ) ];
  · apply_rules [ ContinuousOn.intervalIntegrable ];
    refine' ContinuousOn.add _ _;
    · exact continuousOn_const;
    · -- The logarithmic derivative of the Gamma function is continuous on the domain where the Gamma function is non-zero.
      have h_log_deriv_cont : ContinuousOn (fun s : ℂ => logDeriv Complex.Gamma s) {s : ℂ | 0 < s.re} := by
        refine' ContinuousOn.div _ _ _;
        · have h_cont : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ (deriv Complex.Gamma) s := by
            intro s hs
            have h_diff : DifferentiableOn ℂ (deriv Complex.Gamma) {s : ℂ | 0 < s.re} := by
              have h_diff : DifferentiableOn ℂ Complex.Gamma {s : ℂ | 0 < s.re} := by
                intro s hs; exact Complex.differentiableAt_Gamma _ ( by contrapose! hs; aesop ) |> DifferentiableAt.differentiableWithinAt;
              apply_rules [ DifferentiableOn.deriv, h_diff ];
              exact isOpen_lt continuous_const Complex.continuous_re
            exact h_diff.differentiableAt (IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re) hs);
          exact fun s hs => DifferentiableAt.continuousAt ( h_cont s hs ) |> ContinuousAt.continuousWithinAt;
        · refine' continuousOn_of_forall_continuousAt _;
          intro s hs; exact Complex.differentiableAt_Gamma _ ( by contrapose! hs; aesop ) |> DifferentiableAt.continuousAt;
        · exact fun s hs => Complex.Gamma_ne_zero_of_re_pos hs;
      field_simp;
      exact Complex.continuous_re.comp_continuousOn ( ContinuousOn.div_const ( h_log_deriv_cont.comp ( Continuous.continuousOn ( by continuity ) ) fun x hx => by norm_num [ Complex.div_re ] ) _ );
  · apply_rules [ ContinuousOn.intervalIntegrable ];
    exact ContinuousOn.add ( continuousOn_const.mul continuousOn_const ) ( continuousOn_const.mul ( ContinuousOn.log ( continuousOn_id.div_const _ ) fun x hx => by cases Set.mem_uIcc.mp hx <;> linarith ) )

end RightEdgeGammaMainTerm

/-- The right-edge Γᵣ integral has the Stirling main term up to O(log T).
    This exports the result without using the private `integrand` abbreviation. -/
theorem rightEdge_gamma_integral_main_term_explicit :
    ∃ C : ℝ, ∀ T : ℝ, 14 ≤ T →
      |(∫ y in (1 : ℝ)..T,
          ((-(1 / 2 : ℂ) * Complex.log (↑Real.pi)) +
            (1 / 2 : ℂ) * logDeriv Complex.Gamma (((2 : ℂ) + (↑y : ℂ) * I) / 2)).re) -
        ((T / 2) * Real.log (T / 2) - T / 2 - ((T - 1) / 2) * Real.log Real.pi +
          (Real.log 2 + 1) / 2)| ≤ C * Real.log T :=
  RightEdgeGammaMainTerm.rightEdge_gamma_integral_main_term