/-
# Sharp signed paired-shell integral bound (Lane 4)

Proved by Aristotle run `d2e86ffc-1b1c-4272-8cc2-039253350f9a` (2026-04-18)
on a slim Mathlib-only project, augmented by the three arctan/finset
helpers originally from Aristotle run `5baff472`.

For stand-alone compilability without lake rebuild of sibling files, the
three lower-level arctan/finset helpers are inlined here.

## Statement

For a conjugate-closed finset `S ⊆ ℂ` of "far zeros"
(`|ρ.im - T| > 1`, `ρ.im ≠ T`, `ρ ≠ 0`), the integral of the signed
Hadamard paired integrand `∑_{ρ ∈ S} Im(1/(x+iT-ρ) + 1/ρ)` over
`[1/2 + 1/log T, 1]` is bounded by `S.card · log T + S.card`.

This is **one `log T` tighter** than the termwise absolute-value route.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
Co-authored-by: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
-/

import Mathlib

set_option maxHeartbeats 12800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Complex Real Finset MeasureTheory

namespace Littlewood.ZetaZeros.PairedRemainderLogSq

/-! ### Inlined arctan / finset helpers (Aristotle 5baff472) -/

/-- **FTC identity**: integrating `Im(1/(x+iT-ρ))` over `[a, b]` gives an
arctan difference. -/
theorem integral_im_inv_horizontal_arctan_diff
    (a b T : ℝ) (ρ : ℂ) (hρ : T ≠ ρ.im) :
    ∫ x in a..b, ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - ρ)).im =
      Real.arctan ((a - ρ.re) / (T - ρ.im)) -
        Real.arctan ((b - ρ.re) / (T - ρ.im)) := by
  rw [ intervalIntegral.integral_deriv_eq_sub' ];
  case f => exact fun x => -Real.arctan ( ( x - ρ.re ) / ( T - ρ.im ) );
  · ring;
  · norm_num [ Complex.normSq, Complex.div_im ];
    grind;
  · norm_num;
  · simp +zetaDelta at *;
    exact continuousOn_of_forall_continuousAt fun x _hx => ContinuousAt.div continuousAt_const ( Continuous.continuousAt <| by continuity ) <| ne_of_gt <| Complex.normSq_pos.mpr <| sub_ne_zero.mpr <| by norm_num [ Complex.ext_iff ] ; contrapose! hρ; linarith

/-- **MVT bound**: `|arctan u - arctan v| ≤ |u - v|`. -/
theorem abs_arctan_sub_le (u v : ℝ) :
    |Real.arctan u - Real.arctan v| ≤ |u - v| := by
  by_cases huv : u = v;
  · aesop;
  · cases' lt_or_gt_of_ne huv with huv huv;
    · obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo u v, deriv Real.arctan c = (Real.arctan v - Real.arctan u) / (v - u) := by
        apply_rules [ exists_deriv_eq_slope ];
        · exact Real.continuous_arctan.continuousOn;
        · exact DifferentiableOn.arctan differentiableOn_id;
      norm_num at *;
      rw [ inv_eq_one_div, div_eq_div_iff ] at hc <;> cases abs_cases ( u - v ) <;> cases abs_cases ( Real.arctan u - Real.arctan v ) <;> nlinarith;
    · have h_mean_value : ∃ c ∈ Set.Ioo v u, deriv Real.arctan c = (Real.arctan u - Real.arctan v) / (u - v) := by
        apply_rules [ exists_deriv_eq_slope ];
        · exact Real.continuous_arctan.continuousOn;
        · exact DifferentiableOn.arctan differentiableOn_id;
      obtain ⟨ c, hc ⟩ := h_mean_value; rw [ eq_div_iff ] at hc <;> norm_num at * <;> cases abs_cases ( u-v ) <;> cases abs_cases ( Real.arctan u-Real.arctan v ) <;> nlinarith [ inv_mul_cancel₀ ( show 1+c ^ 2 ≠ 0 by positivity ), show ( 1+c ^ 2 ) ⁻¹ ≤ 1 by exact inv_le_one_of_one_le₀ <| by nlinarith ] ;

/-! ### Conjugate cancellation + distance helpers (Aristotle d2e86ffc) -/

/-- For nonzero `ρ`, `Im(1/ρ) + Im(1/conj ρ) = 0`. -/
lemma im_inv_add_im_inv_conj (ρ : ℂ) (_hρ : ρ ≠ 0) :
    ((1 : ℂ) / ρ).im + ((1 : ℂ) / (starRingEnd ℂ) ρ).im = 0 := by
  simp +zetaDelta at *;
  ring

/-- Over a conjugate-closed finset of nonzero complex numbers, the sum of
`Im(1/ρ)` vanishes. -/
lemma sum_im_inv_conj_closed_eq_zero
    (S : Finset ℂ)
    (hne_zero : ∀ ρ ∈ S, ρ ≠ 0)
    (hconj_closed : ∀ ρ ∈ S, (starRingEnd ℂ) ρ ∈ S) :
    ∑ ρ ∈ S, ((1 : ℂ) / ρ).im = 0 := by
  by_contra h_nonzero_sum;
  have h_involution : ∑ ρ ∈ S, ((1 : ℂ) / ρ).im = ∑ ρ ∈ S, -( (1 : ℂ) / ρ ).im := by
    apply Finset.sum_bij (fun ρ _ => starRingEnd ℂ ρ);
    · assumption;
    · exact fun x hx y hy hxy => star_inj.mp hxy;
    · exact fun ρ hρ => ⟨ starRingEnd ℂ ρ, hconj_closed ρ hρ, by simp +decide ⟩;
    · simp +decide [ Complex.normSq, Complex.div_im ];
      exact fun _ _ => by ring;
  exact h_nonzero_sum ( by rw [ Finset.sum_neg_distrib ] at h_involution; linarith )

/-- The arctan difference arising from integrating `Im(1/(x+iT-ρ))` over
`[a, b]` is bounded by `|b-a|/|T - Im ρ|` when `T ≠ Im ρ`. -/
lemma abs_arctan_diff_le_width_div_dist (a b T : ℝ) (ρ : ℂ) (_hρ : T ≠ ρ.im) :
    |Real.arctan ((a - ρ.re) / (T - ρ.im)) -
      Real.arctan ((b - ρ.re) / (T - ρ.im))| ≤
      |b - a| / |T - ρ.im| := by
  convert abs_arctan_sub_le ( ( a - ρ.re ) / ( T - ρ.im ) ) ( ( b - ρ.re ) / ( T - ρ.im ) ) using 1 ; ring;
  rw [ ← div_eq_mul_inv, ← abs_div ] ; ring;
  rw [ neg_add_eq_sub, abs_sub_comm ]

/-! ### Main theorem -/

/-- **Sharp signed paired-shell integral bound.**

For a conjugate-closed finset `S ⊆ ℂ` of far zeros
(`|ρ.im - T| > 1`, `ρ.im ≠ T`, `ρ ≠ 0`), the integral of the signed
Hadamard paired integrand `∑_{ρ ∈ S} Im(1/(x+iT-ρ) + 1/ρ)` over
`[a, 1]` with `a = 1/2 + 1/log T`, `T ≥ 14`, is bounded by
`S.card · log T + S.card`.

This saves one `log T` over the termwise route. -/
theorem paired_remainder_signed_shell_sum_log_bound
    (T : ℝ) (hT : 14 ≤ T)
    (S : Finset ℂ)
    (hfar : ∀ ρ ∈ S, 1 < |ρ.im - T|)
    (hne : ∀ ρ ∈ S, ρ.im ≠ T)
    (hne_zero : ∀ ρ ∈ S, ρ ≠ 0)
    (hconj_closed : ∀ ρ ∈ S, (starRingEnd ℂ) ρ ∈ S) :
    let a : ℝ := (1 / 2 : ℝ) + 1 / Real.log T
    |∫ x in a..1, (∑ ρ ∈ S, ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - ρ)
                               + (1 : ℂ) / ρ).im)| ≤
      (S.card : ℝ) * Real.log T + S.card := by
  have h_integral_bound : |∫ x in (1 / 2 + 1 / Real.log T)..1, ∑ ρ ∈ S, ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - ρ)).im| ≤ S.card := by
    rw [ intervalIntegral.integral_finset_sum ];
    · refine' le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( le_trans ( Finset.sum_le_sum fun ρ hρ => _ ) _ );
      use fun ρ => |1 - ( 1 / 2 + 1 / Real.log T )| / |T - ρ.im|;
      · convert abs_arctan_diff_le_width_div_dist ( 1 / 2 + 1 / Real.log T ) 1 T ρ ( by cases abs_cases ( ρ.im - T ) <;> cases lt_or_gt_of_ne ( hne ρ hρ ) <;> linarith ) using 1;
        convert congr_arg _ ( integral_im_inv_horizontal_arctan_diff ( 1 / 2 + 1 / Real.log T ) 1 T ρ ( by cases abs_cases ( ρ.im - T ) <;> cases lt_or_gt_of_ne ( hne ρ hρ ) <;> linarith ) ) using 1;
      · refine' le_trans ( Finset.sum_le_sum fun x hx => div_le_self ( abs_nonneg _ ) _ ) _;
        · simpa only [ abs_sub_comm ] using le_of_lt ( hfar x hx );
        · norm_num;
          exact mul_le_of_le_one_right ( Nat.cast_nonneg _ ) ( abs_le.mpr ⟨ by linarith [ inv_le_one_of_one_le₀ ( show 1 ≤ Real.log T by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) ) ], by linarith [ inv_pos.mpr ( show 0 < Real.log T by exact Real.log_pos ( by linarith ) ) ] ⟩ );
    · intro ρ hρ; apply_rules [ ContinuousOn.intervalIntegrable ];
      norm_num [ Complex.normSq, Complex.div_im ];
      exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( Continuous.continuousAt ( by continuity ) ) ( by nlinarith [ abs_mul_abs_self ( ρ.im - T ), hfar ρ hρ ] );
  nontriviality;
  refine' le_trans _ ( le_add_of_nonneg_left <| mul_nonneg ( Nat.cast_nonneg _ ) <| Real.log_nonneg <| by linarith );
  convert h_integral_bound using 1;
  norm_num [ Finset.sum_add_distrib, Complex.normSq, Complex.div_im ];
  have := sum_im_inv_conj_closed_eq_zero S hne_zero hconj_closed; simp_all +decide [ div_eq_mul_inv, Finset.mul_sum _ _ _ ] ;
  simp_all +decide [ Complex.normSq, sq ]

end Littlewood.ZetaZeros.PairedRemainderLogSq
