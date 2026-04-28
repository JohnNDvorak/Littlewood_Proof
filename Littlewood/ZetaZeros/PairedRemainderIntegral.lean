/-
# Paired remainder integral helpers (Mathlib-only)

Three Mathlib-only theorems used in the Lane-4 proof of
`pairedRemainderIntegral_le`
(`Littlewood/ZetaZeros/PairedFarZeroCancellationBridge.lean`).

All three are proved and sorry-free.

## Contents

1. `integral_im_inv_horizontal_arctan_diff` — FTC identity:
   `∫_a^b Im(1/(x+iT-ρ)) dx = arctan((a-Re ρ)/(T-Im ρ)) - arctan((b-Re ρ)/(T-Im ρ))`.

2. `abs_arctan_sub_le` — MVT bound: `|arctan u - arctan v| ≤ |u - v|`.

3. `paired_remainder_integral_finset_bound` — finset sum bound:
   For a finite set `S` of far zeros (`|ρ.im - T| > 1`):
   `|∫_a^b Σ_{ρ ∈ S} Im(1/(x+iT-ρ)) dx| ≤ (b-a) · Σ_{ρ ∈ S} 1/|ρ.im - T|`.

Ported verbatim from Aristotle artifact `5baff472`
(`aristotle_t2_slim_aristotle/Littlewood/PairedRemainderIntegral.lean`).

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
Co-authored-by: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
-/

import Mathlib

set_option maxHeartbeats 12800000

open Real Finset Complex

namespace Littlewood.ZetaZeros.PairedRemainderIntegral

/-
Pointwise arctan-difference bound on integrating `Im(1/(x+iT-ρ))`
over `[a, b]`: equals `arctan((a-Re(ρ))/(T-Im(ρ))) - arctan((b-Re(ρ))/(T-Im(ρ)))`.
-/
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
    exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( Continuous.continuousAt <| by continuity ) <| ne_of_gt <| Complex.normSq_pos.mpr <| sub_ne_zero.mpr <| by norm_num [ Complex.ext_iff ] ; contrapose! hρ; linarith

/-
MVT bound on arctan differences: `|arctan u − arctan v| ≤ |u − v|`.
-/
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

/-
**Paired remainder integral bound** (Mathlib-only abstraction).

For a finite set `S` of "far zero" complex numbers (with `|ρ.im - T| > 1`),
the integral of `Im(∑ 1/(x+iT-ρ))` over `[a, b]` (with `b - a ≤ 1`) is
bounded by `(b - a) · ∑ 1/|ρ.im - T|`.
-/
theorem paired_remainder_integral_finset_bound
    (a b T : ℝ) (hT : 2 ≤ T) (hab : a ≤ b) (hba : b - a ≤ 1)
    (S : Finset ℂ)
    (hfar : ∀ ρ ∈ S, 1 < |ρ.im - T|)
    (hbound : ∀ ρ ∈ S, ρ.im ≠ T) :
    |∫ x in a..b, (∑ ρ ∈ S, ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - ρ)).im)| ≤
      (b - a) * S.sum (fun ρ => 1 / |ρ.im - T|) := by
  rw [ intervalIntegral.integral_finset_sum ];
  · refine' le_trans ( Finset.abs_sum_le_sum_abs _ _ ) _;
    rw [ Finset.mul_sum _ _ _ ];
    gcongr;
    rw [ intervalIntegral.integral_of_le hab ];
    refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
    refine' fun x => 1 / |‹ℂ›.im - T|;
    · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
    · norm_num;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx ; norm_num [ Complex.normSq, Complex.div_im ];
      rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> cases abs_cases ( ( ‹ℂ› : ℂ ).im - T ) <;> cases abs_cases ( ( x - ( ‹ℂ› : ℂ ).re ) * ( x - ( ‹ℂ› : ℂ ).re ) + ( T - ( ‹ℂ› : ℂ ).im ) * ( T - ( ‹ℂ› : ℂ ).im ) ) <;> nlinarith [ hfar _ ‹_› ];
    · norm_num [ hab ];
  · exact fun ρ hρ => Continuous.intervalIntegrable ( by exact Complex.continuous_im.comp <| by exact Continuous.div continuous_const ( by continuity ) fun x => by intro H; exact hbound ρ hρ <| by norm_num [ Complex.ext_iff ] at H; linarith ) _ _

end Littlewood.ZetaZeros.PairedRemainderIntegral
