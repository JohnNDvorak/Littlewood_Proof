/-
# Paired remainder integral bound (Mathlib-only abstraction)

Abstracts the core mathematical content of `pairedRemainderIntegral_le`
(Littlewood/ZetaZeros/PairedFarZeroCancellationBridge.lean:232).

## Mathematical content

For a finite set of "far zeros" `ρ ∈ S` with `|ρ.im − T| > 1`, the
integral of `Im(m_ρ / (x + iT − ρ))` over `[a, b]` is bounded by an
arctan difference (MVT applied to arctan):

    |∫_a^b Im(m_ρ/(x+iT-ρ)) dx| ≤ m_ρ · |b - a| / |ρ.im - T|

Summing over the finite set and applying the corrected shell sum
(`near_height_shell_sum_bound` in `ShellSumBound.lean`, already proved),
the total integral is `O(|b-a| · log²T)`.

For the Littlewood application, `|b-a| ≤ 1/log T` and width × log²T = log T.

## Mathlib ingredients available

- `Real.arctan`, `Real.arctan_lt_pi_div_two`, `Real.neg_pi_div_two_lt_arctan`
- `intervalIntegral`, `Complex.arctan_div_eq_arctan_inv` (or similar)
- `Finset.sum_le_sum`, `abs_sum_le_sum_abs`
- The proved `near_height_shell_sum_bound` in this slim project
-/

import Mathlib
import Littlewood.Aristotle.Standalone.NearHeightShellSumCorrected

set_option maxHeartbeats 12800000

open Real Finset Complex

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
  · norm_num [ Complex.normSq, Complex.div_im ];
    exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( Continuous.continuousAt ( by continuity ) ) ( by nlinarith [ mul_self_pos.2 ( sub_ne_zero.2 hρ ) ] )

/-
MVT bound on arctan differences: `|arctan u − arctan v| ≤ |u − v|`.
-/
theorem abs_arctan_sub_le (u v : ℝ) :
    |Real.arctan u - Real.arctan v| ≤ |u - v| := by
  -- Apply the mean value theorem to the interval $[u, v]$.
  by_cases huv : u = v;
  · aesop;
  · cases' lt_or_gt_of_ne huv with huv huv;
    · have := exists_deriv_eq_slope ( Real.arctan ) huv;
      exact this ( Continuous.continuousOn <| Real.continuous_arctan ) ( Differentiable.differentiableOn <| Real.differentiable_arctan ) |> fun ⟨ c, hc₁, hc₂ ⟩ => by rw [ eq_div_iff ] at hc₂ <;> norm_num at * <;> cases abs_cases ( u - v ) <;> cases abs_cases ( Real.arctan u - Real.arctan v ) <;> nlinarith [ inv_mul_cancel₀ ( by nlinarith : ( 1 + c ^ 2 ) ≠ 0 ) ] ;
    · obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo v u, deriv Real.arctan c = (Real.arctan u - Real.arctan v) / (u - v) := by
        have := exists_deriv_eq_slope ( Real.arctan ) huv;
        exact this ( Continuous.continuousOn ( Real.continuous_arctan ) ) ( Differentiable.differentiableOn ( Real.differentiable_arctan ) );
      rw [ eq_div_iff ] at hc <;> norm_num at * <;> cases abs_cases ( u - v ) <;> cases abs_cases ( Real.arctan u - Real.arctan v ) <;> nlinarith [ mul_inv_cancel₀ ( by nlinarith : ( 1 + c ^ 2 ) ≠ 0 ) ]

/-
**Paired remainder integral bound** (Mathlib-only abstraction).

For a finite set `S` of "far zero" complex numbers (with `|ρ.im - T| > 1`),
the integral of `Im(∑ 1/(x+iT-ρ))` over `[a, b]` (with `b - a ≤ 1`) is
bounded by `(b - a) · ∑ 1/|ρ.im - T|`.

Combined with a shell-sum bound `∑ 1/|ρ.im - T| ≤ C·log²T`, the integral
is `O((b - a) · log²T)`. For `b - a = O(1/logT)`, this gives `O(logT)`.
-/
theorem paired_remainder_integral_finset_bound
    (a b T : ℝ) (hT : 2 ≤ T) (hab : a ≤ b) (hba : b - a ≤ 1)
    (S : Finset ℂ)
    (hfar : ∀ ρ ∈ S, 1 < |ρ.im - T|)
    (hbound : ∀ ρ ∈ S, ρ.im ≠ T) :
    |∫ x in a..b, (∑ ρ ∈ S, ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - ρ)).im)| ≤
      (b - a) * S.sum (fun ρ => 1 / |ρ.im - T|) := by
  -- Use the provided solution to rewrite the integral.
  have h_integral : ∫ x in a..b, ∑ ρ ∈ S, Complex.im (1 / ((x + T * Complex.I) - ρ)) = ∑ ρ ∈ S, (Real.arctan ((a - ρ.re) / (T - ρ.im)) - Real.arctan ((b - ρ.re) / (T - ρ.im))) := by
    rw [ intervalIntegral.integral_finset_sum ];
    · exact Finset.sum_congr rfl fun x hx => by rw [ integral_im_inv_horizontal_arctan_diff a b T x ( by cases abs_cases ( x.im - T ) <;> cases lt_or_gt_of_ne ( hbound x hx ) <;> linarith [ hfar x hx ] ) ] ;
    · norm_num [ Complex.normSq, Complex.div_im ];
      exact fun ρ hρ => Continuous.intervalIntegrable ( continuous_const.div ( by continuity ) fun x => by cases abs_cases ( ρ.im - T ) <;> nlinarith [ hfar ρ hρ ] ) _ _;
  -- Apply the bound $|\arctan u - \arctan v| \leq |u - v|$ to each term in the sum.
  have h_arctan_bound : ∀ ρ ∈ S, |Real.arctan ((a - ρ.re) / (T - ρ.im)) - Real.arctan ((b - ρ.re) / (T - ρ.im))| ≤ |(a - b) / (T - ρ.im)| := by
    intro ρ hρ; convert abs_arctan_sub_le _ _ using 1 ; ring;
  convert Finset.abs_sum_le_sum_abs _ _ |> le_trans <| Finset.sum_le_sum h_arctan_bound using 1;
  · rw [ h_integral ];
  · rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ abs_div ] ; norm_num [ abs_sub_comm, abs_of_nonpos ( sub_nonpos_of_le hab ) ] ; ring;

/-
**Multiplicity-weighted paired remainder integral bound.**

Identical statement to `paired_remainder_integral_finset_bound` but with each
zero ρ ∈ S weighted by a non-negative real coefficient `m ρ` (typically a
multiplicity).  Reduces to the unweighted version by linearity of integration
plus pointwise scaling of the per-zero arctan bound.

For the Littlewood application, `m ρ = (zeta multiplicity at ρ : ℝ)` and the
sum on the right is the multiplicity-counted shell sum, which admits the same
`O(log²T)` bound as the unweighted shell sum because the total
multiplicity in any shell of width 1 is `O(log T)` (Riemann–von Mangoldt).
-/
theorem paired_remainder_integral_finset_bound_weighted
    (a b T : ℝ) (hT : 2 ≤ T) (hab : a ≤ b) (hba : b - a ≤ 1)
    (S : Finset ℂ) (m : ℂ → ℝ)
    (hm : ∀ ρ ∈ S, 0 ≤ m ρ)
    (hfar : ∀ ρ ∈ S, 1 < |ρ.im - T|)
    (hbound : ∀ ρ ∈ S, ρ.im ≠ T) :
    |∫ x in a..b,
        (∑ ρ ∈ S,
          m ρ * ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - ρ)).im)| ≤
      (b - a) * S.sum (fun ρ => m ρ / |ρ.im - T|) := by
  -- Per-zero pointwise arctan equality (same proof obligation as unweighted)
  have h_integral :
      ∫ x in a..b,
        (∑ ρ ∈ S, m ρ * ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - ρ)).im) =
      ∑ ρ ∈ S,
        m ρ *
          (Real.arctan ((a - ρ.re) / (T - ρ.im)) -
            Real.arctan ((b - ρ.re) / (T - ρ.im))) := by
    rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl fun ρ hρ => ?_
      have hT_ne : T ≠ ρ.im := fun h =>
        hbound ρ hρ h.symm
      rw [intervalIntegral.integral_const_mul,
        integral_im_inv_horizontal_arctan_diff a b T ρ hT_ne]
    · intro ρ hρ
      have hT_ne : T ≠ ρ.im := fun h => hbound ρ hρ h.symm
      have hcontinuous : ContinuousOn
          (fun x : ℝ =>
            ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - ρ)).im)
          (Set.uIcc a b) := by
        refine continuousOn_of_forall_continuousAt fun x _ => ?_
        refine (Complex.continuous_im.continuousAt).comp ?_
        refine ContinuousAt.div continuousAt_const ?_ ?_
        · exact ((Complex.continuous_ofReal.continuousAt).add continuousAt_const).sub
            continuousAt_const
        · intro hzero
          have him : T = ρ.im := by
            have := congrArg Complex.im (sub_eq_zero.mp hzero)
            simpa using this
          exact hT_ne him
      exact (continuous_const.intervalIntegrable a b).mul_continuousOn hcontinuous
  -- Per-zero arctan bound, scaled by m ρ ≥ 0
  have h_term_bound : ∀ ρ ∈ S,
      |m ρ *
          (Real.arctan ((a - ρ.re) / (T - ρ.im)) -
            Real.arctan ((b - ρ.re) / (T - ρ.im)))| ≤
        (b - a) * (m ρ / |ρ.im - T|) := by
    intro ρ hρ
    have hmρ : 0 ≤ m ρ := hm ρ hρ
    have hT_ne : T ≠ ρ.im := fun h => hbound ρ hρ h.symm
    have habs := abs_arctan_sub_le ((a - ρ.re) / (T - ρ.im))
                  ((b - ρ.re) / (T - ρ.im))
    have hba_nn : 0 ≤ b - a := sub_nonneg.mpr hab
    have hT_im_ne : (T - ρ.im) ≠ 0 := sub_ne_zero.mpr hT_ne
    have habs_T : |T - ρ.im| = |ρ.im - T| := abs_sub_comm T ρ.im
    have hdiv :
        |((a - ρ.re) / (T - ρ.im)) - ((b - ρ.re) / (T - ρ.im))| =
        (b - a) / |ρ.im - T| := by
      have hsub : ((a - ρ.re) / (T - ρ.im)) - ((b - ρ.re) / (T - ρ.im))
          = (a - b) / (T - ρ.im) := by
        rw [div_sub_div _ _ hT_im_ne hT_im_ne]
        rw [div_eq_div_iff (mul_ne_zero hT_im_ne hT_im_ne) hT_im_ne]
        ring
      rw [hsub, abs_div, ← habs_T]
      rw [show |a - b| = b - a from by
        rw [abs_sub_comm, abs_of_nonneg hba_nn]]
    calc |m ρ *
            (Real.arctan ((a - ρ.re) / (T - ρ.im)) -
              Real.arctan ((b - ρ.re) / (T - ρ.im)))|
        = m ρ * |Real.arctan ((a - ρ.re) / (T - ρ.im)) -
            Real.arctan ((b - ρ.re) / (T - ρ.im))| := by
          rw [abs_mul, abs_of_nonneg hmρ]
      _ ≤ m ρ * |((a - ρ.re) / (T - ρ.im)) - ((b - ρ.re) / (T - ρ.im))| :=
          mul_le_mul_of_nonneg_left habs hmρ
      _ = m ρ * ((b - a) / |ρ.im - T|) := by rw [hdiv]
      _ = (b - a) * (m ρ / |ρ.im - T|) := by ring
  calc |∫ x in a..b,
            (∑ ρ ∈ S,
              m ρ * ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - ρ)).im)|
      = |∑ ρ ∈ S,
            m ρ *
              (Real.arctan ((a - ρ.re) / (T - ρ.im)) -
                Real.arctan ((b - ρ.re) / (T - ρ.im)))| := by rw [h_integral]
    _ ≤ ∑ ρ ∈ S,
            |m ρ *
              (Real.arctan ((a - ρ.re) / (T - ρ.im)) -
                Real.arctan ((b - ρ.re) / (T - ρ.im)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ρ ∈ S, (b - a) * (m ρ / |ρ.im - T|) :=
        Finset.sum_le_sum h_term_bound
    _ = (b - a) * S.sum (fun ρ => m ρ / |ρ.im - T|) := by
        rw [← Finset.mul_sum]

/-
**Index-set form of the multiplicity-weighted integral bound.**

Same content as `paired_remainder_integral_finset_bound_weighted`, but the
finset of zeros is replaced by a finset of indices `S : Finset ℕ` together
with a zero-enumeration `ρ : ℕ → ℂ` and a weight `m : ℕ → ℝ`.  This is the
natural interface for combining with the shell-sum bounds in
`NearHeightShellSumCorrected`, which are also indexed by `ℕ`.
-/
theorem paired_remainder_integral_finset_bound_weighted_indexed
    (a b T : ℝ) (hT : 2 ≤ T) (hab : a ≤ b) (hba : b - a ≤ 1)
    (ρ : ℕ → ℂ) (m : ℕ → ℝ) (S : Finset ℕ)
    (hm : ∀ n ∈ S, 0 ≤ m n)
    (hfar : ∀ n ∈ S, 1 < |(ρ n).im - T|)
    (hbound : ∀ n ∈ S, (ρ n).im ≠ T) :
    |∫ x in a..b,
        (∑ n ∈ S,
          m n * ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - ρ n)).im)| ≤
      (b - a) * S.sum (fun n => m n / |(ρ n).im - T|) := by
  -- Reduce to the unindexed weighted bound by re-indexing along the
  -- composition `m ∘ (· : ρ).fun`.  We avoid issues with non-injective ρ
  -- by working with the indexed sum directly.
  have h_integral :
      ∫ x in a..b,
        (∑ n ∈ S, m n * ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - ρ n)).im) =
      ∑ n ∈ S,
        m n *
          (Real.arctan ((a - (ρ n).re) / (T - (ρ n).im)) -
            Real.arctan ((b - (ρ n).re) / (T - (ρ n).im))) := by
    rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have hT_ne : T ≠ (ρ n).im := fun h => hbound n hn h.symm
      rw [intervalIntegral.integral_const_mul,
        integral_im_inv_horizontal_arctan_diff a b T (ρ n) hT_ne]
    · intro n hn
      have hT_ne : T ≠ (ρ n).im := fun h => hbound n hn h.symm
      have hcontinuous : ContinuousOn
          (fun x : ℝ =>
            ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - ρ n)).im)
          (Set.uIcc a b) := by
        refine continuousOn_of_forall_continuousAt fun x _ => ?_
        refine (Complex.continuous_im.continuousAt).comp ?_
        refine ContinuousAt.div continuousAt_const ?_ ?_
        · exact ((Complex.continuous_ofReal.continuousAt).add continuousAt_const).sub
            continuousAt_const
        · intro hzero
          have him : T = (ρ n).im := by
            have := congrArg Complex.im (sub_eq_zero.mp hzero)
            simpa using this
          exact hT_ne him
      exact (continuous_const.intervalIntegrable a b).mul_continuousOn hcontinuous
  have h_term_bound : ∀ n ∈ S,
      |m n *
          (Real.arctan ((a - (ρ n).re) / (T - (ρ n).im)) -
            Real.arctan ((b - (ρ n).re) / (T - (ρ n).im)))| ≤
        (b - a) * (m n / |(ρ n).im - T|) := by
    intro n hn
    have hmn : 0 ≤ m n := hm n hn
    have hT_ne : T ≠ (ρ n).im := fun h => hbound n hn h.symm
    have habs := abs_arctan_sub_le ((a - (ρ n).re) / (T - (ρ n).im))
                  ((b - (ρ n).re) / (T - (ρ n).im))
    have hba_nn : 0 ≤ b - a := sub_nonneg.mpr hab
    have hT_im_ne : (T - (ρ n).im) ≠ 0 := sub_ne_zero.mpr hT_ne
    have habs_T : |T - (ρ n).im| = |(ρ n).im - T| := abs_sub_comm T (ρ n).im
    have hdiv :
        |((a - (ρ n).re) / (T - (ρ n).im)) -
          ((b - (ρ n).re) / (T - (ρ n).im))| =
        (b - a) / |(ρ n).im - T| := by
      have hsub : ((a - (ρ n).re) / (T - (ρ n).im)) -
            ((b - (ρ n).re) / (T - (ρ n).im))
          = (a - b) / (T - (ρ n).im) := by
        rw [div_sub_div _ _ hT_im_ne hT_im_ne]
        rw [div_eq_div_iff (mul_ne_zero hT_im_ne hT_im_ne) hT_im_ne]
        ring
      rw [hsub, abs_div, ← habs_T]
      rw [show |a - b| = b - a from by
        rw [abs_sub_comm, abs_of_nonneg hba_nn]]
    calc |m n *
            (Real.arctan ((a - (ρ n).re) / (T - (ρ n).im)) -
              Real.arctan ((b - (ρ n).re) / (T - (ρ n).im)))|
        = m n * |Real.arctan ((a - (ρ n).re) / (T - (ρ n).im)) -
            Real.arctan ((b - (ρ n).re) / (T - (ρ n).im))| := by
          rw [abs_mul, abs_of_nonneg hmn]
      _ ≤ m n * |((a - (ρ n).re) / (T - (ρ n).im)) -
            ((b - (ρ n).re) / (T - (ρ n).im))| :=
          mul_le_mul_of_nonneg_left habs hmn
      _ = m n * ((b - a) / |(ρ n).im - T|) := by rw [hdiv]
      _ = (b - a) * (m n / |(ρ n).im - T|) := by ring
  calc |∫ x in a..b,
            (∑ n ∈ S,
              m n * ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - ρ n)).im)|
      = |∑ n ∈ S,
            m n *
              (Real.arctan ((a - (ρ n).re) / (T - (ρ n).im)) -
                Real.arctan ((b - (ρ n).re) / (T - (ρ n).im)))| := by rw [h_integral]
    _ ≤ ∑ n ∈ S,
            |m n *
              (Real.arctan ((a - (ρ n).re) / (T - (ρ n).im)) -
                Real.arctan ((b - (ρ n).re) / (T - (ρ n).im)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ S, (b - a) * (m n / |(ρ n).im - T|) :=
        Finset.sum_le_sum h_term_bound
    _ = (b - a) * S.sum (fun n => m n / |(ρ n).im - T|) := by
        rw [← Finset.mul_sum]

/-
**Combined integral × shell-sum bound** (the headline corollary).

Composes `paired_remainder_integral_finset_bound_weighted_indexed` (per-zero
arctan bound) with `near_height_shell_sum_bound_weighted` (uniform weighted
shell density).  Output: a single bound `O((b-a) · M · log²T)` for the integral
of the multiplicity-weighted far-zero sum, given a uniform multiplicity bound
`M` and the standard local zero density `O(log T)`.

For the Littlewood application:
* `ρ = h.zeros : ℕ → ℂ` (Hadamard zero enumeration)
* `m = (zeta multiplicity at h.zeros n : ℝ)` with `m ≤ M = O(log T)`
* `(b - a) = 1/2 - 1/log T ≈ 1/2` (constant)
* density bound from Riemann–von Mangoldt
* yields `O(log³T)` after applying the multiplicity ceiling, which is too weak
* the actual O(log T) bound in `pairedRemainderIntegralBound` requires
  pair-cancellation analysis beyond this corollary.
-/
theorem paired_remainder_integral_combined_bound
    (a b T : ℝ) (hT : 2 ≤ T) (hab : a ≤ b) (hba : b - a ≤ 1)
    (ρ : ℕ → ℂ) (m : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hfin : ∀ t : ℝ, Set.Finite {n : ℕ | |(ρ n).im - t| ≤ 1})
    (hdensity : ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ,
      ((hfin s).toFinset.card : ℝ) ≤ C * (1 + Real.log (|s| + 2))) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (S : Finset ℕ),
      (∀ n ∈ S, 0 ≤ m n) →
      (∀ n ∈ S, m n ≤ M) →
      (∀ n ∈ S, 1 < |(ρ n).im - T|) →
      (∀ n ∈ S, |(ρ n).im - T| ≤ 2 * |T|) →
      (∀ n ∈ S, (ρ n).im ≠ T) →
      |∫ x in a..b,
          (∑ n ∈ S,
            m n * ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - ρ n)).im)| ≤
        (b - a) * (C₁ * M * (Real.log |T|) ^ 2) := by
  have hT_abs : 2 ≤ |T| := le_trans hT (le_abs_self T)
  obtain ⟨C₁, hC₁_pos, hshell⟩ :=
    near_height_shell_sum_bound_weighted (fun n => (ρ n).im) M hM hfin hdensity
  refine ⟨C₁, hC₁_pos, ?_⟩
  intro S hm_nn hm_le hfar hupper hbound
  have hint :=
    paired_remainder_integral_finset_bound_weighted_indexed a b T hT hab hba ρ m S
      hm_nn hfar hbound
  have hshell_S := hshell T hT_abs S m hm_nn hm_le hfar hupper
  have hba_nn : 0 ≤ b - a := sub_nonneg.mpr hab
  calc |∫ x in a..b,
            (∑ n ∈ S,
              m n * ((1 : ℂ) / (((x : ℂ) + (T : ℂ) * I) - ρ n)).im)|
      ≤ (b - a) * S.sum (fun n => m n / |(ρ n).im - T|) := hint
    _ ≤ (b - a) * (C₁ * M * (Real.log |T|) ^ 2) :=
        mul_le_mul_of_nonneg_left hshell_S hba_nn