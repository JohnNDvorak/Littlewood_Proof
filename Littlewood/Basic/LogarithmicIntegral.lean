/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# The Logarithmic Integral

This file defines the logarithmic integral li(x), which is the main term in the
asymptotic expansion of the prime counting function π(x).

## Definitions

* `logarithmicIntegral x` : li(x) = ∫₂ˣ dt/log(t), the logarithmic integral
* `offsetLogarithmicIntegral x` : Li(x), the offset logarithmic integral with
  principal value at t = 1

## Main Results

* `logarithmicIntegral_asymptotic` : li(x) → ∞ as x → ∞
* `logarithmicIntegral_expansion` : li(x) = x * (finite sum) + O(x)

## References

* Montgomery-Vaughan, "Multiplicative Number Theory I", Section 1.1
-/

open MeasureTheory Set Real Filter Topology
open scoped Interval

namespace LogarithmicIntegral

/-! ## Definitions -/

/-- The logarithmic integral: li(x) = ∫₂ˣ dt/log(t).
    This is the standard definition used in analytic number theory. -/
noncomputable def logarithmicIntegral (x : ℝ) : ℝ :=
  ∫ t in Ioc 2 x, 1 / log t

/-- Notation for li -/
scoped notation "li" => logarithmicIntegral

/-- The constant Li(2) ≈ 1.0451637... -/
noncomputable def offsetLogarithmicIntegralConstant : ℝ :=
  -- This is the Cauchy principal value ∫₀² dt/log(t)
  -- For now we define it axiomatically
  1.0451637107

/-- The offset logarithmic integral Li(x), defined via Cauchy principal value:
    Li(x) = lim_{ε→0⁺} (∫₀^{1-ε} dt/log(t) + ∫_{1+ε}^x dt/log(t))

    We use the relationship Li(x) = li(x) + Li(2) where Li(2) ≈ 1.0451637... -/
noncomputable def offsetLogarithmicIntegral (x : ℝ) : ℝ :=
  logarithmicIntegral x + offsetLogarithmicIntegralConstant

/-- Notation for Li -/
scoped notation "Li" => offsetLogarithmicIntegral

/-! ## Basic Properties -/

section BasicProperties

theorem logarithmicIntegral_of_le_two {x : ℝ} (hx : x ≤ 2) : li x = 0 := by
  unfold logarithmicIntegral
  have h : Ioc 2 x = ∅ := Ioc_eq_empty (by linarith : ¬2 < x)
  simp [h]

theorem logarithmicIntegral_two : li 2 = 0 := logarithmicIntegral_of_le_two le_rfl

theorem logarithmicIntegral_nonneg {x : ℝ} (_hx : 2 ≤ x) : 0 ≤ li x := by
  unfold logarithmicIntegral
  apply setIntegral_nonneg measurableSet_Ioc
  intro t ht
  simp only [mem_Ioc] at ht
  have hlog : 0 < log t := log_pos (by linarith : 1 < t)
  positivity

private lemma continuousOn_one_div_log_Icc {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun t => 1 / log t) (Icc a b) := by
  have hsubset : Icc a b ⊆ ({0}ᶜ : Set ℝ) := by
    intro t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le (lt_trans zero_lt_one ha) ht.1
    exact ne_of_gt htpos
  have hlog : ContinuousOn log (Icc a b) := continuousOn_log.mono hsubset
  have hlog_ne : ∀ t ∈ Icc a b, log t ≠ 0 := by
    intro t ht
    have ht1 : (1 : ℝ) < t := lt_of_lt_of_le ha ht.1
    exact ne_of_gt (log_pos ht1)
  have hcont_inv : ContinuousOn (fun t => (log t)⁻¹) (Icc a b) := hlog.inv₀ hlog_ne
  simpa [one_div] using hcont_inv

private lemma one_div_log_pos {t : ℝ} (ht : 1 < t) : 0 < 1 / log t :=
  one_div_pos.mpr (log_pos ht)

theorem logarithmicIntegral_pos {x : ℝ} (hx : 2 < x) : 0 < li x := by
  unfold logarithmicIntegral
  have hxle : (2 : ℝ) ≤ x := le_of_lt hx
  have hcont : ContinuousOn (fun t => 1 / log t) (Icc (2 : ℝ) x) :=
    continuousOn_one_div_log_Icc (by linarith : (1 : ℝ) < 2)
  have hle : ∀ t ∈ Ioc (2 : ℝ) x, 0 ≤ 1 / log t := by
    intro t ht
    have ht1 : (1 : ℝ) < t := by linarith [ht.1]
    exact (one_div_log_pos ht1).le
  have hlt : ∃ c ∈ Icc (2 : ℝ) x, 0 < 1 / log c := by
    refine ⟨2, ?_, ?_⟩
    · exact ⟨le_rfl, hxle⟩
    · exact one_div_log_pos (by linarith : (1 : ℝ) < 2)
  have hpos : 0 < ∫ t in (2 : ℝ)..x, 1 / log t := by
    exact intervalIntegral.integral_pos hx hcont hle hlt
  simpa [intervalIntegral.integral_of_le hxle] using hpos

theorem logarithmicIntegral_strictMono : StrictMonoOn li (Set.Ici 2) := by
  intro x hx y hy hxy
  have hxy_le : x ≤ y := le_of_lt hxy
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by linarith : (1 : ℝ) < 2) hx
  have hcont : ContinuousOn (fun t => 1 / log t) (Icc x y) :=
    continuousOn_one_div_log_Icc hx1
  have hle : ∀ t ∈ Ioc x y, 0 ≤ 1 / log t := by
    intro t ht
    have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hx1 (le_of_lt ht.1)
    exact (one_div_log_pos ht1).le
  have hlt : ∃ c ∈ Icc x y, 0 < 1 / log c := by
    refine ⟨x, ?_, ?_⟩
    · exact ⟨le_rfl, hxy_le⟩
    · exact one_div_log_pos hx1
  have hpos_interval : 0 < ∫ t in x..y, 1 / log t := by
    exact intervalIntegral.integral_pos hxy hcont hle hlt
  have hpos : 0 < ∫ t in Ioc x y, 1 / log t := by
    simpa [intervalIntegral.integral_of_le hxy_le] using hpos_interval
  have hcont_big : ContinuousOn (fun t => 1 / log t) (Icc (2 : ℝ) y) :=
    continuousOn_one_div_log_Icc (by linarith : (1 : ℝ) < 2)
  have hcont_x : ContinuousOn (fun t => 1 / log t) (Icc (2 : ℝ) x) :=
    hcont_big.mono (by
      intro t ht
      exact ⟨ht.1, ht.2.trans hxy_le⟩)
  have hint_y : IntervalIntegrable (fun t => 1 / log t) volume (2 : ℝ) y :=
    (ContinuousOn.intervalIntegrable_of_Icc (a := (2 : ℝ)) (b := y) (hx.trans hxy_le)
      hcont_big)
  have hint_x : IntervalIntegrable (fun t => 1 / log t) volume (2 : ℝ) x :=
    (ContinuousOn.intervalIntegrable_of_Icc (a := (2 : ℝ)) (b := x) hx hcont_x)
  have hsub_interval :
      (∫ t in (2 : ℝ)..y, 1 / log t) - ∫ t in (2 : ℝ)..x, 1 / log t =
        ∫ t in x..y, 1 / log t := by
    exact intervalIntegral.integral_interval_sub_left hint_y hint_x
  have hsub : li y - li x = ∫ t in Ioc x y, 1 / log t := by
    simpa [logarithmicIntegral, intervalIntegral.integral_of_le (hx.trans hxy_le),
      intervalIntegral.integral_of_le hx, intervalIntegral.integral_of_le hxy_le, one_div]
      using hsub_interval
  have hlt' : 0 < li y - li x := by simpa [hsub] using hpos
  exact sub_pos.mp hlt'

theorem logarithmicIntegral_mono {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) : li x ≤ li y := by
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  · exact le_of_lt (logarithmicIntegral_strictMono hx (hx.trans hxy) hxy')

end BasicProperties

/-! ## Splitting the Integral -/

section Splitting

/-- Additivity: li(y) - li(x) = ∫ₓʸ dt/log(t) for 2 ≤ x ≤ y -/
theorem logarithmicIntegral_sub {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    li y - li x = ∫ t in Ioc x y, 1 / log t := by
  unfold logarithmicIntegral
  -- Use interval integral splitting
  have hxy_le : x ≤ y := hxy
  have hy : 2 ≤ y := hx.trans hxy
  have hcont : ContinuousOn (fun t => 1 / log t) (Icc (2 : ℝ) y) :=
    continuousOn_one_div_log_Icc (by linarith : (1 : ℝ) < 2)
  have hcont_x : ContinuousOn (fun t => 1 / log t) (Icc (2 : ℝ) x) :=
    hcont.mono (by
      intro t ht
      exact ⟨ht.1, ht.2.trans hxy⟩)
  have hint_y : IntervalIntegrable (fun t => 1 / log t) volume (2 : ℝ) y :=
    (ContinuousOn.intervalIntegrable_of_Icc (a := (2 : ℝ)) (b := y) hy hcont)
  have hint_x : IntervalIntegrable (fun t => 1 / log t) volume (2 : ℝ) x :=
    (ContinuousOn.intervalIntegrable_of_Icc (a := (2 : ℝ)) (b := x) hx hcont_x)
  have hsub_interval :
      (∫ t in (2 : ℝ)..y, 1 / log t) - ∫ t in (2 : ℝ)..x, 1 / log t =
        ∫ t in x..y, 1 / log t := by
    exact intervalIntegral.integral_interval_sub_left hint_y hint_x
  have hxle : (2 : ℝ) ≤ x := hx
  have hyle : (2 : ℝ) ≤ y := hy
  simpa [intervalIntegral.integral_of_le hyle, intervalIntegral.integral_of_le hxle,
    intervalIntegral.integral_of_le hxy_le, one_div] using hsub_interval

/-- Integration by parts identity -/
theorem logarithmicIntegral_integration_by_parts {x : ℝ} (hx : 2 < x) :
    li x = x / log x - 2 / log 2 + ∫ t in Ioc 2 x, 1 / (log t)^2 := by
  -- Standard integration by parts with u = 1/log(t), dv = dt
  have hxle : (2 : ℝ) ≤ x := le_of_lt hx
  let u : ℝ → ℝ := fun t => (log t)⁻¹
  let u' : ℝ → ℝ := fun t => -(t⁻¹) / (log t)^2
  let v : ℝ → ℝ := fun t => t
  let v' : ℝ → ℝ := fun _ => (1 : ℝ)
  have hu : ∀ t ∈ [[(2 : ℝ), x]], HasDerivAt u (u' t) t := by
    intro t ht
    have ht' : t ∈ Icc (2 : ℝ) x := by
      simpa [Set.uIcc_of_le hxle] using ht
    have ht0 : t ≠ 0 := by
      have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht'.1
      exact ne_of_gt htpos
    have ht1 : (1 : ℝ) < t := by
      linarith [ht'.1]
    have hlog_ne : log t ≠ 0 := by
      exact ne_of_gt (log_pos ht1)
    simpa [u, u', one_div] using (Real.hasDerivAt_log ht0).inv hlog_ne
  have hv : ∀ t ∈ [[(2 : ℝ), x]], HasDerivAt v (v' t) t := by
    intro t ht
    simpa [v, v'] using (hasDerivAt_id t)
  have hcont_inv : ContinuousOn (fun t => t⁻¹) (Icc (2 : ℝ) x) := by
    have hne : ∀ t ∈ Icc (2 : ℝ) x, t ≠ 0 := by
      intro t ht
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)
    exact (continuousOn_id.inv₀ hne)
  have hcont_log : ContinuousOn log (Icc (2 : ℝ) x) := by
    have hsubset : Icc (2 : ℝ) x ⊆ ({0}ᶜ : Set ℝ) := by
      intro t ht
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)
    exact continuousOn_log.mono hsubset
  have hcont_log_sq : ContinuousOn (fun t => (log t)^2) (Icc (2 : ℝ) x) :=
    hcont_log.pow 2
  have hcont_inv_log_sq : ContinuousOn (fun t => ((log t)^2)⁻¹) (Icc (2 : ℝ) x) := by
    have hne : ∀ t ∈ Icc (2 : ℝ) x, (log t)^2 ≠ 0 := by
      intro t ht
      have ht1 : (1 : ℝ) < t := by
        linarith [ht.1]
      exact pow_ne_zero 2 (ne_of_gt (log_pos ht1))
    exact hcont_log_sq.inv₀ hne
  have hcont_u' : ContinuousOn u' (Icc (2 : ℝ) x) := by
    have hcont_mul :
        ContinuousOn (fun t => t⁻¹ * ((log t)^2)⁻¹) (Icc (2 : ℝ) x) :=
      hcont_inv.mul hcont_inv_log_sq
    simpa [u', div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hcont_mul.neg
  have hint_u' : IntervalIntegrable u' volume (2 : ℝ) x :=
    (ContinuousOn.intervalIntegrable_of_Icc (a := (2 : ℝ)) (b := x) hxle hcont_u')
  have hint_v' : IntervalIntegrable v' volume (2 : ℝ) x := by
    simpa [v'] using
      (intervalIntegrable_const (μ := volume) (a := (2 : ℝ)) (b := x) (c := (1 : ℝ)))
  have hparts :
      ∫ t in (2 : ℝ)..x, u t * v' t =
        u x * v x - u 2 * v 2 - ∫ t in (2 : ℝ)..x, u' t * v t := by
    simpa using
      (intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (2 : ℝ)) (b := x)
        (u := u) (u' := u') (v := v) (v' := v') hu hv hint_u' hint_v')
  have huv : (fun t => u' t * v t) = fun t => -(1 / (log t)^2) := by
    funext t
    by_cases ht : t = 0
    · simp [u', v, ht]
    · simp [u', v, ht, div_eq_mul_inv, mul_comm]
  have hparts' :
      ∫ t in (2 : ℝ)..x, 1 / log t =
        x / log x - 2 / log 2 + ∫ t in (2 : ℝ)..x, 1 / (log t)^2 := by
    have hparts1 :
        ∫ t in (2 : ℝ)..x, 1 / log t =
          x / log x - 2 / log 2 - ∫ t in (2 : ℝ)..x, u' t * v t := by
      simpa [u, v, v', one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hparts
    simpa [huv, sub_eq_add_neg, intervalIntegral.integral_neg] using hparts1
  calc
    li x = ∫ t in (2 : ℝ)..x, 1 / log t := by
      simp [logarithmicIntegral, intervalIntegral.integral_of_le hxle]
    _ = x / log x - 2 / log 2 + ∫ t in (2 : ℝ)..x, 1 / (log t)^2 := hparts'
    _ = x / log x - 2 / log 2 + ∫ t in Ioc 2 x, 1 / (log t)^2 := by
      simp [intervalIntegral.integral_of_le hxle]

end Splitting

/-! ## Asymptotic Expansion -/

section Asymptotics

open Asymptotics

/-- li(x) → ∞ as x → ∞ -/
theorem logarithmicIntegral_asymptotic :
    Tendsto li atTop atTop := by
  have hlog : Tendsto (fun x => log x / x) atTop (𝓝 0) := by
    simpa [pow_one, one_mul, add_zero] using
      (tendsto_pow_log_div_mul_add_atTop (a := (1 : ℝ)) (b := 0) (n := 1) (by norm_num))
  have hdiv : Tendsto (fun x => x / log x) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    by_cases hb : b ≤ 0
    · have hpos : ∀ᶠ x in atTop, 0 ≤ x / log x := by
        refine (eventually_gt_atTop (1 : ℝ)).mono ?_
        intro x hx
        have hxpos : 0 ≤ x := by linarith
        have hlogpos : 0 < log x := log_pos hx
        exact div_nonneg hxpos hlogpos.le
      exact hpos.mono (fun x hx => le_trans hb hx)
    · have hbpos : 0 < b := lt_of_not_ge hb
      have hlt : ∀ᶠ x in atTop, log x / x < 1 / b :=
        (tendsto_order.1 hlog).2 _ (by positivity)
      have hx1 : ∀ᶠ x in (atTop : Filter ℝ), 1 < x := eventually_gt_atTop (1 : ℝ)
      refine (hlt.and hx1).mono ?_
      intro x hx
      rcases hx with ⟨hlt, hx1⟩
      have hxpos : 0 < x := lt_trans (by norm_num) hx1
      have hlogpos : 0 < log x := log_pos hx1
      have h1 : log x < x / b := by
        have h1' : log x < (1 / b) * x := (div_lt_iff₀ hxpos).1 hlt
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h1'
      have h2 : b * log x < x := by
        have h2' : log x * b < x := (lt_div_iff₀ hbpos).1 h1
        simpa [mul_comm, mul_left_comm, mul_assoc] using h2'
      have h3 : b < x / log x := (lt_div_iff₀ hlogpos).2 h2
      exact le_of_lt h3
  have hdiv' : Tendsto (fun x => x / log x - 2 / log 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    have hb := (tendsto_atTop.1 hdiv) (b + 2 / log 2)
    exact hb.mono (fun x hx => by linarith)
  have hbound : ∀ᶠ x in atTop, x / log x - 2 / log 2 ≤ li x := by
    refine (eventually_gt_atTop (2 : ℝ)).mono ?_
    intro x hx
    have hxle : (2 : ℝ) ≤ x := le_of_lt hx
    have hEq := logarithmicIntegral_integration_by_parts (x := x) hx
    have hnonneg : 0 ≤ ∫ t in Ioc 2 x, 1 / (log t)^2 := by
      have hnonneg' : 0 ≤ ∫ t in (2 : ℝ)..x, 1 / (log t)^2 := by
        refine intervalIntegral.integral_nonneg hxle ?_
        intro t ht
        have ht1 : (1 : ℝ) < t := by linarith [ht.1]
        have hpos : 0 < log t := log_pos ht1
        have hpos' : 0 < (log t) ^ (2 : ℕ) := pow_pos hpos _
        exact (one_div_pos.mpr hpos').le
      simpa [intervalIntegral.integral_of_le hxle] using hnonneg'
    linarith [hEq, hnonneg]
  exact tendsto_atTop_mono' atTop hbound hdiv'

/-- li(x) = x/log(x) + O(x) -/
theorem logarithmicIntegral_bigO_one :
    (fun x => li x - x / log x) =O[atTop] (fun x => x) := by
  have hli : (fun x => li x) =O[atTop] (fun x => x) := by
    refine IsBigO.of_bound (1 / log 2) ?_
    refine Filter.eventually_atTop.2 ?_
    refine ⟨2, ?_⟩
    intro x hx
    have hxpos : 0 ≤ x := by linarith
    have hli_nonneg : 0 ≤ li x := logarithmicIntegral_nonneg hx
    have hbound : ∀ t ∈ Ι (2 : ℝ) x, ‖1 / log t‖ ≤ 1 / log 2 := by
      intro t ht
      have ht' : t ∈ Ioc (2 : ℝ) x := by
        simpa [uIoc_of_le hx] using ht
      have ht1 : (1 : ℝ) < t := lt_trans (by norm_num) ht'.1
      have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
      have hlogt : 0 < log t := log_pos ht1
      have hlogle : log (2 : ℝ) ≤ log t := log_le_log (by norm_num) (le_of_lt ht'.1)
      have hle : 1 / log t ≤ 1 / log (2 : ℝ) :=
        one_div_le_one_div_of_le hlog2 hlogle
      simpa [Real.norm_eq_abs, abs_of_nonneg hlogt.le, abs_of_nonneg hlog2.le] using hle
    have hnorm :
        ‖∫ t in (2 : ℝ)..x, 1 / log t‖ ≤ (1 / log (2 : ℝ)) * |x - 2| := by
      simpa using (intervalIntegral.norm_integral_le_of_norm_le_const (a := (2 : ℝ)) (b := x)
        (f := fun t => 1 / log t) (C := 1 / log (2 : ℝ)) hbound)
    have hli : li x = ∫ t in (2 : ℝ)..x, 1 / log t := by
      simp [logarithmicIntegral, intervalIntegral.integral_of_le hx]
    have hli_le : li x ≤ (1 / log (2 : ℝ)) * (x - 2) := by
      have hnorm' : |∫ t in (2 : ℝ)..x, 1 / log t| ≤ (1 / log (2 : ℝ)) * |x - 2| := by
        simpa [Real.norm_eq_abs] using hnorm
      have hnonneg : 0 ≤ ∫ t in (2 : ℝ)..x, 1 / log t := by
        refine intervalIntegral.integral_nonneg hx ?_
        intro t ht
        have ht1 : (1 : ℝ) < t := by linarith [ht.1]
        exact (one_div_pos.mpr (log_pos ht1)).le
      have habs : |∫ t in (2 : ℝ)..x, 1 / log t| = ∫ t in (2 : ℝ)..x, 1 / log t := by
        exact abs_of_nonneg hnonneg
      have habs' : |x - 2| = x - 2 := by
        exact abs_of_nonneg (sub_nonneg.mpr hx)
      calc
        li x = ∫ t in (2 : ℝ)..x, 1 / log t := hli
        _ = |∫ t in (2 : ℝ)..x, 1 / log t| := by
          symm
          exact habs
        _ ≤ (1 / log (2 : ℝ)) * |x - 2| := hnorm'
        _ = (1 / log (2 : ℝ)) * (x - 2) := by simpa [habs']
    have hle : (1 / log (2 : ℝ)) * (x - 2) ≤ x / log 2 := by
      have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
      have hlog2_nonneg : 0 ≤ (1 / log (2 : ℝ)) := (one_div_pos.mpr hlog2).le
      have hsub : x - 2 ≤ x := by linarith
      have hmul : (1 / log (2 : ℝ)) * (x - 2) ≤ (1 / log (2 : ℝ)) * x :=
        mul_le_mul_of_nonneg_left hsub hlog2_nonneg
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    have hli_le' : li x ≤ x / log 2 := hli_le.trans hle
    simpa [Real.norm_eq_abs, abs_of_nonneg hli_nonneg, abs_of_nonneg hxpos,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hli_le'
  have hdiv : (fun x => x / log x) =O[atTop] (fun x => x) := by
    refine IsBigO.of_bound (1 / log 2) ?_
    refine Filter.eventually_atTop.2 ?_
    refine ⟨2, ?_⟩
    intro x hx
    have hxpos : 0 ≤ x := by linarith
    have hlog2pos : 0 < log (2 : ℝ) := log_pos (by norm_num)
    have hlogle : log (2 : ℝ) ≤ log x := log_le_log (by norm_num) hx
    have hle : 1 / log x ≤ 1 / log (2 : ℝ) :=
      one_div_le_one_div_of_le hlog2pos hlogle
    have hle' : x / log x ≤ x / log 2 := by
      have hmul : x * (1 / log x) ≤ x * (1 / log (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hle hxpos
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    have hlogpos : 0 < log x := log_pos (by linarith : (1 : ℝ) < x)
    have hdiv_nonneg : 0 ≤ x / log x := div_nonneg hxpos hlogpos.le
    have hnorm1 : ‖x / log x‖ = x / log x := by
      exact norm_of_nonneg hdiv_nonneg
    have hnorm2 : ‖x‖ = x := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hxpos]
    calc
      ‖x / log x‖ = x / log x := hnorm1
      _ ≤ x / log 2 := hle'
      _ = (1 / log 2) * x := by simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      _ = (1 / log 2) * ‖x‖ := by simpa [hnorm2]
  exact hli.sub hdiv

/-- li(x) = x/log(x) + x/log²(x) + O(x) -/
theorem logarithmicIntegral_bigO_two :
    (fun x => li x - x / log x - x / (log x)^2) =O[atTop] (fun x => x) := by
  have h1 : (fun x => li x - x / log x) =O[atTop] (fun x => x) :=
    logarithmicIntegral_bigO_one
  have h2 : (fun x => x / (log x)^2) =O[atTop] (fun x => x) := by
    refine IsBigO.of_bound (1 / (log 2) ^ (2 : ℕ)) ?_
    refine Filter.eventually_atTop.2 ?_
    refine ⟨2, ?_⟩
    intro x hx
    have hxpos : 0 ≤ x := by linarith
    have hlog2pos : 0 < log (2 : ℝ) := log_pos (by norm_num)
    have hlogle : log (2 : ℝ) ≤ log x := log_le_log (by norm_num) hx
    have hpow : (log (2 : ℝ)) ^ (2 : ℕ) ≤ (log x) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hlog2pos.le hlogle _
    have hle : 1 / (log x) ^ (2 : ℕ) ≤ 1 / (log (2 : ℝ)) ^ (2 : ℕ) :=
      one_div_le_one_div_of_le (pow_pos hlog2pos _) hpow
    have hmul : x * (1 / (log x) ^ (2 : ℕ)) ≤ x * (1 / (log (2 : ℝ)) ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hle hxpos
    have hle' : x / (log x) ^ (2 : ℕ) ≤ x / (log 2) ^ (2 : ℕ) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    have hdiv_nonneg : 0 ≤ x / (log x) ^ (2 : ℕ) := by
      have hlogpos : 0 < log x := log_pos (by linarith : (1 : ℝ) < x)
      have hpow_nonneg : 0 ≤ (log x) ^ (2 : ℕ) := pow_nonneg hlogpos.le _
      exact div_nonneg hxpos hpow_nonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg hdiv_nonneg, abs_of_nonneg hxpos,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hle'
  simpa [sub_eq_add_neg, add_assoc] using (h1.sub h2)

/-- Coarse expansion: li(x) = x * (finite sum) + O(x) -/
theorem logarithmicIntegral_expansion (n : ℕ) :
    (fun x => li x - x * ∑ k ∈ Finset.range n, k.factorial / (log x)^(k+1))
    =O[atTop] (fun x => x) := by
  have h1 : (fun x => li x - x / log x) =O[atTop] (fun x => x) :=
    logarithmicIntegral_bigO_one
  have h2 : (fun x => x / log x) =O[atTop] (fun x => x) := by
    refine IsBigO.of_bound (1 / log 2) ?_
    refine Filter.eventually_atTop.2 ?_
    refine ⟨2, ?_⟩
    intro x hx
    have hxpos : 0 ≤ x := by linarith
    have hlog2pos : 0 < log (2 : ℝ) := log_pos (by norm_num)
    have hlogle : log (2 : ℝ) ≤ log x := log_le_log (by norm_num) hx
    have hle : 1 / log x ≤ 1 / log (2 : ℝ) :=
      one_div_le_one_div_of_le hlog2pos hlogle
    have hle' : x / log x ≤ x / log 2 := by
      have hmul : x * (1 / log x) ≤ x * (1 / log (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hle hxpos
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    have hlogpos : 0 < log x := log_pos (by linarith : (1 : ℝ) < x)
    have hdiv_nonneg : 0 ≤ x / log x := div_nonneg hxpos hlogpos.le
    have hnorm1 : ‖x / log x‖ = x / log x := by
      exact norm_of_nonneg hdiv_nonneg
    have hnorm2 : ‖x‖ = x := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hxpos]
    calc
      ‖x / log x‖ = x / log x := hnorm1
      _ ≤ x / log 2 := hle'
      _ = (1 / log 2) * x := by simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      _ = (1 / log 2) * ‖x‖ := by simpa [hnorm2]
  have hli : (fun x => li x) =O[atTop] (fun x => x) := by
    have hsum := h1.add h2
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
  have hsum :
      (fun x => x * ∑ k ∈ Finset.range n, k.factorial / (log x)^(k+1))
        =O[atTop] (fun x => x) := by
    let C : ℝ := ∑ k ∈ Finset.range n, (k.factorial : ℝ) / (log 2)^(k+1)
    refine IsBigO.of_bound C ?_
    refine Filter.eventually_atTop.2 ?_
    refine ⟨2, ?_⟩
    intro x hx
    have hlog2pos : 0 < log (2 : ℝ) := log_pos (by norm_num)
    have hlogle : log (2 : ℝ) ≤ log x := log_le_log (by norm_num) hx
    have hterm_le :
        ∀ k ∈ Finset.range n,
          (k.factorial : ℝ) / (log x)^(k+1) ≤ (k.factorial : ℝ) / (log 2)^(k+1) := by
      intro k hk
      have hpow : (log (2 : ℝ)) ^ (k + 1) ≤ (log x) ^ (k + 1) :=
        pow_le_pow_left₀ hlog2pos.le hlogle _
      have hle : 1 / (log x) ^ (k + 1) ≤ 1 / (log (2 : ℝ)) ^ (k + 1) :=
        one_div_le_one_div_of_le (pow_pos hlog2pos _) hpow
      have hfac_nonneg : 0 ≤ (k.factorial : ℝ) := by
        exact_mod_cast (Nat.factorial_pos k).le
      have hmul :
          (k.factorial : ℝ) * (1 / (log x) ^ (k + 1)) ≤
            (k.factorial : ℝ) * (1 / (log (2 : ℝ)) ^ (k + 1)) :=
        mul_le_mul_of_nonneg_left hle hfac_nonneg
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    have hsum_le :
        (∑ k ∈ Finset.range n, (k.factorial : ℝ) / (log x)^(k+1)) ≤ C := by
      simpa [C] using (Finset.sum_le_sum fun k hk => hterm_le k hk)
    have hterm_nonneg :
        ∀ k ∈ Finset.range n, 0 ≤ (k.factorial : ℝ) / (log x)^(k+1) := by
      intro k hk
      have hfac_nonneg : 0 ≤ (k.factorial : ℝ) := by
        exact_mod_cast (Nat.factorial_pos k).le
      have hlogpos : 0 < log x := log_pos (by linarith : (1 : ℝ) < x)
      have hpow_nonneg : 0 ≤ (log x) ^ (k + 1) := pow_nonneg hlogpos.le _
      exact div_nonneg hfac_nonneg hpow_nonneg
    have hsum_nonneg :
        0 ≤ ∑ k ∈ Finset.range n, (k.factorial : ℝ) / (log x)^(k+1) :=
      Finset.sum_nonneg hterm_nonneg
    have hsum_abs :
        |∑ k ∈ Finset.range n, (k.factorial : ℝ) / (log x)^(k+1)| ≤ C := by
      simpa [abs_of_nonneg hsum_nonneg] using hsum_le
    have hmul :
        |x * ∑ k ∈ Finset.range n, (k.factorial : ℝ) / (log x)^(k+1)| ≤ C * |x| := by
      calc
        |x * ∑ k ∈ Finset.range n, (k.factorial : ℝ) / (log x)^(k+1)|
            = |x| * |∑ k ∈ Finset.range n, (k.factorial : ℝ) / (log x)^(k+1)| := by
              simp [abs_mul, mul_comm, mul_left_comm, mul_assoc]
        _ ≤ |x| * C := mul_le_mul_of_nonneg_left hsum_abs (abs_nonneg x)
        _ = C * |x| := by nlinarith
    simpa [Real.norm_eq_abs] using hmul
  exact hli.sub hsum

end Asymptotics

/-! ## Comparison with x/log(x) -/

section Comparison

/-- li(x) > x/log(x) - 2/log(2) for x > 2 -/
theorem logarithmicIntegral_gt_divLog {x : ℝ} (hx : 2 < x) :
    x / log x - 2 / log 2 < li x := by
  have hxle : (2 : ℝ) ≤ x := le_of_lt hx
  have hcont : ContinuousOn (fun t => 1 / (log t)^2) (Icc (2 : ℝ) x) := by
    have hcont' : ContinuousOn (fun t => 1 / log t) (Icc (2 : ℝ) x) :=
      continuousOn_one_div_log_Icc (by linarith : (1 : ℝ) < 2)
    have hcont'' : ContinuousOn (fun t => (1 / log t) ^ (2 : ℕ)) (Icc (2 : ℝ) x) :=
      hcont'.pow 2
    simpa [one_div_pow] using hcont''
  have hle : ∀ t ∈ Ioc (2 : ℝ) x, 0 ≤ 1 / (log t)^2 := by
    intro t ht
    have ht1 : (1 : ℝ) < t := by linarith [ht.1]
    have hpos : 0 < log t := log_pos ht1
    have hpos' : 0 < (log t) ^ (2 : ℕ) := by
      exact pow_pos hpos _
    have : 0 < 1 / (log t)^2 := one_div_pos.mpr hpos'
    exact this.le
  have hlt : ∃ c ∈ Icc (2 : ℝ) x, 0 < 1 / (log c)^2 := by
    refine ⟨2, ?_, ?_⟩
    · exact ⟨le_rfl, hxle⟩
    · have hpos : 0 < log (2 : ℝ) := log_pos (by norm_num)
      have hpos' : 0 < (log (2 : ℝ)) ^ (2 : ℕ) := pow_pos hpos _
      exact one_div_pos.mpr hpos'
  have hpos : 0 < ∫ t in (2 : ℝ)..x, 1 / (log t)^2 := by
    refine intervalIntegral.integral_pos hx hcont ?_ hlt
    intro t ht
    have ht' : t ∈ Ioc (2 : ℝ) x := ht
    simpa [one_div_pow] using hle t ht'
  have hpos' : 0 < ∫ t in Ioc 2 x, 1 / (log t)^2 := by
    simpa [intervalIntegral.integral_of_le hxle] using hpos
  have hEq := logarithmicIntegral_integration_by_parts (x := x) hx
  calc
    x / log x - 2 / log 2
        < x / log x - 2 / log 2 + ∫ t in Ioc 2 x, 1 / (log t)^2 := by
          nlinarith
    _ = li x := by simpa [hEq]

/-- li(x) ≤ x/log(2) for x ≥ 2 -/
theorem logarithmicIntegral_lt_bound {x : ℝ} (hx : 2 ≤ x) :
    li x ≤ x / log 2 := by
  have hbound : ∀ t ∈ Ι (2 : ℝ) x, ‖1 / log t‖ ≤ 1 / log 2 := by
    intro t ht
    have ht' : t ∈ Ioc (2 : ℝ) x := by
      simpa [uIoc_of_le hx] using ht
    have ht1 : (1 : ℝ) < t := lt_trans (by norm_num) ht'.1
    have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
    have hlogt : 0 < log t := log_pos ht1
    have hlogle : log (2 : ℝ) ≤ log t := log_le_log (by norm_num) (le_of_lt ht'.1)
    have hle : 1 / log t ≤ 1 / log (2 : ℝ) :=
      one_div_le_one_div_of_le hlog2 hlogle
    simpa [Real.norm_eq_abs, abs_of_nonneg hlogt.le, abs_of_nonneg hlog2.le] using hle
  have hnorm :
      ‖∫ t in (2 : ℝ)..x, 1 / log t‖ ≤ (1 / log (2 : ℝ)) * |x - 2| := by
    simpa using (intervalIntegral.norm_integral_le_of_norm_le_const (a := (2 : ℝ)) (b := x)
      (f := fun t => 1 / log t) (C := 1 / log (2 : ℝ)) hbound)
  have hli : li x = ∫ t in (2 : ℝ)..x, 1 / log t := by
    simp [logarithmicIntegral, intervalIntegral.integral_of_le hx]
  have hli_le : li x ≤ (1 / log (2 : ℝ)) * (x - 2) := by
    have hnorm' : |∫ t in (2 : ℝ)..x, 1 / log t| ≤ (1 / log (2 : ℝ)) * |x - 2| := by
      simpa [Real.norm_eq_abs] using hnorm
    have hnonneg : 0 ≤ ∫ t in (2 : ℝ)..x, 1 / log t := by
      refine intervalIntegral.integral_nonneg hx ?_
      intro t ht
      have ht1 : (1 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht.1
      exact (one_div_pos.mpr (log_pos ht1)).le
    have habs : |∫ t in (2 : ℝ)..x, 1 / log t| = ∫ t in (2 : ℝ)..x, 1 / log t := by
      exact abs_of_nonneg hnonneg
    have habs' : |x - 2| = x - 2 := by
      exact abs_of_nonneg (sub_nonneg.mpr hx)
    calc
      li x = ∫ t in (2 : ℝ)..x, 1 / log t := hli
      _ = |∫ t in (2 : ℝ)..x, 1 / log t| := by
        symm
        exact habs
      _ ≤ (1 / log (2 : ℝ)) * |x - 2| := hnorm'
      _ = (1 / log (2 : ℝ)) * (x - 2) := by simpa [habs']
  have hle : (1 / log (2 : ℝ)) * (x - 2) ≤ x / log 2 := by
    have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
    have hlog2_nonneg : 0 ≤ (1 / log (2 : ℝ)) := (one_div_pos.mpr hlog2).le
    have hsub : x - 2 ≤ x := by linarith
    have hmul : (1 / log (2 : ℝ)) * (x - 2) ≤ (1 / log (2 : ℝ)) * x :=
      mul_le_mul_of_nonneg_left hsub hlog2_nonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  exact hli_le.trans hle

/-- li(x) - x/log(x) → ∞ as x → ∞ -/
theorem logarithmicIntegral_sub_divLog_tendsto :
    Tendsto (fun x => li x - x / log x) atTop atTop := by
  have hlog2 : Tendsto (fun x => (log x)^2 / x) atTop (𝓝 0) := by
    simpa [pow_two, one_mul, add_zero] using
      (tendsto_pow_log_div_mul_add_atTop (a := (1 : ℝ)) (b := 0) (n := 2) (by norm_num))
  have hdiv2 : Tendsto (fun x => x / (log x)^2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    by_cases hb : b ≤ 0
    · have hpos : ∀ᶠ x in atTop, 0 ≤ x / (log x)^2 := by
        refine (eventually_gt_atTop (1 : ℝ)).mono ?_
        intro x hx
        have hxpos : 0 ≤ x := by linarith
        have hlogpos : 0 < log x := log_pos hx
        have hpow_nonneg : 0 ≤ (log x) ^ (2 : ℕ) := pow_nonneg hlogpos.le _
        exact div_nonneg hxpos hpow_nonneg
      exact hpos.mono (fun x hx => le_trans hb hx)
    · have hbpos : 0 < b := lt_of_not_ge hb
      have hlt : ∀ᶠ x in atTop, (log x)^2 / x < 1 / b :=
        (tendsto_order.1 hlog2).2 _ (by positivity)
      have hx1 : ∀ᶠ x in (atTop : Filter ℝ), 1 < x := eventually_gt_atTop (1 : ℝ)
      refine (hlt.and hx1).mono ?_
      intro x hx
      rcases hx with ⟨hlt, hx1⟩
      have hxpos : 0 < x := lt_trans (by norm_num) hx1
      have hlogpos : 0 < log x := log_pos hx1
      have h1 : (log x)^2 < x / b := by
        have h1' : (log x)^2 < (1 / b) * x := (div_lt_iff₀ hxpos).1 hlt
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h1'
      have h2 : b * (log x)^2 < x := by
        have h2' : (log x)^2 * b < x := (lt_div_iff₀ hbpos).1 h1
        simpa [mul_comm, mul_left_comm, mul_assoc] using h2'
      have h3 : b < x / (log x)^2 := by
        have hpow_pos : 0 < (log x) ^ (2 : ℕ) := pow_pos hlogpos _
        exact (lt_div_iff₀ hpow_pos).2 h2
      exact le_of_lt h3
  have hmain : Tendsto (fun x => (1 / 2) * (x / (log x)^2) - 2 / log 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    have hb := (tendsto_atTop.1 hdiv2) (2 * (b + 2 / log 2))
    exact hb.mono (fun x hx => by linarith)
  have hbound :
      ∀ᶠ x in atTop, (1 / 2) * (x / (log x)^2) - 2 / log 2 ≤ li x - x / log x := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨4, ?_⟩
    intro x hx
    have hxle : (2 : ℝ) ≤ x := by linarith
    have hx2 : (2 : ℝ) ≤ x / 2 := by linarith
    have hxgt : (2 : ℝ) < x := by linarith
    have hEq := logarithmicIntegral_integration_by_parts (x := x) hxgt
    have hEq' :
        li x - x / log x = -2 / log 2 + ∫ t in Ioc 2 x, 1 / (log t)^2 := by
      calc
        li x - x / log x =
            (x / log x - 2 / log 2 + ∫ t in Ioc 2 x, 1 / (log t)^2) - x / log x := by
              simpa [hEq]
        _ = -2 / log 2 + ∫ t in Ioc 2 x, 1 / (log t)^2 := by ring
    have hcont : ContinuousOn (fun t => (1 / log t) ^ (2 : ℕ)) (Icc (2 : ℝ) x) := by
      have hcont' : ContinuousOn (fun t => 1 / log t) (Icc (2 : ℝ) x) :=
        continuousOn_one_div_log_Icc (by linarith : (1 : ℝ) < 2)
      simpa using hcont'.pow 2
    have hcont2 : ContinuousOn (fun t => 1 / (log t)^2) (Icc (2 : ℝ) x) := by
      simpa [one_div_pow] using hcont
    have hcont_sub : ContinuousOn (fun t => 1 / (log t)^2) (Icc (x / 2) x) :=
      hcont2.mono (by
        intro t ht
        have ht2 : (2 : ℝ) ≤ t := by linarith [hx2, ht.1]
        exact ⟨ht2, ht.2⟩)
    have hfi : IntervalIntegrable (fun t => 1 / (log t)^2) volume (2 : ℝ) x :=
      (ContinuousOn.intervalIntegrable_of_Icc (a := (2 : ℝ)) (b := x) hxle hcont2)
    have hfi_sub : IntervalIntegrable (fun t => 1 / (log t)^2) volume (x / 2) x :=
      (ContinuousOn.intervalIntegrable_of_Icc (a := x / 2) (b := x) (by linarith) hcont_sub)
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (2 : ℝ) x)] fun t => 1 / (log t)^2 := by
      refine ae_restrict_of_forall_mem (by simp) ?_
      intro t ht
      have ht1 : (1 : ℝ) < t := by linarith [ht.1]
      have hpos : 0 < log t := log_pos ht1
      have hpos' : 0 < (log t) ^ (2 : ℕ) := pow_pos hpos _
      exact (one_div_pos.mpr hpos').le
    have hmono_interval :
        ∫ t in (x / 2)..x, 1 / (log t)^2 ≤ ∫ t in (2 : ℝ)..x, 1 / (log t)^2 := by
      exact intervalIntegral.integral_mono_interval (a := x / 2) (b := x) (c := (2 : ℝ))
        (d := x) hx2 (by linarith) le_rfl hnonneg hfi
    have hconst_le :
        ∫ t in (x / 2)..x, (1 / (log x)^2) ≤ ∫ t in (x / 2)..x, 1 / (log t)^2 := by
      have hconst : IntervalIntegrable (fun _ => 1 / (log x)^2) volume (x / 2) x := by
        simpa using (intervalIntegrable_const (μ := volume) (a := x / 2) (b := x)
          (c := (1 / (log x)^2)))
      have hle : ∀ t ∈ Icc (x / 2) x, 1 / (log x)^2 ≤ 1 / (log t)^2 := by
        intro t ht
        have ht1 : (1 : ℝ) < t := by linarith [ht.1, hx2]
        have hlogpos : 0 < log t := log_pos ht1
        have hlogle : log t ≤ log x := log_le_log (by linarith : (0 : ℝ) < t) ht.2
        have hpow : (log t) ^ (2 : ℕ) ≤ (log x) ^ (2 : ℕ) :=
          pow_le_pow_left₀ hlogpos.le hlogle _
        have hpos : 0 < (log t) ^ (2 : ℕ) := pow_pos hlogpos _
        exact one_div_le_one_div_of_le hpos hpow
      exact intervalIntegral.integral_mono_on (a := x / 2) (b := x) (by linarith)
        hconst hfi_sub hle
    have hconst_int :
        ∫ t in (x / 2)..x, (1 / (log x)^2) = (x - x / 2) * (1 / (log x)^2) := by
      simp [intervalIntegral.integral_const]
    have hlower :
        (x / 2) * (1 / (log x)^2) ≤ ∫ t in (2 : ℝ)..x, 1 / (log t)^2 := by
      have hlen : x - x / 2 = x / 2 := by ring
      calc
        (x / 2) * (1 / (log x)^2)
            = (x - x / 2) * (1 / (log x)^2) := by simpa [hlen]
        _ = ∫ t in (x / 2)..x, (1 / (log x)^2) := by simpa [hconst_int]
        _ ≤ ∫ t in (x / 2)..x, 1 / (log t)^2 := hconst_le
        _ ≤ ∫ t in (2 : ℝ)..x, 1 / (log t)^2 := hmono_interval
    have hlower' :
        (x / 2) * (1 / (log x)^2) ≤ ∫ t in Ioc 2 x, 1 / (log t)^2 := by
      simpa [intervalIntegral.integral_of_le hxle] using hlower
    have hbound' :
        -2 / log 2 + (x / 2) * (1 / (log x)^2) ≤ li x - x / log x := by
      calc
        -2 / log 2 + (x / 2) * (1 / (log x)^2)
            ≤ -2 / log 2 + ∫ t in Ioc 2 x, 1 / (log t)^2 := by
              have h' := add_le_add_left hlower' (-2 / log 2)
              simpa [add_comm, add_left_comm, add_assoc] using h'
        _ = li x - x / log x := by simpa [hEq']
    have hbound'' :
        (1 / 2) * (x / (log x)^2) - 2 / log 2 ≤ -2 / log 2 + (x / 2) * (1 / (log x)^2) := by
      have hEq :
          (1 / 2) * (x / (log x)^2) - 2 / log 2 =
            -2 / log 2 + (x / 2) * (1 / (log x)^2) := by
        ring_nf
      exact hEq.le
    exact hbound''.trans hbound'
  exact tendsto_atTop_mono' atTop hbound hmain

end Comparison

/-! ## Derivative and Continuity -/

section Calculus

/-- li is differentiable on (2, ∞) with derivative 1/log(x) -/
theorem logarithmicIntegral_hasDerivAt {x : ℝ} (hx : 2 < x) :
    HasDerivAt li (1 / log x) x := by
  let g : ℝ → ℝ := fun u => ∫ t in (2 : ℝ)..u, 1 / log t
  have hxle : (2 : ℝ) ≤ x := le_of_lt hx
  have hcont_Icc : ContinuousOn (fun t => 1 / log t) (Icc (2 : ℝ) x) :=
    continuousOn_one_div_log_Icc (by linarith : (1 : ℝ) < 2)
  have hint : IntervalIntegrable (fun t => 1 / log t) volume (2 : ℝ) x :=
    (ContinuousOn.intervalIntegrable_of_Icc (a := (2 : ℝ)) (b := x) hxle hcont_Icc)
  have hxpos : (0 : ℝ) < x := lt_trans (by linarith : (0 : ℝ) < 2) hx
  have hx1 : (1 : ℝ) < x := lt_trans (by linarith : (1 : ℝ) < 2) hx
  have hcontAt_log : ContinuousAt log x := continuousAt_log (ne_of_gt hxpos)
  have hlog_ne : log x ≠ 0 := ne_of_gt (log_pos hx1)
  have hcontAt : ContinuousAt (fun t => 1 / log t) x := by
    simpa [one_div] using hcontAt_log.inv₀ hlog_ne
  have hmeas : StronglyMeasurableAtFilter (fun t => 1 / log t) (𝓝 x) := by
    have hs : IsOpen (Set.Ioi (1 : ℝ)) := isOpen_Ioi
    have hcont_on : ContinuousOn (fun t => 1 / log t) (Set.Ioi (1 : ℝ)) := by
      intro t ht
      have htpos : (0 : ℝ) < t := lt_trans (by linarith : (0 : ℝ) < 1) ht
      have hlogt : ContinuousAt log t := continuousAt_log (ne_of_gt htpos)
      have hlog_ne : log t ≠ 0 := ne_of_gt (log_pos ht)
      have hcont_inv : ContinuousAt (fun u => (log u)⁻¹) t := hlogt.inv₀ hlog_ne
      simpa [one_div] using hcont_inv.continuousWithinAt
    have hmeas_all :=
      ContinuousOn.stronglyMeasurableAtFilter (μ := volume) hs hcont_on
    exact hmeas_all x (by linarith : (1 : ℝ) < x)
  have hderiv : HasDerivAt g (1 / log x) x :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas hcontAt
  have hEq : (fun u => li u) =ᶠ[𝓝 x] g := by
    have hmem : Ioi (2 : ℝ) ∈ 𝓝 x := Ioi_mem_nhds hx
    refine (Filter.eventually_of_mem hmem ?_)
    intro u hu
    have hu_le : (2 : ℝ) ≤ u := le_of_lt hu
    simp [logarithmicIntegral, g, intervalIntegral.integral_of_le hu_le, one_div]
  exact hderiv.congr_of_eventuallyEq hEq

/-- li is continuous on (2, ∞) -/
theorem logarithmicIntegral_continuousOn : ContinuousOn li (Set.Ioi 2) := by
  intro x hx
  exact (logarithmicIntegral_hasDerivAt hx).continuousAt.continuousWithinAt

/-- The derivative of li is 1/log(x) -/
theorem logarithmicIntegral_deriv {x : ℝ} (hx : 2 < x) :
    deriv li x = 1 / log x := by
  exact (logarithmicIntegral_hasDerivAt hx).deriv

end Calculus

/-! ## Bounds -/

section Bounds

/-- Lower bound: li(x) ≥ x/log(x) - 2/log(2) for x ≥ 2 -/
theorem logarithmicIntegral_lower_bound {x : ℝ} (hx : 2 ≤ x) :
    x / log x - 2 / log 2 ≤ li x := by
  rcases lt_or_eq_of_le hx with hx' | rfl
  · exact le_of_lt (logarithmicIntegral_gt_divLog (x := x) hx')
  · simp [logarithmicIntegral_two]

/-- Upper bound: li(x) ≤ x/log(2) for x ≥ 2 -/
theorem logarithmicIntegral_upper_bound {x : ℝ} (hx : 2 ≤ x) :
    li x ≤ x / log 2 :=
  logarithmicIntegral_lt_bound hx

/-- Basic bounds for li(10). -/
theorem logarithmicIntegral_ten_bounds : 0 < li 10 ∧ li 10 ≤ 10 / log 2 := by
  refine ⟨?_, ?_⟩
  · exact logarithmicIntegral_pos (by norm_num)
  · exact logarithmicIntegral_upper_bound (by norm_num)

/-- Basic bounds for li(100). -/
theorem logarithmicIntegral_hundred_bounds : 0 < li 100 ∧ li 100 ≤ 100 / log 2 := by
  refine ⟨?_, ?_⟩
  · exact logarithmicIntegral_pos (by norm_num)
  · exact logarithmicIntegral_upper_bound (by norm_num)

end Bounds

/-! ## Relationship with Li -/

section OffsetRelation

/-- li(x) = Li(x) - Li(2) -/
theorem logarithmicIntegral_eq_offset_sub : li = fun x => Li x - offsetLogarithmicIntegralConstant := by
  ext x
  unfold offsetLogarithmicIntegral
  ring_nf

/-- Li(x) > li(x) by approximately 1.045 -/
theorem offsetLogarithmicIntegral_gt {x : ℝ} (_hx : 2 ≤ x) : li x < Li x := by
  unfold offsetLogarithmicIntegral offsetLogarithmicIntegralConstant
  linarith

end OffsetRelation

end LogarithmicIntegral
