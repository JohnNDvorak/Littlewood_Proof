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

* `logarithmicIntegral_asymptotic` : li(x) ~ x/log(x) as x → ∞
* `logarithmicIntegral_expansion` : li(x) = x/log(x) + x/log²(x) + O(x/log³(x))

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

/-- li(x) ~ x/log(x) as x → ∞ -/
theorem logarithmicIntegral_asymptotic :
    Tendsto (fun x => li x / (x / log x)) atTop (𝓝 1) := by
  -- The main term of li(x) is x/log(x)
  sorry

/-- li(x) = x/log(x) + O(x/log²(x)) -/
theorem logarithmicIntegral_bigO_one :
    (fun x => li x - x / log x) =O[atTop] (fun x => x / (log x)^2) := by
  sorry

/-- li(x) = x/log(x) + x/log²(x) + O(x/log³(x)) -/
theorem logarithmicIntegral_bigO_two :
    (fun x => li x - x / log x - x / (log x)^2) =O[atTop] (fun x => x / (log x)^3) := by
  sorry

/-- Full asymptotic expansion: li(x) = x ∑_{k=0}^{n-1} k!/log^{k+1}(x) + O(n! x/log^{n+1}(x)) -/
theorem logarithmicIntegral_expansion (n : ℕ) :
    (fun x => li x - x * ∑ k ∈ Finset.range n, k.factorial / (log x)^(k+1))
    =O[atTop] (fun x => n.factorial * x / (log x)^(n+1)) := by
  sorry

end Asymptotics

/-! ## Comparison with x/log(x) -/

section Comparison

/-- li(x) > x/log(x) for x > 1 -/
theorem logarithmicIntegral_gt_divLog {x : ℝ} (hx : ℯ < x) :
    x / log x < li x := by
  sorry

/-- li(x) < x/log(x) + 2x/log²(x) for sufficiently large x -/
theorem logarithmicIntegral_lt_bound :
    ∀ᶠ x in atTop, li x < x / log x + 2 * x / (log x)^2 := by
  sorry

/-- li(x) - x/log(x) → ∞ as x → ∞ -/
theorem logarithmicIntegral_sub_divLog_tendsto :
    Tendsto (fun x => li x - x / log x) atTop atTop := by
  sorry

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

/-- Lower bound: li(x) ≥ x/log(x) for x ≥ e -/
theorem logarithmicIntegral_lower_bound {x : ℝ} (hx : exp 1 ≤ x) :
    x / log x ≤ li x := by
  sorry

/-- Upper bound: li(x) ≤ x/log(x) + 1.5 x/log²(x) for x ≥ e² -/
theorem logarithmicIntegral_upper_bound {x : ℝ} (hx : exp 2 ≤ x) :
    li x ≤ x / log x + 3/2 * x / (log x)^2 := by
  sorry

/-- li(10) ≈ 6.1655... -/
theorem logarithmicIntegral_ten_bounds : 6 < li 10 ∧ li 10 < 7 := by
  sorry

/-- li(100) ≈ 30.126... -/
theorem logarithmicIntegral_hundred_bounds : 30 < li 100 ∧ li 100 < 31 := by
  sorry

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
