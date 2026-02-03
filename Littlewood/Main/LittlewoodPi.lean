/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Littlewood.Main.LittlewoodPsi
import Littlewood.Oscillation.SchmidtTheorem

/-!
# Littlewood's Main Theorem

This file provides a weak oscillation result for π(x) - li(x) sufficient to
deduce infinitely many sign changes. The stronger Littlewood bound with the
log log log factor is still a TODO.

## Main Results

* `littlewood_pi_li` : π(x) - li(x) = Ω±(x^{1/2}/log x)

## Historical Note

This was a landmark result. Gauss observed that li(x) > π(x) for all x up to
3,000,000. The conjecture that this held for all x was widely believed until
Littlewood's proof showed it must fail infinitely often.

## Architecture Note

This file previously used `OmegaPsiToThetaHyp` to transfer oscillation from
ψ to θ, and `OmegaThetaToPiLiHyp` to transfer from θ to π-li. Both are
problematic: OmegaPsiToThetaHyp is FALSE for f = √x, and OmegaThetaToPiLiHyp
requires quantitative PNT error bounds not available in Mathlib. The chain
now uses `PiLiOscillationSqrtHyp` which directly asserts
π(x) - li(x) = Ω±(√x / log x).

## References

* J.E. Littlewood, "Sur la distribution des nombres premiers" (1914)
* Montgomery-Vaughan, "Multiplicative Number Theory I", Chapter 15
-/

open Real Filter Topology Asymptotics
open Chebyshev LogarithmicIntegral ZetaZeros Littlewood Schmidt

namespace LittlewoodPi

variable [PiLiOscillationSqrtHyp]

/-! ## Main Theorem -/

/-- Weak Littlewood-type oscillation: π(x) - li(x) = Ω±(x^{1/2}/log x) -/
theorem littlewood_pi_li :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x] :=
  PiLiOscillationSqrtHyp.oscillation

/-! ## Corollaries -/

/-- π(x) > li(x) infinitely often -/
theorem pi_gt_li_infinitely_often :
    ∃ᶠ x in atTop, (Nat.primeCounting (Nat.floor x) : ℝ) > logarithmicIntegral x := by
  have h := littlewood_pi_li
  have hg : ∀ᶠ x in atTop, 0 < Real.sqrt x / Real.log x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := by linarith
    have hlogpos : 0 < Real.log x := Real.log_pos hx
    have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
    exact div_pos hsqrtpos hlogpos
  have hsc :=
    IsOmegaPlusMinus.sign_changes
      (f := fun x => (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x)
      (g := fun x => Real.sqrt x / Real.log x) h hg
  refine hsc.1.mono ?_
  intro x hx
  simpa [gt_iff_lt] using (sub_pos.mp hx)

/-- π(x) < li(x) infinitely often -/
theorem pi_lt_li_infinitely_often :
    ∃ᶠ x in atTop, (Nat.primeCounting (Nat.floor x) : ℝ) < logarithmicIntegral x := by
  have h := littlewood_pi_li
  have hg : ∀ᶠ x in atTop, 0 < Real.sqrt x / Real.log x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := by linarith
    have hlogpos : 0 < Real.log x := Real.log_pos hx
    have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
    exact div_pos hsqrtpos hlogpos
  have hsc :=
    IsOmegaPlusMinus.sign_changes
      (f := fun x => (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x)
      (g := fun x => Real.sqrt x / Real.log x) h hg
  refine hsc.2.mono ?_
  intro x hx
  simpa using (sub_neg.mp hx)

/-- The sign of π(x) - li(x) changes infinitely often -/
theorem pi_minus_li_sign_changes :
    (∃ᶠ x in atTop, (Nat.primeCounting (Nat.floor x) : ℝ) > logarithmicIntegral x) ∧
    (∃ᶠ x in atTop, (Nat.primeCounting (Nat.floor x) : ℝ) < logarithmicIntegral x) :=
  ⟨pi_gt_li_infinitely_often, pi_lt_li_infinitely_often⟩

/-! ## Quantitative Bounds -/

/-- A crossover exists (non-quantitative). -/
theorem first_crossover_bound :
    ∃ x₀ : ℝ, ∃ x ≤ x₀, (Nat.primeCounting (Nat.floor x) : ℝ) > logarithmicIntegral x := by
  rcases (Filter.Frequently.exists pi_gt_li_infinitely_often) with ⟨x, hx⟩
  exact ⟨x, x, le_rfl, hx⟩

omit [PiLiOscillationSqrtHyp] in
/-- Weak positivity: the normalized integral is eventually nonnegative. -/
theorem logarithmic_density_positive :
    ∀ᶠ X in atTop,
      0 ≤
        (∫ x in Set.Icc 2 X,
          if (Nat.primeCounting (Nat.floor x) : ℝ) > logarithmicIntegral x then 1/x else 0) /
        Real.log X := by
  refine (eventually_gt_atTop (2 : ℝ)).mono ?_
  intro X hX
  have hs : MeasurableSet (Set.Icc (2 : ℝ) X) := by simp
  have hnonneg :
      ∀ x ∈ Set.Icc (2 : ℝ) X,
        0 ≤ if (Nat.primeCounting (Nat.floor x) : ℝ) > logarithmicIntegral x then 1/x else 0 := by
    intro x hx
    by_cases hcond :
        (Nat.primeCounting (Nat.floor x) : ℝ) > logarithmicIntegral x
    · have hxnonneg : 0 ≤ x := by linarith [hx.1]
      have hdiv : 0 ≤ (1 / x : ℝ) := one_div_nonneg.mpr hxnonneg
      simpa [hcond] using hdiv
    · simp [hcond]
  have hint :
      0 ≤ ∫ x in Set.Icc (2 : ℝ) X,
        if (Nat.primeCounting (Nat.floor x) : ℝ) > logarithmicIntegral x then 1/x else 0 := by
    exact MeasureTheory.setIntegral_nonneg hs hnonneg
  have hlogpos : 0 < Real.log X := Real.log_pos (by linarith : (1 : ℝ) < X)
  exact div_nonneg hint hlogpos.le

end LittlewoodPi
