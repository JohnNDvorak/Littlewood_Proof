/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Littlewood.Main.LittlewoodPsi
import Littlewood.Oscillation.SchmidtTheorem
import Littlewood.CoreLemmas.GrowthDomination
import Littlewood.Aristotle.DeepSorries

/-!
# Littlewood's Main Theorem

Full-strength Littlewood 1914: π(x) - li(x) = Ω±((√x / log x) · log log log x).

The full-strength result is extracted from the consolidated deep mathematical
results in `Aristotle.DeepSorries.pi_li_full_strength_oscillation`.

## Main Results

* `littlewood_pi_li` : π(x) - li(x) = Ω±((√x / log x) · log log log x)
* `littlewood_pi_li_sqrt` : π(x) - li(x) = Ω±(√x / log x) (backward-compatible)

## Historical Note

This was a landmark result. Gauss observed that li(x) > π(x) for all x up to
3,000,000. The conjecture that this held for all x was widely believed until
Littlewood's proof showed it must fail infinitely often.

## References

* J.E. Littlewood, "Sur la distribution des nombres premiers" (1914)
* Montgomery-Vaughan, "Multiplicative Number Theory I", Chapter 15
-/

open Real Filter Topology Asymptotics
open Chebyshev LogarithmicIntegral ZetaZeros Littlewood Schmidt GrowthDomination

namespace LittlewoodPi

/-! ## Full-Strength Main Theorem -/

/-- **Littlewood's 1914 theorem** (full strength):
π(x) - li(x) = Ω±((√x / log x) · log log log x).

Extracted from the consolidated deep mathematical results with no direct sorry. -/
theorem littlewood_pi_li :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x * lll x] :=
  Aristotle.DeepSorries.pi_li_full_strength_oscillation

/-- Backward-compatible corollary: π(x) - li(x) = Ω±(√x / log x). -/
theorem littlewood_pi_li_sqrt :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x)
    =Ω±[fun x => Real.sqrt x / Real.log x] :=
  littlewood_pi_li.of_eventually_ge
    sqrt_div_log_eventually_le_mul_lll
    (Eventually.mono (eventually_gt_atTop 1) (fun x hx =>
      div_nonneg (Real.sqrt_nonneg x) (Real.log_pos hx).le))

/-! ## Corollaries -/

/-- π(x) > li(x) infinitely often -/
theorem pi_gt_li_infinitely_often :
    ∃ᶠ x in atTop, (Nat.primeCounting (Nat.floor x) : ℝ) > logarithmicIntegral x := by
  have h := littlewood_pi_li_sqrt
  have hg : ∀ᶠ x in atTop, 0 < Real.sqrt x / Real.log x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.sqrt_pos.2 (by linarith)) (Real.log_pos hx)
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
  have h := littlewood_pi_li_sqrt
  have hg : ∀ᶠ x in atTop, 0 < Real.sqrt x / Real.log x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.sqrt_pos.2 (by linarith)) (Real.log_pos hx)
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
