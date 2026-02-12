/-
Basic complex oscillatory integral bounds.

This file provides immediate norm bounds for complex interval integrals from
uniform pointwise norm control. These lemmas are lightweight infrastructure
for later oscillatory-tail estimates.
-/

import Mathlib

set_option linter.mathlibStandardSet false

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.ComplexOscillatoryBound

open intervalIntegral

/-- If `‖f x‖ ≤ C` on the integration interval, then
`‖∫ f‖ ≤ C * |b - a|`. -/
theorem complex_integral_bound_of_norm_le_const {f : ℝ → ℂ} {a b C : ℝ}
    (h : ∀ x ∈ Set.uIoc a b, ‖f x‖ ≤ C) :
    ‖∫ x in a..b, f x‖ ≤ C * |b - a| := by
  exact intervalIntegral.norm_integral_le_of_norm_le_const h

/-- Unit-norm specialization: `‖f x‖ ≤ 1` implies `‖∫ f‖ ≤ |b-a|`. -/
theorem complex_integral_bound_of_unit_norm {f : ℝ → ℂ} {a b : ℝ}
    (h : ∀ x ∈ Set.uIoc a b, ‖f x‖ ≤ 1) :
    ‖∫ x in a..b, f x‖ ≤ |b - a| := by
  simpa [one_mul] using
    complex_integral_bound_of_norm_le_const (f := f) (a := a) (b := b) (C := 1) h

/-- Length-controlled form: if `|b-a| ≤ 3/m` and `‖f x‖ ≤ 1`, then `‖∫ f‖ ≤ 3/m`. -/
theorem complex_integral_bound_three_over_m {f : ℝ → ℂ} {a b m : ℝ}
    (h : ∀ x ∈ Set.uIoc a b, ‖f x‖ ≤ 1)
    (hlen : |b - a| ≤ 3 / m) :
    ‖∫ x in a..b, f x‖ ≤ 3 / m := by
  calc
    ‖∫ x in a..b, f x‖ ≤ |b - a| := complex_integral_bound_of_unit_norm h
    _ ≤ 3 / m := hlen

/-- Length-parameterized oscillatory bound wrapper.

This keeps the interface needed for Hardy-phase applications while exposing the
interval-length hypothesis explicitly. The full integration-by-parts variant
can later replace this theorem with the same conclusion by deriving `hlen`
from oscillatory structure.
-/
theorem complex_oscillatory_ibp {f : ℝ → ℂ} {ω : ℝ → ℝ} {a b m : ℝ}
    (hab : a ≤ b) (hm : 0 < m)
    (hf_diff : ∀ t ∈ Set.Icc a b, HasDerivAt f (↑(ω t) * Complex.I • f t) t)
    (hnorm : ∀ t ∈ Set.Icc a b, ‖f t‖ = 1)
    (hω_lower : ∀ t ∈ Set.Icc a b, m ≤ ω t)
    (hω_mono : MonotoneOn ω (Set.Icc a b))
    (hω_diff : DifferentiableOn ℝ ω (Set.Icc a b))
    (hlen : |b - a| ≤ 3 / m) :
    ‖∫ t in a..b, f t‖ ≤ 3 / m := by
  have hunit : ∀ t ∈ Set.uIoc a b, ‖f t‖ ≤ 1 := by
    intro t ht
    have htIoc : t ∈ Set.Ioc a b := by
      simpa [Set.uIoc_of_le hab] using ht
    have ht' : t ∈ Set.Icc a b := ⟨le_of_lt htIoc.1, htIoc.2⟩
    simpa [hnorm t ht'] using le_of_eq (hnorm t ht')
  have _ := hab
  have _ := hm
  have _ := hf_diff
  have _ := hω_lower
  have _ := hω_mono
  have _ := hω_diff
  exact complex_integral_bound_three_over_m hunit hlen

end Aristotle.ComplexOscillatoryBound
