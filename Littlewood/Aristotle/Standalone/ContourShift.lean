/-
# Contour Shift Identity via Cauchy-Goursat

We derive the contour shift identity from Mathlib's
`integral_boundary_rect_eq_zero_of_differentiableOn` (Cauchy-Goursat theorem for rectangles).

For a function holomorphic on a closed rectangle with vertices
  (-U - iT), (c - iT), (c + iT), (-U + iT),
the sum of boundary integrals vanishes, and rearranging gives:
  right-edge integral = left-edge integral + top contribution - bottom contribution.

We then apply this to the function s ↦ x^s / s, which is holomorphic away from s = 0.
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Complex MeasureTheory intervalIntegral TopologicalSpace Set Filter
open scoped Real NNReal

noncomputable section

/-! ## General Cauchy-Goursat for the rectangle -/

/-- **Cauchy-Goursat for the rectangle.**
For `f : ℂ → ℂ` holomorphic on the closed rectangle `[-U, c] × [-T, T]`,
the boundary integral vanishes:
  (bottom) - (top) + I·(right) - I·(left) = 0.
This is a direct application of `integral_boundary_rect_eq_zero_of_differentiableOn`. -/
theorem rectangle_boundary_integral_eq_zero (f : ℂ → ℂ) (c U T : ℝ)
    (hf : DifferentiableOn ℂ f (uIcc (-U) c ×ℂ uIcc (-T) T)) :
    (∫ x in (-U)..c, f (↑x + ↑(-T) * I)) - (∫ x in (-U)..c, f (↑x + ↑T * I)) +
      (I * ∫ y in (-T)..T, f (↑c + ↑y * I)) -
      (I * ∫ y in (-T)..T, f (↑(-U) + ↑y * I)) = 0 := by
  have h := integral_boundary_rect_eq_zero_of_differentiableOn f ⟨-U, -T⟩ ⟨c, T⟩ hf
  simp only [smul_eq_mul] at h
  exact h

/-- **Contour shift identity (general).**
For `f : ℂ → ℂ` holomorphic on the closed rectangle `[-U, c] × [-T, T]`,
the right-edge contour integral equals the left-edge contour integral plus
horizontal boundary contributions:

  I · ∫_{-T}^{T} f(c + iy) dy = I · ∫_{-T}^{T} f(-U + iy) dy
                                  + ∫_{-U}^{c} f(x + iT) dx
                                  - ∫_{-U}^{c} f(x - iT) dx
-/
theorem contour_shift_rect (f : ℂ → ℂ) (c U T : ℝ)
    (hf : DifferentiableOn ℂ f (uIcc (-U) c ×ℂ uIcc (-T) T)) :
    (I * ∫ y in (-T)..T, f (↑c + ↑y * I)) =
    (I * ∫ y in (-T)..T, f (↑(-U) + ↑y * I)) +
    (∫ x in (-U)..c, f (↑x + ↑T * I)) -
    (∫ x in (-U)..c, f (↑x + ↑(-T) * I)) := by
  have key := integral_boundary_rect_eq_zero_of_differentiableOn f ⟨-U, -T⟩ ⟨c, T⟩ hf
  simp only [smul_eq_mul] at key
  rw [eq_comm, ← sub_eq_zero]
  rw [show (I * ∫ y in (-T)..T, f (↑(-U) + ↑y * I)) +
    (∫ x in (-U)..c, f (↑x + ↑T * I)) -
    (∫ x in (-U)..c, f (↑x + ↑(-T) * I)) -
    (I * ∫ y in (-T)..T, f (↑c + ↑y * I)) =
    -((((∫ x in (-U)..c, f (↑x + ↑(-T) * I)) - ∫ x in (-U)..c, f (↑x + ↑T * I)) +
        I * ∫ y in (-T)..T, f (↑c + ↑y * I)) -
      I * ∫ y in (-T)..T, f (↑(-U) + ↑y * I)) from by ring]
  rw [key, neg_zero]

/-! ## Differentiability of s ↦ x^s / s -/

/-- For `x > 0`, the function `s ↦ (x : ℂ)^s` is entire (differentiable everywhere). -/
theorem differentiable_cpow_ofReal (x : ℝ) (hx : 0 < x) :
    Differentiable ℂ (fun s : ℂ => (↑x : ℂ) ^ s) := by
  intro s
  apply DifferentiableAt.const_cpow differentiableAt_id
  left; simp; exact_mod_cast hx.ne'

/-- For `x > 0` and `s ≠ 0`, the function `s ↦ (x : ℂ)^s / s` is complex differentiable
at `s`. -/
theorem differentiableAt_cpow_div_id {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (fun s => (↑x : ℂ) ^ s / s) s := by
  apply DifferentiableAt.div
  · exact (differentiable_cpow_ofReal x hx).differentiableAt
  · exact differentiableAt_id
  · exact hs

/-- For `x > 0`, the function `s ↦ (x : ℂ)^s / s` is differentiable on any set not
containing `0`. -/
theorem differentiableOn_cpow_div_id {x : ℝ} (hx : 0 < x) {S : Set ℂ} (hS : (0 : ℂ) ∉ S) :
    DifferentiableOn ℂ (fun s => (↑x : ℂ) ^ s / s) S := by
  intro s hs
  exact (differentiableAt_cpow_div_id hx (ne_of_mem_of_not_mem hs hS)).differentiableWithinAt

/-! ## Contour shift for x^s / s -/

/-- **Contour shift for `x^s / s`.**
For `c > 0`, `T > 0`, `U > 0`, `x > 0`, assuming `s ↦ x^s/s` is holomorphic on the closed
rectangle (which holds when the rectangle avoids `s = 0`), the right-edge vertical contour
integral equals the left-edge integral plus horizontal contributions:

  I · ∫_{-T}^{T} x^{c+iy}/(c+iy) dy = I · ∫_{-T}^{T} x^{-U+iy}/(-U+iy) dy
                                         + ∫_{-U}^{c} x^{t+iT}/(t+iT) dt
                                         - ∫_{-U}^{c} x^{t-iT}/(t-iT) dt
-/
theorem contour_shift_cpow_div (c U T x : ℝ) (_hc : 0 < c) (_hU : 0 < U) (_hT : 0 < T)
    (_hx : 0 < x)
    (hf : DifferentiableOn ℂ (fun s => (↑x : ℂ) ^ s / s) (uIcc (-U) c ×ℂ uIcc (-T) T)) :
    (I * ∫ y in (-T)..T, (↑x : ℂ) ^ (↑c + ↑y * I) / (↑c + ↑y * I)) =
    (I * ∫ y in (-T)..T, (↑x : ℂ) ^ (↑(-U) + ↑y * I) / (↑(-U) + ↑y * I)) +
    (∫ t in (-U)..c, (↑x : ℂ) ^ (↑t + ↑T * I) / (↑t + ↑T * I)) -
    (∫ t in (-U)..c, (↑x : ℂ) ^ (↑t + ↑(-T) * I) / (↑t + ↑(-T) * I)) :=
  contour_shift_rect _ c U T hf

/-- **Contour shift for `x^s/s` on a rectangle with positive real parts.**
When `0 < a ≤ b`, the rectangle `[a, b] × [-T, T]` avoids `s = 0`,
so the differentiability hypothesis is automatically verified and
the contour shift identity holds unconditionally. -/
theorem contour_shift_cpow_div_pos_real {a b T x : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (_hT : 0 < T) (hx : 0 < x) :
    (I * ∫ y in (-T)..T, (↑x : ℂ) ^ (↑b + ↑y * I) / (↑b + ↑y * I)) =
    (I * ∫ y in (-T)..T, (↑x : ℂ) ^ (↑a + ↑y * I) / (↑a + ↑y * I)) +
    (∫ t in a..b, (↑x : ℂ) ^ (↑t + ↑T * I) / (↑t + ↑T * I)) -
    (∫ t in a..b, (↑x : ℂ) ^ (↑t + ↑(-T) * I) / (↑t + ↑(-T) * I)) := by
  have hmem : (0 : ℂ) ∉ (uIcc a b ×ℂ uIcc (-T) T) := by
    simp only [mem_reProdIm, zero_re, zero_im, uIcc_of_le hab, mem_Icc]
    intro ⟨h1, _⟩
    linarith [h1.1]
  have hf : DifferentiableOn ℂ (fun s => (↑x : ℂ) ^ s / s) (uIcc a b ×ℂ uIcc (-T) T) :=
    differentiableOn_cpow_div_id hx hmem
  have key := integral_boundary_rect_eq_zero_of_differentiableOn
    (fun s => (↑x : ℂ) ^ s / s) ⟨a, -T⟩ ⟨b, T⟩ hf
  simp only [smul_eq_mul] at key
  rw [eq_comm, ← sub_eq_zero]
  rw [show (I * ∫ y in (-T)..T, (↑x : ℂ) ^ (↑a + ↑y * I) / (↑a + ↑y * I)) +
    (∫ t in a..b, (↑x : ℂ) ^ (↑t + ↑T * I) / (↑t + ↑T * I)) -
    (∫ t in a..b, (↑x : ℂ) ^ (↑t + ↑(-T) * I) / (↑t + ↑(-T) * I)) -
    (I * ∫ y in (-T)..T, (↑x : ℂ) ^ (↑b + ↑y * I) / (↑b + ↑y * I)) =
    -((((∫ t in a..b, (↑x : ℂ) ^ (↑t + ↑(-T) * I) / (↑t + ↑(-T) * I)) -
        ∫ t in a..b, (↑x : ℂ) ^ (↑t + ↑T * I) / (↑t + ↑T * I)) +
       I * ∫ y in (-T)..T, (↑x : ℂ) ^ (↑b + ↑y * I) / (↑b + ↑y * I)) -
      I * ∫ y in (-T)..T, (↑x : ℂ) ^ (↑a + ↑y * I) / (↑a + ↑y * I)) from by ring]
  rw [key, neg_zero]

end
