import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRectangleHolomorphicCompat

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTZetaRectangleBoundCompat

open Complex
open Aristotle.Standalone.ExternalPort.StrongPNTRectangleHolomorphicCompat

/-- `ζ` is differentiable on the right half-plane `Re(s) > 1`. -/
theorem differentiableOn_riemannZeta_re_gt_one :
    DifferentiableOn ℂ riemannZeta {s : ℂ | 1 < s.re} := by
  intro s hs
  have hs_ne_one : s ≠ 1 := by
    intro hs1
    have : (1 : ℝ) < (1 : ℂ).re := by simpa [hs1] using hs
    norm_num at this
  exact (differentiableAt_riemannZeta hs_ne_one).differentiableWithinAt

/-- `1 / ζ` is differentiable on `Re(s) > 1`. -/
theorem differentiableOn_inv_riemannZeta_re_gt_one :
    DifferentiableOn ℂ (fun s : ℂ => (riemannZeta s)⁻¹) {s : ℂ | 1 < s.re} :=
  DifferentiableOn.inv
    differentiableOn_riemannZeta_re_gt_one
    (by
      intro s hs
      exact riemannZeta_ne_zero_of_one_le_re (le_of_lt hs))

/-- Boundedness of `‖ζ‖` on a closed rectangle inside `Re(s) > 1`. -/
theorem bddAbove_norm_riemannZeta_image_rectangle_of_re_gt_one
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    BddAbove (norm ∘ riemannZeta '' (z.Rectangle w)) := by
  exact bddAbove_norm_image_rectangle_of_holomorphicOn
    (differentiableOn_riemannZeta_re_gt_one.mono hRect)

/-- Pointwise bound for `‖ζ‖` on a closed rectangle inside `Re(s) > 1`. -/
theorem exists_norm_riemannZeta_bound_on_rectangle_of_re_gt_one
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    ∃ B : ℝ, ∀ s ∈ z.Rectangle w, ‖riemannZeta s‖ ≤ B := by
  rcases bddAbove_norm_riemannZeta_image_rectangle_of_re_gt_one hRect with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro s hs
  exact hB ⟨s, hs, rfl⟩

/-- Boundedness of `‖1/ζ‖` on a closed rectangle inside `Re(s) > 1`. -/
theorem bddAbove_norm_inv_riemannZeta_image_rectangle_of_re_gt_one
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    BddAbove (norm ∘ (fun s : ℂ => (riemannZeta s)⁻¹) '' (z.Rectangle w)) := by
  exact bddAbove_norm_image_rectangle_of_holomorphicOn
    (differentiableOn_inv_riemannZeta_re_gt_one.mono hRect)

/-- Pointwise bound for `‖1/ζ‖` on a closed rectangle inside `Re(s) > 1`. -/
theorem exists_norm_inv_riemannZeta_bound_on_rectangle_of_re_gt_one
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    ∃ B : ℝ, ∀ s ∈ z.Rectangle w, ‖(riemannZeta s)⁻¹‖ ≤ B := by
  rcases bddAbove_norm_inv_riemannZeta_image_rectangle_of_re_gt_one hRect with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro s hs
  exact hB ⟨s, hs, rfl⟩

end Aristotle.Standalone.ExternalPort.StrongPNTZetaRectangleBoundCompat
