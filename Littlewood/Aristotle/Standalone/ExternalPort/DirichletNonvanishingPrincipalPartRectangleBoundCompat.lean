import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRectangleHolomorphicCompat

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.DirichletNonvanishingPrincipalPartRectangleBoundCompat

open Complex
open Aristotle.Standalone.ExternalPort.StrongPNTRectangleHolomorphicCompat

/-- Differentiability of the principal-part reciprocal `(s - 1)⁻¹` on
`Re(s) > 1`. -/
theorem differentiableOn_inv_sub_one_re_gt_one :
    DifferentiableOn ℂ (fun s : ℂ => (s - 1)⁻¹) {s : ℂ | 1 < s.re} := by
  have hSub : DifferentiableOn ℂ (fun s : ℂ => s - (1 : ℂ)) {s : ℂ | 1 < s.re} := by
    intro s _hs
    simpa using (differentiableAt_id.sub_const (1 : ℂ)).differentiableWithinAt
  exact
    DifferentiableOn.inv hSub
      (by
        intro s hs
        have hs_ne_one : s ≠ 1 := by
          intro hs1
          have : (1 : ℝ) < (1 : ℂ).re := by simpa [hs1] using hs
          norm_num at this
        exact sub_ne_zero.mpr hs_ne_one)

/-- Boundedness of `‖1/(s-1)‖` on any closed rectangle contained in `Re(s) > 1`. -/
theorem bddAbove_norm_inv_sub_one_image_rectangle_of_re_gt_one
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    BddAbove
      (norm ∘ (fun s : ℂ => (s - 1)⁻¹) '' (z.Rectangle w)) := by
  exact bddAbove_norm_image_rectangle_of_holomorphicOn
    (differentiableOn_inv_sub_one_re_gt_one.mono hRect)

/-- Pointwise bound extracted from
`bddAbove_norm_inv_sub_one_image_rectangle_of_re_gt_one`. -/
theorem exists_norm_inv_sub_one_bound_on_rectangle_of_re_gt_one
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    ∃ B : ℝ, ∀ s ∈ z.Rectangle w, ‖(s - 1)⁻¹‖ ≤ B := by
  rcases bddAbove_norm_inv_sub_one_image_rectangle_of_re_gt_one hRect with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro s hs
  exact hB ⟨s, hs, rfl⟩

end Aristotle.Standalone.ExternalPort.DirichletNonvanishingPrincipalPartRectangleBoundCompat
