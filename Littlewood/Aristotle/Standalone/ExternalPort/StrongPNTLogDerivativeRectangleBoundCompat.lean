import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTLogDerivativeHolomorphicCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRectangleHolomorphicCompat

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTLogDerivativeRectangleBoundCompat

open Complex
open Aristotle.Standalone.ExternalPort.StrongPNTLogDerivativeHolomorphicCompat
open Aristotle.Standalone.ExternalPort.StrongPNTRectangleHolomorphicCompat

/-- External-port specialization of strongpnt rectangle boundedness:
`‖-ζ'/ζ‖` is bounded on any closed rectangle contained in `Re(s) > 1`. -/
theorem bddAbove_norm_neg_logDeriv_image_rectangle_of_re_gt_one
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    BddAbove
      (norm ∘ (fun s : ℂ => -deriv riemannZeta s / riemannZeta s) '' (z.Rectangle w)) := by
  have hDiffRect :
      DifferentiableOn ℂ (fun s : ℂ => -deriv riemannZeta s / riemannZeta s) (z.Rectangle w) := by
    intro s hs
    exact
      (differentiableOn_neg_logDeriv_riemannZeta_re_gt_one s (hRect hs)).mono hRect
  exact bddAbove_norm_image_rectangle_of_holomorphicOn hDiffRect

/-- Pointwise bound extracted from
`bddAbove_norm_neg_logDeriv_image_rectangle_of_re_gt_one`. -/
theorem exists_norm_neg_logDeriv_bound_on_rectangle_of_re_gt_one
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    ∃ B : ℝ, ∀ s ∈ z.Rectangle w, ‖-deriv riemannZeta s / riemannZeta s‖ ≤ B := by
  rcases bddAbove_norm_neg_logDeriv_image_rectangle_of_re_gt_one hRect with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro s hs
  exact hB ⟨s, hs, rfl⟩

end Aristotle.Standalone.ExternalPort.StrongPNTLogDerivativeRectangleBoundCompat
