import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTRectangleHolomorphicCompat

open Complex

/-- External-port adaptation of strongpnt's `BddAboveOnRect` helper:
a holomorphic function on a closed rectangle has bounded norm-image. -/
theorem bddAbove_norm_image_rectangle_of_holomorphicOn
    {g : ℂ → ℂ} {z w : ℂ}
    (holoOn : DifferentiableOn ℂ g (z.Rectangle w)) :
    BddAbove (norm ∘ g '' (z.Rectangle w)) := by
  have hCompact : IsCompact (z.Rectangle w) := by
    apply IsCompact.reProdIm <;> apply isCompact_uIcc
  refine IsCompact.bddAbove_image hCompact ?_
  exact holoOn.continuousOn.norm

end Aristotle.Standalone.ExternalPort.StrongPNTRectangleHolomorphicCompat
