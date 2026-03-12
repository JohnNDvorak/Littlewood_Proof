import Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingPoleCancellationCompat

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfRectangleBoundCompat

open Complex
open Aristotle.Standalone.ExternalPort.DirichletNonvanishingPoleCancellationCompat

/-- Boundedness of `‖-ζ₁'/ζ₁‖` on a closed rectangle contained in the nonvanishing
domain `{z | z = 1 ∨ ζ z ≠ 0}` (`ζ₁ = (s-1)ζ`, called `zrf` in-repo). -/
theorem bddAbove_norm_neg_logDeriv_zrf_image_rectangle_of_one_or_zeta_nonzero
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | s = 1 ∨ riemannZeta s ≠ 0}) :
    BddAbove
      (norm ∘
        (fun s : ℂ =>
          -deriv Aristotle.ZetaPoleCancellation.zrf s /
            Aristotle.ZetaPoleCancellation.zrf s) '' (z.Rectangle w)) := by
  have hCompact : IsCompact (z.Rectangle w) := by
    apply IsCompact.reProdIm <;> apply isCompact_uIcc
  have hCont :
      ContinuousOn
        (fun s : ℂ =>
          -deriv Aristotle.ZetaPoleCancellation.zrf s /
            Aristotle.ZetaPoleCancellation.zrf s)
        (z.Rectangle w) := by
    simpa using (continuousOn_neg_logDeriv_zrf_port.mono hRect)
  exact IsCompact.bddAbove_image hCompact hCont.norm

/-- Pointwise bound extracted from
`bddAbove_norm_neg_logDeriv_zrf_image_rectangle_of_one_or_zeta_nonzero`. -/
theorem exists_norm_neg_logDeriv_zrf_bound_on_rectangle_of_one_or_zeta_nonzero
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | s = 1 ∨ riemannZeta s ≠ 0}) :
    ∃ B : ℝ, ∀ s ∈ z.Rectangle w,
      ‖-deriv Aristotle.ZetaPoleCancellation.zrf s /
        Aristotle.ZetaPoleCancellation.zrf s‖ ≤ B := by
  rcases
    bddAbove_norm_neg_logDeriv_zrf_image_rectangle_of_one_or_zeta_nonzero hRect with
      ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro s hs
  exact hB ⟨s, hs, rfl⟩

/-- Specialized endpoint on rectangles in the right half-plane `Re(s) > 1`. -/
theorem exists_norm_neg_logDeriv_zrf_bound_on_rectangle_of_re_gt_one
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    ∃ B : ℝ, ∀ s ∈ z.Rectangle w,
      ‖-deriv Aristotle.ZetaPoleCancellation.zrf s /
        Aristotle.ZetaPoleCancellation.zrf s‖ ≤ B := by
  have hOneOrNonzero : z.Rectangle w ⊆ {s : ℂ | s = 1 ∨ riemannZeta s ≠ 0} := by
    intro s hs
    exact Or.inr (riemannZeta_ne_zero_of_one_le_re (le_of_lt (hRect hs)))
  exact exists_norm_neg_logDeriv_zrf_bound_on_rectangle_of_one_or_zeta_nonzero hOneOrNonzero

end Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfRectangleBoundCompat
