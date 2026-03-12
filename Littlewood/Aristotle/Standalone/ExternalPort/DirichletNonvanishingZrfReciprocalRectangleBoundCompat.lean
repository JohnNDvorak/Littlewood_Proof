import Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingPoleCancellationCompat

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfReciprocalRectangleBoundCompat

open Complex
open Aristotle.Standalone.ExternalPort.DirichletNonvanishingPoleCancellationCompat

/-- Continuity of `1/ζ₁` on the nonvanishing set `{z | z = 1 ∨ ζ z ≠ 0}`
(`ζ₁ = (s-1)ζ`, called `zrf` in-repo). -/
theorem continuousOn_inv_zrf_on_one_or_zeta_nonzero :
    ContinuousOn
      (fun s : ℂ => (Aristotle.ZetaPoleCancellation.zrf s)⁻¹)
      {s : ℂ | s = 1 ∨ riemannZeta s ≠ 0} := by
  have hzrf_differentiable : Differentiable ℂ Aristotle.ZetaPoleCancellation.zrf :=
    fun s => (Aristotle.ZetaPoleCancellation.zrf_analyticAt s).differentiableAt
  refine hzrf_differentiable.continuous.continuousOn.inv₀ ?_
  intro s hs
  exact zrf_nonzero_of_one_or_zeta_nonzero_port (by simpa using hs)

/-- Boundedness of `‖1/ζ₁‖` on any closed rectangle contained in the nonvanishing
domain `{z | z = 1 ∨ ζ z ≠ 0}`. -/
theorem bddAbove_norm_inv_zrf_image_rectangle_of_one_or_zeta_nonzero
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | s = 1 ∨ riemannZeta s ≠ 0}) :
    BddAbove
      (norm ∘
        (fun s : ℂ => (Aristotle.ZetaPoleCancellation.zrf s)⁻¹)
          '' (z.Rectangle w)) := by
  have hCompact : IsCompact (z.Rectangle w) := by
    apply IsCompact.reProdIm <;> apply isCompact_uIcc
  have hCont :
      ContinuousOn
        (fun s : ℂ => (Aristotle.ZetaPoleCancellation.zrf s)⁻¹)
        (z.Rectangle w) := by
    exact (continuousOn_inv_zrf_on_one_or_zeta_nonzero.mono hRect)
  exact IsCompact.bddAbove_image hCompact hCont.norm

/-- Pointwise bound extracted from
`bddAbove_norm_inv_zrf_image_rectangle_of_one_or_zeta_nonzero`. -/
theorem exists_norm_inv_zrf_bound_on_rectangle_of_one_or_zeta_nonzero
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | s = 1 ∨ riemannZeta s ≠ 0}) :
    ∃ B : ℝ, ∀ s ∈ z.Rectangle w,
      ‖(Aristotle.ZetaPoleCancellation.zrf s)⁻¹‖ ≤ B := by
  rcases
    bddAbove_norm_inv_zrf_image_rectangle_of_one_or_zeta_nonzero hRect with
      ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro s hs
  exact hB ⟨s, hs, rfl⟩

/-- Specialized endpoint on rectangles in the right half-plane `Re(s) > 1`. -/
theorem exists_norm_inv_zrf_bound_on_rectangle_of_re_gt_one
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    ∃ B : ℝ, ∀ s ∈ z.Rectangle w,
      ‖(Aristotle.ZetaPoleCancellation.zrf s)⁻¹‖ ≤ B := by
  have hOneOrNonzero : z.Rectangle w ⊆ {s : ℂ | s = 1 ∨ riemannZeta s ≠ 0} := by
    intro s hs
    exact Or.inr (riemannZeta_ne_zero_of_one_le_re (le_of_lt (hRect hs)))
  exact exists_norm_inv_zrf_bound_on_rectangle_of_one_or_zeta_nonzero hOneOrNonzero

end Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfReciprocalRectangleBoundCompat
