import Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingPoleCancellationCompat
import Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfRectangleBoundCompat
import Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfReciprocalRectangleBoundCompat
import Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfLogDerivByZetaBoundCompat

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.DirichletNonvanishingRefactorBundle

open Complex
open Aristotle.Standalone.ExternalPort.DirichletNonvanishingPoleCancellationCompat
open Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfRectangleBoundCompat
open Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfReciprocalRectangleBoundCompat
open Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfLogDerivByZetaBoundCompat

/-- Lean-4.27 refactor surface for the Dirichlet-nonvanishing rectangle-bounds
lane (`ζ₁ = (s-1)ζ`, named `zrf` in-repo). -/
structure NonvanishingRectangleRefactorPayload : Type where
  zrfApplyOfNeOne :
    ∀ {z : ℂ}, z ≠ 1 →
      Aristotle.ZetaPoleCancellation.zrf z = (z - 1) * riemannZeta z
  zrfNonzeroOfOneOrZetaNonzero :
    ∀ {z : ℂ}, z = 1 ∨ riemannZeta z ≠ 0 →
      Aristotle.ZetaPoleCancellation.zrf z ≠ 0
  negLogDerivZrfEq :
    ∀ {z : ℂ}, z ≠ 1 → riemannZeta z ≠ 0 →
      -deriv Aristotle.ZetaPoleCancellation.zrf z /
        Aristotle.ZetaPoleCancellation.zrf z =
      -deriv riemannZeta z / riemannZeta z - 1 / (z - 1)
  continuousOnNegLogDerivZrf :
    ContinuousOn
      (fun z =>
        -deriv Aristotle.ZetaPoleCancellation.zrf z /
          Aristotle.ZetaPoleCancellation.zrf z)
      {z : ℂ | z = 1 ∨ riemannZeta z ≠ 0}
  zrfNegLogDerivBoundOnRectangleOfReGtOne :
    ∀ {z w : ℂ}, z.Rectangle w ⊆ {s : ℂ | 1 < s.re} →
      ∃ B : ℝ, ∀ s ∈ z.Rectangle w,
        ‖-deriv Aristotle.ZetaPoleCancellation.zrf s /
          Aristotle.ZetaPoleCancellation.zrf s‖ ≤ B
  zrfInvBoundOnRectangleOfReGtOne :
    ∀ {z w : ℂ}, z.Rectangle w ⊆ {s : ℂ | 1 < s.re} →
      ∃ B : ℝ, ∀ s ∈ z.Rectangle w,
        ‖(Aristotle.ZetaPoleCancellation.zrf s)⁻¹‖ ≤ B
  zrfNegLogDerivBoundViaZetaOnRectangleOfReGtOne :
    ∀ {z w : ℂ}, z.Rectangle w ⊆ {s : ℂ | 1 < s.re} →
      ∃ B : ℝ, ∀ s ∈ z.Rectangle w,
        ‖-deriv Aristotle.ZetaPoleCancellation.zrf s /
          Aristotle.ZetaPoleCancellation.zrf s‖ ≤ B

/-- Canonical payload term assembled from the current compat theorem family. -/
def fromCompat : NonvanishingRectangleRefactorPayload where
  zrfApplyOfNeOne := by
    intro z hz
    exact zrf_apply_of_ne_one_port hz
  zrfNonzeroOfOneOrZetaNonzero := by
    intro z hz
    exact zrf_nonzero_of_one_or_zeta_nonzero_port hz
  negLogDerivZrfEq := by
    intro z hz1 hzeta
    exact neg_logDeriv_zrf_eq_port hz1 hzeta
  continuousOnNegLogDerivZrf := continuousOn_neg_logDeriv_zrf_port
  zrfNegLogDerivBoundOnRectangleOfReGtOne := by
    intro z w hRect
    exact exists_norm_neg_logDeriv_zrf_bound_on_rectangle_of_re_gt_one hRect
  zrfInvBoundOnRectangleOfReGtOne := by
    intro z w hRect
    exact exists_norm_inv_zrf_bound_on_rectangle_of_re_gt_one hRect
  zrfNegLogDerivBoundViaZetaOnRectangleOfReGtOne := by
    intro z w hRect
    exact exists_norm_neg_logDeriv_zrf_bound_via_zeta_on_rectangle_of_re_gt_one hRect

/-- Readiness endpoint: reciprocal and logarithmic-derivative rectangle bounds
from one refactored nonvanishing payload. -/
theorem zrf_inv_and_neg_logDeriv_bounds_on_rectangle_of_re_gt_one_of_refactored_payload
    (hPayload : NonvanishingRectangleRefactorPayload)
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    (∃ B : ℝ, ∀ s ∈ z.Rectangle w,
      ‖(Aristotle.ZetaPoleCancellation.zrf s)⁻¹‖ ≤ B) ∧
    (∃ B : ℝ, ∀ s ∈ z.Rectangle w,
      ‖-deriv Aristotle.ZetaPoleCancellation.zrf s /
        Aristotle.ZetaPoleCancellation.zrf s‖ ≤ B) := by
  exact
    ⟨hPayload.zrfInvBoundOnRectangleOfReGtOne hRect,
      hPayload.zrfNegLogDerivBoundOnRectangleOfReGtOne hRect⟩

/-- Decomposition-style readiness endpoint for `-ζ₁'/ζ₁` from one refactored
nonvanishing payload. -/
theorem zrf_neg_logDeriv_bound_via_zeta_on_rectangle_of_re_gt_one_of_refactored_payload
    (hPayload : NonvanishingRectangleRefactorPayload)
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    ∃ B : ℝ, ∀ s ∈ z.Rectangle w,
      ‖-deriv Aristotle.ZetaPoleCancellation.zrf s /
        Aristotle.ZetaPoleCancellation.zrf s‖ ≤ B := by
  exact hPayload.zrfNegLogDerivBoundViaZetaOnRectangleOfReGtOne hRect

end Aristotle.Standalone.ExternalPort.DirichletNonvanishingRefactorBundle
