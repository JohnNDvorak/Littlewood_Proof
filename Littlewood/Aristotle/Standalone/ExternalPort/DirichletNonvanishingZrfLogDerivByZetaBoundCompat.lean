import Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingPoleCancellationCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTLogDerivativeRectangleBoundCompat
import Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingPrincipalPartRectangleBoundCompat

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfLogDerivByZetaBoundCompat

open Complex
open Aristotle.Standalone.ExternalPort.DirichletNonvanishingPoleCancellationCompat
open Aristotle.Standalone.ExternalPort.StrongPNTLogDerivativeRectangleBoundCompat
open Aristotle.Standalone.ExternalPort.DirichletNonvanishingPrincipalPartRectangleBoundCompat

/-- Decomposition-style rectangle bound for `-ζ₁'/ζ₁` on `Re(s) > 1`
obtained from:
1. a rectangle bound on `-ζ'/ζ`, and
2. a rectangle bound on the principal part `1/(s-1)`,
using `-ζ₁'/ζ₁ = -ζ'/ζ - 1/(s-1)` (`ζ₁ = (s-1)ζ`, called `zrf` in-repo). -/
theorem exists_norm_neg_logDeriv_zrf_bound_via_zeta_on_rectangle_of_re_gt_one
    {z w : ℂ}
    (hRect : z.Rectangle w ⊆ {s : ℂ | 1 < s.re}) :
    ∃ B : ℝ, ∀ s ∈ z.Rectangle w,
      ‖-deriv Aristotle.ZetaPoleCancellation.zrf s /
        Aristotle.ZetaPoleCancellation.zrf s‖ ≤ B := by
  rcases exists_norm_neg_logDeriv_bound_on_rectangle_of_re_gt_one hRect with ⟨Bζ, hBζ⟩
  rcases exists_norm_inv_sub_one_bound_on_rectangle_of_re_gt_one hRect with ⟨Bp, hBp⟩
  refine ⟨Bζ + Bp, ?_⟩
  intro s hs
  have hs_re_gt_one : 1 < s.re := hRect hs
  have hs_ne_one : s ≠ 1 := by
    intro hs1
    have : (1 : ℝ) < (1 : ℂ).re := by simpa [hs1] using hs_re_gt_one
    norm_num at this
  have hs_zeta_ne : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (le_of_lt hs_re_gt_one)
  calc
    ‖-deriv Aristotle.ZetaPoleCancellation.zrf s / Aristotle.ZetaPoleCancellation.zrf s‖
        = ‖-deriv riemannZeta s / riemannZeta s - 1 / (s - 1)‖ := by
            rw [neg_logDeriv_zrf_eq_port hs_ne_one hs_zeta_ne]
    _ ≤ ‖-deriv riemannZeta s / riemannZeta s‖ + ‖1 / (s - 1)‖ := norm_sub_le _ _
    _ ≤ Bζ + Bp := by
      refine add_le_add (hBζ s hs) ?_
      simpa [one_div] using hBp s hs

end Aristotle.Standalone.ExternalPort.DirichletNonvanishingZrfLogDerivByZetaBoundCompat
