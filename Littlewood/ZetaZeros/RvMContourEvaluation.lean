/-
Contour Evaluation for the Riemann-von Mangoldt Formula

This file proves that the "easy" terms in the XiLogDeriv decomposition
have vanishing contour integrals on the rectangle (-1, 2) × (1, T),
and establishes the functional equation symmetry for logDeriv(ξ).

## Proved results (0 sorry):
- `cauchy_goursat_inv_s`: ∮ 1/s ds = 0 on our rectangle
- `cauchy_goursat_inv_s_sub_one`: ∮ 1/(s-1) ds = 0
- `cauchy_goursat_const`: ∮ c ds = 0 for any constant
- `riemannXiAlt_one_sub`: ξ(1-s) = ξ(s) [functional equation]
- `logDeriv_xi_functional_eq`: logDeriv(ξ)(1-s) = -logDeriv(ξ)(s)

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.ZetaZeros.RectArgumentPrinciple
import Littlewood.Aristotle.RiemannXiEntire

set_option maxHeartbeats 3200000
set_option autoImplicit false

noncomputable section

open Complex Real Set MeasureTheory Topology Filter RectArgumentPrinciple
open scoped Real

namespace ZetaZeros.RvMContour

/-! ## Section 1: Points outside the rectangle

The rectangle (-1, 2) × (1, T) has Im ≥ 1 on its boundary and interior.
Both 0 and 1 have Im = 0 < 1, so they're outside. -/

/-- The origin is outside closedRect (-1) 2 1 T for T ≥ 1. -/
private theorem zero_not_in_closedRect (T : ℝ) (hT : 1 ≤ T) :
    (0 : ℂ) ∉ closedRect (-1) 2 1 T := by
  intro ⟨_, _, him_lo, _⟩
  simp only [Complex.zero_im] at him_lo; linarith

/-- The point 1 is outside closedRect (-1) 2 1 T for T ≥ 1. -/
private theorem one_not_in_closedRect (T : ℝ) (hT : 1 ≤ T) :
    (1 : ℂ) ∉ closedRect (-1) 2 1 T := by
  intro ⟨_, _, him_lo, _⟩
  simp only [Complex.one_im] at him_lo; linarith

/-! ## Section 2: Cauchy-Goursat for the simple terms

1/s, 1/(s-1), and constants are holomorphic on closedRect (-1) 2 1 T
(since their poles 0 and 1 are outside). -/

/-- 1/s is holomorphic on the closed rectangle. -/
private theorem diffOn_inv (T : ℝ) (hT : 1 ≤ T) :
    DifferentiableOn ℂ (fun s : ℂ => s⁻¹) (closedRect (-1) 2 1 T) := by
  apply DifferentiableOn.inv differentiableOn_id
  intro s hs heq
  exact zero_not_in_closedRect T hT (heq ▸ hs)

/-- ∮ 1/s ds = 0 on rectangle (-1,2)×(1,T). -/
theorem cauchy_goursat_inv_s (T : ℝ) (hT : 1 ≤ T) :
    contourIntegralRect (fun s : ℂ => s⁻¹) (-1) 2 1 T = 0 :=
  cauchy_goursat_rect _ _ _ _ _ (by norm_num) (by linarith) (diffOn_inv T hT)

/-- 1/(s-1) is holomorphic on the closed rectangle. -/
private theorem diffOn_inv_sub_one (T : ℝ) (hT : 1 ≤ T) :
    DifferentiableOn ℂ (fun s : ℂ => (s - 1)⁻¹) (closedRect (-1) 2 1 T) := by
  apply DifferentiableOn.inv (differentiableOn_id.sub (differentiableOn_const 1))
  intro s hs heq
  have : s = 1 := sub_eq_zero.mp heq
  exact one_not_in_closedRect T hT (this ▸ hs)

/-- ∮ 1/(s-1) ds = 0 on rectangle (-1,2)×(1,T). -/
theorem cauchy_goursat_inv_s_sub_one (T : ℝ) (hT : 1 ≤ T) :
    contourIntegralRect (fun s : ℂ => (s - 1)⁻¹) (-1) 2 1 T = 0 :=
  cauchy_goursat_rect _ _ _ _ _ (by norm_num) (by linarith) (diffOn_inv_sub_one T hT)

/-- ∮ c ds = 0 for any constant. -/
theorem cauchy_goursat_const (c : ℂ) (T : ℝ) (hT : 1 ≤ T) :
    contourIntegralRect (fun _ : ℂ => c) (-1) 2 1 T = 0 :=
  cauchy_goursat_rect _ _ _ _ _ (by norm_num) (by linarith) (differentiableOn_const c)

/-! ## Section 3: Functional equation for RiemannXiAlt

We reprove ξ(1-s) = ξ(s) here to avoid importing RiemannVonMangoldtReal. -/

/-- The functional equation: RiemannXiAlt(1-s) = RiemannXiAlt(s). -/
theorem riemannXiAlt_one_sub' (s : ℂ) : RiemannXiAlt (1 - s) = RiemannXiAlt s := by
  unfold RiemannXiAlt
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- logDeriv(ξ)(1-s) = -logDeriv(ξ)(s) for all s. -/
theorem logDeriv_xi_functional_eq (s : ℂ) :
    logDeriv RiemannXiAlt (1 - s) = -logDeriv RiemannXiAlt s := by
  simp only [logDeriv_apply]
  have h_eq : ∀ᶠ z in nhds s, RiemannXiAlt (1 - z) = RiemannXiAlt z :=
    Filter.Eventually.of_forall (fun z => riemannXiAlt_one_sub' z)
  -- deriv of (ξ ∘ (1 - ·)) at s = -deriv ξ at (1-s)
  have hd : DifferentiableAt ℂ RiemannXiAlt (1 - s) :=
    RiemannXiAlt_entire.differentiableAt
  have hcomp : deriv (fun z => RiemannXiAlt (1 - z)) s = -deriv RiemannXiAlt (1 - s) := by
    have := hd.hasDerivAt.comp s ((hasDerivAt_const s 1).sub (hasDerivAt_id s))
    simp only [Function.comp_def] at this
    rw [this.deriv]; ring
  have hderiv_eq : deriv (fun z => RiemannXiAlt (1 - z)) s = deriv RiemannXiAlt s :=
    Filter.EventuallyEq.deriv_eq h_eq
  rw [riemannXiAlt_one_sub', ← hderiv_eq, hcomp]
  ring

end ZetaZeros.RvMContour
