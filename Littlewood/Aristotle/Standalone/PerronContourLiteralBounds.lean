import Littlewood.Development.ShiftedRemainderInterface

/-!
Retired literal contour pieces for the old A5 Perron lane.

This module is intentionally not on the active `AnalyticAxioms` path. The
literal contour pieces below correspond to:

- the full left edge on `Re(s) = 1/2`,
- the top-minus-bottom horizontal segment on `Re(s) ∈ [1/2, 2]`.

Those are mathematically natural rectangle pieces, but they are not the right
support surface for the current large-`T` interface in
`ShiftedRemainderInterface`:

- the full left edge only carries the honest scale `O(√x · (log T)^3)` after
  splitting off the compact core `|t| ≤ 2`;
- the horizontal top-minus-bottom piece naturally carries the scale
  `O(x^2 · (log T)^2 / T)`.

The active A5 seam therefore works instead with the smaller support cone

- `ShiftedRemainderContourDecompLargeTHyp`,
- `ShiftedRemainderContourVertBoundFromLogDerivLargeTHyp`,
- `ShiftedRemainderContourHorizBoundFromLogDerivLargeTHyp`,

and uses proxy pieces rather than these literal segments.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.PerronContourLiteralBounds

open Littlewood.Development.ShiftedRemainderInterface

/-- Fixed left edge of the literal large-`T` Perron rectangle. -/
def sigmaLeft : ℝ := (1 / 2 : ℝ)

/-- Fixed right edge of the literal large-`T` Perron rectangle. -/
def sigmaRight : ℝ := 2

/-- Standard Perron prefactor `(2πi)⁻¹`. -/
def perronPrefactor : ℂ := (2 * Real.pi * Complex.I)⁻¹

/-- The full Perron integrand `-(ζ'/ζ)(s) x^s / s`. -/
def perronIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  (-deriv riemannZeta s / riemannZeta s) * (((x : ℂ) ^ s) / s)

/-- The literal left-vertical contour integrand on `Re(s)=1/2`. -/
def verticalIntegrand (x _T t : ℝ) : ℂ :=
  perronPrefactor * perronIntegrand x (sigmaLeft + t * Complex.I) * Complex.I

/-- The literal combined top-minus-bottom horizontal contour integrand on
`Re(s) ∈ [1/2, 2]`. -/
def horizontalIntegrand (x T σ : ℝ) : ℂ :=
  perronPrefactor *
    (perronIntegrand x (σ + T * Complex.I) -
      perronIntegrand x (σ + (-T) * Complex.I))

/-- The literal full left-edge contour contribution. -/
def verticalPiece (x T : ℝ) : ℂ :=
  ∫ t in (-T)..T, verticalIntegrand x T t

/-- The literal combined horizontal contour contribution. -/
def horizontalPiece (x T : ℝ) : ℂ :=
  ∫ σ in sigmaLeft..sigmaRight, horizontalIntegrand x T σ

/-- The literal horizontal segment has geometric length `3/2`. -/
theorem sigmaRight_sub_sigmaLeft :
    sigmaRight - sigmaLeft = (3 / 2 : ℝ) := by
  norm_num [sigmaLeft, sigmaRight]

end Aristotle.Standalone.PerronContourLiteralBounds
