/-
# Perron Formula CIF — Gap 2: Meromorphic Rectangle CIF

The meromorphic CIF for (-ζ'/ζ)·x^s/s on the rectangle [1/2, c] × [-T, T].

## Key reuse (all sorry-free)
- RectCircleEquality: rect_cauchy_integral_formula, rect_integral_principal_part
- ResidueExtraction: circle_integral_simple_pole
- PerronResidueAtoms: perron_residue_at_one, perron_residue_at_zero
- PerronKernelBound: horizontal_segment_cpow_bound

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.RectCircleEquality
import Littlewood.Aristotle.Standalone.PerronResidueAtoms
import Littlewood.Aristotle.Standalone.PerronKernelBound

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Littlewood.PerronFormulaCIF

open Complex Real MeasureTheory Set Finset

/-- Splitting {1} ∪ zeros into separate sums (pure Finset algebra). -/
lemma split_pole_sum (zeros : Finset ℂ) (res : ℂ → ℂ) (h_one_not_zero : (1 : ℂ) ∉ zeros) :
    ∑ w ∈ Finset.cons 1 zeros h_one_not_zero, res w = res 1 + ∑ ρ ∈ zeros, res ρ :=
  Finset.sum_cons h_one_not_zero

/-- The meromorphic CIF for a function with finitely many simple poles inside a rectangle.
    ∫_∂R F = 2πi · Σ residues.

    Proof strategy:
    1. Decompose F = Σ_w res(w)/(s-w) + G where G is holomorphic
    2. ∫_∂R G = 0 by Cauchy-Goursat (rect_integral_eq_zero_of_holomorphic)
    3. ∫_∂R res(w)/(s-w) = 2πi·res(w) by rect_integral_principal_part
    4. Linearity: ∫_∂R F = Σ 2πi·res(w) + 0 -/
theorem meromorphic_cif_simple_poles
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (poles : Finset ℂ) (residues : ℂ → ℂ)
    (F : ℂ → ℂ)
    (G : ℂ → ℂ)  -- holomorphic remainder: G = F - Σ res(w)/(s-w)
    -- All poles are strictly inside the rectangle
    (hpoles : ∀ p ∈ poles,
      p ∈ Littlewood.Development.CauchyRectangleFormula.openRect a b c d)
    -- G is holomorphic on the closed rectangle
    (hG : DifferentiableOn ℂ G
      (Littlewood.Development.CauchyRectangleFormula.closedRect a b c d))
    -- F decomposes as sum of principal parts + holomorphic remainder
    (h_decomp : ∀ s, (∀ p ∈ poles, s ≠ p) →
      F s = (∑ w ∈ poles, residues w * (s - w)⁻¹) + G s) :
    Littlewood.Development.CauchyRectangleFormula.rectangleIntegral F a b c d =
    2 * ↑π * I * ∑ w ∈ poles, residues w :=
  RectCircleEquality.rect_integral_eq_sum_residues a b c d hab hcd poles hpoles residues G hG F h_decomp

/-- The horizontal segment bound for the Perron integrand.
    Already proved in PerronKernelBound.horizontal_segment_cpow_bound. -/
-- Re-export with Perron-specific parameters
theorem horizontal_bound_perron (x T : ℝ) (hx : 1 ≤ x) (hT : 0 < T) (a c : ℝ)
    (ha : 0 < a) (hac : a ≤ c) :
    ‖(∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) -
     (∫ t in (-T)..T, (x : ℂ) ^ ((a : ℂ) + (t : ℂ) * I) / ((a : ℂ) + (t : ℂ) * I))‖ ≤
    2 * x ^ c * (c - a) / T :=
  Aristotle.Standalone.PerronKernelBound.perron_contour_difference hx ha hac hT

end Littlewood.PerronFormulaCIF
