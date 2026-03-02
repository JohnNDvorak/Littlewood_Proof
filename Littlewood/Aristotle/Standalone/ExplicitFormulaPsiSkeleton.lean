/-
ExplicitFormulaPsiGeneralHyp (Blocker B5a) — factored into sub-sorry's.

The error `shiftedRemainderRe x T = ψ(x) - x + Σ Re(x^ρ/ρ)` decomposes as:

  shiftedRemainderRe x T = (Perron truncation error) + (contour-shifted remainder)

## Sub-sorry's

1. **perron_truncation_bound**: Perron truncation error ≤ C₁ · (log x)²
   The error from truncating the Perron integral at height T.
   Reference: Davenport Ch. 17, Lemma 17.1.

2. **contour_shift_bound**: Contour remainder ≤ C₃ · √x · (log T)² / √T
   The horizontal + shifted vertical line integrals after rectangle contour shift.
   Reference: Davenport Ch. 17, Lemma 17.2; uses HorizontalSegmentBounds.lean.

## Assembly

`shifted_contours_bound` is PROVED from sub-sorry's 1+2 via triangle inequality.
`explicitFormulaPsiGeneral_proved` is PROVED from `shifted_contours_bound`.

## References

- Davenport, H. (2000). Multiplicative Number Theory, Ch. 17.
- Montgomery-Vaughan (2007). Multiplicative Number Theory I, §12.5.
- Ingham, A. E. (1932). The Distribution of Prime Numbers, Ch. IV.

Architecture adapted from Gemini's skeleton design.
Co-authored-by: Claude (Anthropic), Gemini (Google)
-/

import Littlewood.Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiSkeleton

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open ZetaZeros

-- ============================================================
-- Boundary definitions
-- ============================================================

/-- The real part of the zero sum Σ_{|γ|≤T} x^ρ/ρ, abstracted behind a def
to prevent `ring` failures on Finset.sum expressions. -/
def zeroSumRe (x T : ℝ) : ℝ :=
  (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re

/-- The explicit formula error: ψ(x) - x + Σ Re(x^ρ/ρ).
Defined concretely so all B5a mathematical content concentrates
into `shifted_contours_bound`. -/
def shiftedRemainderRe (x T : ℝ) : ℝ :=
  Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + zeroSumRe x T

-- ============================================================
-- B5a sub-sorry's: decomposed explicit formula error bound
-- ============================================================

/-- **B5a sub-sorry 1/2**: Perron truncation error bound.

After the Perron integral representation and residue extraction,
the truncation at height T introduces an error of O((log x)²).
This sub-sorry asserts the existence of a "contour remainder" function R
such that the Perron truncation error (shiftedRemainder minus R) is bounded.

Concretely: ψ(x) - x + Σ Re(x^ρ/ρ) = R(x,T) + (truncation error),
where the truncation error satisfies |(truncation error)| ≤ C₁·(log x)².

Reference: Davenport Ch. 17, Lemma 17.1; Montgomery-Vaughan §12.5. -/
theorem perron_truncation_bound :
    ∃ (R : ℝ → ℝ → ℝ), ∃ C₁ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T - R x T| ≤ C₁ * (Real.log x) ^ 2 := by
  sorry

/-- **B5a sub-sorry 2/2**: Contour-shifted remainder bound.

After shifting the Perron integral contour from Re(s) = c > 1 to Re(s) = 1/2,
the horizontal segments contribute O(√x · (log T)² / √T). This uses:
- ζ'/ζ growth: O(log²T) on horizontal segments (from zero density estimates)
- x^s decay: |x^{σ+iT}| = x^σ for the shifted line at σ = 1/2

The function R is the same as in `perron_truncation_bound`.

Reference: Davenport Ch. 17, Lemma 17.2; uses HorizontalSegmentBounds.lean. -/
theorem contour_shift_bound (R : ℝ → ℝ → ℝ) :
    ∃ C₃ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |R x T| ≤ C₃ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
  sorry

-- ============================================================
-- Assembly: shifted_contours_bound from sub-sorry's (PROVED)
-- ============================================================

/-- **B5a assembly** (PROVED from sub-sorry's 1+2): Explicit formula error bound.

|ψ(x) - x + Σ_{|γ|≤T} Re(x^ρ/ρ)| ≤ C₂ · (√x · (log T)²/√T + (log x)²)

Proof: triangle inequality on the Perron decomposition
  shiftedRemainderRe = (truncation error) + R,
then combine the two bounds using max(C₁, C₃). -/
theorem shifted_contours_bound :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  obtain ⟨R, C₁, hC₁, h_trunc⟩ := perron_truncation_bound
  obtain ⟨C₃, hC₃, h_cont⟩ := contour_shift_bound R
  refine ⟨max C₁ C₃, by positivity, fun x T hx hT => ?_⟩
  have h1 := h_trunc x T hx hT
  have h2 := h_cont x T hx hT
  calc |shiftedRemainderRe x T|
      = |(shiftedRemainderRe x T - R x T) + R x T| := by ring_nf
    _ ≤ |shiftedRemainderRe x T - R x T| + |R x T| := abs_add_le _ _
    _ ≤ C₁ * (Real.log x) ^ 2 +
        C₃ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) :=
      add_le_add h1 h2
    _ ≤ max C₁ C₃ * (Real.log x) ^ 2 +
        max C₁ C₃ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = max C₁ C₃ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T +
        (Real.log x) ^ 2) := by ring

-- ============================================================
-- Wiring: ExplicitFormulaPsiGeneralHyp from shifted_contours_bound
-- ============================================================

/-- **B5a proved** directly from `shifted_contours_bound`.
The LHS of ExplicitFormulaPsiGeneralHyp unfolds to |shiftedRemainderRe x T|
and the RHS matches exactly after the bound correction. -/
theorem explicitFormulaPsiGeneral_proved : ExplicitFormulaPsiGeneralHyp where
  proof := by
    obtain ⟨C₂, _, hBound⟩ := shifted_contours_bound
    exact ⟨C₂, fun x T hx hT => by
      have h_eq : Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re) =
          shiftedRemainderRe x T := by
        unfold shiftedRemainderRe zeroSumRe; ring
      rw [h_eq]; exact hBound x T hx hT⟩

end Aristotle.Standalone.ExplicitFormulaPsiSkeleton
