/-
ExplicitFormulaPsiGeneralHyp (Blocker B5a) — assembly over one atomic leaf.

This file localizes B5a to one theorem:

`shifted_contours_bound`
  `|ψ(x) - x + Σ_{|γ|≤T} Re(x^ρ/ρ)|`
  `≤ C₂ · (√x · (log T)^2 / √T + (log x)^2)`
  for all `x ≥ 2`, `T ≥ 2`.

All wiring from this bound to `ExplicitFormulaPsiGeneralHyp` is proved below.
The sole atomic contour payload is delegated to
`Standalone.ExplicitFormulaPsiB5aComponents`.

## References

- Davenport, H. (2000). Multiplicative Number Theory, Ch. 17.
- Montgomery-Vaughan (2007). Multiplicative Number Theory I, §12.5.
- Ingham, A. E. (1932). The Distribution of Prime Numbers, Ch. IV.
-/

import Littlewood.Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aDefs
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aComponents
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aContourBounds
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiSkeleton

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.ExplicitFormulaPsiB5aContourBounds
open ZetaZeros

-- ============================================================
-- Boundary definitions
-- ============================================================

-- ============================================================
-- B5a atomic leaf
-- ============================================================

/-- **B5a assembled bound**: General truncated explicit formula error bound.

For all `x ≥ 2`, `T ≥ 2`:
`|ψ(x) - x + Σ_{|γ|≤T} Re(x^ρ/ρ)| ≤ C₂ · (√x · (log T)²/√T + (log x)²)`.

This is the full Davenport/Montgomery-Vaughan truncated explicit-formula
bound after Perron truncation + contour shift + residue extraction.
-/
theorem shifted_contours_bound :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  rcases shifted_contours_components_atomic with
    ⟨perronIntegralRe, contourRemainderRe, hPerronRaw, hResidue, hContour⟩
  exact shifted_contours_bound_of_components
    perronIntegralRe contourRemainderRe hPerronRaw hResidue hContour

-- ============================================================
-- Wiring: ExplicitFormulaPsiGeneralHyp from shifted_contours_bound
-- ============================================================

/-- **B5a proved** directly from `shifted_contours_bound`.
The LHS of ExplicitFormulaPsiGeneralHyp unfolds to |shiftedRemainderRe x T|
and the RHS matches exactly after the bound correction. -/
theorem explicitFormulaPsiGeneral_proved : ExplicitFormulaPsiGeneralHyp where
  proof := by
    exact
      (Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra.explicitFormulaPsiGeneralHyp_of_shifted_remainder_bound
        shifted_contours_bound).proof

end Aristotle.Standalone.ExplicitFormulaPsiSkeleton
