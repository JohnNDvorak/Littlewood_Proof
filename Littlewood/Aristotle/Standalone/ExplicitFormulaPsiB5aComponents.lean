/- 
B5a component leaf: component package for shifted-contour explicit formula.

This file reconstructs the component package used by
`Standalone.ExplicitFormulaPsiSkeleton`:

* Perron truncation `(log x)^2` model error,
* residue extraction identity,
* contour remainder `sqrt/log` bound.

The sole deep payload is now isolated in
`Standalone.ExplicitFormulaPsiB5aShiftedBoundAtomic`.
All downstream algebraic assembly is proved in `ExplicitFormulaPsiB5a*` files.
-/

import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aDefs
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aFromShiftedBound
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundAtomic

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiSkeleton

open Aristotle.Standalone.ExplicitFormulaPsiB5aFromShiftedBound

/-- **B5a component package**: Perron+residue+contour data rebuilt from the
direct shifted-remainder atomic bound.

This is the single analytic contour payload used to derive
`shifted_contours_bound` via proved combiners. -/
theorem shifted_contours_components_atomic :
    ∃ perronIntegralRe contourRemainderRe : ℝ → ℝ → ℝ,
      (∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
          Cₚ * (Real.log x) ^ 2)
      ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T)
      ∧
      (∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |contourRemainderRe x T| ≤
          Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) := by
  exact shifted_contours_components_of_shifted_bound shifted_remainder_bound_atomic

end Aristotle.Standalone.ExplicitFormulaPsiSkeleton
