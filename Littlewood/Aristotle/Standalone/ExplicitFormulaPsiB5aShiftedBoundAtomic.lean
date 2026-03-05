/- 
B5a atomic leaf (simplified target): direct shifted-remainder bound.

This isolates the deepest contour-analysis payload in its most canonical form:

  |shiftedRemainderRe x T|
    ≤ C * (sqrt x * (log T)^2 / sqrt T + (log x)^2),  x,T ≥ 2.

The component-package form (Perron/residue/contour) is reconstructed from this
bound in `ExplicitFormulaPsiB5aFromShiftedBound`.
-/

import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aDefs
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiSkeleton

/-- **B5a atomic wrapper (simplified):** truncated explicit-formula shifted
remainder bound with variable truncation height `T`.

The analytic leaf is delegated to
`ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.shifted_remainder_bound_leaf`. -/
theorem shifted_remainder_bound_atomic :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  simpa using
    Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.shifted_remainder_bound_leaf

end Aristotle.Standalone.ExplicitFormulaPsiSkeleton
