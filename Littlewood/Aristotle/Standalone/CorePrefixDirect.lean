/- Direct wrapper for the current tracked-main large-shift recovery theorem.

The exact remaining analytic content now lives in
`AtkinsonFormula.atkinson_largeShiftBoundaryAbelRemainder_bound`, where the
private kernel language is available.  This file stays as the public tracked
entry point for the large-shift provider. -/

import Littlewood.Aristotle.Standalone.AtkinsonFormula

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.CorePrefixDirect

open Aristotle.Standalone.AtkinsonFormula

theorem atkinsonLargeShiftPrefixBound_direct :
    AtkinsonLargeShiftPrefixBoundHyp := by
  exact atkinson_largeShiftPrefixBound_of_direct_abel

instance : AtkinsonLargeShiftPrefixBoundHyp :=
  atkinsonLargeShiftPrefixBound_direct

end Aristotle.Standalone.CorePrefixDirect
