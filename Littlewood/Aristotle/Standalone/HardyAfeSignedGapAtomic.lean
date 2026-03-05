/- 
B1 atomic leaf: signed AFE mean-square integral gap.

This file isolates the single deep analytic payload needed by
`Standalone.HardyMeanSquareAsymptoticFromZetaMoment`:

  `(fun T => ∫_1^T (|ζ|² - 2|S_N|²)) = O(T)`.

All bridge/plumbing lemmas are proved in
`Standalone.HardyAfeMeanSquareBridgeInfra`.
-/

import Littlewood.Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra
import Littlewood.Aristotle.Standalone.HardyAfeSignedGapDeepLeaf

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.HardyAfeSignedGapAtomic

open Filter Asymptotics MeasureTheory Set
open Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra

/-- **B1 atomic wrapper**: signed AFE gap has `O(T)` integral growth.

Reference payload: Ingham/Titchmarsh AFE mean-square bridge cancellation.
The analytic leaf is delegated to
`HardyAfeSignedGapDeepLeaf.afe_signed_integral_gap_bound_leaf`. -/
theorem afe_signed_integral_gap_bound_atomic :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
    =O[atTop] (fun T => T) := by
  simpa using Aristotle.Standalone.HardyAfeSignedGapDeepLeaf.afe_signed_integral_gap_bound_leaf

end Aristotle.Standalone.HardyAfeSignedGapAtomic
