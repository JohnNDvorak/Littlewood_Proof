import Littlewood.Development.HadamardProductZeta
import Littlewood.Aristotle.Standalone.SmallTPerronLeafInstances
import Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone

/-!
# π-side legacy Perron compatibility leaves

This module retains the old Perron-side compatibility placeholders for legacy
RH-`pi` wiring.

- The retained legacy leaves here are:
  the retained `pi_approx` transfer branch placeholder
  `PerronPiApproxCompatibilityHyp`.
- The bounded-height Perron provider is now shared with the `ψ` lane through
  `Standalone/SmallTPerronLeafInstances.lean`, and the stronger absorbed
  bounded-height class `SmallTPerronBoundHyp` is still recovered automatically
  through `SmallTPerronSqrtBridge`.
- The active `littlewood_pi_li` theorem no longer imports this module. Its RH
  path now consumes direct target/anti-target finite-zero argument-approximation
  payloads from `Standalone/LittlewoodPiArgApproxLeafInstances.lean` instead of
  the false retained `pi_approx` compatibility lane.

The remaining placeholder priority is kept low enough that a future
constructive provider can override this module automatically.
-/

-- REMOVED (Session 12): Legacy pi_approx sorry deleted.
-- Overridden by priority-100 instance in PerronExplicitFormulaProvider:1731.
-- This class is no longer on the active `littlewood_pi_li` path.

end Aristotle.Standalone
