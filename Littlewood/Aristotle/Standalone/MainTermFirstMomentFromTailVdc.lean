import Mathlib
import Littlewood.Bridge.HardyFirstMomentWiring

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.MainTermFirstMomentFromTailVdc

open MeasureTheory Set Filter Topology
open HardyEstimatesPartial

/-- Minimal class-level route to the main-term first-moment bound:
the stationary-window tail `√(n+1)` bound implies
`HardyFirstMomentWiring.MainTermFirstMomentBoundHyp` by existing wiring. -/
theorem mainTermFirstMomentBound_of_stationaryTailPackage
    (hTail :
      HardyFirstMomentWiring.HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp) :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  let _ :
      HardyFirstMomentWiring.HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp := hTail
  infer_instance

/-- Class-level route to the main-term first-moment bound:
the tail-localized `√(n+1)` VdC package implies
`HardyFirstMomentWiring.MainTermFirstMomentBoundHyp` by existing wiring. -/
theorem mainTermFirstMomentBound_of_tailVdcPackage
    (hTail : HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp) :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  let _ : HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp := hTail
  exact mainTermFirstMomentBound_of_stationaryTailPackage inferInstance

/-- Expanded class route (still sorry-free): if the tail phase-side regularity,
tail derivative lower bound, and tail second-derivative decay are available,
the main-term first-moment hypothesis follows automatically. -/
theorem mainTermFirstMomentBound_of_tailPhaseClasses
    [HardyFirstMomentWiring.HardyThetaDifferentiableOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp] :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  infer_instance

end Aristotle.Standalone.MainTermFirstMomentFromTailVdc
