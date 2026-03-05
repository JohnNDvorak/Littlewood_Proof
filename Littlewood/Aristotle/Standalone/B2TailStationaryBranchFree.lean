import Mathlib
import Littlewood.Bridge.HardyFirstMomentWiring

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.B2TailStationaryBranchFree

open HardyEstimatesPartial

/-- Branch-free transfer: a tail bound proved for `hardyCosExp` implies the
required tail bound class for `hardyExpPhase` (using
`hardyExpPhase_eq_hardyCosExp`). -/
theorem stationaryTailClass_of_hardyCosExpTailBound
    (hTail :
      ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ‖∫ t in (hardyStart n + Real.sqrt (n + 1))..T,
            HardyCosSmooth.hardyCosExp n t‖ ≤ B * Real.sqrt (n + 1)) :
    HardyFirstMomentWiring.HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp := by
  refine ⟨?_⟩
  rcases hTail with ⟨B, hB, hBound⟩
  refine ⟨B, hB, ?_⟩
  intro n T hT htail
  have hFunEq :
      (fun t : ℝ => HardyFirstMomentWiring.hardyExpPhase n t)
        = (fun t : ℝ => HardyCosSmooth.hardyCosExp n t) := by
    funext t
    simpa using HardyFirstMomentWiring.hardyExpPhase_eq_hardyCosExp n t
  simpa [hFunEq] using hBound n T hT htail

end Aristotle.Standalone.B2TailStationaryBranchFree
