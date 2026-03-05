import Mathlib
import Littlewood.Aristotle.Standalone.B2StationaryWindowSplit
import Littlewood.Aristotle.Standalone.B2TailStationaryBranchFree

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.B2AngularTailRootInfra

open MeasureTheory Set
open HardyEstimatesPartial

/-- Bundled branch-free payload for B2:
1) near-window cosine bound,
2) tail-window `hardyCosExp` complex oscillatory bound. -/
class B2AngularTailRootPayload : Prop where
  nearWindow :
    Aristotle.Standalone.B2StationaryWindowSplit.B2HardyCosNearWindowPayload
  tailCosExp :
    ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      hardyStart n + Real.sqrt (n + 1) ≤ T →
      ‖∫ t in (hardyStart n + Real.sqrt (n + 1))..T,
          HardyCosSmooth.hardyCosExp n t‖ ≤ B * Real.sqrt (n + 1)

/-- Convert the stationary-tail `hardyExpPhase` class payload into an explicit
tail `hardyCosExp` bound (branch-free representation). -/
theorem hardyCosExpTailBound_of_stationaryTailClass
    [HardyFirstMomentWiring.HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp] :
    ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      hardyStart n + Real.sqrt (n + 1) ≤ T →
      ‖∫ t in (hardyStart n + Real.sqrt (n + 1))..T,
          HardyCosSmooth.hardyCosExp n t‖ ≤ B * Real.sqrt (n + 1) := by
  obtain ⟨B, hB, hBound⟩ :=
    HardyFirstMomentWiring.HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp.bound
  refine ⟨B, hB, ?_⟩
  intro n T hT htail
  have hFunEq :
      (fun t : ℝ => HardyFirstMomentWiring.hardyExpPhase n t)
        = (fun t : ℝ => HardyCosSmooth.hardyCosExp n t) := by
    funext t
    simpa using HardyFirstMomentWiring.hardyExpPhase_eq_hardyCosExp n t
  simpa [hFunEq] using hBound n T hT htail

/-- Build the bundled branch-free payload from explicit near+tail inputs. -/
theorem rootPayload_of_explicit_near_and_tail
    (hNear :
      Aristotle.Standalone.B2StationaryWindowSplit.B2HardyCosNearWindowPayload)
    (hTailCosExp :
      ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ‖∫ t in (hardyStart n + Real.sqrt (n + 1))..T,
            HardyCosSmooth.hardyCosExp n t‖ ≤ B * Real.sqrt (n + 1)) :
    B2AngularTailRootPayload := by
  exact ⟨hNear, hTailCosExp⟩

/-- Build the bundled branch-free payload from near-window data and the
stationary-tail `hardyExpPhase` class. -/
theorem rootPayload_of_near_and_stationaryTailClass
    (hNear :
      Aristotle.Standalone.B2StationaryWindowSplit.B2HardyCosNearWindowPayload)
    [HardyFirstMomentWiring.HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp] :
    B2AngularTailRootPayload := by
  exact ⟨hNear, hardyCosExpTailBound_of_stationaryTailClass⟩

/-- Extract the split tail-window payload from the branch-free root payload. -/
theorem tailWindowPayload_of_rootPayload
    [B2AngularTailRootPayload] :
    Aristotle.Standalone.B2StationaryWindowSplit.B2HardyCosTailWindowPayload := by
  have hStationary :
      HardyFirstMomentWiring.HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp :=
    Aristotle.Standalone.B2TailStationaryBranchFree.stationaryTailClass_of_hardyCosExpTailBound
      B2AngularTailRootPayload.tailCosExp
  exact
    Aristotle.Standalone.B2StationaryWindowSplit.tailWindowPayload_of_hardyExpPhaseTailBound
      hStationary.bound

/-- Direct B2 endpoint from the bundled branch-free near+tail payload. -/
theorem mainTermFirstMomentBound_of_rootPayload
    [B2AngularTailRootPayload] :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  exact
    Aristotle.Standalone.B2StationaryWindowSplit.mainTermFirstMomentBoundHyp_of_near_and_tail
      B2AngularTailRootPayload.nearWindow
      tailWindowPayload_of_rootPayload

instance (priority := 900) [B2AngularTailRootPayload] :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  exact mainTermFirstMomentBound_of_rootPayload

end Aristotle.Standalone.B2AngularTailRootInfra
