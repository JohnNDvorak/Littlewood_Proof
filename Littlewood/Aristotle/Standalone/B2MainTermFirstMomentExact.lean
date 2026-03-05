import Mathlib
import Littlewood.Bridge.HardyFirstMomentWiring
import Littlewood.Aristotle.Standalone.MainTermFirstMomentFromTailVdc

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.B2MainTermFirstMomentExact

open MeasureTheory Set Filter Topology
open HardyEstimatesPartial

/-- Canonical B2 payload shape used by `DeepBlockersResolved.deep_blocker_B2`. -/
def B2HardyCosSqrtPayload : Prop :=
  ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
    |∫ t in Ioc (hardyStart n) T, hardyCos n t| ≤ B * Real.sqrt (n + 1)

/-- Direct conversion from the canonical B2 payload to the main-term first-moment class. -/
theorem mainTermFirstMomentBoundHyp_of_payload
    (hPayload : B2HardyCosSqrtPayload) :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  exact HardyFirstMomentWiring.mainTermFirstMomentBound_of_sqrtMode_hardyCosIntegral hPayload

/-- Build the canonical B2 payload from explicit tail-VdC data for cosine modes. -/
theorem payload_of_vdcFirstDeriv_tail_data
    (hPhaseDiff : ∀ n : ℕ, Differentiable ℝ (HardyFirstMomentWiring.hardyPhaseReal n))
    (hPhaseDerivDiff :
      ∀ n : ℕ, Differentiable ℝ (deriv (HardyFirstMomentWiring.hardyPhaseReal n)))
    (hPhaseSecondCont :
      ∀ n : ℕ, Continuous (deriv (deriv (HardyFirstMomentWiring.hardyPhaseReal n))))
    (hDerivLowerTail :
      ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.Icc (hardyStart n + Real.sqrt (n + 1)) T,
          m / Real.sqrt (n + 1)
            ≤ deriv (HardyFirstMomentWiring.hardyPhaseReal n) t)
    (hSecondNonnegTail :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.Icc (hardyStart n + Real.sqrt (n + 1)) T,
          0 ≤ deriv (deriv (HardyFirstMomentWiring.hardyPhaseReal n)) t) :
    B2HardyCosSqrtPayload := by
  exact
    (HardyFirstMomentWiring.hardyCosIntegralSqrtModeBound_of_vdcFirstDeriv_tail
      hPhaseDiff hPhaseDerivDiff hPhaseSecondCont hDerivLowerTail hSecondNonnegTail).bound

/-- Single-step B2 closure from explicit tail-VdC data. -/
theorem mainTermFirstMomentBoundHyp_of_vdcFirstDeriv_tail_data
    (hPhaseDiff : ∀ n : ℕ, Differentiable ℝ (HardyFirstMomentWiring.hardyPhaseReal n))
    (hPhaseDerivDiff :
      ∀ n : ℕ, Differentiable ℝ (deriv (HardyFirstMomentWiring.hardyPhaseReal n)))
    (hPhaseSecondCont :
      ∀ n : ℕ, Continuous (deriv (deriv (HardyFirstMomentWiring.hardyPhaseReal n))))
    (hDerivLowerTail :
      ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.Icc (hardyStart n + Real.sqrt (n + 1)) T,
          m / Real.sqrt (n + 1)
            ≤ deriv (HardyFirstMomentWiring.hardyPhaseReal n) t)
    (hSecondNonnegTail :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.Icc (hardyStart n + Real.sqrt (n + 1)) T,
          0 ≤ deriv (deriv (HardyFirstMomentWiring.hardyPhaseReal n)) t) :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  exact
    mainTermFirstMomentBoundHyp_of_payload
      (payload_of_vdcFirstDeriv_tail_data
        hPhaseDiff hPhaseDerivDiff hPhaseSecondCont hDerivLowerTail hSecondNonnegTail)

/-- Class-based B2 route: tail support phase classes imply the B2 class directly. -/
theorem mainTermFirstMomentBoundHyp_of_tail_support_classes
    [HardyFirstMomentWiring.HardyThetaDifferentiableOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp] :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  exact Aristotle.Standalone.MainTermFirstMomentFromTailVdc.mainTermFirstMomentBound_of_tailPhaseClasses

end Aristotle.Standalone.B2MainTermFirstMomentExact

