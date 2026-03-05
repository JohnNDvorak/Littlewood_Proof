import Mathlib
import Littlewood.Bridge.HardyFirstMomentWiring
import Littlewood.Aristotle.Standalone.B2MainTermFirstMomentExact

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.B2VdcFirstDerivTailRootInfra

open MeasureTheory Set
open HardyEstimatesPartial

/-- Bundled root payload for the explicit first-derivative VdC tail route to B2.

This captures the exact five analytic hypotheses consumed by
`HardyFirstMomentWiring.hardyCosIntegralSqrtModeBound_of_vdcFirstDeriv_tail`. -/
class B2VdcFirstDerivTailRootPayload : Prop where
  phaseDiff :
    ∀ n : ℕ, Differentiable ℝ (HardyFirstMomentWiring.hardyPhaseReal n)
  phaseDerivDiff :
    ∀ n : ℕ, Differentiable ℝ (deriv (HardyFirstMomentWiring.hardyPhaseReal n))
  phaseSecondCont :
    ∀ n : ℕ, Continuous (deriv (deriv (HardyFirstMomentWiring.hardyPhaseReal n)))
  derivLowerTail :
    ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      hardyStart n + Real.sqrt (n + 1) ≤ T →
      ∀ t ∈ Set.Icc (hardyStart n + Real.sqrt (n + 1)) T,
        m / Real.sqrt (n + 1)
          ≤ deriv (HardyFirstMomentWiring.hardyPhaseReal n) t
  secondNonnegTail :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      hardyStart n + Real.sqrt (n + 1) ≤ T →
      ∀ t ∈ Set.Icc (hardyStart n + Real.sqrt (n + 1)) T,
        0 ≤ deriv (deriv (HardyFirstMomentWiring.hardyPhaseReal n)) t

/-- Direct B2 constructor from an explicit first-derivative VdC tail package. -/
theorem mainTermFirstMomentBound_of_explicit_vdcFirstDeriv_tail
    (hPhaseDiff :
      ∀ n : ℕ, Differentiable ℝ (HardyFirstMomentWiring.hardyPhaseReal n))
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
    Aristotle.Standalone.B2MainTermFirstMomentExact.mainTermFirstMomentBoundHyp_of_vdcFirstDeriv_tail_data
      hPhaseDiff hPhaseDerivDiff hPhaseSecondCont hDerivLowerTail hSecondNonnegTail

/-- Canonical extraction of the B2 main-term class from the bundled
first-derivative VdC root payload. -/
theorem mainTermFirstMomentBound_of_rootPayload
    [B2VdcFirstDerivTailRootPayload] :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  exact
    mainTermFirstMomentBound_of_explicit_vdcFirstDeriv_tail
      B2VdcFirstDerivTailRootPayload.phaseDiff
      B2VdcFirstDerivTailRootPayload.phaseDerivDiff
      B2VdcFirstDerivTailRootPayload.phaseSecondCont
      B2VdcFirstDerivTailRootPayload.derivLowerTail
      B2VdcFirstDerivTailRootPayload.secondNonnegTail

/-- Typeclass lift into `MainTermFirstMomentBoundHyp`. -/
instance (priority := 900) [B2VdcFirstDerivTailRootPayload] :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  exact mainTermFirstMomentBound_of_rootPayload

end Aristotle.Standalone.B2VdcFirstDerivTailRootInfra
