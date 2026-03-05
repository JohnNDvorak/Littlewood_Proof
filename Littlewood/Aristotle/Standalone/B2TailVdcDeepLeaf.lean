/- 
Delegated deep leaf for B2 (tail-localized VdC sqrt-mode package).

This file carries the analytic payload:
`HardyExpPhaseVdcSqrtModeOnTailSupportHyp`.

The main-chain B2 assembly in `B2StationaryWindowLeaves.lean` is kept
sorry-free except for this dedicated leaf import.
-/

import Littlewood.Bridge.HardyFirstMomentWiring
import Littlewood.Aristotle.Standalone.B2TailVdcRootInfra
import Littlewood.Aristotle.Standalone.B2VdcFirstDerivTailRootInfra
import Littlewood.Aristotle.Standalone.B2SupportPhaseRootInfra

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.B2TailVdcDeepLeaf

open HardyEstimatesPartial

/-- Class-assembly route for the B2 tail VdC package.
If the four tail phase classes are available, the required tail VdC package
is synthesized by existing wiring instances. -/
theorem tailVdcSqrtModeClass_of_tailPhaseClasses
    [HardyFirstMomentWiring.HardyThetaDifferentiableOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp] :
    HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp := by
  infer_instance

/-- Candidate closure route for this deep leaf from an explicit (non-typeclass)
tail phase package. -/
theorem tailVdcSqrtModeClass_candidate_of_explicit_tail_package
    (hThetaDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n + Real.sqrt (n + 1)) T,
          DifferentiableAt ℝ hardyTheta t)
    (hPhaseDerivDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n + Real.sqrt (n + 1)) T,
          DifferentiableAt ℝ (deriv (HardyFirstMomentWiring.hardyPhaseReal n)) t)
    (hDerivLower :
      ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n + Real.sqrt (n + 1)) T,
          m / Real.sqrt (n + 1)
            ≤ |deriv (HardyFirstMomentWiring.hardyPhaseReal n) t|)
    (hSecondDeriv :
      ∃ M > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n + Real.sqrt (n + 1)) T,
          |deriv (deriv (HardyFirstMomentWiring.hardyPhaseReal n)) t|
            ≤ M / t ^ (3 / 2 : ℝ)) :
    HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp := by
  exact
    Aristotle.Standalone.B2TailVdcRootInfra.tailVdcSqrtModeClass_of_explicit_tail_package
      hThetaDiff hPhaseDerivDiff hDerivLower hSecondDeriv

/-- Candidate closure route from an explicit *phase-only* tail package on
`hardyPhaseReal`, bypassing `hardyTheta` branch-cut classes. -/
theorem tailVdcSqrtModeClass_candidate_of_explicit_phase_tail_package
    (hPhaseDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n + Real.sqrt (n + 1)) T,
          DifferentiableAt ℝ (HardyFirstMomentWiring.hardyPhaseReal n) t)
    (hPhaseDerivDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n + Real.sqrt (n + 1)) T,
          DifferentiableAt ℝ (deriv (HardyFirstMomentWiring.hardyPhaseReal n)) t)
    (hDerivLower :
      ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n + Real.sqrt (n + 1)) T,
          m / Real.sqrt (n + 1)
            ≤ |deriv (HardyFirstMomentWiring.hardyPhaseReal n) t|)
    (hSecondDeriv :
      ∃ M > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n + Real.sqrt (n + 1)) T,
          |deriv (deriv (HardyFirstMomentWiring.hardyPhaseReal n)) t|
            ≤ M / t ^ (3 / 2 : ℝ)) :
    HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp := by
  exact
    Aristotle.Standalone.B2TailVdcRootInfra.tailVdcSqrtModeClass_of_explicit_phase_tail_package
      hPhaseDiff hPhaseDerivDiff hDerivLower hSecondDeriv

/-- Candidate closure route from the bundled B2 tail VdC root payload class. -/
theorem tailVdcSqrtModeClass_candidate_of_rootPayload
    [Aristotle.Standalone.B2TailVdcRootInfra.B2TailVdcRootPayload] :
    HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp := by
  exact Aristotle.Standalone.B2TailVdcRootInfra.tailVdcSqrtModeClass_of_rootPayload

/-- Candidate closure route from the phase-only tail class triple used by the
new B2 root infra. -/
theorem tailVdcSqrtModeClass_candidate_of_tailPhaseCalculusClasses
    [HardyFirstMomentWiring.HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp] :
    HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp := by
  infer_instance

/-- Candidate route from the phase-only tail class triple to the stationary-tail
split-window class used by B2 assembly. -/
theorem stationaryTailClass_candidate_of_tailPhaseCalculusClasses
    [HardyFirstMomentWiring.HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp] :
    HardyFirstMomentWiring.HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp := by
  exact
    Aristotle.Standalone.B2TailVdcRootInfra.stationaryTailClass_of_tailPhaseCalculusClasses

/-- Candidate route to B2's target class from the explicit first-derivative VdC
tail root payload. -/
theorem mainTermFirstMomentBound_candidate_of_vdcFirstDerivRootPayload
    [Aristotle.Standalone.B2VdcFirstDerivTailRootInfra.B2VdcFirstDerivTailRootPayload] :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  infer_instance

/-- Candidate route to the tail VdC class from the bundled support-side B2 root
payload. -/
theorem tailVdcSqrtModeClass_candidate_of_supportRootPayload
    [Aristotle.Standalone.B2SupportPhaseRootInfra.B2SupportPhaseRootPayload] :
    HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp := by
  let hTailRoot : Aristotle.Standalone.B2TailVdcRootInfra.B2TailVdcRootPayload :=
    Aristotle.Standalone.B2SupportPhaseRootInfra.tailRootPayload_of_supportRootPayload
  exact hTailRoot.tailVdcClass

/-- Candidate route to B2's target class from the bundled support-side B2 root
payload. -/
theorem mainTermFirstMomentBound_candidate_of_supportRootPayload
    [Aristotle.Standalone.B2SupportPhaseRootInfra.B2SupportPhaseRootPayload] :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  infer_instance

/-- **Delegated B2 deep leaf**: tail-localized VdC `sqrt`-mode package on the
stationary-window complement, via the non-circular support-root constructor. -/
theorem tailVdcSqrtModeClass_of_noncircular_support_constructor
    [HardyFirstMomentWiring.HardyGammaInSlitPlaneOnSupportHyp]
    [HardyFirstMomentWiring.HardyThetaPhaseGapLowerSqrtModeOnSupportHyp]
    [HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp := by
  let hSupportRoot :
      Aristotle.Standalone.B2SupportPhaseRootInfra.B2SupportPhaseRootPayload :=
    Aristotle.Standalone.B2SupportPhaseRootInfra.provide_noncircular_constructor_B2SupportPhaseRootPayload
  letI :
      Aristotle.Standalone.B2SupportPhaseRootInfra.B2SupportPhaseRootPayload := hSupportRoot
  exact tailVdcSqrtModeClass_candidate_of_supportRootPayload

/-- **Delegated B2 deep leaf**: tail-localized VdC `sqrt`-mode package on the
stationary-window complement. -/
theorem tailVdcSqrtModeClass_leaf :
    HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp := by
  -- Drop-in closure once an unconditional support payload provider is available:
  -- `exact tailVdcSqrtModeClass_candidate_of_supportRootPayload`
  sorry

end Aristotle.Standalone.B2TailVdcDeepLeaf
