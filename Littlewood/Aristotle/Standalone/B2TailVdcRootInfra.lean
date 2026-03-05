import Mathlib
import Littlewood.Bridge.HardyFirstMomentWiring
import Littlewood.Aristotle.Standalone.MainTermFirstMomentFromTailVdc

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.B2TailVdcRootInfra

open MeasureTheory Set
open HardyEstimatesPartial

/-- Bundled root payload for the B2 tail VdC class leaf. -/
class B2TailVdcRootPayload : Prop where
  tailVdcClass : HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp

/-- Canonical extraction of the B2 tail VdC class from the bundled root payload. -/
theorem tailVdcSqrtModeClass_of_rootPayload
    [B2TailVdcRootPayload] :
    HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp :=
  B2TailVdcRootPayload.tailVdcClass

/-- Explicit (non-typeclass) tail package for the B2 stationary-window complement.

This theorem is a root-infra entry point: if you can produce the four tail
phase-side assumptions directly (as plain hypotheses), it upgrades them to the
canonical `HardyExpPhaseVdcSqrtModeOnTailSupportHyp` class via existing wiring. -/
theorem tailVdcSqrtModeClass_of_explicit_tail_package
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
  letI : HardyFirstMomentWiring.HardyThetaDifferentiableOnTailSupportHyp :=
    ⟨hThetaDiff⟩
  letI : HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnTailSupportHyp :=
    ⟨hPhaseDerivDiff⟩
  letI : HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp :=
    ⟨hDerivLower⟩
  letI : HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp :=
    ⟨hSecondDeriv⟩
  infer_instance

/-- Explicit phase-side route that bypasses `hardyTheta` branch-cut classes:
if you can provide the tail phase-calculus package directly on
`hardyPhaseReal`, together with mode-sensitive lower/upper derivative control,
the tail VdC class follows by existing wiring. -/
theorem tailVdcSqrtModeClass_of_explicit_phase_tail_package
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
  letI : HardyFirstMomentWiring.HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp :=
    ⟨hPhaseDiff, hPhaseDerivDiff⟩
  letI : HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp :=
    ⟨hDerivLower⟩
  letI : HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp :=
    ⟨hSecondDeriv⟩
  infer_instance

/-- Class-level route: the phase-only tail class triple synthesizes the tail VdC
`sqrt`-mode package. -/
theorem tailVdcSqrtModeClass_of_tailPhaseCalculusClasses
    [HardyFirstMomentWiring.HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp] :
    HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp := by
  infer_instance

/-- Class-level route: the phase-only tail class triple synthesizes the
stationary-tail class used by B2's split-window assembly. -/
theorem stationaryTailClass_of_tailPhaseCalculusClasses
    [HardyFirstMomentWiring.HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp] :
    HardyFirstMomentWiring.HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp := by
  let _ : HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp := by
    exact tailVdcSqrtModeClass_of_tailPhaseCalculusClasses
  infer_instance

/-- Direct root-infra route to B2's target class from explicit tail assumptions. -/
theorem mainTermFirstMomentBound_of_explicit_tail_package
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
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  have hTail : HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp :=
    tailVdcSqrtModeClass_of_explicit_tail_package
      hThetaDiff hPhaseDerivDiff hDerivLower hSecondDeriv
  exact
    Aristotle.Standalone.MainTermFirstMomentFromTailVdc.mainTermFirstMomentBound_of_tailVdcPackage
      hTail

/-- Direct root-infra route to B2's target class from explicit phase-only tail
assumptions on `hardyPhaseReal`. -/
theorem mainTermFirstMomentBound_of_explicit_phase_tail_package
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
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  have hTail : HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp :=
    tailVdcSqrtModeClass_of_explicit_phase_tail_package
      hPhaseDiff hPhaseDerivDiff hDerivLower hSecondDeriv
  exact
    Aristotle.Standalone.MainTermFirstMomentFromTailVdc.mainTermFirstMomentBound_of_tailVdcPackage
      hTail

/-- Lift an explicit tail VdC class witness into the bundled B2 root payload. -/
theorem rootPayload_of_tailVdcClass
    (hTail : HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp) :
    B2TailVdcRootPayload := by
  exact ⟨hTail⟩

/-- Lift the four tail phase-side classes into the bundled B2 root payload. -/
theorem rootPayload_of_tailPhaseClasses
    [HardyFirstMomentWiring.HardyThetaDifferentiableOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp] :
    B2TailVdcRootPayload := by
  exact ⟨inferInstance⟩

/-- Typeclass lift: any tail `VdC` package immediately yields the bundled B2
root payload. -/
instance (priority := 950)
    [HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp] :
    B2TailVdcRootPayload := by
  exact rootPayload_of_tailVdcClass inferInstance

/-- Typeclass lift: tail phase-side classes synthesize the bundled B2 root
payload via existing wiring. -/
instance (priority := 900)
    [HardyFirstMomentWiring.HardyThetaDifferentiableOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp] :
    B2TailVdcRootPayload := by
  exact rootPayload_of_tailPhaseClasses

/-- Typeclass lift from phase-only tail classes into the bundled B2 root
payload, bypassing support-level `hardyTheta` branch-cut classes. -/
instance (priority := 875)
    [HardyFirstMomentWiring.HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp] :
    B2TailVdcRootPayload := by
  exact rootPayload_of_tailVdcClass inferInstance

/-- Typeclass lift from support-side phase assumptions into the bundled B2 root
payload (through support→tail instances in `HardyFirstMomentWiring`). -/
instance (priority := 850)
    [HardyFirstMomentWiring.HardyThetaDifferentiableOnSupportHyp]
    [HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    B2TailVdcRootPayload := by
  exact rootPayload_of_tailPhaseClasses

/-- Root-payload endpoint for B2's `MainTermFirstMomentBoundHyp`. -/
theorem mainTermFirstMomentBound_of_rootPayload
    [B2TailVdcRootPayload] :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  exact
    Aristotle.Standalone.MainTermFirstMomentFromTailVdc.mainTermFirstMomentBound_of_tailVdcPackage
      tailVdcSqrtModeClass_of_rootPayload

end Aristotle.Standalone.B2TailVdcRootInfra
