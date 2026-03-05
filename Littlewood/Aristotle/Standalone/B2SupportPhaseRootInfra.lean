import Mathlib
import Littlewood.Bridge.HardyFirstMomentWiring
import Littlewood.Aristotle.Standalone.B2TailVdcRootInfra

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.B2SupportPhaseRootInfra

open MeasureTheory Set
open HardyEstimatesPartial

/-- Bundled support-side phase payload for B2.

This is the exact support-level class quadruple that feeds the existing
`HardyFirstMomentWiring` support→tail VdC chain. -/
class B2SupportPhaseRootPayload : Prop where
  thetaDiff :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (hardyStart n) T,
        DifferentiableAt ℝ hardyTheta t
  phaseDerivDiff :
    ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (hardyStart n) T,
        DifferentiableAt ℝ (deriv (HardyFirstMomentWiring.hardyPhaseReal n)) t
  derivLowerSqrt :
    ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (hardyStart n) T,
        m / Real.sqrt (n + 1)
          ≤ |deriv (HardyFirstMomentWiring.hardyPhaseReal n) t|
  secondDerivBound :
    ∃ M > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      hardyStart n ≤ T →
      ∀ t ∈ Set.uIcc (hardyStart n) T,
        |deriv (deriv (HardyFirstMomentWiring.hardyPhaseReal n)) t|
          ≤ M / t ^ (3 / 2 : ℝ)

/-- Direct constructor for `HardyGammaInSlitPlaneOnSupportHyp` from an explicit
support-side statement. -/
theorem hardyGammaInSlitPlaneOnSupportHyp_of_explicit
    (hGammaSlit :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n) T,
          Complex.Gamma (1 / 4 + Complex.I * (t / 2)) ∈ Complex.slitPlane) :
    HardyFirstMomentWiring.HardyGammaInSlitPlaneOnSupportHyp := by
  exact ⟨hGammaSlit⟩

/-- Direct constructor for `HardyThetaPhaseGapLowerSqrtModeOnSupportHyp` from
an explicit support-side statement. -/
theorem hardyThetaPhaseGapLowerSqrtModeOnSupportHyp_of_explicit
    (hGapSqrt :
      ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n) T,
          m / Real.sqrt (n + 1)
            ≤ |deriv hardyTheta t - Real.log (n + 1)|) :
    HardyFirstMomentWiring.HardyThetaPhaseGapLowerSqrtModeOnSupportHyp := by
  exact ⟨hGapSqrt⟩

/-- Direct constructor for `HardyPhaseDerivDifferentiableOnSupportHyp` from an
explicit support-side statement. -/
theorem hardyPhaseDerivDifferentiableOnSupportHyp_of_explicit
    (hPhaseDerivDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n) T,
          DifferentiableAt ℝ (deriv (HardyFirstMomentWiring.hardyPhaseReal n)) t) :
    HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp := by
  exact ⟨hPhaseDerivDiff⟩

/-- Direct constructor for `HardyExpPhaseSecondDerivAbsBoundOnSupportHyp` from
an explicit support-side statement. -/
theorem hardyExpPhaseSecondDerivAbsBoundOnSupportHyp_of_explicit
    (hSecondDerivBound :
      ∃ M > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n) T,
          |deriv (deriv (HardyFirstMomentWiring.hardyPhaseReal n)) t|
            ≤ M / t ^ (3 / 2 : ℝ)) :
    HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp := by
  exact ⟨hSecondDerivBound⟩

/-- Build the bundled support payload from explicit support-side assumptions. -/
theorem rootPayload_of_explicit_support_package
    (hThetaDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n) T,
          DifferentiableAt ℝ hardyTheta t)
    (hPhaseDerivDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n) T,
          DifferentiableAt ℝ (deriv (HardyFirstMomentWiring.hardyPhaseReal n)) t)
    (hDerivLowerSqrt :
      ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n) T,
          m / Real.sqrt (n + 1)
            ≤ |deriv (HardyFirstMomentWiring.hardyPhaseReal n) t|)
    (hSecondDerivBound :
      ∃ M > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n) T,
          |deriv (deriv (HardyFirstMomentWiring.hardyPhaseReal n)) t|
            ≤ M / t ^ (3 / 2 : ℝ)) :
    B2SupportPhaseRootPayload := by
  exact ⟨hThetaDiff, hPhaseDerivDiff, hDerivLowerSqrt, hSecondDerivBound⟩

/-- Extract the support-side class package from the bundled root payload. -/
theorem supportClasses_of_rootPayload
    [B2SupportPhaseRootPayload] :
    HardyFirstMomentWiring.HardyThetaDifferentiableOnSupportHyp ∧
      HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp ∧
      HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp ∧
      HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp := by
  refine ⟨⟨B2SupportPhaseRootPayload.thetaDiff⟩, ?_⟩
  refine ⟨⟨B2SupportPhaseRootPayload.phaseDerivDiff⟩, ?_⟩
  exact ⟨⟨B2SupportPhaseRootPayload.derivLowerSqrt⟩, ⟨B2SupportPhaseRootPayload.secondDerivBound⟩⟩

/-- Recover support-side phase-gap lower bounds from the bundled support payload.
This is the inverse direction of the usual
`hardyTheta → hardyPhaseReal` derivative transfer. -/
theorem thetaPhaseGapLowerSqrtMode_onSupport_of_rootPayload
    [B2SupportPhaseRootPayload] :
    HardyFirstMomentWiring.HardyThetaPhaseGapLowerSqrtModeOnSupportHyp := by
  obtain ⟨m, hm, hderivLower⟩ := B2SupportPhaseRootPayload.derivLowerSqrt
  refine ⟨m, hm, ?_⟩
  intro n T hT hstart t ht
  have hThetaDiff :
      DifferentiableAt ℝ HardyEstimatesPartial.hardyTheta t :=
    B2SupportPhaseRootPayload.thetaDiff n T hT hstart t ht
  have hphaseEq :
      deriv (HardyFirstMomentWiring.hardyPhaseReal n) t
        = deriv HardyEstimatesPartial.hardyTheta t - Real.log (n + 1) :=
    HardyFirstMomentWiring.hardyPhaseReal_deriv_eq_hardyTheta_deriv_sub_log
      (n := n) hThetaDiff
  simpa [hphaseEq] using hderivLower n T hT hstart t ht

instance (priority := 950) [B2SupportPhaseRootPayload] :
    HardyFirstMomentWiring.HardyThetaDifferentiableOnSupportHyp := by
  exact (supportClasses_of_rootPayload).1

instance (priority := 945) [B2SupportPhaseRootPayload] :
    HardyFirstMomentWiring.HardyThetaPhaseGapLowerSqrtModeOnSupportHyp := by
  exact thetaPhaseGapLowerSqrtMode_onSupport_of_rootPayload

instance (priority := 950) [B2SupportPhaseRootPayload] :
    HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp := by
  exact (supportClasses_of_rootPayload).2.1

instance (priority := 950) [B2SupportPhaseRootPayload] :
    HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp := by
  exact (supportClasses_of_rootPayload).2.2.1

instance (priority := 950) [B2SupportPhaseRootPayload] :
    HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp := by
  exact (supportClasses_of_rootPayload).2.2.2

/-- If the support payload is available, the bundled tail-VdC root payload is
also synthesized through existing support→tail wiring. -/
theorem tailRootPayload_of_supportRootPayload
    [B2SupportPhaseRootPayload] :
    Aristotle.Standalone.B2TailVdcRootInfra.B2TailVdcRootPayload := by
  infer_instance

instance (priority := 900) [B2SupportPhaseRootPayload] :
    Aristotle.Standalone.B2TailVdcRootInfra.B2TailVdcRootPayload := by
  exact tailRootPayload_of_supportRootPayload

/-- Root endpoint to B2 from the support-side payload. -/
theorem mainTermFirstMomentBound_of_rootPayload
    [B2SupportPhaseRootPayload] :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  exact Aristotle.Standalone.B2TailVdcRootInfra.mainTermFirstMomentBound_of_rootPayload

instance (priority := 875) [B2SupportPhaseRootPayload] :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  exact mainTermFirstMomentBound_of_rootPayload

/-- Promote existing support-side class assumptions into the bundled support
payload (non-instance helper, used for explicit wiring in deep-leaf closures). -/
theorem rootPayload_of_supportClasses
    [HardyFirstMomentWiring.HardyThetaDifferentiableOnSupportHyp]
    [HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    B2SupportPhaseRootPayload := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact HardyFirstMomentWiring.HardyThetaDifferentiableOnSupportHyp.differentiable
  · exact HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp.differentiable
  · exact HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp.bound
  · exact HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp.bound

/-- Non-circular constructor route:
support-side `Gamma` slit-plane control + phase-gap lower bounds + derivative
regularity + second-derivative decay imply the bundled B2 support payload.

This packages an upstream analytic route that does not depend on B2's deep
leaf/atomic wrappers. -/
theorem rootPayload_of_gammaSlit_gapSqrt_supportClasses
    [HardyFirstMomentWiring.HardyGammaInSlitPlaneOnSupportHyp]
    [HardyFirstMomentWiring.HardyThetaPhaseGapLowerSqrtModeOnSupportHyp]
    [HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    B2SupportPhaseRootPayload := by
  let _ : HardyFirstMomentWiring.HardyThetaDifferentiableOnSupportHyp := inferInstance
  let _ : HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp := inferInstance
  exact rootPayload_of_supportClasses

/-- Explicit (non-typeclass) non-circular constructor from the upstream
Gamma-slit/phase-gap route assumptions. -/
theorem rootPayload_of_explicit_gammaSlit_gapSqrt_support_package
    (hGammaSlit :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n) T,
          Complex.Gamma (1 / 4 + Complex.I * (t / 2)) ∈ Complex.slitPlane)
    (hGapSqrt :
      ∃ m > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n) T,
          m / Real.sqrt (n + 1)
            ≤ |deriv hardyTheta t - Real.log (n + 1)|)
    (hPhaseDerivDiff :
      ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n) T,
          DifferentiableAt ℝ (deriv (HardyFirstMomentWiring.hardyPhaseReal n)) t)
    (hSecondDerivBound :
      ∃ M > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n ≤ T →
        ∀ t ∈ Set.uIcc (hardyStart n) T,
          |deriv (deriv (HardyFirstMomentWiring.hardyPhaseReal n)) t|
            ≤ M / t ^ (3 / 2 : ℝ)) :
    B2SupportPhaseRootPayload := by
  letI : HardyFirstMomentWiring.HardyGammaInSlitPlaneOnSupportHyp := ⟨hGammaSlit⟩
  letI : HardyFirstMomentWiring.HardyThetaPhaseGapLowerSqrtModeOnSupportHyp := ⟨hGapSqrt⟩
  letI : HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp := ⟨hPhaseDerivDiff⟩
  letI : HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp := ⟨hSecondDerivBound⟩
  exact rootPayload_of_gammaSlit_gapSqrt_supportClasses

/-- Canonical non-circular constructor entrypoint for B2 support payload.
This theorem depends only on upstream support-side classes and does not use any
B2 deep-leaf/atomic closure. -/
theorem provide_noncircular_constructor_B2SupportPhaseRootPayload
    [HardyFirstMomentWiring.HardyGammaInSlitPlaneOnSupportHyp]
    [HardyFirstMomentWiring.HardyThetaPhaseGapLowerSqrtModeOnSupportHyp]
    [HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    B2SupportPhaseRootPayload := by
  exact rootPayload_of_gammaSlit_gapSqrt_supportClasses

/-- Class-level non-circular constructor endpoint for B2 support payload. -/
theorem b2SupportPhaseRootPayload_of_noncircular_support_classes
    [HardyFirstMomentWiring.HardyGammaInSlitPlaneOnSupportHyp]
    [HardyFirstMomentWiring.HardyThetaPhaseGapLowerSqrtModeOnSupportHyp]
    [HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    B2SupportPhaseRootPayload := by
  exact provide_noncircular_constructor_B2SupportPhaseRootPayload

/-- Direct endpoint for the bundled B2 support payload from the upstream
non-circular support class package. -/
theorem b2SupportPhaseRootPayload
    [HardyFirstMomentWiring.HardyGammaInSlitPlaneOnSupportHyp]
    [HardyFirstMomentWiring.HardyThetaPhaseGapLowerSqrtModeOnSupportHyp]
    [HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    B2SupportPhaseRootPayload := by
  exact b2SupportPhaseRootPayload_of_noncircular_support_classes

instance (priority := 840)
    [HardyFirstMomentWiring.HardyGammaInSlitPlaneOnSupportHyp]
    [HardyFirstMomentWiring.HardyThetaPhaseGapLowerSqrtModeOnSupportHyp]
    [HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    B2SupportPhaseRootPayload := by
  exact b2SupportPhaseRootPayload_of_noncircular_support_classes

end Aristotle.Standalone.B2SupportPhaseRootInfra
