import Mathlib
import Littlewood.Aristotle.Standalone.B2StationaryWindowSplit
import Littlewood.Aristotle.Standalone.B2AngularTailRootInfra
import Littlewood.Aristotle.Standalone.B2TailStationaryBranchFree
import Littlewood.Aristotle.Standalone.B2TailVdcDeepLeaf

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.B2StationaryWindowLeaves

open MeasureTheory Set
open HardyEstimatesPartial

/-- Atomic B2 near-window leaf:
uniform `sqrt(n+1)` control for the short interval
`[hardyStart n, min(T, hardyStart n + sqrt(n+1))]`. -/
theorem nearWindowBound_sorry :
    Aristotle.Standalone.B2StationaryWindowSplit.B2HardyCosNearWindowPayload := by
  refine ⟨1, by norm_num, ?_⟩
  intro n T hT
  let c : ℝ := min T (hardyStart n + Real.sqrt (n + 1))
  by_cases hstart : hardyStart n ≤ T
  · have hstart_le_c : hardyStart n ≤ c := by
      unfold c
      exact le_min hstart (le_add_of_nonneg_right (Real.sqrt_nonneg _))
    have h_abs :
        |∫ t in Ioc (hardyStart n) c, hardyCos n t|
          ≤ ∫ t in hardyStart n..c, |hardyCos n t| := by
      calc
        |∫ t in Ioc (hardyStart n) c, hardyCos n t|
            = |∫ t in hardyStart n..c, hardyCos n t| := by
                rw [← intervalIntegral.integral_of_le hstart_le_c]
        _ ≤ ∫ t in hardyStart n..c, |hardyCos n t| := by
              simpa [Real.norm_eq_abs] using
                (intervalIntegral.norm_integral_le_integral_norm
                  (f := fun t : ℝ => hardyCos n t) hstart_le_c)
    have h_int_le :
        ∫ t in hardyStart n..c, |hardyCos n t|
          ≤ ∫ t in hardyStart n..c, (1 : ℝ) := by
      refine intervalIntegral.integral_mono_on hstart_le_c ?_ ?_ ?_
      · exact
          (continuous_abs.comp (HardyCosSmooth.continuous_hardyCos n)).intervalIntegrable _ _
      · exact (continuous_const).intervalIntegrable _ _
      · intro t ht
        simpa [HardyEstimatesPartial.hardyCos] using
          (Real.abs_cos_le_one (hardyTheta t - t * Real.log (n + 1)))
    have hc_le : c ≤ hardyStart n + Real.sqrt (n + 1) := by
      unfold c
      exact min_le_right _ _
    calc
      |∫ t in Ioc (hardyStart n) (min T (hardyStart n + Real.sqrt (n + 1))), hardyCos n t|
          = |∫ t in Ioc (hardyStart n) c, hardyCos n t| := by rfl
      _ ≤ ∫ t in hardyStart n..c, |hardyCos n t| := h_abs
      _ ≤ ∫ t in hardyStart n..c, (1 : ℝ) := h_int_le
      _ = c - hardyStart n := by simp
      _ ≤ Real.sqrt (n + 1) := by linarith
      _ = 1 * Real.sqrt (n + 1) := by ring
  · have hc_le_T : c ≤ T := by
      unfold c
      exact min_le_left _ _
    have hmain_zero :
        ∫ t in Ioc (hardyStart n) c, hardyCos n t = 0 := by
      have hEmpty : Ioc (hardyStart n) c = ∅ := by
        apply Set.Ioc_eq_empty
        intro hlt
        exact hstart (le_trans (le_of_lt hlt) hc_le_T)
      simp [hEmpty]
    calc
      |∫ t in Ioc (hardyStart n) (min T (hardyStart n + Real.sqrt (n + 1))), hardyCos n t|
          = |∫ t in Ioc (hardyStart n) c, hardyCos n t| := by rfl
      _ = 0 := by simp [hmain_zero]
      _ ≤ 1 * Real.sqrt (n + 1) := by positivity

/-- Atomic B2 tail-window leaf packaged as the stationary-tail class payload.

This is the single remaining analytic obligation for B2. -/
private theorem hardyCosExpTailBound_of_stationaryTailClass
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

private theorem stationaryTailClass_of_tailVdcClass
    (hTailVdc : HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp) :
    HardyFirstMomentWiring.HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp := by
  let _ : HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp := hTailVdc
  infer_instance

private theorem stationaryTailClass_sorry :
    HardyFirstMomentWiring.HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp := by
  exact
    stationaryTailClass_of_tailVdcClass
      Aristotle.Standalone.B2TailVdcDeepLeaf.tailVdcSqrtModeClass_leaf

private theorem hardyCosExpTailBound_sorry :
    ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      hardyStart n + Real.sqrt (n + 1) ≤ T →
      ‖∫ t in (hardyStart n + Real.sqrt (n + 1))..T,
          HardyCosSmooth.hardyCosExp n t‖ ≤ B * Real.sqrt (n + 1) := by
  letI :
      HardyFirstMomentWiring.HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp :=
    stationaryTailClass_sorry
  exact hardyCosExpTailBound_of_stationaryTailClass

/-- Existential tail bound extracted from `stationaryTailClass_sorry`. -/
private theorem tailHardyExpPhaseBound_sorry :
    ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      hardyStart n + Real.sqrt (n + 1) ≤ T →
      ‖∫ t in (hardyStart n + Real.sqrt (n + 1))..T,
          HardyFirstMomentWiring.hardyExpPhase n t‖ ≤ B * Real.sqrt (n + 1) :=
  stationaryTailClass_sorry.bound

theorem tailWindowBound_sorry :
    Aristotle.Standalone.B2StationaryWindowSplit.B2HardyCosTailWindowPayload := by
  exact
    Aristotle.Standalone.B2StationaryWindowSplit.tailWindowPayload_of_hardyExpPhaseTailBound
      tailHardyExpPhaseBound_sorry

/-- Consolidated B2 output assembled from the two split-window leaves. -/
theorem mainTermFirstMomentBoundHyp_from_windowLeaves :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  exact
    Aristotle.Standalone.B2StationaryWindowSplit.mainTermFirstMomentBoundHyp_of_near_and_tail
      nearWindowBound_sorry tailWindowBound_sorry

/-- Non-circular B2 endpoint: once the support-side Gamma/phase package is
provided, the split-window assembly closes without the delegated leaf. -/
theorem mainTermFirstMomentBoundHyp_from_windowLeaves_of_noncircular_support_constructor
    [HardyFirstMomentWiring.HardyGammaInSlitPlaneOnSupportHyp]
    [HardyFirstMomentWiring.HardyThetaPhaseGapLowerSqrtModeOnSupportHyp]
    [HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  let hTailVdc :
      HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp :=
    Aristotle.Standalone.B2TailVdcDeepLeaf.tailVdcSqrtModeClass_of_noncircular_support_constructor
  let hStationary :
      HardyFirstMomentWiring.HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp :=
    stationaryTailClass_of_tailVdcClass hTailVdc
  let hTailExp :
      ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ‖∫ t in (hardyStart n + Real.sqrt (n + 1))..T,
            HardyFirstMomentWiring.hardyExpPhase n t‖ ≤ B * Real.sqrt (n + 1) :=
    hStationary.bound
  have hTailWindow :
      Aristotle.Standalone.B2StationaryWindowSplit.B2HardyCosTailWindowPayload := by
    exact
      Aristotle.Standalone.B2StationaryWindowSplit.tailWindowPayload_of_hardyExpPhaseTailBound
        hTailExp
  exact
    Aristotle.Standalone.B2StationaryWindowSplit.mainTermFirstMomentBoundHyp_of_near_and_tail
      nearWindowBound_sorry hTailWindow

/-- Same non-circular endpoint, exposed at the bundled-root-payload layer. -/
theorem mainTermFirstMomentBoundHyp_from_windowLeaves_of_supportRootPayload
    [Aristotle.Standalone.B2SupportPhaseRootInfra.B2SupportPhaseRootPayload] :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  let hTailVdc :
      HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp :=
    Aristotle.Standalone.B2TailVdcDeepLeaf.tailVdcSqrtModeClass_candidate_of_supportRootPayload
  let hStationary :
      HardyFirstMomentWiring.HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp :=
    stationaryTailClass_of_tailVdcClass hTailVdc
  let hTailExp :
      ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
        hardyStart n + Real.sqrt (n + 1) ≤ T →
        ‖∫ t in (hardyStart n + Real.sqrt (n + 1))..T,
            HardyFirstMomentWiring.hardyExpPhase n t‖ ≤ B * Real.sqrt (n + 1) :=
    hStationary.bound
  have hTailWindow :
      Aristotle.Standalone.B2StationaryWindowSplit.B2HardyCosTailWindowPayload := by
    exact
      Aristotle.Standalone.B2StationaryWindowSplit.tailWindowPayload_of_hardyExpPhaseTailBound
        hTailExp
  exact
    Aristotle.Standalone.B2StationaryWindowSplit.mainTermFirstMomentBoundHyp_of_near_and_tail
      nearWindowBound_sorry hTailWindow

/-- If a stationary-tail class provider is available, the branch-free angular
root payload is synthesized by combining it with the proved near-window leaf. -/
theorem angularRootPayload_of_stationaryTailClass
    [HardyFirstMomentWiring.HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp] :
    Aristotle.Standalone.B2AngularTailRootInfra.B2AngularTailRootPayload := by
  exact
    Aristotle.Standalone.B2AngularTailRootInfra.rootPayload_of_near_and_stationaryTailClass
      nearWindowBound_sorry

/-- Branch-free B2 endpoint from the bundled angular near+tail payload. -/
theorem mainTermFirstMomentBoundHyp_from_angularRootPayload
    [Aristotle.Standalone.B2AngularTailRootInfra.B2AngularTailRootPayload] :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  exact Aristotle.Standalone.B2AngularTailRootInfra.mainTermFirstMomentBound_of_rootPayload

end Aristotle.Standalone.B2StationaryWindowLeaves
