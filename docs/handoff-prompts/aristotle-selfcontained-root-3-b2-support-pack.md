# Aristotle Prompt 3: B2 Support Constructor Pack

You are Aristotle. Return exactly one Lean file and nothing else.

Hard constraints:
- No `axiom`, `postulate`, `sorry`, `admit`.
- Keep names/signatures unchanged.

```lean
import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false
noncomputable section

namespace HardyFirstMomentWiring

class HardyGammaInSlitPlaneOnSupportHyp : Prop where
  inSlit : True

class HardyThetaPhaseGapLowerSqrtModeOnSupportHyp : Prop where
  bound : True

class HardyPhaseDerivDifferentiableOnSupportHyp : Prop where
  differentiable : True

class HardyExpPhaseSecondDerivAbsBoundOnSupportHyp : Prop where
  bound : True

class HardyThetaDifferentiableOnSupportHyp : Prop where
  differentiable : True

class HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp : Prop where
  bound : True

end HardyFirstMomentWiring

namespace Aristotle.Standalone.B2SupportPhaseRootInfra
open HardyFirstMomentWiring

class B2SupportPhaseRootPayload : Prop where
  thetaDiff : True
  phaseDerivDiff : True
  derivLowerSqrt : True
  secondDerivBound : True

theorem rootPayload_of_supportClasses
    [HardyThetaDifferentiableOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp]
    [HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    B2SupportPhaseRootPayload := by
  exact ⟨True.intro, True.intro, True.intro, True.intro⟩

instance (priority := 950) [B2SupportPhaseRootPayload] :
    HardyThetaDifferentiableOnSupportHyp := ⟨True.intro⟩

instance (priority := 950) [B2SupportPhaseRootPayload] :
    HardyPhaseDerivDifferentiableOnSupportHyp := ⟨True.intro⟩

instance (priority := 950) [B2SupportPhaseRootPayload] :
    HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp := ⟨True.intro⟩

instance (priority := 950) [B2SupportPhaseRootPayload] :
    HardyExpPhaseSecondDerivAbsBoundOnSupportHyp := ⟨True.intro⟩

theorem rootPayload_of_gammaSlit_gapSqrt_supportClasses
    [HardyGammaInSlitPlaneOnSupportHyp]
    [HardyThetaPhaseGapLowerSqrtModeOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    B2SupportPhaseRootPayload := by
  let _ : HardyThetaDifferentiableOnSupportHyp := ⟨True.intro⟩
  let _ : HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp := ⟨True.intro⟩
  exact rootPayload_of_supportClasses

theorem provide_noncircular_constructor_B2SupportPhaseRootPayload
    [HardyGammaInSlitPlaneOnSupportHyp]
    [HardyThetaPhaseGapLowerSqrtModeOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    B2SupportPhaseRootPayload := by
  exact rootPayload_of_gammaSlit_gapSqrt_supportClasses

instance (priority := 840)
    [HardyGammaInSlitPlaneOnSupportHyp]
    [HardyThetaPhaseGapLowerSqrtModeOnSupportHyp]
    [HardyPhaseDerivDifferentiableOnSupportHyp]
    [HardyExpPhaseSecondDerivAbsBoundOnSupportHyp] :
    B2SupportPhaseRootPayload := by
  exact provide_noncircular_constructor_B2SupportPhaseRootPayload

#check provide_noncircular_constructor_B2SupportPhaseRootPayload
#synth B2SupportPhaseRootPayload

end Aristotle.Standalone.B2SupportPhaseRootInfra
```
