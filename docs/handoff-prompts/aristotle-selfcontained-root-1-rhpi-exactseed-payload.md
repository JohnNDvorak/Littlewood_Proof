# Aristotle Prompt 1: RH-pi Root Payload Constructor

You are Aristotle. Return exactly one Lean file and nothing else.

Hard constraints:
- No `axiom`, `postulate`, `sorry`, `admit`.
- Keep all names and theorem signatures exactly.
- Use only Mathlib + declarations in this prompt.

```lean
import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false
noncomputable section

namespace PiLiDirectOscillationBridge

class TruncatedExplicitFormulaPiHyp : Prop where
  pi_approx : True
  zero_sum_neg_frequently : True

end PiLiDirectOscillationBridge

namespace Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open PiLiDirectOscillationBridge

abbrev TargetTowerExactSeedAbovePerronThreshold
    [TruncatedExplicitFormulaPiHyp] : Prop := True

abbrev AntiTargetTowerExactSeedAbovePerronThreshold
    [TruncatedExplicitFormulaPiHyp] : Prop := True

end Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox

namespace Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra

open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox

class RHPiUnconditionalExactSeedRootPayload : Prop where
  truncated : TruncatedExplicitFormulaPiHyp
  target :
    letI : TruncatedExplicitFormulaPiHyp := truncated
    TargetTowerExactSeedAbovePerronThreshold
  antiTarget :
    letI : TruncatedExplicitFormulaPiHyp := truncated
    AntiTargetTowerExactSeedAbovePerronThreshold

theorem truncatedExplicitFormulaPi_of_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] : TruncatedExplicitFormulaPiHyp :=
  RHPiUnconditionalExactSeedRootPayload.truncated

theorem targetTowerExactSeedAbovePerronThreshold_of_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] :
    TargetTowerExactSeedAbovePerronThreshold := by
  letI : TruncatedExplicitFormulaPiHyp := RHPiUnconditionalExactSeedRootPayload.truncated
  simpa using RHPiUnconditionalExactSeedRootPayload.target

theorem antiTargetTowerExactSeedAbovePerronThreshold_of_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] :
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  letI : TruncatedExplicitFormulaPiHyp := RHPiUnconditionalExactSeedRootPayload.truncated
  simpa using RHPiUnconditionalExactSeedRootPayload.antiTarget

class RHPiConcreteTriplePayload : Prop where
  hTrunc : TruncatedExplicitFormulaPiHyp
  hTarget :
    letI : TruncatedExplicitFormulaPiHyp := hTrunc
    TargetTowerExactSeedAbovePerronThreshold
  hAnti :
    letI : TruncatedExplicitFormulaPiHyp := hTrunc
    AntiTargetTowerExactSeedAbovePerronThreshold

theorem rootPayload_of_concrete_triple
    [RHPiConcreteTriplePayload] :
    RHPiUnconditionalExactSeedRootPayload := by
  refine ⟨RHPiConcreteTriplePayload.hTrunc, ?_, ?_⟩
  · letI : TruncatedExplicitFormulaPiHyp := RHPiConcreteTriplePayload.hTrunc
    simpa using RHPiConcreteTriplePayload.hTarget
  · letI : TruncatedExplicitFormulaPiHyp := RHPiConcreteTriplePayload.hTrunc
    simpa using RHPiConcreteTriplePayload.hAnti

instance (priority := 900)
    [RHPiConcreteTriplePayload] :
    RHPiUnconditionalExactSeedRootPayload :=
  rootPayload_of_concrete_triple

#check truncatedExplicitFormulaPi_of_rootPayload
#check targetTowerExactSeedAbovePerronThreshold_of_rootPayload
#check antiTargetTowerExactSeedAbovePerronThreshold_of_rootPayload

end Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
```
