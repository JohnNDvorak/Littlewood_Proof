import Littlewood.Bridge.PiLiDirectOscillation
import Littlewood.Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra

open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox

/-- Root class for supplying the truncated explicit-formula payload for RH-`pi`. -/
class TruncatedExplicitFormulaPiRootHyp : Prop where
  witness : TruncatedExplicitFormulaPiHyp

/-- Root class for supplying the positive exact-seed payload above Perron's threshold. -/
class TargetTowerExactSeedAbovePerronThresholdRootHyp
    [TruncatedExplicitFormulaPiHyp] : Prop where
  witness : TargetTowerExactSeedAbovePerronThreshold

/-- Root class for supplying the anti-target exact-seed payload above Perron's threshold. -/
class AntiTargetTowerExactSeedAbovePerronThresholdRootHyp
    [TruncatedExplicitFormulaPiHyp] : Prop where
  witness : AntiTargetTowerExactSeedAbovePerronThreshold

/-- Bundled root payload for the three unconditional RH-`pi` boundary obligations.

This avoids circular dependence on `RHPiUnconditionalExactSeedExistence` while
exposing exactly the data needed to close its three endpoint theorems. -/
class RHPiUnconditionalExactSeedRootPayload : Prop where
  truncated : TruncatedExplicitFormulaPiHyp
  target :
    letI : TruncatedExplicitFormulaPiHyp := truncated
    TargetTowerExactSeedAbovePerronThreshold
  antiTarget :
    letI : TruncatedExplicitFormulaPiHyp := truncated
    AntiTargetTowerExactSeedAbovePerronThreshold

/-- Bridge split root explicit-formula payload into the global class instance. -/
instance truncatedExplicitFormulaPi_of_rootHyp
    [TruncatedExplicitFormulaPiRootHyp] : TruncatedExplicitFormulaPiHyp :=
  TruncatedExplicitFormulaPiRootHyp.witness

/-- Bridge bundled root payload into the global explicit-formula payload class. -/
instance truncatedExplicitFormulaPi_inst_of_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] : TruncatedExplicitFormulaPiHyp :=
  RHPiUnconditionalExactSeedRootPayload.truncated

/-- Promote the split root classes to the bundled root payload class. -/
instance rootPayload_of_split
    [TruncatedExplicitFormulaPiRootHyp]
    [TargetTowerExactSeedAbovePerronThresholdRootHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdRootHyp] :
    RHPiUnconditionalExactSeedRootPayload where
  truncated := TruncatedExplicitFormulaPiRootHyp.witness
  target := by
    letI : TruncatedExplicitFormulaPiHyp := TruncatedExplicitFormulaPiRootHyp.witness
    exact TargetTowerExactSeedAbovePerronThresholdRootHyp.witness
  antiTarget := by
    letI : TruncatedExplicitFormulaPiHyp := TruncatedExplicitFormulaPiRootHyp.witness
    exact AntiTargetTowerExactSeedAbovePerronThresholdRootHyp.witness

/-- Recover the explicit-formula payload from the bundled root payload class. -/
theorem truncatedExplicitFormulaPi_of_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] : TruncatedExplicitFormulaPiHyp :=
  RHPiUnconditionalExactSeedRootPayload.truncated

/-- Recover the positive exact-seed payload from the bundled root payload class. -/
theorem targetTowerExactSeedAbovePerronThreshold_of_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] :
    TargetTowerExactSeedAbovePerronThreshold := by
  letI : TruncatedExplicitFormulaPiHyp :=
    RHPiUnconditionalExactSeedRootPayload.truncated
  simpa using RHPiUnconditionalExactSeedRootPayload.target

/-- Recover the anti-target exact-seed payload from the bundled root payload class. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_of_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] :
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  letI : TruncatedExplicitFormulaPiHyp :=
    RHPiUnconditionalExactSeedRootPayload.truncated
  simpa using RHPiUnconditionalExactSeedRootPayload.antiTarget

/-- Bridge split positive exact-seed root payload into the class wrapper used downstream. -/
instance targetTowerExactSeedAbovePerronThresholdHyp_of_split
    [TruncatedExplicitFormulaPiRootHyp]
    [TargetTowerExactSeedAbovePerronThresholdRootHyp] :
    TargetTowerExactSeedAbovePerronThresholdHyp where
  witness := by
    letI : TruncatedExplicitFormulaPiHyp := TruncatedExplicitFormulaPiRootHyp.witness
    exact TargetTowerExactSeedAbovePerronThresholdRootHyp.witness

/-- Bridge split anti-target exact-seed root payload into the class wrapper used downstream. -/
instance antiTargetTowerExactSeedAbovePerronThresholdHyp_of_split
    [TruncatedExplicitFormulaPiRootHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdRootHyp] :
    AntiTargetTowerExactSeedAbovePerronThresholdHyp where
  witness := by
    letI : TruncatedExplicitFormulaPiHyp := TruncatedExplicitFormulaPiRootHyp.witness
    exact AntiTargetTowerExactSeedAbovePerronThresholdRootHyp.witness

/-- Bridge bundled root payload into the positive exact-seed class wrapper. -/
instance targetTowerExactSeedAbovePerronThresholdHyp_of_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] :
    TargetTowerExactSeedAbovePerronThresholdHyp where
  witness := targetTowerExactSeedAbovePerronThreshold_of_rootPayload

/-- Bridge bundled root payload into the anti-target exact-seed class wrapper. -/
instance antiTargetTowerExactSeedAbovePerronThresholdHyp_of_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] :
    AntiTargetTowerExactSeedAbovePerronThresholdHyp where
  witness := antiTargetTowerExactSeedAbovePerronThreshold_of_rootPayload

end Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
