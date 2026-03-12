import Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
import Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedRootEndpoint

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload

open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootEndpoint

/-- External-port payload class for the three RH-`pi` exact-seed obligations. -/
class ExternalExactSeedPayload : Prop where
  truncated : TruncatedExplicitFormulaPiHyp
  target :
    letI : TruncatedExplicitFormulaPiHyp := truncated
    TargetTowerExactSeedAbovePerronThreshold
  antiTarget :
    letI : TruncatedExplicitFormulaPiHyp := truncated
    AntiTargetTowerExactSeedAbovePerronThreshold

/-- Bridge external exact-seed payload into the bundled root payload class. -/
instance (priority := 100)
    [ExternalExactSeedPayload] :
    RHPiUnconditionalExactSeedRootPayload where
  truncated := ExternalExactSeedPayload.truncated
  target := by
    letI : TruncatedExplicitFormulaPiHyp := ExternalExactSeedPayload.truncated
    exact ExternalExactSeedPayload.target
  antiTarget := by
    letI : TruncatedExplicitFormulaPiHyp := ExternalExactSeedPayload.truncated
    exact ExternalExactSeedPayload.antiTarget

/-- Endpoint triple from an external exact-seed payload. -/
theorem exactSeedUnconditionalTriple_of_externalPayload
    [ExternalExactSeedPayload] :
    TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact exactSeedUnconditionalTriple_from_rootPayload

/-- Component endpoint: truncated explicit-formula payload. -/
theorem truncatedExplicitFormulaPi_of_externalPayload
    [ExternalExactSeedPayload] :
    TruncatedExplicitFormulaPiHyp :=
  truncatedExplicitFormulaPi_unconditional_from_rootPayload

/-- Component endpoint: target exact-seed payload. -/
theorem targetTowerExactSeedAbovePerronThreshold_of_externalPayload
    [ExternalExactSeedPayload] :
    TargetTowerExactSeedAbovePerronThreshold :=
  targetTowerExactSeedAbovePerronThreshold_unconditional_from_rootPayload

/-- Component endpoint: anti-target exact-seed payload. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_of_externalPayload
    [ExternalExactSeedPayload] :
    AntiTargetTowerExactSeedAbovePerronThreshold :=
  antiTargetTowerExactSeedAbovePerronThreshold_unconditional_from_rootPayload

end Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload

