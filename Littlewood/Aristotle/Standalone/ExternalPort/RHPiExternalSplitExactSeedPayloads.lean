import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.RHPiExternalSplitExactSeedPayloads

open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload

/-- External split payload lane for the truncated explicit-formula witness only. -/
class ExternalTruncatedPiPayload : Prop where
  witness : TruncatedExplicitFormulaPiHyp

/-- External split payload lane for the positive exact-seed witness, parameterized
by a truncated explicit-formula witness. -/
class ExternalTargetExactSeedPayload
    [TruncatedExplicitFormulaPiHyp] : Prop where
  witness : TargetTowerExactSeedAbovePerronThreshold

/-- External split payload lane for the anti-target exact-seed witness,
parameterized by a truncated explicit-formula witness. -/
class ExternalAntiTargetExactSeedPayload
    [TruncatedExplicitFormulaPiHyp] : Prop where
  witness : AntiTargetTowerExactSeedAbovePerronThreshold

/-- Auto-wire the truncated explicit-formula class from the split truncated lane. -/
instance (priority := 100)
    [ExternalTruncatedPiPayload] :
    TruncatedExplicitFormulaPiHyp :=
  ExternalTruncatedPiPayload.witness

/-- Fuse the three split RH-pi lanes into the canonical external exact-seed
payload class already consumed by root-infra auto-wiring. -/
instance (priority := 90)
    [ExternalTruncatedPiPayload]
    [ExternalTargetExactSeedPayload]
    [ExternalAntiTargetExactSeedPayload] :
    ExternalExactSeedPayload where
  truncated := ExternalTruncatedPiPayload.witness
  target := by
    letI : TruncatedExplicitFormulaPiHyp := ExternalTruncatedPiPayload.witness
    exact ExternalTargetExactSeedPayload.witness
  antiTarget := by
    letI : TruncatedExplicitFormulaPiHyp := ExternalTruncatedPiPayload.witness
    exact ExternalAntiTargetExactSeedPayload.witness

/-- Endpoint: split RH-pi lanes recover the bundled root payload class used by
the unconditional endpoint file. -/
theorem rhpi_rootPayload_of_external_split_payloads
    [ExternalTruncatedPiPayload]
    [ExternalTargetExactSeedPayload]
    [ExternalAntiTargetExactSeedPayload] :
    RHPiUnconditionalExactSeedRootPayload := by
  infer_instance

/-- Endpoint: split RH-pi lanes recover all three exact-seed obligations. -/
theorem exactSeedUnconditionalTriple_of_external_split_payloads
    [ExternalTruncatedPiPayload]
    [ExternalTargetExactSeedPayload]
    [ExternalAntiTargetExactSeedPayload] :
    TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact exactSeedUnconditionalTriple_of_externalPayload

/-- Component endpoint: truncated explicit-formula payload from split RH-pi
lanes. -/
theorem truncatedExplicitFormulaPi_of_external_split_payloads
    [ExternalTruncatedPiPayload]
    [ExternalTargetExactSeedPayload]
    [ExternalAntiTargetExactSeedPayload] :
    TruncatedExplicitFormulaPiHyp := by
  exact truncatedExplicitFormulaPi_of_externalPayload

/-- Component endpoint: positive exact-seed payload from split RH-pi lanes. -/
theorem targetTowerExactSeedAbovePerronThreshold_of_external_split_payloads
    [ExternalTruncatedPiPayload]
    [ExternalTargetExactSeedPayload]
    [ExternalAntiTargetExactSeedPayload] :
    TargetTowerExactSeedAbovePerronThreshold := by
  exact targetTowerExactSeedAbovePerronThreshold_of_externalPayload

/-- Component endpoint: anti-target exact-seed payload from split RH-pi lanes. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_of_external_split_payloads
    [ExternalTruncatedPiPayload]
    [ExternalTargetExactSeedPayload]
    [ExternalAntiTargetExactSeedPayload] :
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact antiTargetTowerExactSeedAbovePerronThreshold_of_externalPayload

end Aristotle.Standalone.ExternalPort.RHPiExternalSplitExactSeedPayloads
