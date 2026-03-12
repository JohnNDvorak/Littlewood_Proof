import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedAutoInstances

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.RHPiExternalConcreteExactSeedLane

open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload
open Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedAutoInstances

/-- Build the external exact-seed payload class from a concrete theorem triple. -/
def externalExactSeedPayload_of_witness
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      TargetTowerExactSeedAbovePerronThreshold)
    (hAntiTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      AntiTargetTowerExactSeedAbovePerronThreshold) :
    ExternalExactSeedPayload where
  truncated := hTruncated
  target := by
    letI : TruncatedExplicitFormulaPiHyp := hTruncated
    simpa using hTarget
  antiTarget := by
    letI : TruncatedExplicitFormulaPiHyp := hTruncated
    simpa using hAntiTarget

/-- Bundled concrete witness carrying all three RH-pi exact-seed obligations. -/
structure ConcreteExactSeedTriple : Type where
  truncated : TruncatedExplicitFormulaPiHyp
  target :
    letI : TruncatedExplicitFormulaPiHyp := truncated
    TargetTowerExactSeedAbovePerronThreshold
  antiTarget :
    letI : TruncatedExplicitFormulaPiHyp := truncated
    AntiTargetTowerExactSeedAbovePerronThreshold

/-- Build the external exact-seed payload class from one bundled witness term. -/
def externalExactSeedPayload_of_triple
    (hTriple : ConcreteExactSeedTriple) :
    ExternalExactSeedPayload :=
  externalExactSeedPayload_of_witness
    hTriple.truncated
    hTriple.target
    hTriple.antiTarget

/-- Endpoint: recover the unconditional truncated explicit-formula payload from a
concrete theorem triple. -/
theorem truncatedExplicitFormulaPi_of_concrete_external_witness
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      TargetTowerExactSeedAbovePerronThreshold)
    (hAntiTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      AntiTargetTowerExactSeedAbovePerronThreshold) :
    TruncatedExplicitFormulaPiHyp := by
  letI : ExternalExactSeedPayload :=
    externalExactSeedPayload_of_witness hTruncated hTarget hAntiTarget
  exact truncatedExplicitFormulaPi_of_externalPayload

/-- Endpoint: recover the positive exact-seed payload from a concrete theorem triple. -/
theorem targetTowerExactSeedAbovePerronThreshold_of_concrete_external_witness
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      TargetTowerExactSeedAbovePerronThreshold)
    (hAntiTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      AntiTargetTowerExactSeedAbovePerronThreshold) :
    TargetTowerExactSeedAbovePerronThreshold := by
  letI : ExternalExactSeedPayload :=
    externalExactSeedPayload_of_witness hTruncated hTarget hAntiTarget
  exact targetTowerExactSeedAbovePerronThreshold_of_externalPayload

/-- Endpoint: recover the anti-target exact-seed payload from a concrete theorem triple. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_of_concrete_external_witness
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      TargetTowerExactSeedAbovePerronThreshold)
    (hAntiTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      AntiTargetTowerExactSeedAbovePerronThreshold) :
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  letI : ExternalExactSeedPayload :=
    externalExactSeedPayload_of_witness hTruncated hTarget hAntiTarget
  exact antiTargetTowerExactSeedAbovePerronThreshold_of_externalPayload

/-- Endpoint: recover all three RH-pi exact-seed obligations from one concrete
theorem triple. -/
theorem exactSeedTriple_of_concrete_external_witness
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      TargetTowerExactSeedAbovePerronThreshold)
    (hAntiTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      AntiTargetTowerExactSeedAbovePerronThreshold) :
    TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  letI : ExternalExactSeedPayload :=
    externalExactSeedPayload_of_witness hTruncated hTarget hAntiTarget
  exact exactSeedUnconditionalTriple_of_externalPayload

/-- Endpoint: recover the unconditional truncated explicit-formula payload from
one bundled witness term. -/
theorem truncatedExplicitFormulaPi_of_concrete_external_triple
    (hTriple : ConcreteExactSeedTriple) :
    TruncatedExplicitFormulaPiHyp := by
  letI : ExternalExactSeedPayload := externalExactSeedPayload_of_triple hTriple
  exact truncatedExplicitFormulaPi_of_externalPayload

/-- Endpoint: recover the positive exact-seed payload from one bundled witness
term. -/
theorem targetTowerExactSeedAbovePerronThreshold_of_concrete_external_triple
    (hTriple : ConcreteExactSeedTriple) :
    letI : TruncatedExplicitFormulaPiHyp := hTriple.truncated
    TargetTowerExactSeedAbovePerronThreshold := by
  letI : ExternalExactSeedPayload := externalExactSeedPayload_of_triple hTriple
  exact targetTowerExactSeedAbovePerronThreshold_of_externalPayload

/-- Endpoint: recover the anti-target exact-seed payload from one bundled witness
term. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_of_concrete_external_triple
    (hTriple : ConcreteExactSeedTriple) :
    letI : TruncatedExplicitFormulaPiHyp := hTriple.truncated
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  letI : ExternalExactSeedPayload := externalExactSeedPayload_of_triple hTriple
  exact antiTargetTowerExactSeedAbovePerronThreshold_of_externalPayload

/-- Endpoint: recover all three RH-pi exact-seed obligations from one bundled
witness term. -/
theorem exactSeedTriple_of_concrete_external_triple
    (hTriple : ConcreteExactSeedTriple) :
    TruncatedExplicitFormulaPiHyp ∧
      (letI : TruncatedExplicitFormulaPiHyp := hTriple.truncated
       TargetTowerExactSeedAbovePerronThreshold ∧
       AntiTargetTowerExactSeedAbovePerronThreshold) := by
  letI : ExternalExactSeedPayload := externalExactSeedPayload_of_triple hTriple
  refine ⟨truncatedExplicitFormulaPi_of_externalPayload, ?_⟩
  exact
    ⟨targetTowerExactSeedAbovePerronThreshold_of_externalPayload,
      antiTargetTowerExactSeedAbovePerronThreshold_of_externalPayload⟩

end Aristotle.Standalone.ExternalPort.RHPiExternalConcreteExactSeedLane
