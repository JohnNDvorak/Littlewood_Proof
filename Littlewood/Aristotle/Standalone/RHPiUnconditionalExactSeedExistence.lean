import Littlewood.Bridge.PiLiDirectOscillation
import Littlewood.Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
import Littlewood.Aristotle.Standalone.RHPiExactSeedDeepLeaf
import Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
import Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedRootEndpoint
import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalConcreteExactSeedLane
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedBundleCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTConcreteProviderAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalTruncatedPiBuilder
import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiUnconditionalExactSeedExistence

open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootEndpoint
open Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedAutoInstances
open Aristotle.Standalone.ExternalPort.RHPiExternalConcreteExactSeedLane
open Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedBundleCompat
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadAutoInstances
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors
open Aristotle.Standalone.ExternalPort.StrongPNTConcreteProviderAutoInstances
open Aristotle.Standalone.ExternalPort.RHPiExternalTruncatedPiBuilder
open Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider

variable [PiLiDirectOscillationBridge.TruncatedExplicitFormulaPiHyp]
variable [Littlewood.Development.ShiftedRemainderInterface.ShiftedRemainderSegmentBoundLargeTHyp]
variable [Littlewood.Development.HadamardProductZeta.SmallTPerronBoundHyp]
variable [Aristotle.Standalone.PerronExplicitFormulaProvider.PerronPiApproxCompatibilityHyp]
variable [Aristotle.Standalone.PerronExplicitFormulaProvider.InhomogeneousPhaseFitAbovePerronThresholdHyp]

/-- Candidate closure route for the truncated explicit-formula payload from the
bundled RH-`pi` root payload class. -/
theorem truncatedExplicitFormulaPi_unconditional_of_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] :
    TruncatedExplicitFormulaPiHyp := by
  exact truncatedExplicitFormulaPi_unconditional_from_rootPayload

/-- Candidate closure route for the positive exact-seed payload from the bundled
RH-`pi` root payload class. -/
theorem targetTowerExactSeedAbovePerronThreshold_unconditional_of_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] :
    TargetTowerExactSeedAbovePerronThreshold := by
  exact targetTowerExactSeedAbovePerronThreshold_unconditional_from_rootPayload

/-- Candidate closure route for the anti-target exact-seed payload from the bundled
RH-`pi` root payload class. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_unconditional_of_rootPayload
    [RHPiUnconditionalExactSeedRootPayload] :
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact antiTargetTowerExactSeedAbovePerronThreshold_unconditional_from_rootPayload

/-- Candidate closure route from an external exact-seed payload class instance
through the auto-wired root-constructor lane. -/
theorem exactSeedUnconditionalTriple_of_externalPayload
    [Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload.ExternalExactSeedPayload] :
    TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact exactSeedUnconditionalTriple_of_externalPayload_auto

/-- Candidate closure route for `truncatedExplicitFormulaPi_unconditional`
from an external exact-seed payload class instance. -/
theorem truncatedExplicitFormulaPi_unconditional_of_externalPayload
    [Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload.ExternalExactSeedPayload] :
    TruncatedExplicitFormulaPiHyp := by
  infer_instance

/-- Candidate closure route for
`targetTowerExactSeedAbovePerronThreshold_unconditional` from an external
exact-seed payload class instance. -/
theorem targetTowerExactSeedAbovePerronThreshold_unconditional_of_externalPayload
    [Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload.ExternalExactSeedPayload] :
    TargetTowerExactSeedAbovePerronThreshold := by
  exact targetTowerExactSeedAbovePerronThreshold_unconditional_from_rootPayload

/-- Candidate closure route for
`antiTargetTowerExactSeedAbovePerronThreshold_unconditional` from an external
exact-seed payload class instance. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_unconditional_of_externalPayload
    [Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload.ExternalExactSeedPayload] :
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact antiTargetTowerExactSeedAbovePerronThreshold_unconditional_from_rootPayload

/-- Candidate closure route from one concrete external exact-seed witness triple. -/
theorem exactSeedUnconditionalTriple_of_concrete_external_witness
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
  exact exactSeedTriple_of_concrete_external_witness hTruncated hTarget hAntiTarget

/-- Candidate closure route from one bundled concrete external witness
carrying all three RH-`pi` exact-seed obligations. -/
theorem exactSeedUnconditionalTriple_of_concrete_external_triple
    (hTriple : ConcreteExactSeedTriple) :
    TruncatedExplicitFormulaPiHyp ∧
      (letI : TruncatedExplicitFormulaPiHyp := hTriple.truncated
       TargetTowerExactSeedAbovePerronThreshold ∧
       AntiTargetTowerExactSeedAbovePerronThreshold) := by
  exact exactSeedTriple_of_concrete_external_triple hTriple

/-- Candidate closure route from one bundled StrongPNT-style exact-seed witness
carrying all three RH-`pi` obligations. -/
theorem exactSeedUnconditionalTriple_of_strongpnt_bundle
    (hBundle : StrongPNTRHPiExactSeedBundle) :
    TruncatedExplicitFormulaPiHyp ∧
      (letI : TruncatedExplicitFormulaPiHyp := hBundle.truncatedPiFormula
       TargetTowerExactSeedAbovePerronThreshold ∧
       AntiTargetTowerExactSeedAbovePerronThreshold) := by
  exact rhpi_exactSeedTriple_of_strongpnt_bundle hBundle

/-- Candidate closure route for `truncatedExplicitFormulaPi_unconditional` from one
concrete external exact-seed witness triple. -/
theorem truncatedExplicitFormulaPi_unconditional_of_concrete_external_witness
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      TargetTowerExactSeedAbovePerronThreshold)
    (hAntiTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      AntiTargetTowerExactSeedAbovePerronThreshold) :
    TruncatedExplicitFormulaPiHyp := by
  exact
    truncatedExplicitFormulaPi_of_concrete_external_witness
      hTruncated hTarget hAntiTarget

/-- Candidate closure route for
`targetTowerExactSeedAbovePerronThreshold_unconditional` from one concrete
external exact-seed witness triple. -/
theorem targetTowerExactSeedAbovePerronThreshold_unconditional_of_concrete_external_witness
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      TargetTowerExactSeedAbovePerronThreshold)
    (hAntiTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      AntiTargetTowerExactSeedAbovePerronThreshold) :
    TargetTowerExactSeedAbovePerronThreshold := by
  exact
    targetTowerExactSeedAbovePerronThreshold_of_concrete_external_witness
      hTruncated hTarget hAntiTarget

/-- Candidate closure route for
`antiTargetTowerExactSeedAbovePerronThreshold_unconditional` from one concrete
external exact-seed witness triple. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_unconditional_of_concrete_external_witness
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      TargetTowerExactSeedAbovePerronThreshold)
    (hAntiTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      AntiTargetTowerExactSeedAbovePerronThreshold) :
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact
    antiTargetTowerExactSeedAbovePerronThreshold_of_concrete_external_witness
      hTruncated hTarget hAntiTarget

/-- Candidate closure route for `truncatedExplicitFormulaPi_unconditional` from one
bundled concrete external witness carrying all three obligations. -/
theorem truncatedExplicitFormulaPi_unconditional_of_concrete_external_triple
    (hTriple : ConcreteExactSeedTriple) :
    TruncatedExplicitFormulaPiHyp := by
  exact truncatedExplicitFormulaPi_of_concrete_external_triple hTriple

/-- Candidate closure route for `truncatedExplicitFormulaPi_unconditional` from one
bundled StrongPNT-style exact-seed witness carrying all three obligations. -/
theorem truncatedExplicitFormulaPi_unconditional_of_strongpnt_bundle
    (hBundle : StrongPNTRHPiExactSeedBundle) :
    TruncatedExplicitFormulaPiHyp := by
  exact truncatedExplicitFormulaPi_of_strongpnt_bundle hBundle

/-- Candidate closure route for
`targetTowerExactSeedAbovePerronThreshold_unconditional` from one bundled
concrete external witness carrying all three obligations. -/
theorem targetTowerExactSeedAbovePerronThreshold_unconditional_of_concrete_external_triple
    (hTriple : ConcreteExactSeedTriple) :
    letI : TruncatedExplicitFormulaPiHyp := hTriple.truncated
    TargetTowerExactSeedAbovePerronThreshold := by
  exact targetTowerExactSeedAbovePerronThreshold_of_concrete_external_triple hTriple

/-- Candidate closure route for
`targetTowerExactSeedAbovePerronThreshold_unconditional` from one bundled
StrongPNT-style exact-seed witness carrying all three obligations. -/
theorem targetTowerExactSeedAbovePerronThreshold_unconditional_of_strongpnt_bundle
    (hBundle : StrongPNTRHPiExactSeedBundle) :
    letI : TruncatedExplicitFormulaPiHyp := hBundle.truncatedPiFormula
    TargetTowerExactSeedAbovePerronThreshold := by
  exact targetTowerExactSeedAbovePerronThreshold_of_strongpnt_bundle hBundle

/-- Candidate closure route for
`antiTargetTowerExactSeedAbovePerronThreshold_unconditional` from one bundled
concrete external witness carrying all three obligations. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_unconditional_of_concrete_external_triple
    (hTriple : ConcreteExactSeedTriple) :
    letI : TruncatedExplicitFormulaPiHyp := hTriple.truncated
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact antiTargetTowerExactSeedAbovePerronThreshold_of_concrete_external_triple hTriple

/-- Candidate closure route for
`antiTargetTowerExactSeedAbovePerronThreshold_unconditional` from one bundled
StrongPNT-style exact-seed witness carrying all three obligations. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_unconditional_of_strongpnt_bundle
    (hBundle : StrongPNTRHPiExactSeedBundle) :
    letI : TruncatedExplicitFormulaPiHyp := hBundle.truncatedPiFormula
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact antiTargetTowerExactSeedAbovePerronThreshold_of_strongpnt_bundle hBundle

/-- Candidate closure route for all three RH-pi exact-seed payload obligations
from one global StrongPNT payload class instance. -/
theorem exactSeedUnconditionalTriple_of_strongpnt_global_payload
    [StrongPNTGlobalPayload] :
    TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadAutoInstances.exactSeedUnconditionalTriple_of_strongpnt_global_payload

/-- Candidate closure route for `truncatedExplicitFormulaPi_unconditional` from
one global StrongPNT payload class instance. -/
theorem truncatedExplicitFormulaPi_unconditional_of_strongpnt_global_payload
    [StrongPNTGlobalPayload] :
    TruncatedExplicitFormulaPiHyp := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadAutoInstances.truncatedExplicitFormulaPi_of_strongpnt_global_payload

/-- Candidate closure route for `truncatedExplicitFormulaPi_unconditional` from
one concrete global StrongPNT witness payload class instance through the
consolidated concrete-provider lane. -/
theorem truncatedExplicitFormulaPi_unconditional_of_strongpnt_concrete_witness_payload
    [StrongPNTConcreteGlobalWitnessPayload] :
    TruncatedExplicitFormulaPiHyp := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTConcreteProviderAutoInstances.b5a_and_rhpi_endpoints_of_strongpnt_concrete_witness_payload.2.1

/-- Candidate closure route for
`targetTowerExactSeedAbovePerronThreshold_unconditional` from one global
StrongPNT payload class instance. -/
theorem targetTowerExactSeedAbovePerronThreshold_unconditional_of_strongpnt_global_payload
    [StrongPNTGlobalPayload] :
    TargetTowerExactSeedAbovePerronThreshold := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadAutoInstances.targetTowerExactSeedAbovePerronThreshold_of_strongpnt_global_payload

/-- Candidate closure route for
`targetTowerExactSeedAbovePerronThreshold_unconditional` from one concrete
global StrongPNT witness payload class instance through the consolidated
concrete-provider lane. -/
theorem targetTowerExactSeedAbovePerronThreshold_unconditional_of_strongpnt_concrete_witness_payload
    [StrongPNTConcreteGlobalWitnessPayload] :
    TargetTowerExactSeedAbovePerronThreshold := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTConcreteProviderAutoInstances.b5a_and_rhpi_endpoints_of_strongpnt_concrete_witness_payload.2.2.1

/-- Candidate closure route for
`antiTargetTowerExactSeedAbovePerronThreshold_unconditional` from one global
StrongPNT payload class instance. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_unconditional_of_strongpnt_global_payload
    [StrongPNTGlobalPayload] :
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadAutoInstances.antiTargetTowerExactSeedAbovePerronThreshold_of_strongpnt_global_payload

/-- Candidate closure route for
`antiTargetTowerExactSeedAbovePerronThreshold_unconditional` from one concrete
global StrongPNT witness payload class instance through the consolidated
concrete-provider lane. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_unconditional_of_strongpnt_concrete_witness_payload
    [StrongPNTConcreteGlobalWitnessPayload] :
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact
    Aristotle.Standalone.ExternalPort.StrongPNTConcreteProviderAutoInstances.b5a_and_rhpi_endpoints_of_strongpnt_concrete_witness_payload.2.2.2

/-- Candidate closure route from the consolidated RH-`pi` concrete provider
payload class. -/
theorem exactSeedUnconditionalTriple_of_concrete_provider
    [RHPiConcreteProviderPayload] :
    TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact
    Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider.exactSeedUnconditionalTriple_of_concrete_provider

/-- Candidate closure route for `truncatedExplicitFormulaPi_unconditional` from
the consolidated RH-`pi` concrete provider payload class. -/
theorem truncatedExplicitFormulaPi_unconditional_of_concrete_provider
    [RHPiConcreteProviderPayload] :
    TruncatedExplicitFormulaPiHyp := by
  exact
    Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider.truncatedExplicitFormulaPi_of_concrete_provider

/-- Candidate closure route for
`targetTowerExactSeedAbovePerronThreshold_unconditional` from the consolidated
RH-`pi` concrete provider payload class. -/
theorem targetTowerExactSeedAbovePerronThreshold_unconditional_of_concrete_provider
    [RHPiConcreteProviderPayload] :
    TargetTowerExactSeedAbovePerronThreshold := by
  exact
    Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider.targetTowerExactSeedAbovePerronThreshold_of_concrete_provider

/-- Candidate closure route for
`antiTargetTowerExactSeedAbovePerronThreshold_unconditional` from the
consolidated RH-`pi` concrete provider payload class. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_unconditional_of_concrete_provider
    [RHPiConcreteProviderPayload] :
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact
    Aristotle.Standalone.ExternalPort.RHPiExternalConcreteProvider.antiTargetTowerExactSeedAbovePerronThreshold_of_concrete_provider

/-- Global instance for the explicit-formula payload.
    References the cross-module deep leaf opaquely to avoid sorry-warning propagation. -/
instance : TruncatedExplicitFormulaPiHyp :=
  Aristotle.Standalone.RHPiExactSeedDeepLeaf.rhpi_exact_seed_leaf.choose

/-- Global target/anti-target exact-seed phase classes at the Perron threshold level. -/
instance : TargetTowerExactSeedAbovePerronThresholdHyp :=
  ⟨Aristotle.Standalone.RHPiExactSeedDeepLeaf.rhpi_exact_seed_leaf.choose_spec.1⟩

instance : AntiTargetTowerExactSeedAbovePerronThresholdHyp :=
  ⟨Aristotle.Standalone.RHPiExactSeedDeepLeaf.rhpi_exact_seed_leaf.choose_spec.2⟩

end Aristotle.Standalone.RHPiUnconditionalExactSeedExistence
