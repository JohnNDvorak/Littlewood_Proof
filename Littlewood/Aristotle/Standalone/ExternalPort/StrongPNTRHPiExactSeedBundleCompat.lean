import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalConcreteExactSeedLane
import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedAutoInstances

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedBundleCompat

open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload
open Aristotle.Standalone.ExternalPort.RHPiExternalConcreteExactSeedLane

/-- StrongPNT-style bundled payload carrying all RH-`pi` exact-seed obligations. -/
structure StrongPNTRHPiExactSeedBundle : Type where
  truncatedPiFormula : TruncatedExplicitFormulaPiHyp
  targetSeedAbovePerron :
    letI : TruncatedExplicitFormulaPiHyp := truncatedPiFormula
    TargetTowerExactSeedAbovePerronThreshold
  antiTargetSeedAbovePerron :
    letI : TruncatedExplicitFormulaPiHyp := truncatedPiFormula
    AntiTargetTowerExactSeedAbovePerronThreshold

/-- Convert a StrongPNT-style exact-seed bundle into the internal concrete
exact-seed triple carrier. -/
def concreteExactSeedTriple_of_strongpnt_bundle
    (hBundle : StrongPNTRHPiExactSeedBundle) :
    ConcreteExactSeedTriple where
  truncated := hBundle.truncatedPiFormula
  target := by
    letI : TruncatedExplicitFormulaPiHyp := hBundle.truncatedPiFormula
    simpa using hBundle.targetSeedAbovePerron
  antiTarget := by
    letI : TruncatedExplicitFormulaPiHyp := hBundle.truncatedPiFormula
    simpa using hBundle.antiTargetSeedAbovePerron

/-- Convert a StrongPNT-style exact-seed bundle into the external exact-seed
payload class used by the RH-`pi` root-constructor lane. -/
def externalExactSeedPayload_of_strongpnt_bundle
    (hBundle : StrongPNTRHPiExactSeedBundle) :
    ExternalExactSeedPayload :=
  externalExactSeedPayload_of_triple
    (concreteExactSeedTriple_of_strongpnt_bundle hBundle)

/-- Endpoint: recover the bundled RH-`pi` root payload class from a
StrongPNT-style exact-seed bundle. -/
theorem rhpi_rootPayload_of_strongpnt_bundle
    (hBundle : StrongPNTRHPiExactSeedBundle) :
    RHPiUnconditionalExactSeedRootPayload := by
  letI : ExternalExactSeedPayload :=
    externalExactSeedPayload_of_strongpnt_bundle hBundle
  infer_instance

/-- Endpoint: recover the three RH-`pi` exact-seed obligations from a
StrongPNT-style exact-seed bundle. -/
theorem rhpi_exactSeedTriple_of_strongpnt_bundle
    (hBundle : StrongPNTRHPiExactSeedBundle) :
    TruncatedExplicitFormulaPiHyp ∧
      (letI : TruncatedExplicitFormulaPiHyp := hBundle.truncatedPiFormula
       TargetTowerExactSeedAbovePerronThreshold ∧
       AntiTargetTowerExactSeedAbovePerronThreshold) := by
  exact
    exactSeedTriple_of_concrete_external_triple
      (concreteExactSeedTriple_of_strongpnt_bundle hBundle)

/-- Component endpoint: truncated explicit-formula payload from a StrongPNT-style
exact-seed bundle. -/
theorem truncatedExplicitFormulaPi_of_strongpnt_bundle
    (hBundle : StrongPNTRHPiExactSeedBundle) :
    TruncatedExplicitFormulaPiHyp := by
  exact
    truncatedExplicitFormulaPi_of_concrete_external_triple
      (concreteExactSeedTriple_of_strongpnt_bundle hBundle)

/-- Component endpoint: target exact-seed payload from a StrongPNT-style
exact-seed bundle. -/
theorem targetTowerExactSeedAbovePerronThreshold_of_strongpnt_bundle
    (hBundle : StrongPNTRHPiExactSeedBundle) :
    letI : TruncatedExplicitFormulaPiHyp := hBundle.truncatedPiFormula
    TargetTowerExactSeedAbovePerronThreshold := by
  exact
    targetTowerExactSeedAbovePerronThreshold_of_concrete_external_triple
      (concreteExactSeedTriple_of_strongpnt_bundle hBundle)

/-- Component endpoint: anti-target exact-seed payload from a StrongPNT-style
exact-seed bundle. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_of_strongpnt_bundle
    (hBundle : StrongPNTRHPiExactSeedBundle) :
    letI : TruncatedExplicitFormulaPiHyp := hBundle.truncatedPiFormula
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact
    antiTargetTowerExactSeedAbovePerronThreshold_of_concrete_external_triple
      (concreteExactSeedTriple_of_strongpnt_bundle hBundle)

end Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedBundleCompat
