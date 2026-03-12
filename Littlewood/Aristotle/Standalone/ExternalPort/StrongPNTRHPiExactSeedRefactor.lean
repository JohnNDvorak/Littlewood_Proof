import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedBundleCompat

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedRefactor

open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedBundleCompat

/-- Lean-4.27 refactor surface for the RH-`pi` exact-seed theorem family used
by the B7 lane.

Field names are intentionally close to the external theorem payload language so
downstream adapters can consume a stable API without importing toolchain-
incompatible repositories. -/
structure RHPiExactSeedRefactorBundle : Type where
  truncatedPiFormula : TruncatedExplicitFormulaPiHyp
  targetSeedAbovePerron :
    letI : TruncatedExplicitFormulaPiHyp := truncatedPiFormula
    TargetTowerExactSeedAbovePerronThreshold
  antiTargetSeedAbovePerron :
    letI : TruncatedExplicitFormulaPiHyp := truncatedPiFormula
    AntiTargetTowerExactSeedAbovePerronThreshold

/-- Convert a refactored RH-`pi` exact-seed bundle into the canonical
StrongPNT-style RH-`pi` bundle. -/
def toStrongPNTBundle
    (hBundle : RHPiExactSeedRefactorBundle) :
    StrongPNTRHPiExactSeedBundle where
  truncatedPiFormula := hBundle.truncatedPiFormula
  targetSeedAbovePerron := by
    letI : TruncatedExplicitFormulaPiHyp := hBundle.truncatedPiFormula
    simpa using hBundle.targetSeedAbovePerron
  antiTargetSeedAbovePerron := by
    letI : TruncatedExplicitFormulaPiHyp := hBundle.truncatedPiFormula
    simpa using hBundle.antiTargetSeedAbovePerron

/-- Component endpoint: truncated explicit-formula payload from a refactored
RH-`pi` exact-seed bundle. -/
theorem truncatedExplicitFormulaPi_of_refactored_bundle
    (hBundle : RHPiExactSeedRefactorBundle) :
    TruncatedExplicitFormulaPiHyp := by
  exact truncatedExplicitFormulaPi_of_strongpnt_bundle (toStrongPNTBundle hBundle)

/-- Component endpoint: target exact-seed payload from a refactored RH-`pi`
exact-seed bundle. -/
theorem targetTowerExactSeedAbovePerronThreshold_of_refactored_bundle
    (hBundle : RHPiExactSeedRefactorBundle) :
    letI : TruncatedExplicitFormulaPiHyp := hBundle.truncatedPiFormula
    TargetTowerExactSeedAbovePerronThreshold := by
  exact
    targetTowerExactSeedAbovePerronThreshold_of_strongpnt_bundle
      (toStrongPNTBundle hBundle)

/-- Component endpoint: anti-target exact-seed payload from a refactored
RH-`pi` exact-seed bundle. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_of_refactored_bundle
    (hBundle : RHPiExactSeedRefactorBundle) :
    letI : TruncatedExplicitFormulaPiHyp := hBundle.truncatedPiFormula
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact
    antiTargetTowerExactSeedAbovePerronThreshold_of_strongpnt_bundle
      (toStrongPNTBundle hBundle)

/-- Endpoint: recover all three RH-`pi` exact-seed obligations from a refactored
RH-`pi` exact-seed bundle. -/
theorem exactSeedTriple_of_refactored_bundle
    (hBundle : RHPiExactSeedRefactorBundle) :
    TruncatedExplicitFormulaPiHyp ∧
      (letI : TruncatedExplicitFormulaPiHyp := hBundle.truncatedPiFormula
       TargetTowerExactSeedAbovePerronThreshold ∧
       AntiTargetTowerExactSeedAbovePerronThreshold) := by
  exact rhpi_exactSeedTriple_of_strongpnt_bundle (toStrongPNTBundle hBundle)

/-- Constructor endpoint: recover the bundled RH-`pi` root payload class from a
refactored RH-`pi` exact-seed bundle. -/
theorem rhpi_rootPayload_of_refactored_bundle
    (hBundle : RHPiExactSeedRefactorBundle) :
    RHPiUnconditionalExactSeedRootPayload := by
  exact rhpi_rootPayload_of_strongpnt_bundle (toStrongPNTBundle hBundle)

end Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedRefactor
