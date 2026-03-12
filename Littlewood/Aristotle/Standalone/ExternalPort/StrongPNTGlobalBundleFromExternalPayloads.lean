import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalLegacyComponentsPayload
import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTB5aComponentBundleCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedBundleCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundlePayloadAutoInstances

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundleFromExternalPayloads

open PiLiDirectOscillationBridge
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.ExternalPort.B5aExternalLegacyComponentsPayload
open Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload
open Aristotle.Standalone.ExternalPort.StrongPNTB5aComponentBundleCompat
open Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedBundleCompat
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundlePayloadAutoInstances

/-- Convert the external B5a component payload lane into a StrongPNT-shaped B5a
component bundle. -/
def strongpnt_b5a_bundle_of_external_components
    [ExternalLegacyLinearLogComponentsPayload] :
    StrongPNTB5aComponentBundle where
  perronIntegralRe := ExternalLegacyLinearLogComponentsPayload.perronIntegralRe
  contourRemainderRe := ExternalLegacyLinearLogComponentsPayload.contourRemainderRe
  smoothedChebyshevPull1 := ExternalLegacyLinearLogComponentsPayload.hPerron
  smoothedChebyshevPull2 := ExternalLegacyLinearLogComponentsPayload.hResidue
  zetaBoxEval := ExternalLegacyLinearLogComponentsPayload.hContour

/-- Convert the external RH-`pi` exact-seed payload lane into a StrongPNT-style
RH-`pi` exact-seed bundle. -/
def strongpnt_rhpi_bundle_of_external_payload
    [ExternalExactSeedPayload] :
    StrongPNTRHPiExactSeedBundle where
  truncatedPiFormula := ExternalExactSeedPayload.truncated
  targetSeedAbovePerron := by
    letI : TruncatedExplicitFormulaPiHyp := ExternalExactSeedPayload.truncated
    exact ExternalExactSeedPayload.target
  antiTargetSeedAbovePerron := by
    letI : TruncatedExplicitFormulaPiHyp := ExternalExactSeedPayload.truncated
    exact ExternalExactSeedPayload.antiTarget

/-- Bundle-level fused auto-instance: external B5a component payload + external
RH-`pi` exact-seed payload produce the global StrongPNT bundle payload. -/
instance (priority := 85)
    [ExternalLegacyLinearLogComponentsPayload]
    [ExternalExactSeedPayload] :
    StrongPNTConcreteGlobalBundlePayload where
  b5aBundle := strongpnt_b5a_bundle_of_external_components
  rhpiBundle := strongpnt_rhpi_bundle_of_external_payload

/-- Root-constructor bundle endpoint from the external payload lanes through the
global StrongPNT bundled payload route. -/
theorem root_constructor_bundle_of_external_payload_lanes_via_bundle
    [ExternalLegacyLinearLogComponentsPayload]
    [ExternalExactSeedPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact root_constructor_bundle_of_concrete_global_bundle_payload

/-- Canonical B5a shifted-bound + RH-`pi` exact-seed endpoint bundle from the
external payload lanes through the global StrongPNT bundled payload route. -/
theorem b5a_and_rhpi_endpoints_of_external_payload_lanes_via_bundle
    [ExternalLegacyLinearLogComponentsPayload]
    [ExternalExactSeedPayload] :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact b5a_and_rhpi_endpoints_of_concrete_global_bundle_payload

end Aristotle.Standalone.ExternalPort.StrongPNTGlobalBundleFromExternalPayloads
