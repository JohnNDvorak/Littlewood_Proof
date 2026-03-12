import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalLegacyComponentsPayload
import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTGlobalExternalPayloadAutoInstances

open PiLiDirectOscillationBridge
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.ExternalPort.B5aExternalLegacyComponentsPayload
open Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors

/-- Fuse the external B5a components payload lane with the external RH-`pi`
exact-seed payload lane into one concrete global root-constructor payload.

This is the key cross-lane auto-instance: once both external payload lanes are
available, all three constructor roots (`ExplicitFormulaPsiHyp`,
`ExplicitFormulaPsiGeneralHyp`, `RHPiUnconditionalExactSeedRootPayload`) can be
synthesized through existing global wiring. -/
instance (priority := 90)
    [ExternalLegacyLinearLogComponentsPayload]
    [ExternalExactSeedPayload] :
    StrongPNTConcreteGlobalWitnessPayload where
  legacyLinearLogWitness :=
    legacy_linear_log_bound_of_external_components_payload
  truncatedPi := ExternalExactSeedPayload.truncated
  targetSeed := by
    letI : TruncatedExplicitFormulaPiHyp := ExternalExactSeedPayload.truncated
    exact ExternalExactSeedPayload.target
  antiTargetSeed := by
    letI : TruncatedExplicitFormulaPiHyp := ExternalExactSeedPayload.truncated
    exact ExternalExactSeedPayload.antiTarget

/-- Constructor-root bundle endpoint from the fused external payload lanes. -/
theorem root_constructor_bundle_of_external_payload_lanes
    [ExternalLegacyLinearLogComponentsPayload]
    [ExternalExactSeedPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  exact root_constructor_bundle_of_concrete_global_witness_payload

/-- Canonical B5a shifted-bound and RH-`pi` exact-seed endpoint bundle from the
fused external payload lanes. -/
theorem b5a_and_rhpi_endpoints_of_external_payload_lanes
    [ExternalLegacyLinearLogComponentsPayload]
    [ExternalExactSeedPayload] :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact b5a_and_rhpi_endpoints_of_concrete_global_witness_payload

end Aristotle.Standalone.ExternalPort.StrongPNTGlobalExternalPayloadAutoInstances
