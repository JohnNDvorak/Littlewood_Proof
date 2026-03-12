import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTLegacyLinearLogWitnessCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedBundleCompat

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadAutoInstances

open PiLiDirectOscillationBridge
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.ExternalPort.B5aExternalLegacyWitnessPayload
open Aristotle.Standalone.ExternalPort.B5aExternalAutoInstances
open Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload
open Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedAutoInstances
open Aristotle.Standalone.ExternalPort.StrongPNTLegacyLinearLogWitnessCompat
open Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedBundleCompat

/-- Single external-port payload class that carries both constructor roots:
one StrongPNT-style B5a legacy witness and one StrongPNT-style RH-pi exact-seed
bundle. -/
class StrongPNTGlobalPayload : Type where
  b5aLegacyWitness : StrongPNTLegacyLinearLogWitnessBundle
  rhpiExactSeed : StrongPNTRHPiExactSeedBundle

/-- Auto-wire B5a external witness payload from the global StrongPNT payload. -/
instance (priority := 100)
    [StrongPNTGlobalPayload] :
    ExternalLegacyLinearLogWitnessPayload :=
  externalLegacyLinearLogWitnessPayload_of_strongpnt_bundle
    StrongPNTGlobalPayload.b5aLegacyWitness

/-- Auto-wire RH-pi external exact-seed payload from the global StrongPNT payload. -/
instance (priority := 100)
    [StrongPNTGlobalPayload] :
    ExternalExactSeedPayload :=
  externalExactSeedPayload_of_strongpnt_bundle
    StrongPNTGlobalPayload.rhpiExactSeed

/-- Convenience endpoint: B5a shifted-remainder payload from one global
StrongPNT payload instance. -/
theorem shifted_remainder_bound_of_strongpnt_global_payload
    [StrongPNTGlobalPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_remainder_bound_of_external_witness_auto

/-- Convenience endpoint: full RH-pi exact-seed triple from one global
StrongPNT payload instance. -/
theorem exactSeedUnconditionalTriple_of_strongpnt_global_payload
    [StrongPNTGlobalPayload] :
    TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact exactSeedUnconditionalTriple_of_externalPayload_auto

/-- Component endpoint: truncated explicit-formula payload from one global
StrongPNT payload instance. -/
theorem truncatedExplicitFormulaPi_of_strongpnt_global_payload
    [StrongPNTGlobalPayload] :
    TruncatedExplicitFormulaPiHyp := by
  infer_instance

/-- Component endpoint: target exact-seed payload from one global StrongPNT
payload instance. -/
theorem targetTowerExactSeedAbovePerronThreshold_of_strongpnt_global_payload
    [StrongPNTGlobalPayload] :
    TargetTowerExactSeedAbovePerronThreshold := by
  exact targetTowerExactSeedAbovePerronThreshold_of_externalPayload

/-- Component endpoint: anti-target exact-seed payload from one global
StrongPNT payload instance. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_of_strongpnt_global_payload
    [StrongPNTGlobalPayload] :
    AntiTargetTowerExactSeedAbovePerronThreshold := by
  exact antiTargetTowerExactSeedAbovePerronThreshold_of_externalPayload

end Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadAutoInstances
