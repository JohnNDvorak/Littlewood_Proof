import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTB5aComponentBundleCompat
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTPNT5StrongRefactor
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedRefactor

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadConcreteLane

open PiLiDirectOscillationBridge
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.ExternalPort.StrongPNTLegacyLinearLogWitnessCompat
open Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedBundleCompat
open Aristotle.Standalone.ExternalPort.StrongPNTB5aComponentBundleCompat
open Aristotle.Standalone.ExternalPort.StrongPNTPNT5StrongRefactor
open Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedRefactor
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadAutoInstances

/-- Build a StrongPNT-style B5a legacy witness bundle from one concrete
legacy linear-log theorem term. -/
def strongpnt_legacy_bundle_of_witness
    (hWitness :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ Aristotle.DirichletPhaseAlignment.ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)) :
    StrongPNTLegacyLinearLogWitnessBundle :=
  ⟨hWitness⟩

/-- Build a StrongPNT-style RH-pi exact-seed bundle from a concrete theorem
triple. -/
def strongpnt_exactSeed_bundle_of_witness
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      TargetTowerExactSeedAbovePerronThreshold)
    (hAntiTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      AntiTargetTowerExactSeedAbovePerronThreshold) :
    StrongPNTRHPiExactSeedBundle where
  truncatedPiFormula := hTruncated
  targetSeedAbovePerron := by
    letI : TruncatedExplicitFormulaPiHyp := hTruncated
    simpa using hTarget
  antiTargetSeedAbovePerron := by
    letI : TruncatedExplicitFormulaPiHyp := hTruncated
    simpa using hAntiTarget

/-- Build one global StrongPNT payload from a concrete B5a legacy witness and a
concrete RH-pi exact-seed triple. -/
def strongpnt_global_payload_of_witnesses
    (hWitness :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ Aristotle.DirichletPhaseAlignment.ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x))
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      TargetTowerExactSeedAbovePerronThreshold)
    (hAntiTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      AntiTargetTowerExactSeedAbovePerronThreshold) :
    StrongPNTGlobalPayload where
  b5aLegacyWitness := strongpnt_legacy_bundle_of_witness hWitness
  rhpiExactSeed := strongpnt_exactSeed_bundle_of_witness hTruncated hTarget hAntiTarget

/-- Build one global StrongPNT payload from a StrongPNT-style B5a component
bundle and a StrongPNT-style RH-pi exact-seed bundle. -/
def strongpnt_global_payload_of_bundles
    (hB5a : StrongPNTB5aComponentBundle)
    (hRhPi : StrongPNTRHPiExactSeedBundle) :
    StrongPNTGlobalPayload where
  b5aLegacyWitness :=
    ⟨legacy_linear_log_bound_of_strongpnt_bundle hB5a⟩
  rhpiExactSeed := hRhPi

/-- Build one StrongPNT-style B5a component bundle from a refactored
`PNT5_Strong` theorem bundle. -/
def strongpnt_b5a_component_bundle_of_pnt5_refactor
    (hPNT5 : PNT5StrongRefactorBundle) :
    StrongPNTB5aComponentBundle :=
  toComponentBundle hPNT5

/-- Build one global StrongPNT payload from a refactored `PNT5_Strong` theorem
bundle and a StrongPNT-style RH-pi exact-seed bundle. -/
def strongpnt_global_payload_of_pnt5_refactor_bundle
    (hPNT5 : PNT5StrongRefactorBundle)
    (hRhPi : StrongPNTRHPiExactSeedBundle) :
    StrongPNTGlobalPayload :=
  strongpnt_global_payload_of_bundles
    (strongpnt_b5a_component_bundle_of_pnt5_refactor hPNT5)
    hRhPi

/-- Build one StrongPNT-style RH-pi exact-seed bundle from a refactored RH-pi
exact-seed theorem bundle. -/
def strongpnt_exactSeed_bundle_of_rhpi_refactor
    (hRhPi : RHPiExactSeedRefactorBundle) :
    StrongPNTRHPiExactSeedBundle :=
  toStrongPNTBundle hRhPi

/-- Build one global StrongPNT payload from refactored `PNT5_Strong` and
refactored RH-pi exact-seed theorem bundles. -/
def strongpnt_global_payload_of_refactored_bundles
    (hPNT5 : PNT5StrongRefactorBundle)
    (hRhPi : RHPiExactSeedRefactorBundle) :
    StrongPNTGlobalPayload :=
  strongpnt_global_payload_of_pnt5_refactor_bundle
    hPNT5
    (strongpnt_exactSeed_bundle_of_rhpi_refactor hRhPi)

/-- One-shot endpoint from concrete witness terms to the canonical B5a shifted
bound and all three RH-pi exact-seed obligations. -/
theorem b5a_and_rhpi_endpoints_of_concrete_global_witnesses
    (hWitness :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ Aristotle.DirichletPhaseAlignment.ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x))
    (hTruncated : TruncatedExplicitFormulaPiHyp)
    (hTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      TargetTowerExactSeedAbovePerronThreshold)
    (hAntiTarget :
      letI : TruncatedExplicitFormulaPiHyp := hTruncated
      AntiTargetTowerExactSeedAbovePerronThreshold) :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  letI : StrongPNTGlobalPayload :=
    strongpnt_global_payload_of_witnesses hWitness hTruncated hTarget hAntiTarget
  refine ⟨shifted_remainder_bound_of_strongpnt_global_payload, ?_⟩
  exact
    ⟨truncatedExplicitFormulaPi_of_strongpnt_global_payload,
      targetTowerExactSeedAbovePerronThreshold_of_strongpnt_global_payload,
      antiTargetTowerExactSeedAbovePerronThreshold_of_strongpnt_global_payload⟩

/-- One-shot endpoint from bundled StrongPNT payloads to the canonical B5a
shifted bound and all three RH-pi exact-seed obligations. -/
theorem b5a_and_rhpi_endpoints_of_strongpnt_bundles
    (hB5a : StrongPNTB5aComponentBundle)
    (hRhPi : StrongPNTRHPiExactSeedBundle) :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      (letI : TruncatedExplicitFormulaPiHyp := hRhPi.truncatedPiFormula
       TargetTowerExactSeedAbovePerronThreshold ∧
       AntiTargetTowerExactSeedAbovePerronThreshold) := by
  letI : StrongPNTGlobalPayload := strongpnt_global_payload_of_bundles hB5a hRhPi
  refine ⟨shifted_remainder_bound_of_strongpnt_global_payload, ?_⟩
  refine ⟨truncatedExplicitFormulaPi_of_strongpnt_global_payload, ?_⟩
  letI : TruncatedExplicitFormulaPiHyp := hRhPi.truncatedPiFormula
  exact
    ⟨targetTowerExactSeedAbovePerronThreshold_of_strongpnt_global_payload,
      antiTargetTowerExactSeedAbovePerronThreshold_of_strongpnt_global_payload⟩

/-- One-shot endpoint from a refactored `PNT5_Strong` theorem bundle and a
StrongPNT-style RH-pi exact-seed bundle to the canonical B5a shifted bound and
all three RH-pi exact-seed obligations. -/
theorem b5a_and_rhpi_endpoints_of_pnt5_refactor_bundle
    (hPNT5 : PNT5StrongRefactorBundle)
    (hRhPi : StrongPNTRHPiExactSeedBundle) :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      (letI : TruncatedExplicitFormulaPiHyp := hRhPi.truncatedPiFormula
       TargetTowerExactSeedAbovePerronThreshold ∧
       AntiTargetTowerExactSeedAbovePerronThreshold) := by
  letI : StrongPNTGlobalPayload :=
    strongpnt_global_payload_of_pnt5_refactor_bundle hPNT5 hRhPi
  refine ⟨shifted_remainder_bound_of_strongpnt_global_payload, ?_⟩
  refine ⟨truncatedExplicitFormulaPi_of_strongpnt_global_payload, ?_⟩
  letI : TruncatedExplicitFormulaPiHyp := hRhPi.truncatedPiFormula
  exact
    ⟨targetTowerExactSeedAbovePerronThreshold_of_strongpnt_global_payload,
      antiTargetTowerExactSeedAbovePerronThreshold_of_strongpnt_global_payload⟩

/-- One-shot endpoint from refactored `PNT5_Strong` and refactored RH-pi
exact-seed bundles to the canonical B5a shifted bound and RH-pi exact-seed
obligations. -/
theorem b5a_and_rhpi_endpoints_of_refactored_bundles
    (hPNT5 : PNT5StrongRefactorBundle)
    (hRhPi : RHPiExactSeedRefactorBundle) :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      (letI : TruncatedExplicitFormulaPiHyp := hRhPi.truncatedPiFormula
       TargetTowerExactSeedAbovePerronThreshold ∧
       AntiTargetTowerExactSeedAbovePerronThreshold) := by
  exact
    b5a_and_rhpi_endpoints_of_pnt5_refactor_bundle
      hPNT5
      (strongpnt_exactSeed_bundle_of_rhpi_refactor hRhPi)

end Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadConcreteLane
