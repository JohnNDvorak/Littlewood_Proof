import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalAutoInstances
import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalConcreteWitnessLane

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTLegacyLinearLogWitnessCompat

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
open Aristotle.Standalone.ExternalPort.B5aExternalLegacyWitnessPayload
open Aristotle.Standalone.ExternalPort.B5aExternalConcreteWitnessLane
open Aristotle.Standalone.ExternalPort.B5aExternalAutoInstances

/-- StrongPNT-style bundle for the legacy linear-log explicit-formula witness. -/
structure StrongPNTLegacyLinearLogWitnessBundle : Type where
  explicitFormulaPsiLinearLog :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)

/-- Convert a StrongPNT-style legacy witness bundle into the external witness
payload class used by the B5a constructor lane. -/
def externalLegacyLinearLogWitnessPayload_of_strongpnt_bundle
    (hBundle : StrongPNTLegacyLinearLogWitnessBundle) :
    ExternalLegacyLinearLogWitnessPayload :=
  externalLegacyLinearLogWitnessPayload_of_witness
    hBundle.explicitFormulaPsiLinearLog

/-- Endpoint: recover the legacy Dirichlet-phase explicit-formula class from a
StrongPNT-style legacy witness bundle. -/
def explicitFormulaPsiHyp_of_strongpnt_bundle
    (hBundle : StrongPNTLegacyLinearLogWitnessBundle) :
    Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp := by
  exact
    explicitFormulaPsiHyp_of_concrete_external_witness
      hBundle.explicitFormulaPsiLinearLog

/-- Endpoint: recover the canonical B5a shifted-remainder bound from a
StrongPNT-style legacy witness bundle. -/
theorem shifted_remainder_bound_of_strongpnt_legacy_witness_bundle
    (hBundle : StrongPNTLegacyLinearLogWitnessBundle) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact
    shifted_remainder_bound_of_concrete_external_witness
      hBundle.explicitFormulaPsiLinearLog

/-- Endpoint: recover the bundled B5a root payload class from a StrongPNT-style
legacy witness bundle. -/
theorem b5a_rootPayload_of_strongpnt_legacy_witness_bundle
    (hBundle : StrongPNTLegacyLinearLogWitnessBundle) :
    ExplicitFormulaPsiB5aRootPayload := by
  letI : ExternalLegacyLinearLogWitnessPayload :=
    externalLegacyLinearLogWitnessPayload_of_strongpnt_bundle hBundle
  infer_instance

end Aristotle.Standalone.ExternalPort.StrongPNTLegacyLinearLogWitnessCompat
