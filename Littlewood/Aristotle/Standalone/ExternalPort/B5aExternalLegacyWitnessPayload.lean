import Littlewood.Aristotle.Standalone.ExternalPort.B5aLegacyPayloadWiring
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogProvider

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.B5aExternalLegacyWitnessPayload

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaPsiLegacyGlobalInstance
open Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogRootInfra
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
open Aristotle.Standalone.ExternalPort.B5aLegacyPayloadWiring

/-- External-port payload class: one concrete legacy linear-log witness theorem
ported from an external source. -/
class ExternalLegacyLinearLogWitnessPayload : Prop where
  witness :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)

/-- Bridge external payload class into the bundled legacy linear-log root payload. -/
instance (priority := 100)
    [ExternalLegacyLinearLogWitnessPayload] :
    ExplicitFormulaPsiLegacyLinearLogRootPayload :=
  legacy_linear_log_rootPayload_of_external_witness
    ExternalLegacyLinearLogWitnessPayload.witness

/-- Endpoint: external payload yields the canonical B5a shifted-remainder bound. -/
theorem shifted_remainder_bound_of_external_payload
    [ExternalLegacyLinearLogWitnessPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  have hWitness := ExternalLegacyLinearLogWitnessPayload.witness
  exact shifted_remainder_bound_of_external_legacy_witness hWitness

/-- Endpoint: external payload yields a concrete legacy explicit-formula class term. -/
def explicitFormulaPsiHyp_of_external_payload
    [ExternalLegacyLinearLogWitnessPayload] :
    Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp := by
  have hWitness := ExternalLegacyLinearLogWitnessPayload.witness
  exact dirichletPhase_explicitFormulaPsiHyp_of_external_witness hWitness

end Aristotle.Standalone.ExternalPort.B5aExternalLegacyWitnessPayload
