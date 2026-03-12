import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalConcreteWitnessLane
import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalAutoInstances

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.B5aExternalConcreteProvider

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
open Aristotle.Standalone.ExternalPort.B5aExternalLegacyWitnessPayload
open Aristotle.Standalone.ExternalPort.B5aExternalConcreteWitnessLane
open Aristotle.Standalone.ExternalPort.B5aExternalAutoInstances

/-- Consolidated concrete payload class for the B5a external integration lane.
Providing one theorem term in legacy linear-log shape is enough to recover all
B5a constructor-level classes. -/
class B5aConcreteProviderPayload : Prop where
  witness :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)

/-- Auto-wire the external legacy witness payload from the consolidated B5a
provider class. -/
instance (priority := 100)
    [B5aConcreteProviderPayload] :
    ExternalLegacyLinearLogWitnessPayload :=
  externalLegacyLinearLogWitnessPayload_of_witness
    B5aConcreteProviderPayload.witness

/-- Constructor-bundle endpoint from the consolidated B5a provider class. -/
theorem b5a_constructor_bundle_of_concrete_provider
    [B5aConcreteProviderPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      ExplicitFormulaPsiB5aRootPayload := by
  refine ⟨inferInstance, ?_⟩
  exact ⟨inferInstance, inferInstance⟩

/-- Deep-leaf payload endpoint from the consolidated B5a provider class. -/
theorem shifted_remainder_bound_of_concrete_provider
    [B5aConcreteProviderPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact
    shifted_remainder_bound_of_concrete_external_witness
      B5aConcreteProviderPayload.witness

end Aristotle.Standalone.ExternalPort.B5aExternalConcreteProvider
