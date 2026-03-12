import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalAutoInstances

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.B5aExternalConcreteWitnessLane

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.ExternalPort.B5aExternalLegacyWitnessPayload
open Aristotle.Standalone.ExternalPort.B5aExternalAutoInstances

/-- Build the external legacy linear-log witness payload class from a concrete
legacy witness theorem term. -/
def externalLegacyLinearLogWitnessPayload_of_witness
    (hWitness :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)) :
    ExternalLegacyLinearLogWitnessPayload :=
  ⟨hWitness⟩

/-- Endpoint: recover the legacy Dirichlet-phase explicit-formula class from one
concrete external witness theorem term. -/
def explicitFormulaPsiHyp_of_concrete_external_witness
    (hWitness :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)) :
    Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp := by
  letI : ExternalLegacyLinearLogWitnessPayload :=
    externalLegacyLinearLogWitnessPayload_of_witness hWitness
  infer_instance

/-- Endpoint: recover the standalone general truncated explicit-formula class from
one concrete external witness theorem term. -/
def explicitFormulaPsiGeneralHyp_of_concrete_external_witness
    (hWitness :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)) :
    ExplicitFormulaPsiGeneralHyp := by
  letI : ExternalLegacyLinearLogWitnessPayload :=
    externalLegacyLinearLogWitnessPayload_of_witness hWitness
  infer_instance

/-- Endpoint: recover the canonical B5a shifted-remainder bound from one concrete
external legacy linear-log witness theorem term. -/
theorem shifted_remainder_bound_of_concrete_external_witness
    (hWitness :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  letI : ExternalLegacyLinearLogWitnessPayload :=
    externalLegacyLinearLogWitnessPayload_of_witness hWitness
  exact shifted_remainder_bound_of_external_witness_auto

end Aristotle.Standalone.ExternalPort.B5aExternalConcreteWitnessLane
