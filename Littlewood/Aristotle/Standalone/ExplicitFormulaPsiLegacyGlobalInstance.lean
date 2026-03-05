import Littlewood.Aristotle.DirichletPhaseAlignment

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiLegacyGlobalInstance

open Aristotle.DirichletPhaseAlignment (ZerosBelow)

/-- Root payload for the legacy Dirichlet-phase explicit-formula class.

This packages the exact witness shape required by
`Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp`. -/
class ExplicitFormulaPsiLegacyPayload : Type where
  witness :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)

/-- Exact legacy linear-log witness endpoint carried by the payload class. -/
theorem legacy_linear_log_bound_of_payload
    [hPayload : ExplicitFormulaPsiLegacyPayload] :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) :=
  hPayload.witness

/-- Package a concrete legacy explicit-formula witness theorem as payload. -/
def explicitFormulaPsiLegacyPayload_of_witness
    (hWitness :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)) :
    ExplicitFormulaPsiLegacyPayload :=
  ⟨hWitness⟩

/-- Concrete payload constructor from a legacy class witness. -/
def explicitFormulaPsiLegacyPayload_of_legacy
    (hLegacy : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp) :
    ExplicitFormulaPsiLegacyPayload := by
  refine explicitFormulaPsiLegacyPayload_of_witness ?_
  refine ⟨hLegacy.C, ?_⟩
  intro x T hx hT
  simpa using hLegacy.psi_approx x T hx hT

/-- Exact legacy linear-log witness extracted from a legacy class term. -/
theorem legacy_linear_log_bound_of_legacy
    (hLegacy : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp) :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) := by
  exact (explicitFormulaPsiLegacyPayload_of_legacy hLegacy).witness

/-- Concrete payload instance term built from an explicit legacy witness argument. -/
instance explicitFormulaPsiLegacyPayload_concrete
    (hLegacy : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp) :
    ExplicitFormulaPsiLegacyPayload :=
  explicitFormulaPsiLegacyPayload_of_legacy hLegacy

/-- Build the legacy Dirichlet-phase explicit-formula class from a payload witness. -/
def explicitFormulaPsiHyp_of_payload
    [hPayload : ExplicitFormulaPsiLegacyPayload] :
    Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp := by
  let C : ℝ := Classical.choose hPayload.witness
  have hC :
      ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) := by
    simpa [C] using Classical.choose_spec hPayload.witness
  exact ⟨C, hC⟩

/-- Global instance constructor for
`Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp`. -/
instance (priority := 100)
    [ExplicitFormulaPsiLegacyPayload] :
    Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp :=
  explicitFormulaPsiHyp_of_payload

end Aristotle.Standalone.ExplicitFormulaPsiLegacyGlobalInstance
