import Littlewood.Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourCompat
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogProvider
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.B5aLegacyPayloadWiring

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaPsiLegacyGlobalInstance
open Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogRootInfra
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra

/-- Package an externally ported legacy linear-log witness into the bundled
root payload class expected by in-repo legacy/global-instance wiring. -/
theorem legacy_linear_log_rootPayload_of_external_witness
    (hWitness :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)) :
    ExplicitFormulaPsiLegacyLinearLogRootPayload :=
  ⟨hWitness⟩

/-- From an externally ported legacy witness theorem, recover a concrete
`DirichletPhaseAlignment.ExplicitFormulaPsiHyp` term. -/
def dirichletPhase_explicitFormulaPsiHyp_of_external_witness
    (hWitness :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)) :
    Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp := by
  letI : ExplicitFormulaPsiLegacyLinearLogRootPayload :=
    legacy_linear_log_rootPayload_of_external_witness hWitness
  letI : ExplicitFormulaPsiLegacyPayload :=
    legacyPayload_of_rootPayload
  exact inferInstance

/-- One-hop B5a endpoint from an externally ported legacy linear-log witness:
derive the canonical shifted-remainder bound used by the deep leaf. -/
theorem shifted_remainder_bound_of_external_legacy_witness
    (hWitness :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  letI : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp :=
    dirichletPhase_explicitFormulaPsiHyp_of_external_witness hWitness
  exact shifted_remainder_bound_of_legacy_explicit_formula

end Aristotle.Standalone.ExternalPort.B5aLegacyPayloadWiring
