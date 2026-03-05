import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogRootInfra

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogProvider

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.ExplicitFormulaPsiLegacyGlobalInstance
open Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogRootInfra

/-- Root-payload provider endpoint for the exact legacy linear-log witness. -/
theorem legacy_linear_log_bound_provider_of_rootPayload
    [ExplicitFormulaPsiLegacyLinearLogRootPayload] :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) :=
  legacy_linear_log_bound_of_rootPayload

/-- Split-component provider endpoint for the exact legacy linear-log witness. -/
theorem legacy_linear_log_bound_provider_of_components
    [ExplicitFormulaPsiLegacyLinearLogComponentsHyp] :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) :=
  legacy_linear_log_bound_of_componentsHyp

/-- Bridge root payload into the legacy payload class. -/
instance (priority := 100)
    [ExplicitFormulaPsiLegacyLinearLogRootPayload] :
    ExplicitFormulaPsiLegacyPayload :=
  legacyPayload_of_rootPayload

end Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogProvider

