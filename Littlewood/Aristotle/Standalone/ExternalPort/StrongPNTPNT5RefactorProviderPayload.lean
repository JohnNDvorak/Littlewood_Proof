import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTPNT5StrongRefactor
import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalConcreteProvider

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTPNT5RefactorProviderPayload

open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
open Aristotle.Standalone.ExternalPort.StrongPNTPNT5StrongRefactor
open Aristotle.Standalone.ExternalPort.B5aExternalConcreteProvider

/-- Split concrete provider lane for B5a: one refactored `PNT5_Strong` bundle
is enough to synthesize the consolidated B5a concrete provider payload. -/
class PNT5StrongRefactorProviderPayload : Type where
  pnt5 : PNT5StrongRefactorBundle

/-- Auto-wire the consolidated B5a concrete provider payload from one refactored
`PNT5_Strong` bundle. -/
instance (priority := 100)
    [PNT5StrongRefactorProviderPayload] :
    B5aConcreteProviderPayload where
  witness :=
    legacy_linear_log_bound_of_refactored_pnt5
      PNT5StrongRefactorProviderPayload.pnt5

/-- Constructor-bundle endpoint for B5a from the split refactored
`PNT5_Strong` provider class. -/
theorem b5a_constructor_bundle_of_pnt5_refactor_provider_payload
    [PNT5StrongRefactorProviderPayload] :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      ExplicitFormulaPsiB5aRootPayload := by
  exact b5a_constructor_bundle_of_concrete_provider

/-- Canonical B5a shifted-remainder endpoint from the split refactored
`PNT5_Strong` provider class. -/
theorem shifted_remainder_bound_of_pnt5_refactor_provider_payload
    [PNT5StrongRefactorProviderPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_remainder_bound_of_concrete_provider

/-- Package one refactored `PNT5_Strong` bundle as a split B5a provider
payload term. -/
def pnt5_refactor_provider_payload_of_bundle
    (hPNT5 : PNT5StrongRefactorBundle) :
    PNT5StrongRefactorProviderPayload where
  pnt5 := hPNT5

end Aristotle.Standalone.ExternalPort.StrongPNTPNT5RefactorProviderPayload
