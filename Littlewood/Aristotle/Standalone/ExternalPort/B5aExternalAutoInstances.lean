import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalLegacyWitnessPayload
import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalLegacyComponentsPayload
import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalShiftedComponentsPayload
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aRootLifts

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.B5aExternalAutoInstances

open Aristotle.Standalone.ExternalPort.B5aExternalLegacyWitnessPayload
open Aristotle.Standalone.ExternalPort.B5aExternalLegacyComponentsPayload
open Aristotle.Standalone.ExternalPort.B5aExternalShiftedComponentsPayload
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootLifts
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries

/-- Auto-wire a legacy explicit-formula class witness from the external
legacy linear-log witness payload class. -/
instance (priority := 100)
    [ExternalLegacyLinearLogWitnessPayload] :
    Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp :=
  explicitFormulaPsiHyp_of_external_payload

/-- Auto-wire the bundled B5a root payload from the external witness payload. -/
instance (priority := 95)
    [ExternalLegacyLinearLogWitnessPayload] :
    ExplicitFormulaPsiB5aRootPayload :=
  rootPayload_of_legacy_explicit_formula

/-- Auto-wire the standalone general truncated explicit-formula class from the
external witness payload. -/
instance (priority := 90)
    [ExternalLegacyLinearLogWitnessPayload] :
    ExplicitFormulaPsiGeneralHyp :=
  explicitFormulaPsiGeneralHyp_of_rootPayload

/-- Auto-wire a legacy explicit-formula class witness from the external
legacy component payload class. -/
instance (priority := 100)
    [ExternalLegacyLinearLogComponentsPayload] :
    Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp :=
  explicitFormulaPsiHyp_of_external_legacy_components_payload

/-- Auto-wire the bundled B5a root payload from the external legacy component
payload class. -/
instance (priority := 95)
    [ExternalLegacyLinearLogComponentsPayload] :
    ExplicitFormulaPsiB5aRootPayload :=
  rootPayload_of_legacy_explicit_formula

/-- Auto-wire the standalone general truncated explicit-formula class from the
external legacy component payload class. -/
instance (priority := 90)
    [ExternalLegacyLinearLogComponentsPayload] :
    ExplicitFormulaPsiGeneralHyp :=
  explicitFormulaPsiGeneralHyp_of_rootPayload

/-- Auto-wire the standalone general truncated explicit-formula class directly
from the external shifted-component payload class. -/
instance (priority := 95)
    [ExternalShiftedBoundComponentsPayload] :
    ExplicitFormulaPsiGeneralHyp :=
  explicitFormulaPsiGeneralHyp_of_rootPayload

/-- Endpoint theorem: any external witness payload provides the canonical B5a
shifted-remainder bound through the auto-wiring lane. -/
theorem shifted_remainder_bound_of_external_witness_auto
    [ExternalLegacyLinearLogWitnessPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_remainder_bound_of_rootPayload

/-- Endpoint theorem: any external legacy-component payload provides the
canonical B5a shifted-remainder bound through the auto-wiring lane. -/
theorem shifted_remainder_bound_of_external_legacy_components_auto
    [ExternalLegacyLinearLogComponentsPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_remainder_bound_of_rootPayload

/-- Endpoint theorem: any external shifted-component payload provides the
canonical B5a shifted-remainder bound through the auto-wiring lane. -/
theorem shifted_remainder_bound_of_external_shifted_components_auto
    [ExternalShiftedBoundComponentsPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_remainder_bound_of_rootPayload

end Aristotle.Standalone.ExternalPort.B5aExternalAutoInstances
