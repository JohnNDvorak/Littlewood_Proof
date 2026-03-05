import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiLegacyGlobalInstance
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogFromComponents

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogRootInfra

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.ExplicitFormulaPsiLegacyGlobalInstance
open Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogFromComponents

/-- Bundled root payload carrying the exact legacy linear-log witness shape. -/
class ExplicitFormulaPsiLegacyLinearLogRootPayload : Prop where
  witness :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)

/-- Canonical witness extraction from the bundled root payload. -/
theorem legacy_linear_log_bound_of_rootPayload
    [ExplicitFormulaPsiLegacyLinearLogRootPayload] :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) :=
  ExplicitFormulaPsiLegacyLinearLogRootPayload.witness

/-- Promote the root payload witness into the legacy payload class used by the
global `DirichletPhaseAlignment.ExplicitFormulaPsiHyp` instance. -/
def legacyPayload_of_rootPayload
    [ExplicitFormulaPsiLegacyLinearLogRootPayload] :
    ExplicitFormulaPsiLegacyPayload :=
  explicitFormulaPsiLegacyPayload_of_witness
    legacy_linear_log_bound_of_rootPayload

/-- Split component package for constructing the legacy linear-log witness via
`legacy_linear_log_bound_of_components_exact`. -/
class ExplicitFormulaPsiLegacyLinearLogComponentsHyp where
  perronIntegralRe : ℝ → ℝ → ℝ
  contourRemainderRe : ℝ → ℝ → ℝ
  hPerron :
    ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
        Cₚ * Real.log x
  hResidue :
    ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      perronIntegralRe x T = x -
        (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re +
        contourRemainderRe x T
  hContour :
    ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |contourRemainderRe x T| ≤
        Cc * (Real.sqrt x * Real.log T / Real.sqrt T)

/-- Build the legacy linear-log witness from the split component package. -/
theorem legacy_linear_log_bound_of_componentsHyp
    [h : ExplicitFormulaPsiLegacyLinearLogComponentsHyp] :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) := by
  exact legacy_linear_log_bound_of_components_exact
    h.perronIntegralRe
    h.contourRemainderRe
    h.hPerron
    h.hResidue
    h.hContour

/-- Promote the split component package into the bundled root payload. -/
instance rootPayload_of_componentsHyp
    [ExplicitFormulaPsiLegacyLinearLogComponentsHyp] :
    ExplicitFormulaPsiLegacyLinearLogRootPayload where
  witness := legacy_linear_log_bound_of_componentsHyp

end Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogRootInfra
