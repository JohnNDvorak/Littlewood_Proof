import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalAutoInstances

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.B5aExternalConcreteComponentsLane

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExternalPort.B5aExternalLegacyComponentsPayload
open Aristotle.Standalone.ExternalPort.B5aExternalAutoInstances

/-- Build the external legacy-component payload class from a concrete
Perron/residue/contour theorem package. -/
def externalLegacyComponentsPayload_of_witness
    (perronIntegralRe contourRemainderRe : ℝ → ℝ → ℝ)
    (hPerron :
      ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
          Cₚ * Real.log x)
    (hResidue :
      ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T)
    (hContour :
      ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |contourRemainderRe x T| ≤
          Cc * (Real.sqrt x * Real.log T / Real.sqrt T)) :
    ExternalLegacyLinearLogComponentsPayload where
  perronIntegralRe := perronIntegralRe
  contourRemainderRe := contourRemainderRe
  hPerron := hPerron
  hResidue := hResidue
  hContour := hContour

/-- Endpoint: recover the legacy linear-log witness theorem from a concrete
component package. -/
theorem legacy_linear_log_bound_of_concrete_external_components
    (perronIntegralRe contourRemainderRe : ℝ → ℝ → ℝ)
    (hPerron :
      ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
          Cₚ * Real.log x)
    (hResidue :
      ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T)
    (hContour :
      ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |contourRemainderRe x T| ≤
          Cc * (Real.sqrt x * Real.log T / Real.sqrt T)) :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) := by
  letI : ExternalLegacyLinearLogComponentsPayload :=
    externalLegacyComponentsPayload_of_witness
      perronIntegralRe contourRemainderRe hPerron hResidue hContour
  exact legacy_linear_log_bound_of_external_components_payload

/-- Endpoint: recover a concrete legacy explicit-formula class term from a
concrete component package. -/
def explicitFormulaPsiHyp_of_concrete_external_components
    (perronIntegralRe contourRemainderRe : ℝ → ℝ → ℝ)
    (hPerron :
      ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
          Cₚ * Real.log x)
    (hResidue :
      ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T)
    (hContour :
      ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |contourRemainderRe x T| ≤
          Cc * (Real.sqrt x * Real.log T / Real.sqrt T)) :
    Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp := by
  letI : ExternalLegacyLinearLogComponentsPayload :=
    externalLegacyComponentsPayload_of_witness
      perronIntegralRe contourRemainderRe hPerron hResidue hContour
  exact explicitFormulaPsiHyp_of_external_legacy_components_payload

/-- Endpoint: recover the canonical B5a shifted-remainder bound from a concrete
component package. -/
theorem shifted_remainder_bound_of_concrete_external_components
    (perronIntegralRe contourRemainderRe : ℝ → ℝ → ℝ)
    (hPerron :
      ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
          Cₚ * Real.log x)
    (hResidue :
      ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T)
    (hContour :
      ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |contourRemainderRe x T| ≤
          Cc * (Real.sqrt x * Real.log T / Real.sqrt T)) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  letI : ExternalLegacyLinearLogComponentsPayload :=
    externalLegacyComponentsPayload_of_witness
      perronIntegralRe contourRemainderRe hPerron hResidue hContour
  exact shifted_remainder_bound_of_external_legacy_components_auto

end Aristotle.Standalone.ExternalPort.B5aExternalConcreteComponentsLane
