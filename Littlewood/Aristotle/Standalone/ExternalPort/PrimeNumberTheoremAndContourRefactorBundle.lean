import Littlewood.Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourCompat
import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalConcreteComponentsLane

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourRefactorBundle

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
open Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourCompat
open Aristotle.Standalone.ExternalPort.B5aExternalConcreteComponentsLane
open Aristotle.Standalone.ExternalPort.B5aExternalLegacyComponentsPayload

/-- Lean-4.27 refactor surface for the `PrimeNumberTheoremAndContour` external
lane used in B5a integration. -/
structure PrimeNumberTheoremAndContourRefactorPayload : Type where
  perronIntegralRe : ℝ → ℝ → ℝ
  contourRemainderRe : ℝ → ℝ → ℝ
  perronPullLogSq :
    ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
        Cₚ * (Real.log x) ^ 2
  residuePull :
    ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T
  contourBoundLogSq :
    ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |contourRemainderRe x T| ≤
        Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)
  perronPullLog :
    ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
        Cₚ * Real.log x
  contourBoundLog :
    ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |contourRemainderRe x T| ≤
        Cc * (Real.sqrt x * Real.log T / Real.sqrt T)

private theorem log_le_scaled_log_sq
    {x : ℝ} (hx : x ≥ 2) :
    Real.log x ≤ (1 / Real.log 2) * (Real.log x) ^ 2 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlogx_nonneg : 0 ≤ Real.log x := le_trans (le_of_lt hlog2_pos) hlog2_le
  have hmul : Real.log x * Real.log 2 ≤ (Real.log x) ^ 2 := by
    nlinarith [hlog2_le, hlogx_nonneg]
  have hdiv : Real.log x ≤ (Real.log x) ^ 2 / Real.log 2 := by
    have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
    field_simp [hlog2_ne]
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul
  calc
    Real.log x ≤ (Real.log x) ^ 2 / Real.log 2 := hdiv
    _ = (1 / Real.log 2) * (Real.log x) ^ 2 := by ring

private theorem sqrt_log_term_le_scaled_log_sq_term
    {x T : ℝ} (hT : T ≥ 2) :
    Real.sqrt x * Real.log T / Real.sqrt T ≤
      (1 / Real.log 2) * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
  have hscale_nonneg : 0 ≤ Real.sqrt x / Real.sqrt T := by
    exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hlog_upgrade := log_le_scaled_log_sq hT
  have hmul := mul_le_mul_of_nonneg_left hlog_upgrade hscale_nonneg
  calc
    Real.sqrt x * Real.log T / Real.sqrt T
        = (Real.sqrt x / Real.sqrt T) * Real.log T := by ring
    _ ≤ (Real.sqrt x / Real.sqrt T) * ((1 / Real.log 2) * (Real.log T) ^ 2) := hmul
    _ = (1 / Real.log 2) * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by ring

/-- Build a refactored `PrimeNumberTheoremAndContour` payload from the existing
legacy component payload class by upgrading `log` bounds to `log^2` bounds. -/
def of_external_legacy_components_payload
    [ExternalLegacyLinearLogComponentsPayload] :
    PrimeNumberTheoremAndContourRefactorPayload := by
  refine
    { perronIntegralRe := ExternalLegacyLinearLogComponentsPayload.perronIntegralRe
      contourRemainderRe := ExternalLegacyLinearLogComponentsPayload.contourRemainderRe
      perronPullLogSq := ?_
      residuePull := ExternalLegacyLinearLogComponentsPayload.hResidue
      contourBoundLogSq := ?_
      perronPullLog := ExternalLegacyLinearLogComponentsPayload.hPerron
      contourBoundLog := ExternalLegacyLinearLogComponentsPayload.hContour }
  · rcases ExternalLegacyLinearLogComponentsPayload.hPerron with ⟨Cₚ, hCₚ_pos, hCₚ⟩
    refine ⟨Cₚ / Real.log 2, by positivity, ?_⟩
    intro x T hx hT
    have hBase := hCₚ x T hx hT
    have hUpgrade : Cₚ * Real.log x ≤ (Cₚ / Real.log 2) * (Real.log x) ^ 2 := by
      have hLog := log_le_scaled_log_sq hx
      have hCₚ_nonneg : 0 ≤ Cₚ := le_of_lt hCₚ_pos
      have hMul := mul_le_mul_of_nonneg_left hLog hCₚ_nonneg
      calc
        Cₚ * Real.log x ≤ Cₚ * ((1 / Real.log 2) * (Real.log x) ^ 2) := hMul
        _ = (Cₚ / Real.log 2) * (Real.log x) ^ 2 := by ring
    exact le_trans hBase hUpgrade
  · rcases ExternalLegacyLinearLogComponentsPayload.hContour with ⟨Cc, hCc_pos, hCc⟩
    refine ⟨Cc / Real.log 2, by positivity, ?_⟩
    intro x T hx hT
    have hBase := hCc x T hx hT
    have hUpgrade :
        Cc * (Real.sqrt x * Real.log T / Real.sqrt T) ≤
          (Cc / Real.log 2) * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
      have hTerm := sqrt_log_term_le_scaled_log_sq_term (x := x) (T := T) hT
      have hCc_nonneg : 0 ≤ Cc := le_of_lt hCc_pos
      have hMul := mul_le_mul_of_nonneg_left hTerm hCc_nonneg
      calc
        Cc * (Real.sqrt x * Real.log T / Real.sqrt T)
            ≤ Cc * ((1 / Real.log 2) * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) := hMul
        _ = (Cc / Real.log 2) * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by ring
    exact le_trans hBase hUpgrade

/-- Endpoint: Perron truncation error bound from one refactored payload. -/
theorem perron_truncation_error_of_refactored_payload
    (hPayload : PrimeNumberTheoremAndContourRefactorPayload) :
    ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T - hPayload.contourRemainderRe x T| ≤
        Cₚ * (Real.log x) ^ 2 := by
  exact
    perron_truncation_error_port
      hPayload.perronIntegralRe
      hPayload.contourRemainderRe
      hPayload.perronPullLogSq
      hPayload.residuePull

/-- Endpoint: canonical shifted-contours B5a bound from one refactored payload. -/
theorem shifted_contours_bound_of_refactored_payload
    (hPayload : PrimeNumberTheoremAndContourRefactorPayload) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact
    shifted_contours_bound_of_components_port
      hPayload.perronIntegralRe
      hPayload.contourRemainderRe
      hPayload.perronPullLogSq
      hPayload.residuePull
      hPayload.contourBoundLogSq

/-- Endpoint: legacy linear-log witness shape from one refactored payload. -/
theorem legacy_linear_log_bound_of_refactored_payload
    (hPayload : PrimeNumberTheoremAndContourRefactorPayload) :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) := by
  exact
    legacy_linear_log_bound_of_components_exact_port
      hPayload.perronIntegralRe
      hPayload.contourRemainderRe
      hPayload.perronPullLog
      hPayload.residuePull
      hPayload.contourBoundLog

/-- Constructor endpoint: explicit-formula class from one refactored payload
via the existing concrete-components lane. -/
def explicitFormulaPsiHyp_of_refactored_payload
    (hPayload : PrimeNumberTheoremAndContourRefactorPayload) :
    Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp := by
  exact
    explicitFormulaPsiHyp_of_concrete_external_components
      hPayload.perronIntegralRe
      hPayload.contourRemainderRe
      hPayload.perronPullLog
      hPayload.residuePull
      hPayload.contourBoundLog

/-- Constructor-bundle endpoint for B5a from one refactored payload. -/
theorem b5a_constructor_bundle_of_refactored_payload
    (hPayload : PrimeNumberTheoremAndContourRefactorPayload) :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      ExplicitFormulaPsiGeneralHyp ∧
      ExplicitFormulaPsiB5aRootPayload := by
  letI : ExternalLegacyLinearLogComponentsPayload :=
    externalLegacyComponentsPayload_of_witness
      hPayload.perronIntegralRe
      hPayload.contourRemainderRe
      hPayload.perronPullLog
      hPayload.residuePull
      hPayload.contourBoundLog
  refine ⟨inferInstance, ?_⟩
  exact ⟨inferInstance, inferInstance⟩

end Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourRefactorBundle
