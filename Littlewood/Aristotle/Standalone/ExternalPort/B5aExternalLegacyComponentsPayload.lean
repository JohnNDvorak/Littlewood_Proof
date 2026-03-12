import Littlewood.Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourCompat
import Littlewood.Aristotle.Standalone.ExternalPort.B5aExternalLegacyWitnessPayload
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogProvider
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiLegacyGlobalInstance
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.B5aExternalLegacyComponentsPayload

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.ExternalPort.PrimeNumberTheoremAndContourCompat
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogRootInfra
open Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogProvider
open Aristotle.Standalone.ExplicitFormulaPsiLegacyGlobalInstance
open Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
open Aristotle.Standalone.ExternalPort.B5aExternalLegacyWitnessPayload

/-- External payload class for legacy linear-log explicit-formula components.
This mirrors the exact shape expected by
`ExplicitFormulaPsiLegacyLinearLogComponentsHyp`. -/
class ExternalLegacyLinearLogComponentsPayload : Type where
  perronIntegralRe : ℝ → ℝ → ℝ
  contourRemainderRe : ℝ → ℝ → ℝ
  hPerron :
    ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
        Cₚ * Real.log x
  hResidue :
    ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T
  hContour :
    ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |contourRemainderRe x T| ≤
        Cc * (Real.sqrt x * Real.log T / Real.sqrt T)

/-- Construct a legacy component package from a direct legacy witness by splitting
the remainder into contour (`sqrt*log/sqrt`) and Perron (`log`) parts. -/
theorem external_legacy_components_of_witness
    (hWitness :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)) :
    ∃ perronIntegralRe contourRemainderRe : ℝ → ℝ → ℝ,
      (∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
          Cₚ * Real.log x)
      ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T)
      ∧
      (∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |contourRemainderRe x T| ≤
          Cc * (Real.sqrt x * Real.log T / Real.sqrt T)) := by
  rcases hWitness with ⟨C, hC⟩
  let K : ℝ := max |C| 1
  let contourRemainderRe : ℝ → ℝ → ℝ := fun x T =>
    shiftedRemainderRe x T *
      (Real.sqrt x * Real.log T / Real.sqrt T) /
      (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)
  let perronIntegralRe : ℝ → ℝ → ℝ := fun x T =>
    x - zeroSumRe x T + contourRemainderRe x T
  refine ⟨perronIntegralRe, contourRemainderRe, ?_, ?_, ?_⟩
  · refine ⟨K, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro x T hx hT
    let A : ℝ := Real.sqrt x * Real.log T / Real.sqrt T
    let B : ℝ := Real.log x
    let D : ℝ := A + B
    have hA_nonneg : 0 ≤ A := by
      dsimp [A]
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith)))
        (Real.sqrt_nonneg _)
    have hB_pos : 0 < B := by
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlog2_le : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
      dsimp [B]
      linarith
    have hB_nonneg : 0 ≤ B := le_of_lt hB_pos
    have hD_pos : 0 < D := by
      dsimp [D]
      linarith
    have hD_nonneg : 0 ≤ D := le_of_lt hD_pos
    have hEq :
        Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
            (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re) =
          shiftedRemainderRe x T := by
      unfold shiftedRemainderRe zeroSumRe
      ring
    have hShift : |shiftedRemainderRe x T| ≤ K * D := by
      have hBase : |shiftedRemainderRe x T| ≤ C * D := by
        calc
          |shiftedRemainderRe x T|
              = |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
                  (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| := by
                  rw [hEq]
          _ ≤ C * (A + B) := hC x T hx hT
          _ = C * D := by simp [D]
      calc
        |shiftedRemainderRe x T|
            ≤ C * D := hBase
        _ ≤ |C| * D := mul_le_mul_of_nonneg_right (le_abs_self C) hD_nonneg
        _ ≤ K * D := mul_le_mul_of_nonneg_right (le_max_left _ _) hD_nonneg
    have hPerEq :
        Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T =
          shiftedRemainderRe x T - contourRemainderRe x T := by
      unfold perronIntegralRe contourRemainderRe shiftedRemainderRe zeroSumRe
      ring
    have hContour_def :
        contourRemainderRe x T = shiftedRemainderRe x T * (A / D) := by
      unfold contourRemainderRe
      ring
    have hSplit :
        shiftedRemainderRe x T - contourRemainderRe x T =
          shiftedRemainderRe x T * (B / D) := by
      calc
        shiftedRemainderRe x T - contourRemainderRe x T
            = shiftedRemainderRe x T - shiftedRemainderRe x T * (A / D) := by
                rw [hContour_def]
        _ = shiftedRemainderRe x T * ((D - A) / D) := by
              field_simp [hD_pos.ne']
        _ = shiftedRemainderRe x T * (B / D) := by
              simp [D]
    have hFracB_nonneg : 0 ≤ B / D := div_nonneg hB_nonneg hD_nonneg
    calc
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T|
          = |shiftedRemainderRe x T * (B / D)| := by rw [hPerEq, hSplit]
      _ = |shiftedRemainderRe x T| * (B / D) := by
            rw [abs_mul, abs_of_nonneg hFracB_nonneg]
      _ ≤ (K * D) * (B / D) := mul_le_mul_of_nonneg_right hShift hFracB_nonneg
      _ = K * B := by
            field_simp [hD_pos.ne']
      _ = K * Real.log x := by simp [B]
  · intro x T _hx _hT
    unfold perronIntegralRe
    ring
  · refine ⟨K, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro x T hx hT
    let A : ℝ := Real.sqrt x * Real.log T / Real.sqrt T
    let B : ℝ := Real.log x
    let D : ℝ := A + B
    have hA_nonneg : 0 ≤ A := by
      dsimp [A]
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith)))
        (Real.sqrt_nonneg _)
    have hB_pos : 0 < B := by
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlog2_le : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
      dsimp [B]
      linarith
    have hD_pos : 0 < D := by
      dsimp [D]
      linarith [hA_nonneg, hB_pos]
    have hD_nonneg : 0 ≤ D := le_of_lt hD_pos
    have hEq :
        Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
            (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re) =
          shiftedRemainderRe x T := by
      unfold shiftedRemainderRe zeroSumRe
      ring
    have hShift : |shiftedRemainderRe x T| ≤ K * D := by
      have hBase : |shiftedRemainderRe x T| ≤ C * D := by
        calc
          |shiftedRemainderRe x T|
              = |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
                  (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| := by
                  rw [hEq]
          _ ≤ C * (A + B) := hC x T hx hT
          _ = C * D := by simp [D]
      calc
        |shiftedRemainderRe x T|
            ≤ C * D := hBase
        _ ≤ |C| * D := mul_le_mul_of_nonneg_right (le_abs_self C) hD_nonneg
        _ ≤ K * D := mul_le_mul_of_nonneg_right (le_max_left _ _) hD_nonneg
    have hFracA_nonneg : 0 ≤ A / D := div_nonneg hA_nonneg hD_nonneg
    have hContour_def :
        contourRemainderRe x T = shiftedRemainderRe x T * (A / D) := by
      unfold contourRemainderRe
      ring
    calc
      |contourRemainderRe x T|
          = |shiftedRemainderRe x T * (A / D)| := by rw [hContour_def]
      _ = |shiftedRemainderRe x T| * (A / D) := by
            rw [abs_mul, abs_of_nonneg hFracA_nonneg]
      _ ≤ (K * D) * (A / D) := mul_le_mul_of_nonneg_right hShift hFracA_nonneg
      _ = K * A := by
            field_simp [hD_pos.ne']
      _ = K * (Real.sqrt x * Real.log T / Real.sqrt T) := by simp [A]

/-- A direct witness payload can be promoted to the external legacy-component
payload class through the constructive split above. -/
theorem external_legacy_components_payload_nonempty_of_witness
    (hWitness :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x)) :
    Nonempty ExternalLegacyLinearLogComponentsPayload := by
  rcases external_legacy_components_of_witness hWitness with
    ⟨perronIntegralRe, contourRemainderRe, hPerron, hResidue, hContour⟩
  exact
    ⟨{ perronIntegralRe := perronIntegralRe
      , contourRemainderRe := contourRemainderRe
      , hPerron := hPerron
      , hResidue := hResidue
      , hContour := hContour }⟩

/-- A direct witness payload can be promoted to the external legacy-component
payload class through the constructive split above. -/
instance (priority := 90)
    [ExternalLegacyLinearLogWitnessPayload] :
    ExternalLegacyLinearLogComponentsPayload := by
  classical
  exact Classical.choice
    (external_legacy_components_payload_nonempty_of_witness
      ExternalLegacyLinearLogWitnessPayload.witness)

/-- Promote the external component payload into the internal legacy component class. -/
instance (priority := 100)
    [ExternalLegacyLinearLogComponentsPayload] :
    ExplicitFormulaPsiLegacyLinearLogComponentsHyp where
  perronIntegralRe := ExternalLegacyLinearLogComponentsPayload.perronIntegralRe
  contourRemainderRe := ExternalLegacyLinearLogComponentsPayload.contourRemainderRe
  hPerron := ExternalLegacyLinearLogComponentsPayload.hPerron
  hResidue := ExternalLegacyLinearLogComponentsPayload.hResidue
  hContour := ExternalLegacyLinearLogComponentsPayload.hContour

/-- Export the exact legacy linear-log witness from the external component payload. -/
theorem legacy_linear_log_bound_of_external_components_payload
    [ExternalLegacyLinearLogComponentsPayload] :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) := by
  exact legacy_linear_log_bound_provider_of_components

/-- Recover a concrete legacy explicit-formula class term from external components. -/
def explicitFormulaPsiHyp_of_external_legacy_components_payload
    [ExternalLegacyLinearLogComponentsPayload] :
    Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp := by
  infer_instance

/-- Endpoint from external legacy component payload to the B5a shifted bound. -/
theorem shifted_remainder_bound_of_external_legacy_components_payload
    [ExternalLegacyLinearLogComponentsPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact shifted_remainder_bound_of_legacy_explicit_formula

end Aristotle.Standalone.ExternalPort.B5aExternalLegacyComponentsPayload
