import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aDefs
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aFromShiftedBound
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aContourBounds
import Littlewood.Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra

open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaPsiB5aFromShiftedBound
open Aristotle.Standalone.ExplicitFormulaPsiB5aContourBounds
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.DirichletPhaseAlignment (ZerosBelow)

/-- Bundled root payload for the B5a shifted-remainder bound leaf. -/
class ExplicitFormulaPsiB5aRootPayload : Prop where
  shiftedBound :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)

/-- Canonical extraction of the shifted-remainder bound from the bundled root payload. -/
theorem shifted_remainder_bound_of_rootPayload
    [ExplicitFormulaPsiB5aRootPayload] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) :=
  ExplicitFormulaPsiB5aRootPayload.shiftedBound

private lemma log_le_inv_log_two_mul_log_sq {u : ℝ} (hu : 2 ≤ u) :
    Real.log u ≤ (Real.log 2)⁻¹ * (Real.log u) ^ 2 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le : Real.log 2 ≤ Real.log u := by
    exact Real.log_le_log (by norm_num) hu
  have hmul : Real.log u * Real.log 2 ≤ (Real.log u) ^ 2 := by
    nlinarith
  have hdiv : Real.log u ≤ (Real.log u) ^ 2 / Real.log 2 := by
    exact (le_div_iff₀ hlog2_pos).2 (by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul)
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

/-- Root bridge: any `ExplicitFormulaPsiGeneralHyp` directly yields the
shifted-remainder bound used by B5a component assembly. -/
theorem shifted_remainder_bound_of_general_hyp
    [h : ExplicitFormulaPsiGeneralHyp] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  rcases h.proof with ⟨C, hC⟩
  refine ⟨max |C| 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x T hx hT
  have hExpr_nonneg :
      0 ≤ Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2 := by
    positivity
  have hEq :
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re) =
        shiftedRemainderRe x T := by
    have hzero :
        (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re = zeroSumRe x T := rfl
    calc
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)
          = -x + (Aristotle.DirichletPhaseAlignment.chebyshevPsi x +
              (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re) := by
              ring
      _ = -x + (Aristotle.DirichletPhaseAlignment.chebyshevPsi x + zeroSumRe x T) := by
            rw [hzero]
      _ = shiftedRemainderRe x T := by
            rw [show shiftedRemainderRe x T =
                Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + zeroSumRe x T by rfl]
            ring
  have hBase :
      |shiftedRemainderRe x T| ≤
        C * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
    calc
      |shiftedRemainderRe x T|
          = |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
              (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| := by
              rw [hEq]
      _ ≤ C * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) :=
        hC x T hx hT
  calc
    |shiftedRemainderRe x T|
        ≤ C * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := hBase
    _ ≤ |C| * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
          exact mul_le_mul_of_nonneg_right (le_abs_self C) hExpr_nonneg
    _ ≤ max |C| 1 * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hExpr_nonneg

/-- Root route with an explicit (non-typeclass) general truncated explicit-formula
input. This is the direct nonclass interface for B5a integration. -/
theorem shifted_remainder_bound_of_general_formula
    (hGeneral :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  letI : ExplicitFormulaPsiGeneralHyp := ⟨hGeneral⟩
  exact shifted_remainder_bound_of_general_hyp

/-- Build `ExplicitFormulaPsiGeneralHyp` directly from any shifted-remainder
bound in the B5a target shape. -/
theorem explicitFormulaPsiGeneralHyp_of_shifted_remainder_bound
    (hBound :
      ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |shiftedRemainderRe x T| ≤
          C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) :
    ExplicitFormulaPsiGeneralHyp := by
  rcases hBound with ⟨C₂, hC₂, hBoundC₂⟩
  refine ⟨⟨C₂, ?_⟩⟩
  intro x T hx hT
  have hEq :
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re) =
        shiftedRemainderRe x T := by
    have hzero :
        (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re = zeroSumRe x T := rfl
    calc
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)
          = -x + (Aristotle.DirichletPhaseAlignment.chebyshevPsi x +
              (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re) := by
              ring
      _ = -x + (Aristotle.DirichletPhaseAlignment.chebyshevPsi x + zeroSumRe x T) := by
            rw [hzero]
      _ = shiftedRemainderRe x T := by
            rw [show shiftedRemainderRe x T =
                Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + zeroSumRe x T by rfl]
            ring
  calc
    |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)|
        = |shiftedRemainderRe x T| := by rw [hEq]
    _ ≤ C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) :=
      hBoundC₂ x T hx hT

/-- Root-payload endpoint for the standalone general truncated explicit-formula class. -/
theorem explicitFormulaPsiGeneralHyp_of_rootPayload
    [ExplicitFormulaPsiB5aRootPayload] :
    ExplicitFormulaPsiGeneralHyp := by
  exact explicitFormulaPsiGeneralHyp_of_shifted_remainder_bound
    shifted_remainder_bound_of_rootPayload

/-- Non-circular component package provider from `ExplicitFormulaPsiGeneralHyp`. -/
theorem shifted_contours_components_of_general_hyp
    [h : ExplicitFormulaPsiGeneralHyp] :
    ∃ perronIntegralRe contourRemainderRe : ℝ → ℝ → ℝ,
      (∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
          Cₚ * (Real.log x) ^ 2)
      ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T)
      ∧
      (∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |contourRemainderRe x T| ≤
          Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) := by
  exact
    shifted_contours_components_of_shifted_bound
      shifted_remainder_bound_of_general_hyp

/-- Component-package route from an explicit (non-typeclass) general
truncated explicit-formula theorem. -/
theorem shifted_contours_components_of_general_formula
    (hGeneral :
      ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
          C * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) :
    ∃ perronIntegralRe contourRemainderRe : ℝ → ℝ → ℝ,
      (∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
          Cₚ * (Real.log x) ^ 2)
      ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T)
      ∧
      (∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |contourRemainderRe x T| ≤
          Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) := by
  letI : ExplicitFormulaPsiGeneralHyp := ⟨hGeneral⟩
  exact shifted_contours_components_of_general_hyp

/-- Bridge from the legacy Dirichlet-phase explicit-formula class
(`sqrt*log/sqrt + log`) into the B5a shifted-remainder shape
(`sqrt*log^2/sqrt + log^2`). -/
theorem shifted_remainder_bound_of_legacy_explicit_formula
    [hLegacy : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  let K : ℝ := (Real.log 2)⁻¹
  have hK_pos : 0 < K := by
    dsimp [K]
    exact inv_pos.mpr (Real.log_pos (by norm_num))
  refine ⟨max (|hLegacy.C| * K) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x T hx hT
  have hLin_nonneg :
      0 ≤ Real.sqrt x * Real.log T / Real.sqrt T + Real.log x := by
    have hlogT_nonneg : 0 ≤ Real.log T := by
      exact Real.log_nonneg (by linarith)
    have hlogx_nonneg : 0 ≤ Real.log x := by
      exact Real.log_nonneg (by linarith)
    have hmain_nonneg : 0 ≤ Real.sqrt x * Real.log T / Real.sqrt T := by
      exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hlogT_nonneg) (Real.sqrt_nonneg _)
    linarith
  have hSq_nonneg :
      0 ≤ Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2 := by
    positivity
  have hlogT_sq :
      Real.log T ≤ K * (Real.log T) ^ 2 := by
    have hlog := log_le_inv_log_two_mul_log_sq hT
    simpa [K] using hlog
  have hlogx_sq :
      Real.log x ≤ K * (Real.log x) ^ 2 := by
    have hlog := log_le_inv_log_two_mul_log_sq hx
    simpa [K] using hlog
  have hmain_sq :
      Real.sqrt x * Real.log T / Real.sqrt T ≤
        K * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
    have hfactor_nonneg : 0 ≤ Real.sqrt x / Real.sqrt T := by positivity
    calc
      Real.sqrt x * Real.log T / Real.sqrt T
          = (Real.sqrt x / Real.sqrt T) * Real.log T := by ring
      _ ≤ (Real.sqrt x / Real.sqrt T) * (K * (Real.log T) ^ 2) :=
            mul_le_mul_of_nonneg_left hlogT_sq hfactor_nonneg
      _ = K * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by ring
  have hLinear_to_sq :
      Real.sqrt x * Real.log T / Real.sqrt T + Real.log x ≤
        K * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
    calc
      Real.sqrt x * Real.log T / Real.sqrt T + Real.log x
          ≤ K * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) +
              K * (Real.log x) ^ 2 := add_le_add hmain_sq hlogx_sq
      _ = K * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
            ring
  have hEq :
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re) =
        shiftedRemainderRe x T := by
    have hzero :
        (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re = zeroSumRe x T := rfl
    calc
      Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
          (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)
          = -x + (Aristotle.DirichletPhaseAlignment.chebyshevPsi x +
              (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re) := by
              ring
      _ = -x + (Aristotle.DirichletPhaseAlignment.chebyshevPsi x + zeroSumRe x T) := by
            rw [hzero]
      _ = shiftedRemainderRe x T := by
            rw [show shiftedRemainderRe x T =
                Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + zeroSumRe x T by rfl]
            ring
  have hBase :
      |shiftedRemainderRe x T| ≤
        hLegacy.C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) := by
    calc
      |shiftedRemainderRe x T|
          = |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
              (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| := by
              rw [hEq]
      _ ≤ hLegacy.C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) := by
          simpa using hLegacy.psi_approx x T hx hT
  calc
    |shiftedRemainderRe x T|
        ≤ hLegacy.C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) := hBase
    _ ≤ |hLegacy.C| * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) := by
          exact mul_le_mul_of_nonneg_right (le_abs_self hLegacy.C) hLin_nonneg
    _ ≤ |hLegacy.C| * (K * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hLinear_to_sq (abs_nonneg _)
    _ = (|hLegacy.C| * K) * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
          ring
    _ ≤ max (|hLegacy.C| * K) 1 *
          (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hSq_nonneg

/-- Legacy-class bridge exported as an explicit (non-typeclass) general
truncated explicit-formula theorem payload. -/
theorem general_formula_of_legacy_explicit_formula
    [Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp] :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact
    (explicitFormulaPsiGeneralHyp_of_shifted_remainder_bound
      shifted_remainder_bound_of_legacy_explicit_formula).proof

/-- Term-style variant of `general_formula_of_legacy_explicit_formula`, useful at
call sites that have a legacy witness term but do not use typeclass inference. -/
theorem general_formula_of_legacy_explicit_formula_term
    (hLegacy : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp) :
    ∃ C : ℝ, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x -
        (-(∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re)| ≤
        C * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  letI : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp := hLegacy
  exact general_formula_of_legacy_explicit_formula

/-- Legacy-class route rebuilt through the explicit `hGeneral` API. -/
theorem shifted_remainder_bound_of_legacy_via_general_formula
    [Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp] :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  exact
    shifted_remainder_bound_of_general_formula
      general_formula_of_legacy_explicit_formula

/-- Non-circular component package provider from the legacy
Dirichlet-phase explicit-formula class. -/
theorem shifted_contours_components_of_legacy_explicit_formula
    [hLegacy : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp] :
    ∃ perronIntegralRe contourRemainderRe : ℝ → ℝ → ℝ,
      (∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
          Cₚ * (Real.log x) ^ 2)
      ∧
      (∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T)
      ∧
      (∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |contourRemainderRe x T| ≤
          Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) := by
  exact
    shifted_contours_components_of_shifted_bound
      shifted_remainder_bound_of_legacy_explicit_formula

end Aristotle.Standalone.ExplicitFormulaPsiB5aRootInfra
