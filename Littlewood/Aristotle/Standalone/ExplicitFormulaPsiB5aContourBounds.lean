import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aPerron

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiB5aContourBounds

open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaPsiB5aPerron

/-- Triangle-inequality combiner:
`(log x)^2` Perron truncation error + contour remainder bound imply the final
`sqrt/log + log^2` bound for `shiftedRemainderRe`. -/
theorem contour_remainder_bound
    (contourRemainderRe : ℝ → ℝ → ℝ)
    (hPerron :
      ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |shiftedRemainderRe x T - contourRemainderRe x T| ≤
          Cₚ * (Real.log x) ^ 2)
    (hContour :
      ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |contourRemainderRe x T| ≤
          Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  rcases hPerron with ⟨Cₚ, hCₚ_pos, hCₚ⟩
  rcases hContour with ⟨Cc, hCc_pos, hCc⟩
  refine ⟨max Cₚ Cc, lt_of_lt_of_le hCₚ_pos (le_max_left _ _), ?_⟩
  intro x T hx hT
  set mainErr : ℝ := Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T
  have hlog_sq_nonneg : 0 ≤ (Real.log x) ^ 2 := sq_nonneg (Real.log x)
  have hmain_nonneg : 0 ≤ mainErr := by
    unfold mainErr
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (Real.sqrt_nonneg _)
  have htri :
      |shiftedRemainderRe x T| ≤
        |shiftedRemainderRe x T - contourRemainderRe x T| + |contourRemainderRe x T| := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (abs_sub_le (shiftedRemainderRe x T) (contourRemainderRe x T) (0 : ℝ))
  calc
    |shiftedRemainderRe x T|
        ≤ |shiftedRemainderRe x T - contourRemainderRe x T| + |contourRemainderRe x T| := htri
    _ ≤ Cₚ * (Real.log x) ^ 2 + Cc * mainErr := add_le_add (hCₚ x T hx hT) (by
          simpa [mainErr] using hCc x T hx hT)
    _ ≤ max Cₚ Cc * (Real.log x) ^ 2 + max Cₚ Cc * mainErr := add_le_add
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog_sq_nonneg)
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hmain_nonneg)
    _ = max Cₚ Cc * (mainErr + (Real.log x) ^ 2) := by ring
    _ = max Cₚ Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
          rw [show mainErr = Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T by rfl]

/-- Full B5a assembly from the three component hypotheses:
Perron truncation error, residue extraction identity, and contour remainder bound. -/
theorem shifted_contours_bound_of_components
    (perronIntegralRe contourRemainderRe : ℝ → ℝ → ℝ)
    (hPerronRaw :
      ∃ Cₚ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| ≤
          Cₚ * (Real.log x) ^ 2)
    (hResidue :
      ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        perronIntegralRe x T = x - zeroSumRe x T + contourRemainderRe x T)
    (hContour :
      ∃ Cc > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |contourRemainderRe x T| ≤
          Cc * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T)) :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  have hPerron := perron_truncation_error perronIntegralRe contourRemainderRe hPerronRaw hResidue
  exact contour_remainder_bound contourRemainderRe hPerron hContour

end Aristotle.Standalone.ExplicitFormulaPsiB5aContourBounds
