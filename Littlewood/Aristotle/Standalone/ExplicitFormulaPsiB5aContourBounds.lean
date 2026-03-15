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

/-- **Contour bound from Hadamard product decomposition** (C50).

    Total contour: (A·(logT)³ + 2B·(logT)²)/T ≤ (A+2B)·(logT)²/√T for T ≥ 16.
    Uses logT ≤ √T and √T ≤ T. -/
theorem contour_bound_assembly
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (x T : ℝ) (_hx : 2 ≤ x) (hT : 16 ≤ T) :
    A * (Real.sqrt x * (Real.log T) ^ 3 / T) +
    2 * B * (Real.sqrt x * (Real.log T) ^ 2 / T) ≤
    (A + 2 * B) * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
  have hT_pos : 0 < T := by linarith
  have h_sqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos_of_pos hT_pos
  have h_sqrtT_le_T : Real.sqrt T ≤ T := by
    calc Real.sqrt T ≤ Real.sqrt T * Real.sqrt T :=
          le_mul_of_one_le_right (Real.sqrt_nonneg T) (by rw [Real.one_le_sqrt]; linarith)
      _ = T := Real.mul_self_sqrt hT_pos.le
  -- (logT)²/T ≤ (logT)²/√T since √T ≤ T
  have h_num_nn : 0 ≤ Real.sqrt x * (Real.log T) ^ 2 :=
    mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _)
  have h_T_sqrtT : Real.sqrt x * (Real.log T) ^ 2 / T ≤
      Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T := by
    rw [div_le_div_iff₀ hT_pos h_sqrtT_pos]
    exact mul_le_mul_of_nonneg_left h_sqrtT_le_T h_num_nn
  -- (logT)³/T = logT · (logT)²/T ≤ √T · (logT)²/T = (logT)²·√T/T = (logT)²/√T
  -- actually: (logT)³/T ≤ (logT)²/√T ⟺ (logT)³·√T ≤ (logT)²·T
  -- ⟺ logT ≤ T/√T = √T (true for T ≥ 16 by logT_le_sqrtT)
  have h_vert : Real.sqrt x * (Real.log T) ^ 3 / T ≤
      Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T := by
    rw [div_le_div_iff₀ hT_pos h_sqrtT_pos]
    rw [show Real.sqrt x * (Real.log T) ^ 2 * T =
        Real.sqrt x * (Real.log T) ^ 2 * (Real.sqrt T * Real.sqrt T) from by
      rw [Real.mul_self_sqrt hT_pos.le]]
    -- logT ≤ √T for T ≥ 16: T = (√T)² ≤ exp(√T) since exp(u) ≥ u² for u ≥ 4
    have h_log_le : Real.log T ≤ Real.sqrt T := by
      rw [← Real.exp_le_exp]
      calc Real.exp (Real.log T) = T := Real.exp_log hT_pos
        _ = (Real.sqrt T) ^ 2 := (Real.sq_sqrt hT_pos.le).symm
        _ ≤ Real.exp (Real.sqrt T) := by
            have h4 : (4 : ℝ) ≤ Real.sqrt T := by
              calc (4 : ℝ) = Real.sqrt 16 := by
                    rw [show (16 : ℝ) = 4 ^ 2 from by norm_num,
                        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
                _ ≤ Real.sqrt T := Real.sqrt_le_sqrt (by linarith)
            have hst := Real.sum_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ Real.sqrt T) 4
            simp [Finset.sum_range_succ, Nat.factorial] at hst
            nlinarith [sq_nonneg (Real.sqrt T - 4)]
    -- Goal: √x·(logT)³·√T ≤ √x·(logT)²·(√T·√T)
    -- Factor: √x·(logT)²·(logT·√T) ≤ √x·(logT)²·(√T·√T) from logT ≤ √T
    have hlog_nn : (0 : ℝ) ≤ Real.log T := by linarith [Real.log_nonneg (by linarith : (1:ℝ) ≤ T)]
    have hfactor : Real.sqrt x * (Real.log T) ^ 2 * (Real.log T * Real.sqrt T)
        ≤ Real.sqrt x * (Real.log T) ^ 2 * (Real.sqrt T * Real.sqrt T) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right h_log_le h_sqrtT_pos.le
      · exact mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _)
    nlinarith [hfactor]
  -- Piece 1: A · vert ≤ A · target
  have h1 : A * (Real.sqrt x * (Real.log T) ^ 3 / T) ≤
      A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) :=
    mul_le_mul_of_nonneg_left h_vert hA.le
  -- Piece 2: 2B · horiz ≤ 2B · target
  have h2 : 2 * B * (Real.sqrt x * (Real.log T) ^ 2 / T) ≤
      2 * B * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) :=
    mul_le_mul_of_nonneg_left h_T_sqrtT (by positivity)
  -- Sum ≤ (A + 2B) · target
  have h_target_nn : 0 ≤ Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _)) h_sqrtT_pos.le
  linarith

end Aristotle.Standalone.ExplicitFormulaPsiB5aContourBounds
