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

    If we have:
    1. A pointwise bound on ζ'/ζ: |ζ'/ζ(1/2+it)| ≤ A·(logT)² for 1 ≤ |t| ≤ T
    2. A contour geometry bound: the Perron rectangle ∫ gives
       √x · ∫₁ᵀ A·(logT)²/t dt ≤ A·√x·(logT)²·logT = A·√x·(logT)³
    3. Horizontal segment bounds: ≤ B·√x·(logT)²/T each

    Then for T ≥ 16, the total contour bound is
    (A + 2B) · √x · (logT)² / √T.

    This lemma captures the pure algebra: (logT)³/T ≤ (logT)²/√T for T ≥ 16. -/
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
  -- First piece: logT ≤ √T for T ≥ 16, so (logT)³/T ≤ (logT)²·√T/T = (logT)²/√T
  have h_vert : A * (Real.sqrt x * (Real.log T) ^ 3 / T) ≤
      A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
    apply mul_le_mul_of_nonneg_left _ hA.le
    rw [div_le_div_iff₀ hT_pos h_sqrtT_pos]
    rw [show Real.sqrt x * (Real.log T) ^ 2 * T =
        Real.sqrt x * (Real.log T) ^ 2 * (Real.sqrt T * Real.sqrt T) from by
      rw [Real.mul_self_sqrt hT_pos.le]]
    have h_log_sqrt : Real.log T ≤ Real.sqrt T := by
      calc Real.log T = Real.log (Real.sqrt T * Real.sqrt T) := by
            rw [Real.mul_self_sqrt hT_pos.le]
        _ ≤ Real.sqrt T := by
            rw [Real.log_le_iff_le_exp (mul_pos h_sqrtT_pos h_sqrtT_pos)]
            calc Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT_pos.le
              _ ≤ Real.exp (Real.sqrt T) := by
                  rw [← Real.sq_sqrt hT_pos.le]
                  exact Littlewood.Bridge.PerronAssumptionsBridge.exp_ge_sq_of_ge_four
                    (Real.sqrt T) (by rw [show (4 : ℝ) = Real.sqrt 16 from by
                      rw [show (16 : ℝ) = 4 ^ 2 from by norm_num,
                          Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
                    ; exact Real.sqrt_le_sqrt (by linarith))
    nlinarith [sq_nonneg (Real.log T), Real.sqrt_nonneg x]
  -- Second piece: √T ≤ T so (logT)²/T ≤ (logT)²/√T
  have h_horiz : 2 * B * (Real.sqrt x * (Real.log T) ^ 2 / T) ≤
      2 * B * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact div_le_div_of_nonneg_left
      (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _)) hT_pos h_sqrtT_pos h_sqrtT_le_T
  linarith [mul_nonneg hA.le (div_nonneg (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _))
    h_sqrtT_pos.le)]

end Aristotle.Standalone.ExplicitFormulaPsiB5aContourBounds
