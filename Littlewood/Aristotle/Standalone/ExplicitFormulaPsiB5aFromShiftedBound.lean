import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aDefs

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiB5aFromShiftedBound

open Aristotle.Standalone.ExplicitFormulaPsiSkeleton

private def mainErr (x T : ℝ) : ℝ :=
  Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T

private def logSqErr (x : ℝ) : ℝ :=
  (Real.log x) ^ 2

private def denom (x T : ℝ) : ℝ :=
  mainErr x T + logSqErr x

private lemma split_weighted_bounds
    {C z a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b)
    (hz : |z| ≤ C * (a + b)) :
    |z * (a / (a + b))| ≤ C * a ∧
      |z * (b / (a + b))| ≤ C * b := by
  have hden_ne : a + b ≠ 0 := ne_of_gt hab
  have ha_div_nonneg : 0 ≤ a / (a + b) := by
    exact div_nonneg ha hab.le
  have hb_div_nonneg : 0 ≤ b / (a + b) := by
    exact div_nonneg hb hab.le
  constructor
  · calc
      |z * (a / (a + b))|
          = |z| * (a / (a + b)) := by
              rw [abs_mul, abs_of_nonneg ha_div_nonneg]
      _ ≤ (C * (a + b)) * (a / (a + b)) :=
            mul_le_mul_of_nonneg_right hz ha_div_nonneg
      _ = C * a := by
            field_simp [hden_ne]
  · calc
      |z * (b / (a + b))|
          = |z| * (b / (a + b)) := by
              rw [abs_mul, abs_of_nonneg hb_div_nonneg]
      _ ≤ (C * (a + b)) * (b / (a + b)) :=
            mul_le_mul_of_nonneg_right hz hb_div_nonneg
      _ = C * b := by
            field_simp [hden_ne]

/-- Construct the Perron/residue/contour component package from the direct
shifted-remainder bound. This is pure algebraic splitting of the error budget
between the `(log x)^2` and `sqrt/log` channels. -/
theorem shifted_contours_components_of_shifted_bound
    (hShifted :
      ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
        |shiftedRemainderRe x T| ≤
          C₂ * (mainErr x T + logSqErr x)) :
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
  rcases hShifted with ⟨C₂, hC₂_pos, hC₂⟩
  let contourRemainderRe : ℝ → ℝ → ℝ :=
    fun x T => shiftedRemainderRe x T * (mainErr x T / denom x T)
  let perronIntegralRe : ℝ → ℝ → ℝ :=
    fun x T => x - zeroSumRe x T + contourRemainderRe x T
  refine ⟨perronIntegralRe, contourRemainderRe, ?_, ?_, ?_⟩
  · refine ⟨C₂, hC₂_pos, ?_⟩
    intro x T hx hT
    have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hb_pos : 0 < logSqErr x := by
      unfold logSqErr
      exact sq_pos_of_pos hlog_pos
    have ha_nonneg : 0 ≤ mainErr x T := by
      unfold mainErr
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
        (Real.sqrt_nonneg _)
    have hden_pos : 0 < denom x T := by
      unfold denom
      linarith
    have hsplit := split_weighted_bounds
      (ha := ha_nonneg) (hb := hb_pos.le) (hab := hden_pos)
      (hz := hC₂ x T hx hT)
    have hdiff :
        Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T =
          shiftedRemainderRe x T * (logSqErr x / denom x T) := by
      unfold perronIntegralRe contourRemainderRe shiftedRemainderRe denom
      have hden_ne : mainErr x T + logSqErr x ≠ 0 := ne_of_gt hden_pos
      field_simp [hden_ne]
      ring
    rw [hdiff]
    convert hsplit.2 using 1
  · intro x T _ _
    unfold perronIntegralRe
    rfl
  · refine ⟨C₂, hC₂_pos, ?_⟩
    intro x T hx hT
    have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hb_pos : 0 < logSqErr x := by
      unfold logSqErr
      exact sq_pos_of_pos hlog_pos
    have ha_nonneg : 0 ≤ mainErr x T := by
      unfold mainErr
      exact div_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
        (Real.sqrt_nonneg _)
    have hden_pos : 0 < denom x T := by
      unfold denom
      linarith
    have hsplit := split_weighted_bounds
      (ha := ha_nonneg) (hb := hb_pos.le) (hab := hden_pos)
      (hz := hC₂ x T hx hT)
    unfold contourRemainderRe
    convert hsplit.1 using 1

end Aristotle.Standalone.ExplicitFormulaPsiB5aFromShiftedBound
