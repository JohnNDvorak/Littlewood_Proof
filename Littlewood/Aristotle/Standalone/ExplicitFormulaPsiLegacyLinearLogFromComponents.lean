import Littlewood.Aristotle.DirichletPhaseAlignment

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogFromComponents

open Aristotle.DirichletPhaseAlignment (ZerosBelow)

private def zeroSumRe (x T : ℝ) : ℝ :=
  (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re

private def legacyRemainderRe (x T : ℝ) : ℝ :=
  Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + zeroSumRe x T

/-- Build the legacy linear-log explicit-formula witness from a
Perron/residue/contour component package. -/
theorem legacy_linear_log_bound_of_components
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
    ∃ C > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |legacyRemainderRe x T| ≤
        C * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) := by
  rcases hPerron with ⟨Cₚ, hCₚ_pos, hCₚ⟩
  rcases hContour with ⟨Cc, hCc_pos, hCc⟩
  refine ⟨max Cₚ Cc, lt_of_lt_of_le hCₚ_pos (le_max_left _ _), ?_⟩
  intro x T hx hT
  have hmain_nonneg : 0 ≤ Real.sqrt x * Real.log T / Real.sqrt T := by
    exact div_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith)))
      (Real.sqrt_nonneg _)
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hrewrite :
      legacyRemainderRe x T =
        (Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T) +
          contourRemainderRe x T := by
    unfold legacyRemainderRe
    rw [hResidue x T hx hT]
    ring
  calc
    |legacyRemainderRe x T|
        = |(Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T) +
            contourRemainderRe x T| := by rw [hrewrite]
    _ ≤ |Aristotle.DirichletPhaseAlignment.chebyshevPsi x - perronIntegralRe x T| +
          |contourRemainderRe x T| := abs_add_le _ _
    _ ≤ Cₚ * Real.log x + Cc * (Real.sqrt x * Real.log T / Real.sqrt T) :=
          add_le_add (hCₚ x T hx hT) (hCc x T hx hT)
    _ ≤ max Cₚ Cc * Real.log x +
          max Cₚ Cc * (Real.sqrt x * Real.log T / Real.sqrt T) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog_nonneg)
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hmain_nonneg)
    _ = max Cₚ Cc * (Real.sqrt x * Real.log T / Real.sqrt T + Real.log x) := by
          ring

/-- Same component combiner, exported in the exact legacy class witness shape. -/
theorem legacy_linear_log_bound_of_components_exact
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
  rcases legacy_linear_log_bound_of_components
      perronIntegralRe contourRemainderRe hPerron hResidue hContour with
    ⟨C, _hC_pos, hC⟩
  refine ⟨C, ?_⟩
  intro x T hx hT
  simpa [legacyRemainderRe, zeroSumRe, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    hC x T hx hT

end Aristotle.Standalone.ExplicitFormulaPsiLegacyLinearLogFromComponents
