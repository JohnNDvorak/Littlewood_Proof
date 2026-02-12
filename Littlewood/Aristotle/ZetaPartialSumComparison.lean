import Mathlib
import Littlewood.Aristotle.HardyApproxFunctionalEq

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.ZetaPartialSumComparison

open HardyApproxFunctional

/-- Remainder between zeta on the critical line and the partial Dirichlet sum. -/
def zetaRemainder (t : ℝ) : ℂ :=
  riemannZeta (1 / 2 + t * Complex.I) - partial_sum_approx t

/-- Elementary norm-square comparison:
`‖a‖² ≥ ‖b‖² - 2‖b‖‖a-b‖`. -/
theorem norm_sq_ge_norm_sq_sub_two_mul (a b : ℂ) :
    ‖a‖ ^ 2 ≥ ‖b‖ ^ 2 - 2 * ‖b‖ * ‖a - b‖ := by
  by_cases hnonneg : 0 ≤ ‖b‖ - ‖a - b‖
  · have hrev : ‖b - a‖ = ‖a - b‖ := by
      simpa using (norm_sub_rev b a)
    have haux : ‖b‖ - ‖a‖ ≤ ‖a - b‖ := by
      have htmp : ‖b‖ - ‖a‖ ≤ ‖b - a‖ := norm_sub_norm_le b a
      simpa [hrev] using htmp
    have hlin : ‖b‖ - ‖a - b‖ ≤ ‖a‖ := by
      linarith
    have hsq : (‖b‖ - ‖a - b‖) ^ 2 ≤ ‖a‖ ^ 2 := by
      nlinarith [hlin, hnonneg, norm_nonneg a]
    have hcross : ‖b‖ ^ 2 - 2 * ‖b‖ * ‖a - b‖ ≤ (‖b‖ - ‖a - b‖) ^ 2 := by
      nlinarith [sq_nonneg ‖a - b‖]
    have hmain : ‖b‖ ^ 2 - 2 * ‖b‖ * ‖a - b‖ ≤ ‖a‖ ^ 2 :=
      le_trans hcross hsq
    linarith
  · have hlt : ‖b‖ - ‖a - b‖ < 0 := lt_of_not_ge hnonneg
    have hrhs_nonpos : ‖b‖ ^ 2 - 2 * ‖b‖ * ‖a - b‖ ≤ 0 := by
      nlinarith [hlt, norm_nonneg b, norm_nonneg (a - b)]
    nlinarith [hrhs_nonpos, sq_nonneg ‖a‖]

/-- Pointwise comparison between `hardyZ` and the partial sum approximation. -/
theorem hardyZ_sq_ge_partial_sum_sq_sub_cross (t : ℝ) :
    (hardyZ t) ^ 2 ≥
      ‖partial_sum_approx t‖ ^ 2 - 2 * ‖partial_sum_approx t‖ * ‖zetaRemainder t‖ := by
  change ‖riemannZeta (1 / 2 + t * Complex.I)‖ ^ 2 ≥
      ‖partial_sum_approx t‖ ^ 2 -
        2 * ‖partial_sum_approx t‖ *
          ‖riemannZeta (1 / 2 + t * Complex.I) - partial_sum_approx t‖
  simpa [zetaRemainder] using
    (norm_sq_ge_norm_sq_sub_two_mul
      (a := riemannZeta (1 / 2 + t * Complex.I))
      (b := partial_sum_approx t))

/-- A weaker but sometimes convenient variant with an extra `-‖R‖²` term. -/
theorem hardyZ_sq_ge_partial_sum_sq_sub_cross_sub_remainder_sq (t : ℝ) :
    (hardyZ t) ^ 2 ≥
      ‖partial_sum_approx t‖ ^ 2 -
        2 * ‖partial_sum_approx t‖ * ‖zetaRemainder t‖ -
        ‖zetaRemainder t‖ ^ 2 := by
  have h0 : 0 ≤ ‖zetaRemainder t‖ ^ 2 := sq_nonneg _
  have hbase := hardyZ_sq_ge_partial_sum_sq_sub_cross t
  linarith

end Aristotle.ZetaPartialSumComparison
