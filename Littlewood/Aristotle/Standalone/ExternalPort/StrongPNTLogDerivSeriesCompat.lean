import Littlewood.Aristotle.Standalone.ExternalPort.DirichletNonvanishingCompat

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTLogDerivSeriesCompat

open Aristotle.Standalone.ExternalPort.DirichletNonvanishingCompat

/-- StrongPNT-style identity for `-ζ'/ζ` as a von Mangoldt Dirichlet series,
on the half-plane `Re(s) > 1`. -/
theorem neg_logDeriv_riemannZeta_eq_vonMangoldt_tsum_of_re_gt_one
    {s : ℂ}
    (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      ∑' n : ℕ, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n := by
  exact neg_logDeriv_riemannZeta_eq_tsum_term_vonMangoldt_port hs

/-- Line-specialized series identity for `-ζ'/ζ` at `s = σ + it`, `σ > 1`. -/
theorem neg_logDeriv_riemannZeta_eq_vonMangoldt_tsum_on_line
    {σ t : ℝ}
    (hσ : 1 < σ) :
    -deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I) =
      ∑' n : ℕ,
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (σ + t * Complex.I) n := by
  have hs : 1 < (σ + t * Complex.I).re := by
    simpa using hσ
  exact neg_logDeriv_riemannZeta_eq_tsum_term_vonMangoldt_port hs

/-- Summability of the von Mangoldt line series for `σ > 1`. -/
theorem summable_vonMangoldt_tsum_on_line
    {σ t : ℝ}
    (hσ : 1 < σ) :
    Summable
      (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (σ + t * Complex.I)) := by
  have hs : 1 < (σ + t * Complex.I).re := by
    simpa using hσ
  exact summable_LSeries_term_vonMangoldt_port hs

/-- Real-part series identity on the line `s = σ + it`, `σ > 1`. -/
theorem neg_logDeriv_riemannZeta_re_eq_tsum_re_on_line
    {σ t : ℝ}
    (hσ : 1 < σ) :
    (-deriv riemannZeta (σ + t * Complex.I) /
        riemannZeta (σ + t * Complex.I)).re =
      ∑' n : ℕ,
        (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (σ + t * Complex.I) n).re := by
  have hEq := neg_logDeriv_riemannZeta_eq_vonMangoldt_tsum_on_line (σ := σ) (t := t) hσ
  calc
    (-deriv riemannZeta (σ + t * Complex.I) /
        riemannZeta (σ + t * Complex.I)).re
      = (∑' n : ℕ, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (σ + t * Complex.I) n).re := by
          simpa using congrArg Complex.re hEq
    _ = ∑' n : ℕ,
          (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (σ + t * Complex.I) n).re := by
          simpa using
            Complex.re_tsum
              (summable_vonMangoldt_tsum_on_line (σ := σ) (t := t) hσ)

/-- Pointwise real-part/norm comparison for the line value of `-ζ'/ζ`. -/
theorem abs_re_neg_logDeriv_riemannZeta_on_line_le_norm
    (σ t : ℝ) :
    |(-deriv riemannZeta (σ + t * Complex.I) /
        riemannZeta (σ + t * Complex.I)).re| ≤
      ‖-deriv riemannZeta (σ + t * Complex.I) /
        riemannZeta (σ + t * Complex.I)‖ := by
  simpa using
    (Complex.abs_re_le_norm
      (-deriv riemannZeta (σ + t * Complex.I) /
        riemannZeta (σ + t * Complex.I)))

end Aristotle.Standalone.ExternalPort.StrongPNTLogDerivSeriesCompat
