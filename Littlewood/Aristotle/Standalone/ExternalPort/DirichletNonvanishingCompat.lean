import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.DirichletNonvanishingCompat

open Complex

/-- External-port adapter for `DirichletNonvanishing/Project/EulerProducts/PNT.lean`:
`riemannZeta_ne_zero_of_one_le_re`. -/
theorem riemannZeta_ne_zero_of_one_le_re_port
    {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- External-port adapter for the simple-pole residue statement at `s = 1`. -/
theorem riemannZeta_residue_one_port :
    Filter.Tendsto (fun s => (s - 1) * riemannZeta s)
      (nhdsWithin 1 ({1}ᶜ))
      (nhds 1) :=
  riemannZeta_residue_one

/-- External-port adapter for the von Mangoldt L-series identity (right
half-plane `Re(s) > 1`). -/
theorem neg_logDeriv_riemannZeta_eq_LSeries_vonMangoldt_port
    {s : ℂ} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  simpa using
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs).symm

/-- Same identity, unfolded to the `tsum` over `LSeries.term`. -/
theorem neg_logDeriv_riemannZeta_eq_tsum_term_vonMangoldt_port
    {s : ℂ} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      ∑' n : ℕ, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n := by
  simpa [LSeries] using
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs).symm

/-- Summability adapter for the same L-series term on `Re(s) > 1`. -/
theorem summable_LSeries_term_vonMangoldt_port
    {s : ℂ} (hs : 1 < s.re) :
    Summable (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) :=
  ArithmeticFunction.LSeriesSummable_vonMangoldt hs

end Aristotle.Standalone.ExternalPort.DirichletNonvanishingCompat
