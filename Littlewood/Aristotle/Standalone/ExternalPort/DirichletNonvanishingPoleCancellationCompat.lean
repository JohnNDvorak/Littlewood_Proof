import Littlewood.Aristotle.ZetaPoleCancellation

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.DirichletNonvanishingPoleCancellationCompat

open Complex
open Aristotle.ZetaPoleCancellation

/-- External-port adapter for the pole-cancelled zeta function `ζ₁` (named `zrf`
in this repository): on `z ≠ 1`, it agrees with `(z - 1) * ζ(z)`. -/
theorem zrf_apply_of_ne_one_port
    {z : ℂ} (hz : z ≠ 1) :
    zrf z = (z - 1) * riemannZeta z :=
  zrf_of_ne hz

/-- External-port adapter for nonvanishing of `zrf` on the set
`{z | z = 1 ∨ ζ z ≠ 0}`. -/
theorem zrf_nonzero_of_one_or_zeta_nonzero_port
    {z : ℂ} (hz : z = 1 ∨ riemannZeta z ≠ 0) :
    zrf z ≠ 0 := by
  rcases hz with rfl | hzeta
  · simpa [zrf_one]
  · by_cases hz1 : z = 1
    · subst hz1
      simpa [zrf_one]
    · rw [zrf_of_ne hz1]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) hzeta

/-- External-port adapter for the logarithmic-derivative identity used in the
DirichletNonvanishing PNT lane:
`-ζ₁'/ζ₁ = -ζ'/ζ - 1/(z-1)` (on `z ≠ 1`, `ζ z ≠ 0`). -/
theorem neg_logDeriv_zrf_eq_port
    {z : ℂ} (hz1 : z ≠ 1) (hzeta : riemannZeta z ≠ 0) :
    -deriv zrf z / zrf z = -deriv riemannZeta z / riemannZeta z - 1 / (z - 1) := by
  rw [zrf_of_ne hz1, deriv_zrf_of_ne hz1]
  field_simp [sub_ne_zero.mpr hz1, hzeta]
  ring

/-- External-port adapter for continuity of `-ζ₁'/ζ₁` away from zeros of `ζ₁`. -/
theorem continuousOn_neg_logDeriv_zrf_port :
    ContinuousOn (fun z => -deriv zrf z / zrf z) {z | z = 1 ∨ riemannZeta z ≠ 0} := by
  have hzrf_differentiable : Differentiable ℂ zrf := fun z => (zrf_analyticAt z).differentiableAt
  have hdiv :
      ContinuousOn (fun z => deriv zrf z / zrf z) {z | z = 1 ∨ riemannZeta z ≠ 0} := by
    refine (hzrf_differentiable.contDiff.continuous_deriv le_rfl).continuousOn.div
      hzrf_differentiable.continuous.continuousOn (fun z hz => ?_)
    exact zrf_nonzero_of_one_or_zeta_nonzero_port (by simpa using hz)
  simpa [neg_div] using hdiv.neg

end Aristotle.Standalone.ExternalPort.DirichletNonvanishingPoleCancellationCompat
