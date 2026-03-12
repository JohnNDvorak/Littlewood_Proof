import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTLogDerivativeHolomorphicCompat

open Complex

/-- External-port helper: logarithmic derivative of a complex function. -/
def logDeriv (f : ℂ → ℂ) : ℂ → ℂ := fun z => deriv f z / f z

/-- External-port adaptation of the Riemann-project helper:
the logarithmic derivative is differentiable on an open set where the function
is differentiable and nonvanishing. -/
theorem differentiableOn_logDeriv
    {U : Set ℂ} (hU_open : IsOpen U)
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U)
    (hf_ne : ∀ z ∈ U, f z ≠ 0) :
    DifferentiableOn ℂ (logDeriv f) U := by
  intro z hz
  have hf_at : DifferentiableAt ℂ f z :=
    hf.differentiableAt (hU_open.mem_nhds hz)
  have hderiv_at : DifferentiableAt ℂ (deriv f) z :=
    (hf.deriv hU_open).differentiableAt (hU_open.mem_nhds hz)
  unfold logDeriv
  exact (DifferentiableAt.div hderiv_at hf_at (hf_ne z hz)).differentiableWithinAt

/-- Continuous version of `differentiableOn_logDeriv`. -/
theorem continuousOn_logDeriv
    {U : Set ℂ} (hU_open : IsOpen U)
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U)
    (hf_ne : ∀ z ∈ U, f z ≠ 0) :
    ContinuousOn (logDeriv f) U :=
  (differentiableOn_logDeriv hU_open hf hf_ne).continuousOn

/-- Specialized external-port endpoint:
`ζ'/ζ` is differentiable on the right half-plane `Re(s) > 1`. -/
theorem differentiableOn_logDeriv_riemannZeta_re_gt_one :
    DifferentiableOn ℂ (logDeriv riemannZeta) {s : ℂ | 1 < s.re} := by
  refine
    differentiableOn_logDeriv
      (isOpen_lt continuous_const continuous_re)
      ?_ ?_
  · intro z hz
    have hz_ne_one : z ≠ 1 := by
      intro hz1
      have : (1 : ℝ) < (1 : ℂ).re := by simpa [hz1] using hz
      norm_num at this
    exact (differentiableAt_riemannZeta hz_ne_one).differentiableWithinAt
  · intro z hz
    exact riemannZeta_ne_zero_of_one_le_re (le_of_lt hz)

/-- Specialized external-port endpoint:
`-ζ'/ζ` is differentiable on the right half-plane `Re(s) > 1`. -/
theorem differentiableOn_neg_logDeriv_riemannZeta_re_gt_one :
    DifferentiableOn ℂ (fun s : ℂ => -deriv riemannZeta s / riemannZeta s)
      {s : ℂ | 1 < s.re} := by
  simpa [logDeriv, neg_div] using
    (DifferentiableOn.neg differentiableOn_logDeriv_riemannZeta_re_gt_one)

/-- Continuous version of `differentiableOn_neg_logDeriv_riemannZeta_re_gt_one`. -/
theorem continuousOn_neg_logDeriv_riemannZeta_re_gt_one :
    ContinuousOn (fun s : ℂ => -deriv riemannZeta s / riemannZeta s)
      {s : ℂ | 1 < s.re} :=
  differentiableOn_neg_logDeriv_riemannZeta_re_gt_one.continuousOn

end Aristotle.Standalone.ExternalPort.StrongPNTLogDerivativeHolomorphicCompat
