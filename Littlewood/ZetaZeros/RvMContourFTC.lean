/-
Fundamental Theorem of Calculus for logDeriv along vertical lines.

**THIS FILE IS SORRY-FREE.**

Provides the key FTC lemma needed for the Riemann-von Mangoldt contour evaluation:
for f holomorphic and nonzero with f mapping into the slit plane along a vertical
line σ+i[a,b], we have:

  ∫_a^b logDeriv(f)(σ+iy) · i dy = log(f(σ+ib)) - log(f(σ+ia))

Also provides the bound:
  ‖∫_a^b logDeriv(f)(σ+iy) · i dy‖ ≤ |log f(σ+ib)| + |log f(σ+ia)|

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option maxHeartbeats 3200000
set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace ZetaZeros.RvMFTC

/-! ## FTC for logDeriv along vertical lines -/

/-- Derivative of the path y ↦ σ + iy is I. -/
private theorem hasDerivAt_vertical_path (σ : ℝ) (y : ℝ) :
    HasDerivAt (fun t : ℝ => (↑σ : ℂ) + ↑t * I) I y := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 y := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => (↑t : ℂ) * I) (1 * I) y := h1.mul_const I
  simp only [one_mul] at h2
  have h3 : HasDerivAt (fun _ : ℝ => (↑σ : ℂ)) 0 y := hasDerivAt_const y (↑σ : ℂ)
  convert h3.add h2 using 1; simp

/-- d/dy log(f(σ+iy)) = i · logDeriv(f)(σ+iy), when f(σ+iy) ∈ slitPlane. -/
theorem hasDerivAt_log_comp_vertical (f : ℂ → ℂ) (σ : ℝ) (y : ℝ)
    (hf_diff : DifferentiableAt ℂ f (↑σ + ↑y * I))
    (hf_slit : f (↑σ + ↑y * I) ∈ slitPlane) :
    HasDerivAt (fun t : ℝ => log (f (↑σ + ↑t * I)))
      (I * logDeriv f (↑σ + ↑y * I)) y := by
  have h_path := hasDerivAt_vertical_path σ y
  have h_logf : HasDerivAt (log ∘ f)
      ((f (↑σ + ↑y * I))⁻¹ * deriv f (↑σ + ↑y * I)) (↑σ + ↑y * I) :=
    (hasDerivAt_log hf_slit).comp _ hf_diff.hasDerivAt
  have h_comp := h_logf.scomp y h_path
  refine h_comp.congr_deriv ?_
  simp only [smul_eq_mul, logDeriv_apply]; ring

/-- **FTC for logDeriv along a vertical line.**
    If f is differentiable, nonzero, and maps into slitPlane along σ+i[a,b], then
    ∫_a^b i · logDeriv(f)(σ+iy) dy = log(f(σ+ib)) - log(f(σ+ia)). -/
theorem vertical_logDeriv_integral (f : ℂ → ℂ) (σ a b : ℝ)
    (hf_diff : ∀ y ∈ uIcc a b, DifferentiableAt ℂ f (↑σ + ↑y * I))
    (hf_slit : ∀ y ∈ uIcc a b, f (↑σ + ↑y * I) ∈ slitPlane)
    (hf_cont : ContinuousOn (fun y : ℝ => I * logDeriv f (↑σ + ↑y * I)) (uIcc a b)) :
    ∫ y in a..b, I * logDeriv f (↑σ + ↑y * I) =
      log (f (↑σ + ↑b * I)) - log (f (↑σ + ↑a * I)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hy
    exact hasDerivAt_log_comp_vertical f σ y (hf_diff y hy) (hf_slit y hy)
  · exact hf_cont.intervalIntegrable

/-- The norm of the vertical logDeriv integral is bounded by the sum of log norms. -/
theorem vertical_logDeriv_integral_bound (f : ℂ → ℂ) (σ a b : ℝ)
    (hf_diff : ∀ y ∈ uIcc a b, DifferentiableAt ℂ f (↑σ + ↑y * I))
    (hf_slit : ∀ y ∈ uIcc a b, f (↑σ + ↑y * I) ∈ slitPlane)
    (hf_cont : ContinuousOn (fun y : ℝ => I * logDeriv f (↑σ + ↑y * I)) (uIcc a b)) :
    ‖∫ y in a..b, I * logDeriv f (↑σ + ↑y * I)‖ ≤
      ‖log (f (↑σ + ↑b * I))‖ + ‖log (f (↑σ + ↑a * I))‖ := by
  rw [vertical_logDeriv_integral f σ a b hf_diff hf_slit hf_cont]
  exact norm_sub_le _ _

/-! ## FTC for logDeriv along horizontal lines -/

/-- Derivative of the path x ↦ x + it is 1. -/
private theorem hasDerivAt_horizontal_path (t : ℝ) (x : ℝ) :
    HasDerivAt (fun u : ℝ => (↑u : ℂ) + ↑t * I) 1 x := by
  have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun _ : ℝ => (↑t : ℂ) * I) 0 x := hasDerivAt_const x (↑t * I)
  convert h1.add h2 using 1; simp

/-- d/dx log(f(x+it)) = logDeriv(f)(x+it), when f(x+it) ∈ slitPlane. -/
theorem hasDerivAt_log_comp_horizontal (f : ℂ → ℂ) (t : ℝ) (x : ℝ)
    (hf_diff : DifferentiableAt ℂ f (↑x + ↑t * I))
    (hf_slit : f (↑x + ↑t * I) ∈ slitPlane) :
    HasDerivAt (fun u : ℝ => log (f (↑u + ↑t * I)))
      (logDeriv f (↑x + ↑t * I)) x := by
  have h_path := hasDerivAt_horizontal_path t x
  have h_logf : HasDerivAt (log ∘ f)
      ((f (↑x + ↑t * I))⁻¹ * deriv f (↑x + ↑t * I)) (↑x + ↑t * I) :=
    (hasDerivAt_log hf_slit).comp _ hf_diff.hasDerivAt
  have h_comp := h_logf.scomp x h_path
  refine h_comp.congr_deriv ?_
  simp only [smul_eq_mul, logDeriv_apply, one_mul, inv_mul_eq_div]

/-- **FTC for logDeriv along a horizontal line.**
    If f is differentiable and maps into slitPlane along [a,b]+it, then
    ∫_a^b logDeriv(f)(x+it) dx = log(f(b+it)) - log(f(a+it)). -/
theorem horizontal_logDeriv_integral (f : ℂ → ℂ) (t a b : ℝ)
    (hf_diff : ∀ x ∈ uIcc a b, DifferentiableAt ℂ f (↑x + ↑t * I))
    (hf_slit : ∀ x ∈ uIcc a b, f (↑x + ↑t * I) ∈ slitPlane)
    (hf_cont : ContinuousOn (fun x : ℝ => logDeriv f (↑x + ↑t * I)) (uIcc a b)) :
    ∫ x in a..b, logDeriv f (↑x + ↑t * I) =
      log (f (↑b + ↑t * I)) - log (f (↑a + ↑t * I)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    exact hasDerivAt_log_comp_horizontal f t x (hf_diff x hx) (hf_slit x hx)
  · exact hf_cont.intervalIntegrable

end ZetaZeros.RvMFTC
