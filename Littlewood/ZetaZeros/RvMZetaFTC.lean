/-
Sub-lemma 4 for rvm_N_formula_bound:
FTC on right vertical edge for logDeriv(ζ).

**THIS FILE IS SORRY-FREE.**

Shows that on the right edge σ=2 of the RvM rectangle:
  ∫₁ᵀ i·logDeriv(ζ)(2+iy) dy = log(ζ(2+iT)) - log(ζ(2+i))
and this quantity is O(1) since ‖log ζ(s)‖ ≤ C uniformly on σ=2.

Uses:
- RvMContourFTC.vertical_logDeriv_integral (FTC for logDeriv along vertical lines)
- RvMFormulaProof.zeta_in_slitPlane (ζ(s) ∈ slitPlane for Re(s) ≥ 2)
- ZetaAnalyticProperties.log_zeta_bounded_on_line_two (uniform ‖log ζ‖ bound)

References:
- Titchmarsh, "Theory of the Riemann Zeta-Function", §9.3

Co-authored-by: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
-/

import Littlewood.ZetaZeros.RvMContourFTC
import Littlewood.ZetaZeros.RvMFormulaProof
import Littlewood.Aristotle.ZetaAnalyticProperties

set_option maxHeartbeats 3200000
set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace ZetaZeros.RvMZetaFTC

/-! ## Infrastructure: ζ properties on σ=2 -/

/-- riemannZeta is differentiable at σ+iy for σ > 1. -/
private theorem zeta_diff_at_sigma (σ y : ℝ) (hσ : 1 < σ) :
    DifferentiableAt ℂ riemannZeta ((↑σ : ℂ) + ↑y * I) := by
  apply differentiableAt_riemannZeta
  intro h
  have := congr_arg Complex.re h
  simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im] at this
  linarith

/-- ζ(2+iy) ∈ slitPlane for all y. -/
private theorem zeta_slit_at_two (y : ℝ) :
    riemannZeta ((↑(2 : ℝ) : ℂ) + ↑y * I) ∈ slitPlane := by
  apply RvMFormula.zeta_in_slitPlane
  simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im]

/-- I * logDeriv(ζ)(2+iy) is continuous in y on any interval. -/
private theorem zeta_logDeriv_cont_on_two (a b : ℝ) :
    ContinuousOn (fun y : ℝ => I * logDeriv riemannZeta ((↑(2 : ℝ) : ℂ) + ↑y * I))
      (uIcc a b) := by
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.logDeriv
  · intro y _
    exact (zeta_diff_at_sigma 2 y (by norm_num)).comp_of_eq
      ((continuous_const.add
        (Complex.ofRealCLM.continuous.mul continuous_const)).continuousAt.differentiableAt)
      rfl
  · intro y _
    exact (zeta_slit_at_two y).ne'

/-! ## Main result: FTC + O(1) bound -/

/-- **FTC for logDeriv(ζ) on σ=2.**
    ∫₁ᵀ i·logDeriv(ζ)(2+iy) dy = log(ζ(2+iT)) - log(ζ(2+i)).

    Proof: Apply RvMFTC.vertical_logDeriv_integral with f = riemannZeta, σ = 2.
    Hypotheses verified: ζ differentiable (σ > 1), ζ ∈ slitPlane (|ζ-1| < 1),
    continuity of logDeriv composition. -/
theorem right_edge_zeta_logDeriv_FTC (T : ℝ) :
    ∫ y in (1 : ℝ)..T, I * logDeriv riemannZeta ((↑(2 : ℝ) : ℂ) + ↑y * I) =
      log (riemannZeta ((↑(2 : ℝ) : ℂ) + ↑T * I)) -
        log (riemannZeta ((↑(2 : ℝ) : ℂ) + ↑(1 : ℝ) * I)) :=
  RvMFTC.vertical_logDeriv_integral riemannZeta 2 1 T
    (fun y _ => zeta_diff_at_sigma 2 y (by norm_num))
    (fun y _ => zeta_slit_at_two y)
    (zeta_logDeriv_cont_on_two 1 T)

/-- **O(1) bound on the right-edge ζ-logDeriv integral.**
    ‖∫₁ᵀ i·logDeriv(ζ)(2+iy) dy‖ ≤ 2C where C is the uniform log bound on σ=2.

    Uses log_zeta_bounded_on_line_two from ZetaAnalyticProperties, which
    proves ∃ C, ∀ T, ‖log(ζ(2+iT))‖ ≤ C. -/
theorem right_edge_zeta_logDeriv_norm_bound :
    ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
      ‖∫ y in (1 : ℝ)..T, I * logDeriv riemannZeta ((↑(2 : ℝ) : ℂ) + ↑y * I)‖ ≤ C := by
  -- Get the uniform bound ‖log ζ(2+iT)‖ ≤ B from ZetaAnalyticProperties
  obtain ⟨B, hB⟩ := Aristotle.ZetaAnalyticProperties.log_zeta_bounded_on_line_two
  refine ⟨2 * B, fun T _ => ?_⟩
  -- Apply FTC to evaluate the integral
  rw [right_edge_zeta_logDeriv_FTC T]
  -- Triangle inequality: ‖log ζ(2+iT) - log ζ(2+i)‖ ≤ ‖log ζ(2+iT)‖ + ‖log ζ(2+i)‖ ≤ 2B
  calc ‖log (riemannZeta ((↑(2:ℝ):ℂ) + ↑T * I)) -
        log (riemannZeta ((↑(2:ℝ):ℂ) + ↑(1:ℝ) * I))‖
      ≤ ‖log (riemannZeta ((↑(2:ℝ):ℂ) + ↑T * I))‖ +
        ‖log (riemannZeta ((↑(2:ℝ):ℂ) + ↑(1:ℝ) * I))‖ := norm_sub_le _ _
    _ ≤ B + B := by
        gcongr
        · -- Need to match the convention: (↑(2:ℝ):ℂ) + ↑T * I vs 2 + T * Complex.I
          convert hB T using 2
          push_cast; ring
        · convert hB 1 using 2
          push_cast; ring
    _ = 2 * B := by ring

/-- **Sub-lemma 4: The O(1) bound as an asymptotic.**
    ∫₁ᵀ i·logDeriv(ζ)(2+iy) dy = O(1) as T → ∞.
    This is certainly O(log T), which is the form consumed by rvm_N_formula_bound. -/
theorem right_edge_zeta_logDeriv_is_O_one :
    (fun T => ∫ y in (1 : ℝ)..T, I * logDeriv riemannZeta ((↑(2 : ℝ) : ℂ) + ↑y * I))
    =O[atTop] (fun _ : ℝ => (1 : ℂ)) := by
  obtain ⟨C, hC⟩ := right_edge_zeta_logDeriv_norm_bound
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [norm_one, mul_one]
  exact hC T hT

end ZetaZeros.RvMZetaFTC
