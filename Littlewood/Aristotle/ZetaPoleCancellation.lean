/-
Pole cancellation at s = 1 for the Landau formula.

The Landau formula `s*C/(s-α) + σ*s/(s-1) + σ*ζ'/ζ(s)` has cancelling poles
at s = 1: the simple pole of s/(s-1) cancels with the simple pole of ζ'/ζ(s)
(which has residue -1 at s = 1, from the simple pole of ζ).

This file constructs the "corrected formula" that is analytic at s = 1 by
using the residue function `(s-1)*ζ(s)` with its removable singularity removed.

## Main Results

* `zrf` : The function `(s-1)*ζ(s)` with removable singularity at s=1 removed.
    `zrf(1) = 1` (the residue). Analytic at s = 1.
* `zrf_ne_zero_of_real_pos` : `zrf(↑x) ≠ 0` for real x > 0.
* `corrected_logDeriv_eq` : For s ≠ 1, `1 + zrf'/zrf = s/(s-1) + ζ'/ζ`.
* `landau_formula_analyticAt_real` : The corrected Landau formula is analytic
    at every real point x > α (including x = 1).

SORRY COUNT: 0

REFERENCES:
  - Titchmarsh, "The Theory of the Riemann Zeta-Function", §3.12
  - Montgomery-Vaughan, "Multiplicative Number Theory I", §1.3

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Complex.RemovableSingularity
import Littlewood.Aristotle.ZetaRealNonvanishing

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.ZetaPoleCancellation

open Complex Real Filter Topology Set

/-! ## The residue function (s-1)*ζ(s) -/

/-- The function `(s-1)*ζ(s)` with the removable singularity at s = 1 removed.
At s = 1, the value is 1 (the residue of ζ at its simple pole). -/
def zrf : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1

@[simp] theorem zrf_one : zrf 1 = 1 := Function.update_self 1 1 _

theorem zrf_of_ne {s : ℂ} (hs : s ≠ 1) : zrf s = (s - 1) * riemannZeta s :=
  Function.update_of_ne hs _ _

/-- `zrf` agrees with `(s-1)*ζ(s)` on the punctured plane {s ≠ 1}. -/
private theorem zrf_eventuallyEq_of_ne {z : ℂ} (hz : z ≠ 1) :
    zrf =ᶠ[𝓝 z] (fun s => (s - 1) * riemannZeta s) := by
  filter_upwards [isOpen_ne.mem_nhds hz] with s hs
  exact zrf_of_ne hs

/-- `zrf` is analytic at s = 1 (removable singularity). -/
theorem zrf_analyticAt_one : AnalyticAt ℂ zrf 1 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · -- Differentiable on punctured neighborhood
    filter_upwards [eventually_mem_nhdsWithin] with z hz
    simp only [mem_compl_iff, mem_singleton_iff] at hz
    exact (zrf_eventuallyEq_of_ne hz).differentiableAt_iff.mpr
      ((differentiableAt_id.sub (differentiableAt_const _)).mul
        (differentiableAt_riemannZeta hz))
  · -- Continuous at 1
    exact continuousAt_update_same.mpr riemannZeta_residue_one

/-- `zrf` is analytic at any s ≠ 1. -/
theorem zrf_analyticAt_of_ne {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ zrf s := by
  have h_eq := zrf_eventuallyEq_of_ne hs
  have h_diff : DifferentiableOn ℂ (fun s => (s - 1) * riemannZeta s) {t | t ≠ 1} :=
    fun t ht => ((differentiableAt_id.sub (differentiableAt_const _)).mul
      (differentiableAt_riemannZeta ht)).differentiableWithinAt
  have h_anal := h_diff.analyticOnNhd isOpen_ne
  exact (analyticAt_congr h_eq).mpr (h_anal s hs)

/-- `zrf` is analytic everywhere. -/
theorem zrf_analyticAt (s : ℂ) : AnalyticAt ℂ zrf s := by
  rcases eq_or_ne s 1 with rfl | hs
  · exact zrf_analyticAt_one
  · exact zrf_analyticAt_of_ne hs

/-! ## Nonvanishing of zrf on the real axis -/

/-- `zrf(↑x) ≠ 0` for real x > 0. Uses ζ(x) ≠ 0 for real x > 0. -/
theorem zrf_ne_zero_of_real_pos (x : ℝ) (hx : 0 < x) : zrf (↑x : ℂ) ≠ 0 := by
  by_cases hx1 : x = 1
  · subst hx1; simp
  · rw [zrf_of_ne (by exact_mod_cast hx1)]
    exact mul_ne_zero
      (sub_ne_zero.mpr (by exact_mod_cast hx1))
      (ZetaRealNonvanishing.riemannZeta_ne_zero_of_real_pos x hx)

/-! ## Product rule for zrf -/

/-- The derivative of `(s-1)*ζ(s)` at s ≠ 1 is `ζ(s) + (s-1)*ζ'(s)`. -/
private theorem hasDerivAt_sub_one_mul_zeta {s : ℂ} (hs : s ≠ 1) :
    HasDerivAt (fun s => (s - 1) * riemannZeta s)
      (riemannZeta s + (s - 1) * deriv riemannZeta s) s := by
  have h1 : HasDerivAt (fun s => s - 1) 1 s :=
    hasDerivAt_id s |>.sub_const 1
  have h2 : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs).hasDerivAt
  convert h1.mul h2 using 1; ring

/-- For s ≠ 1, `deriv zrf s = ζ(s) + (s-1)*ζ'(s)`. -/
theorem deriv_zrf_of_ne {s : ℂ} (hs : s ≠ 1) :
    deriv zrf s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
  have h_eq := zrf_eventuallyEq_of_ne hs
  rw [h_eq.deriv_eq]
  exact (hasDerivAt_sub_one_mul_zeta hs).deriv

/-! ## The corrected logarithmic derivative formula -/

/-- For s ≠ 1 with zrf(s) ≠ 0:
`1 + deriv zrf s / zrf s = s / (s - 1) + deriv ζ s / ζ s` -/
theorem corrected_logDeriv_eq {s : ℂ} (hs : s ≠ 1) (hs_zrf : zrf s ≠ 0) :
    1 + deriv zrf s / zrf s =
      s / (s - 1) + deriv riemannZeta s / riemannZeta s := by
  rw [deriv_zrf_of_ne hs, zrf_of_ne hs]
  have h_sub : s - 1 ≠ (0 : ℂ) := sub_ne_zero.mpr hs
  have h_zeta : riemannZeta s ≠ 0 := by
    rw [zrf_of_ne hs] at hs_zrf
    exact (mul_ne_zero_iff.mp hs_zrf).2
  -- Goal: 1 + (ζ(s) + (s-1)*ζ'(s)) / ((s-1)*ζ(s)) = s/(s-1) + ζ'(s)/ζ(s)
  field_simp
  ring

/-! ## Analyticity of the corrected Landau formula -/

/-- The corrected Landau formula: `s*C/(s-α) + σ*(1 + zrf'/zrf)`.
Analytic at all real points x > α > 0, including x = 1. -/
theorem landau_formula_analyticAt_real (α : ℝ) (hα : 1 / 2 < α) (C σ : ℝ)
    (x : ℝ) (hx : α < x) :
    AnalyticAt ℂ (fun s => s * (↑C : ℂ) / (s - (↑α : ℂ)) +
      (↑σ : ℂ) * (1 + deriv zrf s / zrf s)) (↑x : ℂ) := by
  have hx_pos : 0 < x := by linarith
  have hα_pos : 0 < α := by linarith
  -- s*C/(s-α) is analytic at x (since x ≠ α)
  have h_frac : AnalyticAt ℂ (fun s => s * (↑C : ℂ) / (s - (↑α : ℂ))) (↑x : ℂ) := by
    apply AnalyticAt.div
    · exact analyticAt_id.mul analyticAt_const
    · exact analyticAt_id.sub analyticAt_const
    · intro h; have := congr_arg re h; simp at this; linarith
  -- zrf is analytic at x with zrf(x) ≠ 0
  have h_zrf_anal := zrf_analyticAt (↑x : ℂ)
  have h_zrf_ne := zrf_ne_zero_of_real_pos x hx_pos
  -- 1 + zrf'/zrf is analytic at x
  have h_logDeriv : AnalyticAt ℂ (fun s => 1 + deriv zrf s / zrf s) (↑x : ℂ) := by
    exact analyticAt_const.add (h_zrf_anal.deriv.div h_zrf_anal h_zrf_ne)
  -- σ * (1 + zrf'/zrf) is analytic
  have h_right : AnalyticAt ℂ (fun s => (↑σ : ℂ) * (1 + deriv zrf s / zrf s)) (↑x : ℂ) :=
    analyticAt_const.mul h_logDeriv
  exact h_frac.add h_right

/-- The corrected formula equals the original formula on {Re > 1}.
For real σ₀ > 1: `s₀*C/(s₀-α) + σ*(1 + zrf'/zrf) = s₀*C/(s₀-α) + σ*s₀/(s₀-1) + σ*ζ'/ζ`. -/
theorem landau_formula_eq_original (α : ℝ) (C σ₀ : ℝ) (hσ₀ : 1 < σ₀) (σ : ℝ) :
    (↑σ₀ : ℂ) * (↑C : ℂ) / ((↑σ₀ : ℂ) - (↑α : ℂ)) +
      (↑σ : ℂ) * (1 + deriv zrf (↑σ₀ : ℂ) / zrf (↑σ₀ : ℂ)) =
    (↑σ₀ : ℂ) * (↑C : ℂ) / ((↑σ₀ : ℂ) - (↑α : ℂ)) +
      (↑σ : ℂ) * ((↑σ₀ : ℂ) / ((↑σ₀ : ℂ) - 1)) +
      (↑σ : ℂ) * (deriv riemannZeta (↑σ₀ : ℂ) / riemannZeta (↑σ₀ : ℂ)) := by
  have hne : (↑σ₀ : ℂ) ≠ 1 := by
    intro h; have := congr_arg re h; simp at this; linarith
  have h_zrf_ne : zrf (↑σ₀ : ℂ) ≠ 0 := by
    rw [zrf_of_ne hne]
    exact mul_ne_zero (sub_ne_zero.mpr hne)
      (riemannZeta_ne_zero_of_one_le_re (by simp; linarith))
  rw [corrected_logDeriv_eq hne h_zrf_ne]
  ring

end Aristotle.ZetaPoleCancellation
