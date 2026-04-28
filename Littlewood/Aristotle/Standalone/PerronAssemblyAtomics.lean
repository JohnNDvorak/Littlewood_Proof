/-
# Perron Assembly Atomics

Norm/bound atoms for the Perron formula assembly: horizontal integrand bounds,
vertical pointwise bounds, and the integration of logDeriv ζ estimates.

These build on:
- `PerronKernelAtomics.norm_cpow_real_exponent`: ‖x^(σ+ti)‖ = x^σ
- `PerronKernelAtomics.norm_add_mul_I_ge`: |T| ≤ ‖σ+Ti‖
- `PerronKernelBound.integrand_pointwise_bound`: ‖x^(σ+iT)/(σ+iT)‖ ≤ x^σ/T

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.PerronKernelAtomics
import Littlewood.Aristotle.Standalone.PerronKernelBound
import Mathlib

set_option maxHeartbeats 400000
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Complex Real MeasureTheory

noncomputable section

namespace PerronAssemblyAtomics

/-! ## 3.9a: Horizontal denominator bound

T ≤ ‖σ + T·I‖ for T > 0.  Re-exports `norm_add_mul_I_ge` with the positivity
hypothesis absorbed. -/

theorem horiz_denom_ge_T (σ T : ℝ) (hT : 0 < T) :
    T ≤ ‖(σ : ℂ) + (T : ℂ) * I‖ := by
  have := PerronKernelAtomics.norm_add_mul_I_ge σ T
  rwa [abs_of_pos hT] at this

/-! ## 3.9b: Horizontal numerator bound

‖x^(σ+ti)‖ ≤ x^c for σ ≤ c, x ≥ 1. -/

theorem horiz_num_le (x σ c t : ℝ) (hx : 1 ≤ x) (hσ : σ ≤ c) :
    ‖(x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ x ^ c := by
  rw [PerronKernelAtomics.norm_cpow_real_exponent x σ t (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hx hσ

/-! ## 3.9c: Horizontal integrand bound (with Hadamard hypothesis)

‖(-ζ'/ζ)(σ+iT) · x^(σ+iT)/(σ+iT)‖ ≤ C·log²T · x^c / T

This combines the logDeriv bound (Hadamard-based, sorry-backed upstream) with
the kernel bound from PerronKernelBound. -/

theorem horiz_integrand_bound (x σ c T C_zeta : ℝ) (hx : 1 ≤ x) (hσ2 : σ ≤ c)
    (hT : 0 < T) (hC : 0 ≤ C_zeta)
    (h_zeta : ‖logDeriv riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖ ≤
              C_zeta * (Real.log T) ^ 2) :
    ‖logDeriv riemannZeta ((σ : ℂ) + (T : ℂ) * I) *
      ((x : ℂ) ^ ((σ : ℂ) + (T : ℂ) * I) / ((σ : ℂ) + (T : ℂ) * I))‖ ≤
    C_zeta * (Real.log T) ^ 2 * x ^ c / T := by
  rw [norm_mul, norm_div]
  have hx_pos : (0 : ℝ) < x := by linarith
  have h_num : ‖(x : ℂ) ^ ((σ : ℂ) + (T : ℂ) * I)‖ ≤ x ^ c := by
    rw [PerronKernelAtomics.norm_cpow_real_exponent x σ T hx_pos]
    exact Real.rpow_le_rpow_of_exponent_le hx hσ2
  have h_denom : T ≤ ‖(σ : ℂ) + (T : ℂ) * I‖ := horiz_denom_ge_T σ T hT
  have h_norm_pos : 0 < ‖(σ : ℂ) + (T : ℂ) * I‖ := lt_of_lt_of_le hT h_denom
  have h_quot : ‖(x : ℂ) ^ ((σ : ℂ) + (T : ℂ) * I)‖ / ‖(σ : ℂ) + (T : ℂ) * I‖ ≤
      x ^ c / T := by
    calc ‖(x : ℂ) ^ ((σ : ℂ) + (T : ℂ) * I)‖ / ‖(σ : ℂ) + (T : ℂ) * I‖
        ≤ x ^ c / ‖(σ : ℂ) + (T : ℂ) * I‖ := by
          apply div_le_div_of_nonneg_right h_num h_norm_pos.le
      _ ≤ x ^ c / T := by
          apply div_le_div_of_nonneg_left (rpow_pos_of_pos hx_pos c).le hT h_denom
  calc ‖logDeriv riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖ *
        (‖(x : ℂ) ^ ((σ : ℂ) + (T : ℂ) * I)‖ / ‖(σ : ℂ) + (T : ℂ) * I‖)
      ≤ (C_zeta * (Real.log T) ^ 2) * (x ^ c / T) := by
        apply mul_le_mul h_zeta h_quot (by positivity) (by positivity)
    _ = C_zeta * (Real.log T) ^ 2 * x ^ c / T := by ring

/-! ## 3.12b: Vertical pointwise norm at σ = 1/2

‖x^(1/2+ti)‖ = x^(1/2) = √x for x > 0. -/

theorem vertical_pointwise_norm_half (x t : ℝ) (hx : 0 < x) :
    ‖(x : ℂ) ^ ((1/2 : ℂ) + (t : ℂ) * I)‖ = x ^ (1/2 : ℝ) := by
  have : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by push_cast; ring
  rw [this]
  exact PerronKernelAtomics.norm_cpow_real_exponent x (1/2 : ℝ) t hx

theorem vertical_pointwise_norm_half_sqrt (x t : ℝ) (hx : 0 < x) :
    ‖(x : ℂ) ^ ((1/2 : ℂ) + (t : ℂ) * I)‖ = Real.sqrt x := by
  rw [vertical_pointwise_norm_half x t hx, Real.sqrt_eq_rpow]

/-! ## 3.11: Triangle inequality for horizontal combined

The sum of top and bottom horizontal segments: ‖top - bottom‖ ≤ ‖top‖ + ‖bottom‖.
This is `norm_sub_le` — we just record the shaped version for documentation. -/

theorem horiz_combined_triangle (top bottom : ℂ) :
    ‖top - bottom‖ ≤ ‖top‖ + ‖bottom‖ := norm_sub_le top bottom

/-! ## General vertical integrand bound

For σ > 0, x > 0: ‖x^(σ+ti)/(σ+ti)‖ ≤ x^σ / |σ|.
When σ is away from 0, the denominator gives a useful lower bound. -/

theorem vertical_integrand_bound_at_sigma (x σ t : ℝ) (hx : 0 < x) (hσ : 0 < σ) :
    ‖(x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I) / ((σ : ℂ) + (t : ℂ) * I)‖ ≤ x ^ σ / σ := by
  rw [norm_div, PerronKernelAtomics.norm_cpow_real_exponent x σ t hx]
  apply div_le_div_of_nonneg_left (rpow_pos_of_pos hx σ).le hσ
  rw [Complex.norm_add_mul_I]
  calc σ = Real.sqrt (σ ^ 2) := by rw [Real.sqrt_sq (le_of_lt hσ)]
    _ ≤ Real.sqrt (σ ^ 2 + t ^ 2) := by
        apply Real.sqrt_le_sqrt; linarith [sq_nonneg t]

/-! ## Monotonicity of horizontal segment bound in x

For x ≥ 1, σ ≤ c: x^σ / T ≤ x^c / T.  Wraps rpow monotonicity for direct use. -/

theorem horiz_bound_mono_exponent (x σ c T : ℝ) (hx : 1 ≤ x) (hσ : σ ≤ c) (hT : 0 < T) :
    x ^ σ / T ≤ x ^ c / T := by
  apply div_le_div_of_nonneg_right _ hT.le
  exact Real.rpow_le_rpow_of_exponent_le hx hσ

/-! ## Norm-I absorption

‖I · z‖ = ‖z‖ — re-export from PerronKernelBound for assembly use. -/

theorem norm_I_mul (v : ℂ) : ‖I * v‖ = ‖v‖ :=
  Aristotle.Standalone.PerronKernelBound.norm_I_mul v

end PerronAssemblyAtomics
