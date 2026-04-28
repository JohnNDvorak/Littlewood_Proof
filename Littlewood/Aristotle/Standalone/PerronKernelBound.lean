/-
# Perron Kernel Truncation Bound

Assembles the Perron kernel truncation bound for y > 1:
  For y > 1, 0 < a ≤ c, T > 0, the difference of vertical contour integrals
  at Re=c and Re=a is bounded by the horizontal segment contributions.

Uses:
- `contour_shift_cpow_div_pos_real` (ContourShift): rectangle Cauchy-Goursat
- `perron_horizontal_segment_bound` (PerronSegmentBound): ‖∫ x^σ/(σ+iT) dσ‖ ≤ x^b·(b-a)/T
- `norm_cpow_real_exponent`, `norm_add_mul_I_ge` (PerronKernelAtomics): pointwise bounds

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.PerronKernelAtomics
import Littlewood.Aristotle.Standalone.ContourShift
import Littlewood.Aristotle.Standalone.PerronSegmentBound

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Complex Real MeasureTheory intervalIntegral Set Filter
open scoped Real

noncomputable section

namespace Aristotle.Standalone.PerronKernelBound

/-! ## Integrand form bridge

The contour shift identity uses `(↑x : ℂ) ^ (↑σ + ↑T * I) / (↑σ + ↑T * I)`,
while `perron_horizontal_segment_bound` uses `(↑(x ^ σ) : ℂ) / (↑σ + ↑T * I)`.
We prove these have the same norm, so bounds transfer.
-/

/-- For `x > 0`, the cpow form `(↑x)^(σ+Ti)` has norm `x^σ`, matching the rpow form. -/
lemma norm_cpow_eq_rpow (x σ T : ℝ) (hx : 0 < x) :
    ‖(x : ℂ) ^ ((σ : ℂ) + (T : ℂ) * I)‖ = x ^ σ :=
  PerronKernelAtomics.norm_cpow_real_exponent x σ T hx

/-- Pointwise bound on the contour-shift integrand: for `x > 0`, `T > 0`,
    `‖x^(σ+iT)/(σ+iT)‖ ≤ x^σ/T`. -/
lemma integrand_pointwise_bound (x σ T : ℝ) (hx : 0 < x) (hT : 0 < T) :
    ‖(x : ℂ) ^ ((σ : ℂ) + (T : ℂ) * I) / ((σ : ℂ) + (T : ℂ) * I)‖ ≤ x ^ σ / T := by
  rw [norm_div, norm_cpow_eq_rpow x σ T hx]
  apply div_le_div_of_nonneg_left (rpow_pos_of_pos hx σ).le hT
  have h := PerronKernelAtomics.norm_add_mul_I_ge σ T
  rwa [abs_of_pos hT] at h

/-- The same bound for negative T (bottom horizontal segment). -/
lemma integrand_pointwise_bound_neg (x σ T : ℝ) (hx : 0 < x) (hT : 0 < T) :
    ‖(x : ℂ) ^ ((σ : ℂ) + ↑(-T) * I) / ((σ : ℂ) + ↑(-T) * I)‖ ≤ x ^ σ / T := by
  rw [norm_div]
  have h_norm : ‖(x : ℂ) ^ ((σ : ℂ) + ↑(-T) * I)‖ = x ^ σ :=
    norm_cpow_eq_rpow x σ (-T) hx
  rw [h_norm]
  apply div_le_div_of_nonneg_left (rpow_pos_of_pos hx σ).le hT
  have h := PerronKernelAtomics.norm_add_mul_I_ge σ (-T)
  rwa [abs_neg, abs_of_pos hT] at h

/-! ## Horizontal segment norm bounds

Bound the horizontal segments from the contour shift using pointwise estimates.
These integrands are in cpow form (matching the contour shift output).
-/

/-- Bound on the top horizontal segment: `‖∫ σ in a..b, x^(σ+iT)/(σ+iT) dσ‖ ≤ x^b·(b-a)/T`.
    Uses pointwise monotonicity of `x^σ` for `x ≥ 1`. -/
theorem horizontal_segment_cpow_bound {x T a b : ℝ} (hx : 1 ≤ x) (hT : 0 < T)
    (hab : a ≤ b) :
    ‖∫ σ in a..b, (x : ℂ) ^ ((σ : ℂ) + (T : ℂ) * I) /
      ((σ : ℂ) + (T : ℂ) * I)‖ ≤ x ^ b * (b - a) / T := by
  have hx_pos : (0 : ℝ) < x := by linarith
  apply le_trans (intervalIntegral.norm_integral_le_of_norm_le_const _)
  · rw [abs_of_nonneg (sub_nonneg.mpr hab), div_mul_eq_mul_div]
  · intro σ hσ
    have hσb : σ ≤ b := by
      cases Set.mem_uIoc.mp hσ with
      | inl h => linarith [h.2]
      | inr h => linarith [h.2]
    calc ‖(x : ℂ) ^ ((σ : ℂ) + (T : ℂ) * I) / ((σ : ℂ) + (T : ℂ) * I)‖
        ≤ x ^ σ / T := integrand_pointwise_bound x σ T hx_pos hT
      _ ≤ x ^ b / T := by
          apply div_le_div_of_nonneg_right _ hT.le
          exact rpow_le_rpow_of_exponent_le hx hσb

/-- Bound on the bottom horizontal segment (negative T direction). -/
theorem horizontal_segment_cpow_bound_neg {x T a b : ℝ} (hx : 1 ≤ x) (hT : 0 < T)
    (hab : a ≤ b) :
    ‖∫ σ in a..b, (x : ℂ) ^ ((σ : ℂ) + ↑(-T) * I) /
      ((σ : ℂ) + ↑(-T) * I)‖ ≤ x ^ b * (b - a) / T := by
  have hx_pos : (0 : ℝ) < x := by linarith
  apply le_trans (intervalIntegral.norm_integral_le_of_norm_le_const _)
  · rw [abs_of_nonneg (sub_nonneg.mpr hab), div_mul_eq_mul_div]
  · intro σ hσ
    have hσb : σ ≤ b := by
      cases Set.mem_uIoc.mp hσ with
      | inl h => linarith [h.2]
      | inr h => linarith [h.2]
    calc ‖(x : ℂ) ^ ((σ : ℂ) + ↑(-T) * I) / ((σ : ℂ) + ↑(-T) * I)‖
        ≤ x ^ σ / T := integrand_pointwise_bound_neg x σ T hx_pos hT
      _ ≤ x ^ b / T := by
          apply div_le_div_of_nonneg_right _ hT.le
          exact rpow_le_rpow_of_exponent_le hx hσb

/-! ## Contour difference bound

The main result: the difference of vertical contour integrals at Re=c and Re=a
is bounded by `2·x^c·(c-a)/T`, using the contour shift identity and horizontal
segment bounds.
-/

/-- **Contour shift identity rearranged.**
For `0 < a ≤ b`, `T > 0`, `x > 0`, the difference of vertical integrals equals
the horizontal segment contributions (from Cauchy-Goursat). -/
theorem vertical_difference_eq_horizontal {a b T x : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hT : 0 < T) (hx : 0 < x) :
    I * (∫ y in (-T)..T, (x : ℂ) ^ ((b : ℂ) + (y : ℂ) * I) / ((b : ℂ) + (y : ℂ) * I)) -
    I * (∫ y in (-T)..T, (x : ℂ) ^ ((a : ℂ) + (y : ℂ) * I) / ((a : ℂ) + (y : ℂ) * I)) =
    (∫ t in a..b, (x : ℂ) ^ ((t : ℂ) + (T : ℂ) * I) / ((t : ℂ) + (T : ℂ) * I)) -
    (∫ t in a..b, (x : ℂ) ^ ((t : ℂ) + ↑(-T) * I) / ((t : ℂ) + ↑(-T) * I)) := by
  have h := contour_shift_cpow_div_pos_real ha hab hT hx
  linear_combination h

/-- **Norm bound on `I * v`**: `‖I * v‖ = ‖v‖`. -/
lemma norm_I_mul (v : ℂ) : ‖I * v‖ = ‖v‖ := by
  rw [norm_mul, Complex.norm_I, one_mul]

/-- **Perron contour difference bound.**
For `x ≥ 1`, `0 < a ≤ c`, `T > 0`, the difference of vertical contour integrals
at `Re = c` and `Re = a` satisfies:
  `‖∫_{-T}^T x^(c+it)/(c+it) dt - ∫_{-T}^T x^(a+it)/(a+it) dt‖ ≤ 2·x^c·(c-a)/T`

This follows from the contour shift identity (Cauchy-Goursat) which expresses
the difference as two horizontal segments, each bounded by `x^c·(c-a)/T`. -/
theorem perron_contour_difference {x a c T : ℝ} (hx : 1 ≤ x)
    (ha : 0 < a) (hac : a ≤ c) (hT : 0 < T) :
    ‖(∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) -
     (∫ t in (-T)..T, (x : ℂ) ^ ((a : ℂ) + (t : ℂ) * I) / ((a : ℂ) + (t : ℂ) * I))‖ ≤
    2 * x ^ c * (c - a) / T := by
  have hx_pos : (0 : ℝ) < x := by linarith
  have h_shift := vertical_difference_eq_horizontal ha hac hT hx_pos
  -- h_shift: I*(∫c) - I*(∫a) = ∫top - ∫bottom
  -- Strategy: bound ‖I*(∫c) - I*(∫a)‖ = ‖∫top - ∫bottom‖ via triangle inequality,
  -- then use ‖I*z‖ = ‖z‖ to relate back to ‖∫c - ∫a‖.
  -- Step 1: ‖∫c - ∫a‖ = ‖I*(∫c - ∫a)‖ = ‖I*∫c - I*∫a‖
  set Ic := ∫ t in (-T)..T,
    (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)
  set Ia := ∫ t in (-T)..T,
    (x : ℂ) ^ ((a : ℂ) + (t : ℂ) * I) / ((a : ℂ) + (t : ℂ) * I)
  set Ht := ∫ t in a..c,
    (x : ℂ) ^ ((t : ℂ) + (T : ℂ) * I) / ((t : ℂ) + (T : ℂ) * I)
  set Hb := ∫ t in a..c,
    (x : ℂ) ^ ((t : ℂ) + ↑(-T) * I) / ((t : ℂ) + ↑(-T) * I)
  -- h_shift : I * Ic - I * Ia = Ht - Hb
  have h1 : ‖Ic - Ia‖ = ‖I * (Ic - Ia)‖ := (norm_I_mul _).symm
  have h2 : I * (Ic - Ia) = I * Ic - I * Ia := mul_sub I Ic Ia
  have h3 : I * Ic - I * Ia = Ht - Hb := h_shift
  rw [h1, h2, h3]
  -- Triangle inequality: ‖top - bottom‖ ≤ ‖top‖ + ‖bottom‖
  calc ‖(∫ t in a..c, (x : ℂ) ^ ((t : ℂ) + (T : ℂ) * I) /
        ((t : ℂ) + (T : ℂ) * I)) -
       (∫ t in a..c, (x : ℂ) ^ ((t : ℂ) + ↑(-T) * I) /
        ((t : ℂ) + ↑(-T) * I))‖
      ≤ ‖∫ t in a..c, (x : ℂ) ^ ((t : ℂ) + (T : ℂ) * I) /
          ((t : ℂ) + (T : ℂ) * I)‖ +
        ‖∫ t in a..c, (x : ℂ) ^ ((t : ℂ) + ↑(-T) * I) /
          ((t : ℂ) + ↑(-T) * I)‖ := norm_sub_le _ _
    _ ≤ x ^ c * (c - a) / T + x ^ c * (c - a) / T := by
        gcongr
        · exact horizontal_segment_cpow_bound hx hT hac
        · exact horizontal_segment_cpow_bound_neg hx hT hac
    _ = 2 * x ^ c * (c - a) / T := by ring

/-! ## Vertical integral norm bound

Direct bound on the vertical integral itself (not just the difference).
For `x > 0`, `c > 0`, `T > 0`:
  `‖∫_{-T}^T x^(c+it)/(c+it) dt‖ ≤ 2T·x^c/c`

This is a crude but useful bound obtained by bounding the integrand pointwise.
-/

/-- **Crude vertical integral bound.**
For `x > 0`, `c > 0`, `T > 0`:
  `‖∫_{-T}^T x^(c+it)/(c+it) dt‖ ≤ 2·T·x^c/c`

Obtained by bounding `|x^(c+it)/(c+it)| ≤ x^c/c` (since `|c+it| ≥ c`). -/
theorem perron_vertical_crude_bound {x c T : ℝ} (hx : 0 < x) (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
      ((c : ℂ) + (t : ℂ) * I)‖ ≤ 2 * T * x ^ c / c := by
  have hbound : ∀ t, t ∈ Set.uIoc (-T) T →
      ‖(x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
        ((c : ℂ) + (t : ℂ) * I)‖ ≤ x ^ c / c := by
    intro t _
    rw [norm_div, norm_cpow_eq_rpow x c t hx]
    apply div_le_div_of_nonneg_left (rpow_pos_of_pos hx c).le hc
    apply Real.le_sqrt_of_sq_le
    rw [Complex.normSq_add_mul_I]
    nlinarith [sq_nonneg t]
  calc ‖∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
        ((c : ℂ) + (t : ℂ) * I)‖
      ≤ x ^ c / c * |T - (-T)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = 2 * T * x ^ c / c := by
        rw [show T - (-T) = 2 * T from by ring, abs_of_nonneg (by linarith)]
        ring

/-! ## Left-edge decay for contour shifting to -∞

For `y > 1`, shifting the contour to `Re = -U` and taking `U → ∞`:
the left-edge integral vanishes, and the horizontal segments contribute O(y^c/T).
This gives the Perron kernel approximation.
-/

/-- **Left-edge integral vanishes for y > 1.**
The integral on `Re = -U` is `O(y^{-U})` which tends to 0 as `U → ∞`.
Uses `PerronKernelAtomics.left_edge_integral_bound` and `left_edge_tendsto_zero`. -/
theorem left_edge_vanishes (y T : ℝ) (hy : 1 < y) (hT : 0 < T) :
    Tendsto (fun U => ‖∫ t in (-T)..T,
      (y : ℂ) ^ (((-U : ℝ) : ℂ) + (t : ℂ) * I) /
        (((-U : ℝ) : ℂ) + (t : ℂ) * I)‖) atTop (nhds 0) := by
  have hy_pos : 0 < y := by linarith
  apply squeeze_zero' (Eventually.of_forall (fun U => norm_nonneg _))
  · -- Eventually, ‖∫ ...‖ ≤ 2*T*y^(-U)/U (for U > 0)
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with U hU
    exact PerronKernelAtomics.left_edge_integral_bound y T U hy_pos hT hU
  · exact PerronKernelAtomics.left_edge_tendsto_zero y T hy hT

/-! ## Perron kernel bound: combined contour estimate

The key bound combining all pieces: for `0 < a ≤ c` and `x ≥ 1`,
the vertical integral at `Re = c` can be related to the one at `Re = a`
with error `2·x^c·(c-a)/T`. As `a → 0⁺`, the integral at `Re = a`
captures the residue at `s = 0` (which gives the "1" in the Perron formula).
-/

/-- **Perron kernel: contour can be moved freely on Re > 0.**
For any `0 < a ≤ c`, `T > 0`, `x ≥ 1`:
  `‖∫ at c - ∫ at a‖ ≤ 2·x^c·(c-a)/T`
This is the main tool for Perron's formula error analysis. -/
theorem perron_kernel_contour_shift_bound {x a c T : ℝ} (hx : 1 ≤ x)
    (ha : 0 < a) (hac : a ≤ c) (hT : 0 < T) :
    ‖(∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)) -
     (∫ t in (-T)..T, (x : ℂ) ^ ((a : ℂ) + (t : ℂ) * I) / ((a : ℂ) + (t : ℂ) * I))‖ ≤
    2 * x ^ c * (c - a) / T :=
  perron_contour_difference hx ha hac hT

end Aristotle.Standalone.PerronKernelBound
