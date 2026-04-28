import Mathlib

open Complex MeasureTheory intervalIntegral Set

/-! # Perron horizontal segment bound

We prove that for `x > 1`, `T > 0`, and `a ≤ b`, the interval integral of
`x ^ σ / (σ + T * I)` over `[a, b]` satisfies
  `‖∫ σ in a..b, ↑(x ^ σ) / (↑σ + ↑T * I)‖ ≤ x ^ b * (b - a) / T`.

The proof uses:
- `|x ^ σ| = x ^ σ` for `x > 0`
- `|σ + T * I| ≥ T` for `T > 0`
- Monotonicity of `x ^ σ` in `σ` for `x ≥ 1`
-/

/-
The norm of `↑σ + ↑T * I` is at least `T` when `T > 0`.
-/
lemma norm_ofReal_add_T_mul_I_ge (σ T : ℝ) (_hT : 0 < T) :
    T ≤ ‖(↑σ + ↑T * I : ℂ)‖ := by
      exact Real.le_sqrt_of_sq_le ( by simpa [ Complex.normSq ] using by nlinarith )

/-
Pointwise bound on the integrand.
-/
lemma integrand_norm_le {x T : ℝ} (hx : 1 ≤ x) (hT : 0 < T) {σ b : ℝ} (hσ : σ ≤ b) :
    ‖(↑(x ^ σ) : ℂ) / (↑σ + ↑T * I)‖ ≤ x ^ b / T := by
      norm_num [ Complex.norm_def, Complex.normSq ];
      gcongr;
      · rw [ abs_of_nonneg ( by positivity ) ] ; exact Real.rpow_le_rpow_of_exponent_le hx hσ;
      · exact Real.le_sqrt_of_sq_le ( by nlinarith )

/-
**Perron horizontal segment bound.**
For `x ≥ 1`, `T > 0`, and `a ≤ b`, the integral of `x^σ / (σ + iT)` over `[a,b]`
is bounded by `x^b * (b - a) / T`.
-/
theorem perron_horizontal_segment_bound {x T a b : ℝ} (hx : 1 ≤ x) (hT : 0 < T)
    (hab : a ≤ b) :
    ‖∫ σ in a..b, (↑(x ^ σ) : ℂ) / (↑σ + ↑T * I)‖ ≤ x ^ b * (b - a) / T := by
      convert intervalIntegral.norm_integral_le_of_norm_le_const _ using 1;
      rotate_left;
      exact x ^ b / T;
      · exact fun y hy => integrand_norm_le hx hT <| by cases Set.mem_uIoc.mp hy <;> linarith;
      · rw [ abs_of_nonneg ( sub_nonneg.mpr hab ), div_mul_eq_mul_div ]