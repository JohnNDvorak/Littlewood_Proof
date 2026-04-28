/-
# Perron Kernel Truncation Bound

For y > 0, y ≠ 1, c > 0, T > 0:
  ‖(1/2π) ∫_{-T}^{T} y^{c+it}/(c+it) dt - 𝟙(y>1)‖ ≤ y^c / (T · |log y|)

Proof strategy:
  • Case y < 1: Cauchy-Goursat rectangle shift to the right (no pole).
  • Case y > 1: Rectangle residue theorem via sub-rectangle decomposition.

Key tools from Mathlib: `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`,
  `norm_integral_le_of_norm_le_const`.
-/
import Mathlib
import Littlewood.Aristotle.IntegralArctanFormula

set_option maxHeartbeats 800000

open Complex MeasureTheory Set Real intervalIntegral Filter Topology

noncomputable section

namespace PerronKernel

/-! ## Core definitions -/

/-- The truncated Perron integral: `(1/(2π)) ∫_{-T}^{T} y^{c+it}/(c+it) dt`. -/
def perronIntegral (y c T : ℝ) : ℂ :=
  (1 / (2 * ↑Real.pi) : ℂ) • ∫ t in (-T)..T,
    ((y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))

/-- The indicator: 1 if y > 1, 0 if y ≤ 1. -/
def perronIndicator (y : ℝ) : ℝ := if 1 < y then 1 else 0

/-- Move the real part of the Perron kernel inside the interval integral.

This is the exact signed form needed by the boundary-aware Perron cancellation:
the remaining Abel/Stieltjes work should operate on this real kernel rather
than on a false global positivity claim for `perronIntegral y c T`. -/
theorem perronIntegral_re_eq_integral_re_of_intervalIntegrable (y c T : ℝ)
    (hInt : IntervalIntegrable (fun t : ℝ =>
      ((y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I)))
      MeasureTheory.volume (-T) T) :
    (perronIntegral y c T).re =
      (1 / (2 * Real.pi)) *
        ∫ t in (-T)..T,
          (((y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))).re := by
  unfold perronIntegral
  simp only [one_div, smul_eq_mul]
  have hconst : ((2 * (↑Real.pi : ℂ))⁻¹ : ℂ) = (↑((2 * Real.pi)⁻¹) : ℂ) := by
    norm_num
  rw [hconst, Complex.re_ofReal_mul]
  have hcomm := Complex.reCLM.intervalIntegral_comp_comm hInt
  simp only [Complex.reCLM_apply] at hcomm
  rw [← hcomm]

/-- Move the real part of the Perron kernel inside the interval integral.

This is the same signed real-kernel identity as
`perronIntegral_re_eq_integral_re_of_intervalIntegrable`, with the needed
interval integrability discharged from `0 < y` and `0 < c`. -/
theorem perronIntegral_re_eq_integral_re (y c T : ℝ) (hy : 0 < y) (hc : 0 < c) :
    (perronIntegral y c T).re =
      (1 / (2 * Real.pi)) *
        ∫ t in (-T)..T,
          (((y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))).re := by
  apply perronIntegral_re_eq_integral_re_of_intervalIntegrable
  refine Continuous.intervalIntegrable ?_ _ _
  refine Continuous.div ?_ (by continuity) ?_
  · exact Continuous.cpow continuous_const (by continuity) (fun _ => Or.inl (by positivity))
  · intro t hzero
    have hc0 : c = 0 := by
      simpa using congrArg Complex.re hzero
    exact hc.ne' hc0

/-- Explicit real part of the Perron kernel integrand.

This is the signed oscillatory kernel needed for Abel/Stieltjes cancellation:
after moving `.re` through the truncated Perron integral, the integrand is a
real multiple of `c cos(t log y) + t sin(t log y)`. -/
theorem perronIntegrand_re_eq (y c t : ℝ) (hy : 0 < y) :
    (((y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) / ((c : ℂ) + (t : ℂ) * I))).re =
      y ^ c * (c * Real.cos (t * Real.log y) + t * Real.sin (t * Real.log y)) /
        (c ^ 2 + t ^ 2) := by
  have hy_ne : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have h_cpow :
      (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) =
        Complex.exp (Complex.log (y : ℂ) * ((c : ℂ) + (t : ℂ) * I)) :=
    Complex.cpow_def_of_ne_zero hy_ne _
  rw [h_cpow]
  have h_log : Complex.log (y : ℂ) = ((Real.log y) : ℂ) := by
    exact (Complex.ofReal_log hy.le).symm
  rw [h_log]
  set L := Real.log y
  have h_exp_arg :
      (↑L : ℂ) * ((↑c : ℂ) + (↑t : ℂ) * I) =
        ↑(c * L) + ↑(t * L) * I := by
    push_cast
    ring
  rw [h_exp_arg, Complex.exp_add_mul_I]
  have htL : ((↑t : ℂ) * ↑L) = (↑(t * L) : ℂ) := by
    push_cast
    ring
  have h_exp_rpow : Real.exp (c * L) = y ^ c := by
    rw [Real.rpow_def_of_pos hy]
    simp [L, mul_comm]
  rw [← Complex.ofReal_exp (c * L), h_exp_rpow]
  simp [Complex.div_re, Complex.normSq]
  have hcos_re : (Complex.cos ((↑t : ℂ) * ↑L)).re = Real.cos (t * L) := by
    rw [htL]
    exact Complex.cos_ofReal_re (t * L)
  have hcos_im : (Complex.cos ((↑t : ℂ) * ↑L)).im = 0 := by
    rw [htL]
    exact Complex.cos_ofReal_im (t * L)
  have hsin_re : (Complex.sin ((↑t : ℂ) * ↑L)).re = Real.sin (t * L) := by
    rw [htL]
    exact Complex.sin_ofReal_re (t * L)
  have hsin_im : (Complex.sin ((↑t : ℂ) * ↑L)).im = 0 := by
    rw [htL]
    exact Complex.sin_ofReal_im (t * L)
  rw [hcos_re, hcos_im, hsin_re, hsin_im]
  ring_nf

/-- Real-integral form of the truncated Perron kernel.

This combines `perronIntegral_re_eq_integral_re` with the explicit real-part
formula `perronIntegrand_re_eq`.  It is the preferred starting point for the
remaining signed Abel/Stieltjes cancellation, because it exposes the real
oscillatory kernel directly. -/
theorem perronIntegral_re_eq_real_kernel_integral (y c T : ℝ)
    (hy : 0 < y) (hc : 0 < c) :
    (perronIntegral y c T).re =
      (1 / (2 * Real.pi)) *
        ∫ t in (-T)..T,
          y ^ c * (c * Real.cos (t * Real.log y) + t * Real.sin (t * Real.log y)) /
            (c ^ 2 + t ^ 2) := by
  rw [perronIntegral_re_eq_integral_re y c T hy hc]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _ht
  exact perronIntegrand_re_eq y c t hy

/- At the boundary value `y = 1`, the Perron kernel is the average of
`1 / (c + it)`, whose real part is nonnegative on the symmetric interval. -/
theorem perronIntegral_one_re_nonneg (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    0 ≤ (perronIntegral 1 c T).re := by
  unfold perronIntegral
  simp only [one_div, smul_eq_mul]
  have hcpow : ∀ t : ℝ, (↑(1 : ℝ) : ℂ) ^ ((↑c : ℂ) + ↑t * I) = 1 := by
    intro t
    simp
  simp_rw [hcpow]
  rw [show ((2 * (↑Real.pi : ℂ))⁻¹ : ℂ) = (↑((2 * Real.pi)⁻¹) : ℂ) by norm_num]
  rw [Complex.re_ofReal_mul]
  apply mul_nonneg
  · positivity
  · let f : ℝ → ℂ := fun t => 1 / ((↑c : ℂ) + ↑t * I)
    have hfcont : Continuous f := by
      dsimp [f]
      exact continuous_const.div (by continuity) (by
        intro x
        norm_num [Complex.ext_iff]
        intro hc0
        exact (hc.ne' hc0).elim)
    have hfint : IntervalIntegrable f MeasureTheory.volume (-T) T := by
      exact hfcont.intervalIntegrable _ _
    have hcomm := Complex.reCLM.intervalIntegral_comp_comm hfint
    simp only [Complex.reCLM_apply] at hcomm
    change 0 ≤ (∫ t in (-T)..T, f t).re
    rw [← hcomm]
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    have hdenpos : 0 < c * c + t * t := by
      nlinarith [sq_pos_of_pos hc, sq_nonneg t]
    have hnonneg : 0 ≤ c / (c * c + t * t) := div_nonneg hc.le hdenpos.le
    simpa [f, one_div, Complex.inv_re, Complex.normSq] using hnonneg

/-- Exact value of the real part of the truncated Perron kernel at the jump. -/
theorem perronIntegral_one_re_eq_arctan (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    (perronIntegral 1 c T).re = Real.arctan (T / c) / Real.pi := by
  unfold perronIntegral
  simp only [one_div, smul_eq_mul]
  have hcpow : ∀ t : ℝ, (↑(1 : ℝ) : ℂ) ^ ((↑c : ℂ) + ↑t * I) = 1 := by
    intro t
    simp
  simp_rw [hcpow]
  rw [show ((2 * (↑Real.pi : ℂ))⁻¹ : ℂ) = (↑((2 * Real.pi)⁻¹) : ℂ) by norm_num]
  rw [Complex.re_ofReal_mul]
  let f : ℝ → ℂ := fun t => 1 / ((↑c : ℂ) + ↑t * I)
  have hfcont : Continuous f := by
    dsimp [f]
    exact continuous_const.div (by continuity) (by
      intro x
      norm_num [Complex.ext_iff]
      intro hc0
      exact (hc.ne' hc0).elim)
  have hfint : IntervalIntegrable f MeasureTheory.volume (-T) T := by
    exact hfcont.intervalIntegrable _ _
  have hcomm := Complex.reCLM.intervalIntegral_comp_comm hfint
  simp only [Complex.reCLM_apply] at hcomm
  change (2 * Real.pi)⁻¹ * (∫ x in (-T)..T, f x).re = Real.arctan (T / c) / Real.pi
  rw [← hcomm]
  have harctan := integral_real_part_arctan c hc T hT
  calc
    (2 * Real.pi)⁻¹ * (∫ x in (-T)..T, (1 / ((↑c : ℂ) + ↑x * I)).re)
        = (2 * Real.pi)⁻¹ * (2 * Real.arctan (T / c)) := by rw [harctan]
    _ = Real.arctan (T / c) / Real.pi := by
        field_simp [Real.pi_ne_zero]

/-- At `y = 1`, the truncated Perron kernel real part is at most `1`. -/
theorem perronIntegral_one_re_le_one (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    (perronIntegral 1 c T).re ≤ 1 := by
  rw [perronIntegral_one_re_eq_arctan c T hc hT]
  have hlt : Real.arctan (T / c) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [div_le_iff₀ hpi]
  linarith

/-- At `y = 1`, the strict indicator is `0`, so the boundary kernel error
`indicator - K_T(1).re` is nonpositive. -/
theorem perronIndicator_one_sub_perronIntegral_re_nonpos
    (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    perronIndicator 1 - (perronIntegral 1 c T).re ≤ 0 := by
  simpa [perronIndicator] using
    (neg_nonpos.mpr (perronIntegral_one_re_nonneg c T hc hT))

/-- At `y = 1`, the strict indicator is `0`, and the kernel real part is at
most `1`, so the signed boundary loss is at worst `-1`. -/
theorem neg_one_le_perronIndicator_one_sub_perronIntegral_re
    (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    -(1 : ℝ) ≤ perronIndicator 1 - (perronIntegral 1 c T).re := by
  simpa [perronIndicator] using
    (neg_le_neg (perronIntegral_one_re_le_one c T hc hT))

/-- At `y = 1`, the strict-indicator Perron kernel error has absolute value
at most `1`. -/
theorem abs_perronIndicator_one_sub_perronIntegral_re_le_one
    (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    |perronIndicator 1 - (perronIntegral 1 c T).re| ≤ 1 := by
  exact abs_le.mpr
    ⟨neg_one_le_perronIndicator_one_sub_perronIntegral_re c T hc hT,
      (perronIndicator_one_sub_perronIntegral_re_nonpos c T hc hT).trans zero_le_one⟩

/-! ## Auxiliary lemmas -/

/-
`exp(-x) ≤ 1/x` for `x > 0`, equivalently `y^T ≤ 1/(T * |log y|)` for `0 < y < 1`.
-/
lemma exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  rw [ Real.exp_neg ];
  rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> linarith [ Real.add_one_le_exp x ]

/-
For `0 < y < 1`, `y ^ t ≤ 1 / (t * |log y|)` when `t > 0`.
-/
lemma rpow_le_inv_mul_abs_log {y t : ℝ} (hy : 0 < y) (hy1 : y < 1) (ht : 0 < t) :
    y ^ t ≤ 1 / (t * |Real.log y|) := by
  -- Write $y^t = \exp(t \log y)$
  have hyt_exp : y ^ t = Real.exp (t * Real.log y) := by
    rw [ Real.rpow_def_of_pos hy, mul_comm ];
  have := exp_neg_le_inv ( show 0 < t * |Real.log y| by exact mul_pos ht ( abs_pos.mpr ( ne_of_lt ( Real.log_neg hy hy1 ) ) ) );
  exact hyt_exp ▸ le_trans ( Real.exp_le_exp.mpr ( by cases abs_cases ( Real.log y ) <;> nlinarith [ Real.log_le_sub_one_of_pos hy ] ) ) this

/-
Norm of `y^(x + it) / (x + it)` is `y^x / |x + it|` for real `y > 0`.
-/
lemma norm_cpow_div {y x t : ℝ} (hy : 0 < y) :
    ‖(y : ℂ) ^ ((x : ℂ) + (t : ℂ) * I) / ((x : ℂ) + (t : ℂ) * I)‖ =
      y ^ x / ‖(x : ℂ) + (t : ℂ) * I‖ := by
  norm_num [ Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hy ]

/-
`|x + it| ≥ |t|` for real `x`, `t`.
-/
lemma norm_add_mul_I_ge_abs_right (x t : ℝ) :
    |t| ≤ ‖(x : ℂ) + (t : ℂ) * I‖ := by
  exact Real.abs_le_sqrt ( by norm_num [ Complex.normSq ] ; nlinarith )

/-
`|x + it| ≥ |x|` for real `x`, `t`.
-/
lemma norm_add_mul_I_ge_abs_left (x t : ℝ) :
    |x| ≤ ‖(x : ℂ) + (t : ℂ) * I‖ := by
  exact Real.abs_le_sqrt ( by norm_num [ Complex.normSq ] ; nlinarith )

/-
Integral of `y^x` over `[a, b]` for `y > 0`, `y ≠ 1`.
-/
lemma integral_rpow_eq {y a b : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) :
    ∫ x in a..b, y ^ x = (y ^ b - y ^ a) / Real.log y := by
  by_cases hy' : Real.log y = 0 <;> simp_all +decide [ div_eq_inv_mul, Real.rpow_def_of_pos, intervalIntegral.integral_comp_mul_left ]
  rcases hy' with rfl | rfl <;> linarith

/-
Bound on `∫_a^b y^x dx` for `0 < y < 1`: bounded by `y^a / |log y|`.
-/
lemma integral_rpow_le_div_abs_log {y a b : ℝ} (hy : 0 < y) (hy1 : y < 1)
    (hab : a ≤ b) :
    ‖∫ x in a..b, y ^ x‖ ≤ y ^ a / |Real.log y| := by
  rw [ intervalIntegral.integral_congr fun x hx => by rw [ Real.rpow_def_of_pos hy ] ];
  rw [ intervalIntegral.integral_comp_mul_left ] <;> norm_num;
  · rw [ Real.rpow_def_of_pos hy ] ; ring_nf;
    exact mul_le_mul_of_nonneg_left ( by cases abs_cases ( Real.exp ( Real.log y * b ) - Real.exp ( Real.log y * a ) ) <;> cases abs_cases ( Real.log y ) <;> nlinarith [ Real.exp_pos ( Real.log y * b ), Real.exp_pos ( Real.log y * a ), Real.exp_le_exp.mpr ( mul_le_mul_of_nonpos_left hab ( Real.log_nonpos hy.le hy1.le ) ) ] ) ( by positivity );
  · exact ⟨ hy.ne', hy1.ne, by linarith ⟩

/-! ## Case y < 1: Contour shift to the right -/

/-
**Perron bound for y < 1**.
    Uses Cauchy-Goursat with a rectangle shifted right.
    The function `y^s / s` is holomorphic in `[c, R] × [-T, T]` (since `c > 0`),
    so the boundary integral vanishes, giving
      `∫ vertical_left = horizontal + vertical_right`.
    Each piece is bounded to get `≤ y^c / (T |log y|)`.
-/
theorem perron_bound_lt_one (y c T : ℝ) (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    ‖perronIntegral y c T‖ ≤ y ^ c / (T * |Real.log y|) := by
  -- Apply Cauchy-Goursat `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` to `f(s) = y^s / s` on the rectangle with corners `z = c - iT` and `w = (c+T) + iT`.
  have h_cauchy : (∫ x in c..(c + T), y ^ (x - T * I) / (x - T * I)) - (∫ x in c..(c + T), y ^ (x + T * I) / (x + T * I)) + Complex.I * (∫ t in (-T)..T, y ^ (c + T + t * Complex.I) / (c + T + t * Complex.I)) - Complex.I * (∫ t in (-T)..T, y ^ (c + t * Complex.I) / (c + t * Complex.I)) = 0 := by
    have h_cauchy : ∀ z w : ℂ, z.re > 0 → w.re > 0 → DifferentiableOn ℂ (fun s : ℂ => y ^ s / s) (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
      intro z w hz hw; refine' DifferentiableOn.div _ _ _ ;
      · refine' DifferentiableOn.cpow _ _ _ <;> norm_num;
        · exact differentiableOn_id;
        · exact fun x hx => Or.inl <| by simpa using hy;
      · exact differentiableOn_id;
      · norm_num [ Complex.ext_iff ];
        intro x hx hx'; cases Set.mem_uIcc.mp hx.1 <;> linarith;
    have := @Complex.integral_boundary_rect_eq_zero_of_differentiableOn;
    convert this ( fun s => ( y : ℂ ) ^ s / s ) ( c - T * I ) ( c + T + T * I ) ( h_cauchy ( c - T * I ) ( c + T + T * I ) ( by simpa using hc ) ( by simpa using by linarith ) ) using 1 ; norm_num;
    rfl;
  -- Rearrange the Cauchy-Goursat identity to isolate the integral over the vertical line.
  have h_isolate : ∫ t in (-T)..T, y ^ (c + t * Complex.I) / (c + t * Complex.I) = (1 / Complex.I) * ((∫ x in c..(c + T), y ^ (x - T * I) / (x - T * I)) - (∫ x in c..(c + T), y ^ (x + T * I) / (x + T * I))) + (∫ t in (-T)..T, y ^ (c + T + t * Complex.I) / (c + T + t * Complex.I)) := by
    norm_num [ Complex.ext_iff ] at * ; constructor <;> linarith;
  -- Bound each component by `y^c / (T |log y|)` and use `4/(2π) < 1`.
  have h_bound : ‖∫ t in (-T)..T, y ^ (c + t * Complex.I) / (c + t * Complex.I)‖ ≤ 4 * y ^ c / (T * |Real.log y|) := by
    -- Bound the horizontal integrals.
    have h_horizontal : ‖∫ x in c..(c + T), y ^ (x - T * Complex.I) / (x - T * Complex.I)‖ ≤ y ^ c / (T * |Real.log y|) ∧ ‖∫ x in c..(c + T), y ^ (x + T * Complex.I) / (x + T * Complex.I)‖ ≤ y ^ c / (T * |Real.log y|) := by
      have h_horizontal_bound : ∀ (x : ℝ), c ≤ x → x ≤ c + T → ‖y ^ (x - T * Complex.I) / (x - T * Complex.I)‖ ≤ y ^ x / T ∧ ‖y ^ (x + T * Complex.I) / (x + T * Complex.I)‖ ≤ y ^ x / T := by
        intros x hx_left hx_right
        have h_norm : ‖(y : ℂ) ^ ((x : ℂ) - (T : ℂ) * I)‖ = y ^ x ∧ ‖(y : ℂ) ^ ((x : ℂ) + (T : ℂ) * I)‖ = y ^ x := by
          norm_num [ Complex.norm_cpow_eq_rpow_re_of_pos hy ];
        simp_all +decide [ Complex.norm_def, Complex.normSq ];
        gcongr ; nlinarith [ Real.sqrt_nonneg ( x * x + T * T ), Real.mul_self_sqrt ( by nlinarith : 0 ≤ x * x + T * T ) ];
      have h_horizontal_bound : ‖∫ x in c..(c + T), y ^ (x - T * Complex.I) / (x - T * Complex.I)‖ ≤ ∫ x in c..(c + T), y ^ x / T ∧ ‖∫ x in c..(c + T), y ^ (x + T * Complex.I) / (x + T * Complex.I)‖ ≤ ∫ x in c..(c + T), y ^ x / T := by
        constructor <;> rw [ intervalIntegral.integral_of_le ( by linarith ), intervalIntegral.integral_of_le ( by linarith ) ];
        · refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( MeasureTheory.integral_mono_of_nonneg _ _ _ );
          · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
          · exact Continuous.integrableOn_Ioc ( by exact Continuous.div_const ( by exact Continuous.rpow continuous_const continuous_id' <| by continuity ) _ );
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using h_horizontal_bound x hx.1.le hx.2 |>.1;
        · refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( MeasureTheory.integral_mono_of_nonneg _ _ _ );
          · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
          · exact Continuous.integrableOn_Ioc ( by exact Continuous.div_const ( by exact Continuous.rpow continuous_const continuous_id' <| by continuity ) _ );
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using h_horizontal_bound x hx.1.le hx.2 |>.2;
      have h_integral_bound : ∫ x in c..(c + T), y ^ x / T ≤ y ^ c / (T * |Real.log y|) := by
        norm_num [ Real.rpow_def_of_pos hy ];
        rw [ intervalIntegral.integral_comp_mul_left ] <;> norm_num [ Real.exp_ne_zero, hy.ne', hy1.ne', hc.ne', hT.ne' ];
        · rw [ abs_of_neg ( Real.log_neg hy hy1 ) ] ; ring_nf;
          nlinarith [ show ( Real.log y ) ⁻¹ * T⁻¹ < 0 by exact mul_neg_of_neg_of_pos ( inv_lt_zero.mpr ( Real.log_neg hy hy1 ) ) ( inv_pos.mpr hT ), Real.exp_pos ( Real.log y * c + Real.log y * T ), Real.exp_pos ( Real.log y * c ), Real.exp_le_exp.mpr ( show Real.log y * c + Real.log y * T ≤ Real.log y * c by nlinarith [ Real.log_le_sub_one_of_pos hy ] ) ];
        · exact ⟨ by linarith, by linarith ⟩;
      exact ⟨ h_horizontal_bound.1.trans h_integral_bound, h_horizontal_bound.2.trans h_integral_bound ⟩;
    -- Bound the vertical integral.
    have h_vertical : ‖∫ t in (-T)..T, y ^ (c + T + t * Complex.I) / (c + T + t * Complex.I)‖ ≤ 2 * y ^ c / (T * |Real.log y|) := by
      -- Apply the bound on the vertical integral.
      have h_vertical_bound : ∀ t ∈ Set.Icc (-T) T, ‖y ^ (c + T + t * Complex.I) / (c + T + t * Complex.I)‖ ≤ y ^ (c + T) / T := by
        intros t ht
        have h_norm : ‖(y : ℂ) ^ ((c + T : ℂ) + (t : ℂ) * I)‖ = y ^ (c + T) := by
          rw [ Complex.norm_cpow_eq_rpow_re_of_pos ] <;> norm_num [ hy ];
        simp_all +decide [ Complex.norm_def, Complex.normSq ];
        gcongr ; nlinarith [ Real.sqrt_nonneg ( ( c + T ) * ( c + T ) + t * t ), Real.mul_self_sqrt ( by nlinarith : 0 ≤ ( c + T ) * ( c + T ) + t * t ) ];
      -- Apply the bound on the vertical integral to get the final result.
      have h_vertical_final : ‖∫ t in (-T)..T, y ^ (c + T + t * Complex.I) / (c + T + t * Complex.I)‖ ≤ (2 * T) * (y ^ (c + T) / T) := by
        refine' le_trans ( intervalIntegral.norm_integral_le_of_norm_le_const _ ) _;
        exact y ^ ( c + T ) / T;
        · exact fun x hx => h_vertical_bound x <| by constructor <;> cases Set.mem_uIoc.mp hx <;> linarith;
        · rw [ abs_of_nonneg ] <;> linarith;
      -- Apply the bound on $y^{c+T}$.
      have h_y_bound : y ^ (c + T) ≤ y ^ c / (T * |Real.log y|) := by
        have h_y_bound : y ^ T ≤ 1 / (T * |Real.log y|) := by
          convert rpow_le_inv_mul_abs_log hy hy1 hT using 1;
        rw [ Real.rpow_add hy ] ; convert mul_le_mul_of_nonneg_left h_y_bound ( Real.rpow_nonneg hy.le c ) using 1 ; ring;
      refine le_trans h_vertical_final ?_;
      convert mul_le_mul_of_nonneg_left h_y_bound ( show 0 ≤ 2 by norm_num ) using 1 ; ring;
      · norm_num [ mul_comm T, hT.ne' ];
      · ring;
    rw [ h_isolate ];
    refine' le_trans ( norm_add_le _ _ ) _;
    norm_num [ div_eq_mul_inv ] at *;
    exact le_trans ( add_le_add ( norm_sub_le _ _ ) le_rfl ) ( by linarith );
  unfold perronIntegral; norm_num [ h_bound ] ; ring_nf; norm_num [ Real.pi_pos.ne' ] ;
  rw [ abs_of_nonneg Real.pi_pos.le ] ; ring_nf at * ; norm_num at *;
  norm_num [ mul_comm ] at * ; nlinarith [ Real.pi_gt_three, mul_inv_cancel₀ Real.pi_ne_zero, show 0 ≤ y ^ c * T⁻¹ * |Real.log y|⁻¹ by positivity ] ;

/-! ## Case y > 1: Contour shift to the left with residue -/

/-
Each side integral of `1/s` around the square `[-δ,δ]²` contributes `iπ/2`.
    Bottom: `∫_{-δ}^δ 1/(x - δI) dx = iπ/2`.
-/
lemma square_integral_inv_bottom (δ : ℝ) (hδ : 0 < δ) :
    ∫ x in (-δ)..δ, ((x : ℂ) + (-δ : ℝ) * I)⁻¹ = ↑(Real.pi / 2) * I := by
  erw [ intervalIntegral.integral_of_le ];
  · -- The integral of $1/(x - δi)$ over $[-δ, δ]$ can be computed using the fundamental theorem of calculus.
    have h_ftc : ∀ a b : ℝ, ∫ x in a..b, (x - δ * Complex.I)⁻¹ = Complex.log (b - δ * Complex.I) - Complex.log (a - δ * Complex.I) := by
      intros a b; rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
      · intro x hx; convert HasDerivAt.comp x ( Complex.hasDerivAt_log _ ) ( HasDerivAt.sub ( hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) ( hasDerivAt_const _ _ ) ) using 1 <;> norm_num [ Complex.ext_iff, hδ.ne' ] ;
        norm_num [ Complex.ext_iff, slitPlane ] ; aesop;
      · exact Continuous.intervalIntegrable ( by exact Continuous.inv₀ ( by continuity ) fun x => by norm_num [ Complex.ext_iff ] ; intros; nlinarith ) _ _;
    convert h_ftc ( -δ ) δ using 1 <;> norm_num [ ← intervalIntegral.integral_of_le, hδ.le ];
    · rfl;
    · norm_num [ Complex.log, Complex.arg ];
      norm_num [ Complex.normSq, Complex.norm_def, hδ.le ];
      split_ifs <;> ring_nf <;> norm_num [ hδ.le, hδ.ne' ];
      · linarith;
      · norm_num [ mul_assoc, mul_comm, mul_left_comm, hδ.ne' ] ; ring;
        rw [ show ( Real.sqrt 2 ) ⁻¹ = Real.sin ( Real.pi / 4 ) by norm_num [ Real.sqrt_div_self ], Real.arcsin_sin ] <;> norm_num <;> ring <;> linarith [ Real.pi_pos ];
  · linarith

/-
Top: `∫_{-δ}^δ 1/(x + δI) dx = -iπ/2`.
-/
lemma square_integral_inv_top (δ : ℝ) (hδ : 0 < δ) :
    ∫ x in (-δ)..δ, ((x : ℂ) + (δ : ℝ) * I)⁻¹ = -↑(Real.pi / 2) * I := by
  -- The integral of $\frac{1}{x + \delta i}$ over $[-\delta, \delta]$ is equal to the integral of $\frac{1}{x - \delta i}$ over $[-\delta, \delta]$ because they are complex conjugates.
  have h_conj : ∫ x in (-δ)..δ, (x + δ * I)⁻¹ = starRingEnd ℂ (∫ x in (-δ)..δ, (x - δ * I)⁻¹) := by
    convert intervalIntegral.integral_congr fun x _ => ?_ using 2 ; ring;
    rotate_left;
    exact fun x => ( x - δ * I ) ⁻¹ |> starRingEnd ℂ;
    · norm_num [ Complex.normSq, Complex.ext_iff ];
    · rw [ intervalIntegral.integral_of_le ( by linarith ), intervalIntegral.integral_of_le ( by linarith ) ];
      rw [ ← integral_conj ];
  have := @square_integral_inv_bottom δ hδ; simp_all +decide [ div_eq_mul_inv, Complex.ext_iff ] ;
  tauto

/-
Right: `∫_{-δ}^δ 1/(δ + yI) dy = π/2`.
-/
lemma square_integral_inv_right (δ : ℝ) (hδ : 0 < δ) :
    ∫ y in (-δ)..δ, ((δ : ℂ) + (y : ℝ) * I)⁻¹ = ↑(Real.pi / 2) := by
  rw [ intervalIntegral.integral_deriv_eq_sub' ];
  case f => exact fun y => ( Complex.log ( δ + y * Complex.I ) ) / Complex.I;
  · norm_num [ Complex.log, Complex.ext_iff ];
    norm_num [ Complex.normSq, Complex.norm_def, Complex.arg ];
    ring_nf; norm_num [ hδ.le, hδ.ne' ];
    norm_num [ mul_left_comm δ, hδ.ne' ];
    rw [ show ( Real.sqrt 2 ) ⁻¹ = Real.sin ( Real.pi / 4 ) by norm_num [ Real.sqrt_div_self ], Real.arcsin_sin ] <;> linarith [ Real.pi_pos ];
  · ext y; norm_num [ Complex.ext_iff, Complex.log_re, Complex.log_im ];
    erw [ HasDerivAt.deriv ( HasDerivAt.comp y ( Complex.hasDerivAt_log _ ) ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) <| hasDerivAt_const _ _ ) ) ) ] <;> norm_num [ Complex.normSq, Complex.div_re, Complex.div_im, hδ.ne' ];
    exact Or.inl <| by norm_num; positivity;
  · intro x hx;
    refine' DifferentiableAt.div_const _ _;
    convert HasDerivAt.differentiableAt ( HasDerivAt.comp x ( Complex.hasDerivAt_log _ ) ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) ( hasDerivAt_const _ _ ) ) ) ) using 1 ; norm_num;
    exact Or.inl ( by norm_num; linarith );
  · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.inv₀ ( continuousAt_const.add ( continuousAt_id.smul continuousAt_const ) ) ( by norm_num [ Complex.ext_iff, hδ.ne' ] )

/-
Left: `∫_{-δ}^δ 1/(-δ + yI) dy = -π/2`.
-/
lemma square_integral_inv_left (δ : ℝ) (hδ : 0 < δ) :
    ∫ y in (-δ)..δ, ((-δ : ℂ) + (y : ℝ) * I)⁻¹ = -↑(Real.pi / 2) := by
  convert congr_arg ( fun x : ℂ => -x ) ( square_integral_inv_right δ hδ ) using 1;
  rw [ ← intervalIntegral.integral_neg ] ; convert intervalIntegral.integral_comp_neg _ using 3 <;> norm_num;
  rw [ ← inv_neg ] ; ring

/-- **Boundary integral of `1/s` around the square `[-δ,δ]²` equals `2πi`**.
    This is proved by direct computation of each side using `arctan`. -/
lemma boundary_integral_inv_eq_two_pi_I (δ : ℝ) (hδ : 0 < δ) :
    (∫ x in (-δ)..δ, ((x : ℂ) + (-δ : ℝ) * I)⁻¹) -
    (∫ x in (-δ)..δ, ((x : ℂ) + (δ : ℝ) * I)⁻¹) +
    I • (∫ y in (-δ)..δ, ((δ : ℂ) + (y : ℝ) * I)⁻¹) -
    I • (∫ y in (-δ)..δ, ((-δ : ℂ) + (y : ℝ) * I)⁻¹) = 2 * ↑Real.pi * I := by
  rw [square_integral_inv_bottom δ hδ, square_integral_inv_top δ hδ,
      square_integral_inv_right δ hδ, square_integral_inv_left δ hδ]
  simp only [smul_eq_mul]
  push_cast
  ring

/-
The function `(y^s - 1)/s` (extended by `log y` at `s = 0`) is differentiable on `ℂ`.
-/
lemma diffOn_cpow_sub_one_div (y : ℝ) (hy : 0 < y) :
    DifferentiableOn ℂ (fun s : ℂ => if s = 0 then (↑(Real.log y) : ℂ)
      else ((y : ℂ) ^ s - 1) / s) Set.univ := by
  -- To prove differentiability everywhere, we need to show that the function is differentiable at `s = 0` and for `s ≠ 0`.
  have h_diff : DifferentiableAt ℂ (fun s : ℂ => if s = 0 then (Real.log y : ℂ) else (y ^ s - 1) / s) 0 := by
    refine' ⟨ _, hasDerivAt_iff_tendsto_slope_zero.mpr _ ⟩;
    exact ( Real.log y ) ^ 2 / 2;
    -- We'll use the fact that $y^t = e^{t \log y}$ and the series expansion of the exponential function.
    have h_exp : Filter.Tendsto (fun t : ℂ => (Complex.exp (t * Complex.log y) - 1 - t * Complex.log y) / t^2) (nhdsWithin 0 {0}ᶜ) (nhds ((Complex.log y)^2 / 2)) := by
      -- We'll use the fact that $e^{z} = \sum_{n=0}^{\infty} \frac{z^n}{n!}$ to expand $e^{t \ln y}$.
      have h_expansion : ∀ t : ℂ, Complex.exp (t * Complex.log y) = ∑' n : ℕ, (t * Complex.log y)^n / Nat.factorial n := by
        norm_num [ Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div ];
      -- Substitute the expansion into the expression.
      have h_subst : ∀ t : ℂ, t ≠ 0 → (Complex.exp (t * Complex.log y) - 1 - t * Complex.log y) / t^2 = ∑' n : ℕ, (Complex.log y)^(n+2) / Nat.factorial (n+2) * t^n := by
        intro t ht; rw [ h_expansion t ] ; rw [ div_eq_iff ( pow_ne_zero 2 ht ) ] ; rw [ ← Summable.sum_add_tsum_nat_add 2 ] ; norm_num [ Finset.sum_range_succ' ];
        · rw [ ← tsum_mul_right ] ; ring;
        · exact Summable.of_norm <| by simpa using Real.summable_pow_div_factorial _;
      -- The series $\sum_{n=0}^{\infty} \frac{(t \ln y)^n}{n!}$ converges uniformly to $e^{t \ln y}$ on any compact subset of $\mathbb{C}$.
      have h_uniform : ContinuousOn (fun t : ℂ => ∑' n : ℕ, (Complex.log y)^(n+2) / Nat.factorial (n+2) * t^n) (Metric.closedBall 0 1) := by
        refine' continuousOn_tsum _ _ _;
        use fun n => ‖Complex.log y‖ ^ ( n + 2 ) / ( n + 2 ).factorial;
        · exact fun n => Continuous.continuousOn ( by continuity );
        · exact Real.summable_pow_div_factorial _ |> Summable.comp_injective <| Nat.succ_injective.comp <| Nat.succ_injective;
        · norm_num;
          exact fun n x hx => mul_le_of_le_one_right ( by positivity ) ( pow_le_one₀ ( by positivity ) hx );
      have h_limit : Filter.Tendsto (fun t : ℂ => ∑' n : ℕ, (Complex.log y)^(n+2) / Nat.factorial (n+2) * t^n) (nhdsWithin 0 {0}ᶜ) (nhds (∑' n : ℕ, (Complex.log y)^(n+2) / Nat.factorial (n+2) * 0^n)) := by
        exact tendsto_nhdsWithin_of_tendsto_nhds ( h_uniform.continuousAt ( Metric.closedBall_mem_nhds _ zero_lt_one ) );
      exact Filter.Tendsto.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ h_subst x hx ] ) ( h_limit.trans ( by rw [ tsum_eq_single 0 ] <;> aesop ) );
    convert h_exp using 2
    · norm_num [ Complex.ofReal_log hy.le, Complex.cpow_def_of_ne_zero ( Complex.ofReal_ne_zero.mpr hy.ne' ) ]
      split_ifs with h
      · subst h; simp
      · field_simp
    · norm_num [ Complex.ofReal_log hy.le, Complex.cpow_def_of_ne_zero ( Complex.ofReal_ne_zero.mpr hy.ne' ) ]
  refine' fun s hs => DifferentiableAt.differentiableWithinAt _;
  by_cases hs' : s = 0 <;> simp_all +decide [ Complex.cpow_def ];
  exact DifferentiableAt.congr_of_eventuallyEq ( show DifferentiableAt ℂ ( fun s => ( Complex.exp ( Complex.log y * s ) - 1 ) / s ) s from DifferentiableAt.div ( DifferentiableAt.sub ( Complex.differentiableAt_exp.comp s <| differentiableAt_id.const_mul _ ) <| differentiableAt_const _ ) differentiableAt_id hs' ) <| by filter_upwards [ IsOpen.mem_nhds isOpen_ne hs' ] with x hx; aesop;

/-
Cauchy-Goursat for `(y^s - 1)/s`: boundary integral over any rectangle = 0.
-/
lemma boundary_integral_cpow_sub_one_div_eq_zero (y : ℝ) (hy : 0 < y)
    (z w : ℂ) :
    (∫ x in z.re..w.re, (fun s : ℂ => if s = 0 then (↑(Real.log y) : ℂ) else ((y : ℂ) ^ s - 1) / s) (x + z.im * I)) -
    (∫ x in z.re..w.re, (fun s : ℂ => if s = 0 then (↑(Real.log y) : ℂ) else ((y : ℂ) ^ s - 1) / s) (x + w.im * I)) +
    I • (∫ t in z.im..w.im, (fun s : ℂ => if s = 0 then (↑(Real.log y) : ℂ) else ((y : ℂ) ^ s - 1) / s) (w.re + t * I)) -
    I • (∫ t in z.im..w.im, (fun s : ℂ => if s = 0 then (↑(Real.log y) : ℂ) else ((y : ℂ) ^ s - 1) / s) (z.re + t * I)) = 0 := by
  have h_int : DifferentiableOn ℂ (fun s : ℂ => if s = 0 then (↑(Real.log y) : ℂ) else ((y : ℂ) ^ s - 1) / s) Set.univ := by
    exact?;
  have := @Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable;
  exact this _ _ _ _ ( Set.countable_singleton 0 ) ( h_int.continuousOn.mono ( by simp +decide ) ) fun x hx => h_int.differentiableAt ( by simp +decide )

/-
Boundary integral of `1/s` around any rectangle `[a,b]×[-T,T]` containing 0
    (i.e., `a < 0 < b` and `T > 0`) equals `2πi`.
    Proved by decomposing `1/s` boundary integral using
    edge cancellation (4 sub-rectangles) and `boundary_integral_inv_eq_two_pi_I`.
-/
lemma boundary_integral_inv_rect (a b T : ℝ) (ha : a < 0) (hb : 0 < b) (hT : 0 < T) :
    (∫ x in a..b, ((x : ℂ) + (-T : ℝ) * I)⁻¹) -
    (∫ x in a..b, ((x : ℂ) + (T : ℝ) * I)⁻¹) +
    I • (∫ t in (-T)..T, ((b : ℂ) + (t : ℝ) * I)⁻¹) -
    I • (∫ t in (-T)..T, ((a : ℂ) + (t : ℝ) * I)⁻¹) = 2 * ↑Real.pi * I := by
  -- Evaluate the integrals explicitly.
  have h_eval_integrals : ∀ a b : ℝ, a < 0 → b > 0 → T > 0 → (∫ x in a..b, (x + (-T) * I)⁻¹) = Real.log (b ^ 2 + T ^ 2) / 2 + Complex.I * Real.arctan (b / T) - (Real.log (a ^ 2 + T ^ 2) / 2 + Complex.I * Real.arctan (a / T)) ∧ (∫ x in a..b, (x + T * I)⁻¹) = Real.log (b ^ 2 + T ^ 2) / 2 - Complex.I * Real.arctan (b / T) - (Real.log (a ^ 2 + T ^ 2) / 2 - Complex.I * Real.arctan (a / T)) := by
    intros a b ha hb hT;
    constructor <;> rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
    · intro x hx; convert HasDerivAt.add ( HasDerivAt.div_const ( HasDerivAt.ofReal_comp <| HasDerivAt.log ( HasDerivAt.add ( hasDerivAt_pow 2 x ) <| hasDerivAt_const _ _ ) _ ) _ ) ( HasDerivAt.const_mul I <| HasDerivAt.ofReal_comp <| HasDerivAt.arctan <| HasDerivAt.div_const ( hasDerivAt_id x ) _ ) using 1 <;> norm_num ; ring;
      · rw [ inv_eq_of_mul_eq_one_right ] ; ring ; norm_num [ Complex.ext_iff, sq, hT.ne' ];
        norm_num [ Complex.normSq, hT.ne' ] ; ring;
        field_simp;
        exact ⟨ by ring, by ring ⟩;
      · positivity;
    · exact Continuous.intervalIntegrable ( by exact Continuous.inv₀ ( by continuity ) fun x => by norm_num [ Complex.ext_iff ] ; intros; nlinarith ) _ _;
    · intro x hx; convert HasDerivAt.sub ( HasDerivAt.div_const ( HasDerivAt.ofReal_comp <| HasDerivAt.log ( HasDerivAt.add ( hasDerivAt_pow 2 x ) <| hasDerivAt_const _ _ ) _ ) _ ) ( HasDerivAt.const_mul I <| HasDerivAt.ofReal_comp <| HasDerivAt.arctan <| HasDerivAt.div_const ( hasDerivAt_id x ) _ ) using 1 <;> norm_num ; ring;
      · rw [ inv_eq_of_mul_eq_one_right ] ; ring ; norm_num [ Complex.ext_iff, sq, hT.ne' ];
        norm_num [ Complex.normSq, hT.ne' ] ; ring;
        field_simp;
        exact ⟨ by ring, by ring ⟩;
      · positivity;
    · exact Continuous.intervalIntegrable ( by exact Continuous.inv₀ ( by continuity ) fun x => by norm_num [ Complex.ext_iff ] ; intros; nlinarith ) _ _;
  -- Evaluate the integrals explicitly for the right and left sides.
  have h_eval_integrals_right : ∀ b : ℝ, b > 0 → (∫ t in (-T)..T, (b + t * I)⁻¹) = 2 * Real.arctan (T / b) := by
    intro b hb; rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
    rotate_right;
    use fun x => Complex.log ( b + x * I ) / I;
    · norm_num [ Complex.log, Complex.arg ];
      norm_num [ Complex.normSq, Complex.norm_def, hb.le ] ; ring;
      norm_cast ; norm_num [ Real.arctan_eq_arcsin ] ; ring;
      field_simp;
      rw [ Real.sqrt_div ( by positivity ), Real.sqrt_sq hb.le, mul_div_cancel₀ _ hb.ne' ] ; ring;
    · intro x hx; convert HasDerivAt.div_const ( HasDerivAt.comp x ( Complex.hasDerivAt_log _ ) ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) ( hasDerivAt_const _ _ ) ) ) ) _ using 1 <;> norm_num;
      exact Or.inl <| by simpa [ Complex.ext_iff ] using hb;
    · exact Continuous.intervalIntegrable ( by exact Continuous.inv₀ ( by continuity ) fun x => by norm_num [ Complex.ext_iff, hb.ne' ] ) _ _
  have h_eval_integrals_left : ∀ a : ℝ, a < 0 → (∫ t in (-T)..T, (a + t * I)⁻¹) = -2 * Real.arctan (T / |a|) := by
    intro a ha; specialize h_eval_integrals_right ( -a ) ( neg_pos.mpr ha ) ; simp_all +decide [ abs_of_neg ] ;
    rw [ ← h_eval_integrals_right ];
    rw [ ← intervalIntegral.integral_neg ] ; convert intervalIntegral.integral_comp_neg _ using 3 <;> norm_num;
    rw [ ← inv_neg ] ; ring;
  simp_all +decide [ Complex.ext_iff ];
  norm_cast; norm_num [ abs_of_neg ha ] ; ring_nf ; norm_num [ ha.ne, hb.ne', hT.ne' ] ;
  -- Use the fact that $\arctan(x) + \arctan(1/x) = \pi/2$ for $x > 0$.
  have h_arctan_identity : ∀ x : ℝ, 0 < x → Real.arctan x + Real.arctan (1 / x) = Real.pi / 2 := by
    intro x hx; rw [ add_comm, Real.arctan_eq_of_tan_eq ];
    rw [ sub_add_cancel ];
    · simp +decide [ Real.tan_pi_div_two_sub ];
    · constructor <;> linarith [ Real.arctan_pos.2 hx, Real.arctan_lt_pi_div_two x ];
  have := h_arctan_identity ( b * T⁻¹ ) ( by positivity ) ; have := h_arctan_identity ( -T⁻¹ * a ) ( by nlinarith [ mul_inv_cancel₀ ( ne_of_gt hT ) ] ) ; norm_num [ Real.arctan_neg, mul_comm ] at * ; ring_nf at * ; linarith;

/-
**Perron bound for y > 1**.
    Uses Cauchy-Goursat with rectangle shifted left + residue computation.
    The residue of `y^s / s` at `s = 0` is `1`, giving indicator value `1`.
-/
theorem perron_bound_gt_one (y c T : ℝ) (hy : 1 < y)
    (hc : 0 < c) (hT : 0 < T) :
    ‖perronIntegral y c T - 1‖ ≤ y ^ c / (T * Real.log y) := by
  -- By Cauchy-Goursat, the boundary integral of y^s/s around [-T, c] × [-T, T] = 2πI.
  have h_bc : (∫ x in (-T)..c, (y ^ ((x : ℂ) + (-T : ℝ) * I) / ((x : ℂ) + (-T : ℝ) * I))) -
                (∫ x in (-T)..c, (y ^ ((x : ℂ) + T * I) / ((x : ℂ) + T * I))) +
                I • (∫ t in (-T)..T, (y ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) -
                I • (∫ t in (-T)..T, (y ^ ((-T : ℂ) + t * I) / ((-T : ℂ) + t * I))) = 2 * Real.pi * I := by
                  have h_bc : (∫ x in (-T)..c, ((x : ℂ) + (-T : ℝ) * I)⁻¹) -
                                (∫ x in (-T)..c, ((x : ℂ) + T * I)⁻¹) +
                                I • (∫ t in (-T)..T, ((c : ℂ) + t * I)⁻¹) -
                                I • (∫ t in (-T)..T, ((-T : ℂ) + t * I)⁻¹) = 2 * Real.pi * I := by
                                  convert boundary_integral_inv_rect ( -T ) c T _ _ _ using 1 <;> norm_num [ hT, hc ];
                  convert congr_arg ( fun x : ℂ => x + ( ∫ x in ( -T )..c, ( ( y : ℂ ) ^ ( x + ( -T : ℝ ) * I ) - 1 ) / ( x + ( -T : ℝ ) * I ) ) - ( ∫ x in ( -T )..c, ( ( y : ℂ ) ^ ( x + T * I ) - 1 ) / ( x + T * I ) ) + I • ( ∫ t in ( -T )..T, ( ( y : ℂ ) ^ ( c + t * I ) - 1 ) / ( c + t * I ) ) - I • ( ∫ t in ( -T )..T, ( ( y : ℂ ) ^ ( -T + t * I ) - 1 ) / ( -T + t * I ) ) ) h_bc using 1;
                  · norm_num [ sub_div ] ; ring;
                    rw [ intervalIntegral.integral_sub, intervalIntegral.integral_sub ];
                    · rw [ intervalIntegral.integral_sub, intervalIntegral.integral_sub ] ; ring;
                      · apply_rules [ ContinuousOn.intervalIntegrable ];
                        refine' ContinuousOn.mul _ _;
                        · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.cpow continuousAt_const ( Continuous.continuousAt <| by continuity ) <| Or.inl <| by positivity;
                        · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.inv₀ ( continuousAt_const.add ( Complex.continuous_ofReal.continuousAt ) ) ( by norm_num [ Complex.ext_iff ] ; intros; nlinarith [ Set.mem_Icc.mp ( by simpa [ hc.le, hT.le ] using hx ) ] );
                      · apply_rules [ ContinuousOn.intervalIntegrable ];
                        exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.inv₀ ( continuousAt_const.add ( Complex.continuous_ofReal.continuousAt ) ) ( by norm_num [ Complex.ext_iff ] ; intros; nlinarith [ Set.mem_Icc.mp ( by simpa [ hc.le, hT.le ] using hx ) ] );
                      · apply_rules [ ContinuousOn.intervalIntegrable ];
                        refine' ContinuousOn.mul _ _;
                        · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.cpow continuousAt_const ( Continuous.continuousAt <| by continuity ) <| Or.inl <| by positivity;
                        · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.inv₀ ( continuousAt_const.add ( Complex.continuous_ofReal.continuousAt ) ) ( by norm_num [ Complex.ext_iff ] ; intros; nlinarith [ Set.mem_Icc.mp ( by simpa [ hc.le, hT.le ] using hx ) ] );
                      · apply_rules [ ContinuousOn.intervalIntegrable ];
                        exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.inv₀ ( continuousAt_const.add ( Complex.continuous_ofReal.continuousAt ) ) ( by norm_num [ Complex.ext_iff ] ; intros; nlinarith [ Set.mem_Icc.mp ( by simpa [ hc.le, hT.le ] using hx ) ] );
                    · apply_rules [ ContinuousOn.intervalIntegrable ];
                      refine' ContinuousOn.mul _ _;
                      · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.cpow continuousAt_const ( Continuous.continuousAt <| by continuity ) <| Or.inl <| by norm_num; linarith;
                      · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.inv₀ ( continuousAt_const.add ( continuousAt_const.mul ( Complex.continuous_ofReal.continuousAt ) ) ) ( by norm_num [ Complex.ext_iff ] ; intros; nlinarith );
                    · exact Continuous.intervalIntegrable ( by exact Continuous.inv₀ ( by continuity ) fun x => by norm_num [ Complex.ext_iff ] ; intros; nlinarith ) _ _;
                    · apply_rules [ ContinuousOn.intervalIntegrable ];
                      refine' ContinuousOn.mul _ _;
                      · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.cpow continuousAt_const ( Continuous.continuousAt <| by continuity ) <| Or.inl <| by positivity;
                      · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.inv₀ ( Continuous.continuousAt ( by continuity ) ) ( by norm_num [ Complex.ext_iff ] ; intros; nlinarith );
                    · apply_rules [ ContinuousOn.intervalIntegrable ];
                      exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.inv₀ ( Continuous.continuousAt ( by continuity ) ) ( by norm_num [ Complex.ext_iff ] ; intros; nlinarith );
                  · have := boundary_integral_cpow_sub_one_div_eq_zero y ( by positivity ) ( -T - T * I ) ( c + T * I ) ; norm_num at *;
                    convert congr_arg ( fun x : ℂ => 2 * Real.pi * I + x ) this.symm using 1 ; ring;
                    rw [ intervalIntegral.integral_congr fun x hx => if_neg <| by norm_num [ Complex.ext_iff ] ; intros ; nlinarith [ Set.mem_Icc.mp <| by simpa [ hc.le, hT.le ] using hx ], intervalIntegral.integral_congr fun x hx => if_neg <| by norm_num [ Complex.ext_iff ] ; intros ; nlinarith [ Set.mem_Icc.mp <| by simpa [ hc.le, hT.le ] using hx ], intervalIntegral.integral_congr fun t ht => if_neg <| by norm_num [ Complex.ext_iff ] ; intros ; nlinarith [ Set.mem_Icc.mp <| by simpa [ hc.le, hT.le ] using ht ], intervalIntegral.integral_congr fun t ht => if_neg <| by norm_num [ Complex.ext_iff ] ; intros ; nlinarith [ Set.mem_Icc.mp <| by simpa [ hc.le, hT.le ] using ht ] ] ; ring;
  -- Bounds using norm_cpow_div and norm_add_mul_I_ge_abs_right:
  have h_bounds : ‖∫ x in (-T)..c, (y : ℂ) ^ ((x : ℂ) + T * I) / ((x : ℂ) + T * I)‖ ≤ y ^ c / (T * Real.log y) ∧ ‖∫ x in (-T)..c, (y : ℂ) ^ ((x : ℂ) + (-T : ℝ) * I) / ((x : ℂ) + (-T : ℝ) * I)‖ ≤ y ^ c / (T * Real.log y) ∧ ‖∫ t in (-T)..T, (y : ℂ) ^ ((-T : ℂ) + t * I) / ((-T : ℂ) + t * I)‖ ≤ 2 / (T * Real.log y) := by
    refine' ⟨ _, _, _ ⟩;
    · -- The integral of $y^x / |x + iT|$ over $[-T, c]$ is bounded by $\int_{-T}^c y^x / T \, dx$.
      have h_top_bound : ‖∫ x in (-T)..c, (y : ℂ) ^ ((x : ℂ) + T * I) / ((x : ℂ) + T * I)‖ ≤ ∫ x in (-T)..c, y ^ x / T := by
        rw [ intervalIntegral.integral_of_le ( by linarith ), intervalIntegral.integral_of_le ( by linarith ) ];
        refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( MeasureTheory.integral_mono_of_nonneg _ _ _ );
        · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
        · exact Continuous.integrableOn_Ioc ( by exact Continuous.div_const ( by exact Continuous.rpow continuous_const continuous_id' <| by intro x; exact Or.inl <| by linarith ) _ );
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx;
          norm_num [ Complex.norm_cpow_eq_rpow_re_of_pos ( zero_lt_one.trans hy ), Complex.normSq, Complex.norm_def ];
          gcongr ; nlinarith [ hx.1, hx.2, Real.sqrt_nonneg ( x * x + T * T ), Real.mul_self_sqrt ( by nlinarith : 0 ≤ x * x + T * T ) ];
      refine' le_trans h_top_bound _;
      norm_num [ Real.rpow_def_of_pos ( zero_lt_one.trans hy ) ];
      rw [ intervalIntegral.integral_comp_mul_left ] <;> norm_num <;> ring_nf <;> norm_num [ ne_of_gt, Real.log_pos hy, hT ];
      · positivity;
      · exact ⟨ by linarith, by linarith, by linarith ⟩;
    · -- Using the bound on the integral of $y^x$ over $[-T, c]$, we get:
      have h_integral_bound : ‖∫ x in (-T)..c, (y : ℂ) ^ ((x : ℂ) + (-T : ℝ) * I) / ((x : ℂ) + (-T : ℝ) * I)‖ ≤ ∫ x in (-T)..c, y ^ x / T := by
        have h_integral_bound : ∀ x ∈ Set.Icc (-T) c, ‖(y : ℂ) ^ ((x : ℂ) + (-T : ℝ) * I) / ((x : ℂ) + (-T : ℝ) * I)‖ ≤ y ^ x / T := by
          intros x hx
          have h_norm : ‖(y : ℂ) ^ ((x : ℂ) + (-T : ℝ) * I)‖ = y ^ x := by
            rw [ Complex.norm_cpow_of_ne_zero ] <;> norm_num [ show y ≠ 0 by positivity ];
            norm_num [ abs_of_pos ( zero_lt_one.trans hy ), Complex.arg_ofReal_of_nonneg ( zero_le_one.trans hy.le ) ];
          simp_all +decide [ Complex.norm_def, Complex.normSq ];
          gcongr ; nlinarith [ Real.sqrt_nonneg ( x * x + T * T ), Real.mul_self_sqrt ( by nlinarith : 0 ≤ x * x + T * T ) ];
        rw [ intervalIntegral.integral_of_le ( by linarith ), intervalIntegral.integral_of_le ( by linarith ) ];
        refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( MeasureTheory.integral_mono_of_nonneg _ _ _ );
        · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
        · exact Continuous.integrableOn_Ioc ( by exact Continuous.div_const ( by exact Continuous.rpow continuous_const continuous_id' <| by intro x; exact Or.inl <| by linarith ) _ );
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using h_integral_bound x <| Set.Ioc_subset_Icc_self hx;
      simp_all +decide [ div_eq_mul_inv, Real.rpow_def_of_pos ( zero_lt_one.trans hy ) ];
      rw [ intervalIntegral.integral_comp_mul_left ] at *; norm_num at *;
      · exact h_integral_bound.trans ( by nlinarith [ show 0 ≤ ( Real.log y ) ⁻¹ * T⁻¹ by exact mul_nonneg ( inv_nonneg.2 ( Real.log_nonneg hy.le ) ) ( inv_nonneg.2 hT.le ), Real.exp_pos ( Real.log y * c ), Real.exp_pos ( - ( Real.log y * T ) ) ] )
      · exact ne_of_gt (Real.log_pos hy)
    · -- Using the bound on the norm of the integrand, we can bound the integral.
      have h_integrand_bound : ∀ t ∈ Set.Icc (-T) T, ‖(y : ℂ) ^ ((-T : ℂ) + t * I) / ((-T : ℂ) + t * I)‖ ≤ y ^ (-T) / T := by
        intros t ht
        have h_norm : ‖(y : ℂ) ^ ((-T : ℂ) + t * I)‖ = y ^ (-T) := by
          rw [ Complex.norm_cpow_eq_rpow_re_of_pos ( by positivity ) ] ; norm_num;
        simp_all +decide [ Complex.norm_def, Complex.normSq ];
        gcongr ; nlinarith [ Real.sqrt_nonneg ( T * T + t * t ), Real.mul_self_sqrt ( by nlinarith : 0 ≤ T * T + t * t ) ];
      refine' le_trans ( intervalIntegral.norm_integral_le_of_norm_le_const _ ) _;
      exact y ^ ( -T ) / T;
      · exact fun x hx => h_integrand_bound x <| by constructor <;> cases Set.mem_uIoc.mp hx <;> linarith;
      · -- Using the bound on the norm of the integrand, we can bound the integral. We know that $y^{-T} \leq 1 / (T \log y)$ for $y > 1$.
        have h_exp_bound : y ^ (-T) ≤ 1 / (T * Real.log y) := by
          have := rpow_le_inv_mul_abs_log ( show 0 < y⁻¹ by positivity ) ( show y⁻¹ < 1 by exact inv_lt_one_of_one_lt₀ hy ) hT;
          simp_all +decide [ Real.rpow_neg_eq_inv_rpow, abs_of_pos, Real.log_pos hy ];
        rw [ abs_of_nonneg ( by linarith ) ] ; convert mul_le_mul_of_nonneg_right h_exp_bound ( show 0 ≤ 2 by norm_num ) using 1 <;> ring;
        norm_num [ mul_comm T, hT.ne' ];
  -- Using the bounds, we can estimate the norm of the Perron integral.
  have h_norm : ‖(1 / (2 * Real.pi)) • (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) - 1‖ ≤ (1 / (2 * Real.pi)) * (2 * y ^ c / (T * Real.log y) + 2 / (T * Real.log y)) := by
    have h_norm : ‖(∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) - 2 * Real.pi * I / I‖ ≤ 2 * y ^ c / (T * Real.log y) + 2 / (T * Real.log y) := by
      have h_norm : ‖(∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) - 2 * Real.pi * I / I‖ ≤ ‖(∫ x in (-T)..c, (y : ℂ) ^ ((x : ℂ) + T * I) / ((x : ℂ) + T * I)) - (∫ x in (-T)..c, (y : ℂ) ^ ((x : ℂ) + (-T : ℝ) * I) / ((x : ℂ) + (-T : ℝ) * I)) + I • (∫ t in (-T)..T, (y : ℂ) ^ ((-T : ℂ) + t * I) / ((-T : ℂ) + t * I))‖ := by
        -- From h_bc, derive that the LHS expression equals the RHS expression
        -- h_bc: bot - top + I * right - I * left = 2πi
        -- Solve: right = (2πi + top - bot + I * left) / I = -I*(2πi + top - bot + I*left)
        -- right - 2π = -I*(top - bot) + left (since -I*2πi = 2π and -I*I = 1)
        -- And 2πi/I = 2π.
        -- ‖-I*(top - bot) + left‖ = ‖I*(-I*(top - bot) + left)‖ = ‖(top - bot) + I*left‖
        suffices h : (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) - 2 * ↑Real.pi * I / I =
          -I * ((∫ x in (-T)..c, (y : ℂ) ^ ((x : ℂ) + T * I) / ((x : ℂ) + T * I)) -
                 (∫ x in (-T)..c, (y : ℂ) ^ ((x : ℂ) + (-T : ℝ) * I) / ((x : ℂ) + (-T : ℝ) * I)) +
                 I • (∫ t in (-T)..T, (y : ℂ) ^ ((-T : ℂ) + t * I) / ((-T : ℂ) + t * I))) by
          rw [h]; simp [norm_neg, norm_mul, Complex.norm_I]
        -- The two expressions are equal (up to multiplication by unit -I)
        -- Using h_bc, we show LHS = -I * RHS, then ‖-I*z‖ = ‖z‖
        have h := h_bc; simp only [smul_eq_mul] at h ⊢
        set R := ∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)
        set A := ∫ x in (-T)..c, (y : ℂ) ^ ((x : ℂ) + T * I) / ((x : ℂ) + T * I)
        set B := ∫ x in (-T)..c, (y : ℂ) ^ ((x : ℂ) + ↑(-T) * I) / ((x : ℂ) + ↑(-T) * I)
        set L := ∫ t in (-T)..T, (y : ℂ) ^ ((-T : ℂ) + t * I) / ((-T : ℂ) + t * I)
        -- h : B - A + I * R - I * L = 2 * π * I
        -- Goal: ‖R - 2πi/I‖ ≤ ‖A - B + I * L‖
        have h_div : (2 : ℂ) * ↑Real.pi * I / I = 2 * ↑Real.pi := by field_simp [Complex.I_ne_zero]
        have hI2 : (I : ℂ) * I = -1 := by have := Complex.I_sq; rw [sq] at this; exact this
        have h_key : R - 2 * ↑Real.pi = -I * (A - B + I * L) := by
          -- Strategy: prove I * LHS = I * RHS, then cancel I
          -- I * (R - 2π) = I*R - 2π*I = (from h) A - B + I*L
          -- I * (-I*(A - B + I*L)) = -(I*I)*(A-B+I*L) = A - B + I*L
          apply mul_left_cancel₀ (a := I) Complex.I_ne_zero
          have lhs : I * (R - 2 * ↑Real.pi) = I * R - 2 * ↑Real.pi * I := by ring
          have rhs : I * (-I * (A - B + I * L)) = A - B + I * L := by
            have : I * (-I * (A - B + I * L)) = -(I * I) * (A - B + I * L) := by ring
            rw [this, hI2]; ring
          rw [lhs, rhs]; linear_combination h
        rw [h_div, h_key]
      refine le_trans h_norm <| le_trans ( norm_add_le _ _ ) ?_;
      refine' add_le_add _ _;
      · exact le_trans ( norm_sub_le _ _ ) ( by convert add_le_add h_bounds.1 h_bounds.2.1 using 1 ; ring );
      · simpa [ norm_smul ] using h_bounds.2.2;
    convert mul_le_mul_of_nonneg_left h_norm ( by positivity : 0 ≤ 1 / ( 2 * Real.pi ) ) using 1;
    norm_num [ Complex.ext_iff, Real.pi_ne_zero ];
    rw [ show ( ( Real.pi : ℂ ) ⁻¹ * ( 1 / 2 ) * ∫ t in -T..T, ( y : ℂ ) ^ ( c + t * I ) / ( c + t * I ) ) - 1 = ( Real.pi : ℂ ) ⁻¹ * ( 1 / 2 ) * ( ( ∫ t in -T..T, ( y : ℂ ) ^ ( c + t * I ) / ( c + t * I ) ) - 2 * Real.pi ) by simp [ mul_sub, mul_assoc, mul_comm, mul_left_comm, Real.pi_ne_zero ] ] ; norm_num [ abs_of_pos, Real.pi_pos ];
  convert h_norm.trans _ using 1;
  · unfold perronIntegral; norm_num [ mul_comm ] ;
  · field_simp;
    rw [ div_le_div_iff_of_pos_right ( Real.log_pos hy ) ];
    nlinarith [ Real.pi_gt_three, show y ^ c > 1 by exact Real.one_lt_rpow hy hc ]

/-! ## Main theorem -/

/-
**Perron kernel truncation bound**.
For `y > 0`, `y ≠ 1`, `c > 0`, `T > 0`:
  `‖(1/(2π)) ∫_{-T}^{T} y^{c+it}/(c+it) dt − 𝟙(y>1)‖ ≤ y^c / (T · |log y|)`
-/
theorem perron_truncation_bound (y c T : ℝ) (hy : 0 < y) (hy1 : y ≠ 1)
    (hc : 0 < c) (hT : 0 < T) :
    ‖perronIntegral y c T - ↑(perronIndicator y)‖ ≤
      y ^ c / (T * |Real.log y|) := by
  cases lt_or_gt_of_ne hy1;
  · simpa [ perronIndicator, if_neg ( not_lt.mpr ( le_of_lt ‹y < 1› ) ) ] using perron_bound_lt_one y c T hy ‹_› hc hT;
  · convert perron_bound_gt_one y c T ‹_› hc hT using 2;
    · unfold perronIndicator; aesop;
    · rw [ abs_of_pos ( Real.log_pos ‹_› ) ]

/-- Per-term signed bound obtained from the norm Perron truncation estimate.

This is the one-sided real form used by the boundary-aware signed Perron
comparison; the aggregate near-boundary estimate still requires Abel/Stieltjes
summation. -/
theorem perronIndicator_sub_perronIntegral_re_le (y c T : ℝ)
    (hy : 0 < y) (hy1 : y ≠ 1) (hc : 0 < c) (hT : 0 < T) :
    perronIndicator y - (perronIntegral y c T).re ≤
      y ^ c / (T * |Real.log y|) := by
  refine le_trans (le_abs_self _) ?_
  refine le_trans ?_ (perron_truncation_bound y c T hy hy1 hc hT)
  convert Complex.abs_re_le_norm (perronIntegral y c T - ↑(perronIndicator y)) using 1
  norm_num [abs_sub_comm]

/-- Conditional positivity of the truncated Perron kernel to the right of the
jump.

The unconditional statement `0 ≤ (perronIntegral y c T).re` for all `y > 1` is
false for this truncated kernel.  This usable version follows from the existing
truncation estimate when the truncation error is at most `1`. -/
theorem perronIntegral_re_nonneg_of_one_lt_of_rpow_le (y c T : ℝ)
    (hy : 1 < y) (hc : 0 < c) (hT : 0 < T)
    (hbound : y ^ c ≤ T * Real.log y) :
    0 ≤ (perronIntegral y c T).re := by
  have h_error_bound : ‖perronIntegral y c T - 1‖ ≤ 1 := by
    exact le_trans (perron_bound_gt_one y c T hy hc hT) (by
      rw [div_le_iff₀]
      · simpa [one_mul] using hbound
      · exact mul_pos hT (Real.log_pos hy))
  norm_num [Norm.norm] at h_error_bound
  norm_num [Complex.normSq] at h_error_bound
  nlinarith

end PerronKernel
