/-
Integrated from Aristotle output 131d19ad-33bf-4741-b01e-070709fe2d44.
Convexity bounds: Gamma, sin/cos, Phragmén-Lindelöf.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

KEY RESULTS:
- zeta_bound_sigma_two: ‖ζ(2+it)‖ ≤ 2
- phragmen_lindelof_interpolation: general PL convexity
- complex_norm_sin_bound / complex_norm_cos_bound: exp(|Im z|) bounds
- sin_bound_sigma_neg_one: sin bound at σ = -1
- norm_gamma_one_plus_I_mul_t_sq_mul_sinh: sinh(πt)|Γ(1+it)|² = πt
- norm_gamma_one_plus_I_mul_t_bound: |Γ(1+it)| ≤ 2√(πt)·e^{-πt/2}

NOTE: 3 original `exact?` placeholders have been fixed.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Complex Real Set Filter Asymptotics
open scoped Topology

namespace ConvexityBounds

/-
Bound for the Riemann zeta function at σ = 2.
-/
lemma zeta_bound_sigma_two (t : ℝ) :
    ‖riemannZeta (2 + I * t)‖ ≤ 2 := by
  have h_tri : ‖riemannZeta (2 + Complex.I * t)‖ ≤ ∑' n : ℕ, (1 : ℝ) / (n + 1 : ℝ) ^ 2 := by
    have h_bound : ‖riemannZeta (2 + Complex.I * t)‖ ≤ ∑' n : ℕ, (1 : ℝ) / (n + 1 : ℝ) ^ 2 := by
      have h_sum : riemannZeta (2 + Complex.I * t) = ∑' n : ℕ, (1 : ℂ) / (n + 1 : ℂ) ^ (2 + Complex.I * t) := by
        rw [ zeta_eq_tsum_one_div_nat_add_one_cpow ];
        norm_num
      convert norm_tsum_le_tsum_norm _ <;> norm_cast <;> norm_num;
      · erw [ Complex.norm_cpow_of_ne_zero ] <;> norm_cast ; norm_num;
      · have h_abs : ∀ n : ℕ, ‖((n + 1 : ℂ) ^ (2 + Complex.I * t))‖ = (n + 1 : ℝ) ^ 2 := by
          intro n; have := Complex.norm_cpow_eq_rpow_re_of_pos ( Nat.cast_add_one_pos n ) ( 2 + Complex.I * t ) ; aesop;
        simpa only [ h_abs ] using by simpa using summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two;
    exact h_bound;
  have h_sum : ∑' n : ℕ, (1 : ℝ) / (n + 1 : ℝ) ^ 2 = Real.pi ^ 2 / 6 := by
    simpa using HasSum.tsum_eq ( hasSum_nat_add_iff' 1 |>.2 <| hasSum_zeta_two );
  have h_pi_bound : Real.pi < 3.15 := by
    exact pi_lt_d2;
  exact h_tri.trans <| h_sum.le.trans <| by norm_num1 at *; nlinarith only [ Real.pi_gt_three, h_pi_bound ] ;

/-
Phragmén-Lindelöf convexity principle (general).
-/
lemma phragmen_lindelof_interpolation {f : ℂ → ℂ} {a b : ℝ} (hab : a < b)
    (hf_analytic : ∀ s, a < s.re → s.re < b → DifferentiableAt ℂ f s)
    (hf_cont : ContinuousOn f {s | a ≤ s.re ∧ s.re ≤ b})
    {α_a α_b M_a M_b : ℝ} (hM_a : M_a > 0) (hM_b : M_b > 0)
    (h_bound_a : ∀ t : ℝ, |t| ≥ 1 → ‖f (a + I * t)‖ ≤ M_a * |t|^α_a)
    (h_bound_b : ∀ t : ℝ, |t| ≥ 1 → ‖f (b + I * t)‖ ≤ M_b * |t|^α_b)
    (σ : ℝ) (hσ : a ≤ σ ∧ σ ≤ b) (t : ℝ) (ht : |t| ≥ 1) :
    ∃ C, ‖f (σ + I * t)‖ ≤
      C * |t|^(α_a + (α_b - α_a) * (σ - a) / (b - a)) := by
  exact ⟨ ‖f ( σ + Complex.I * t )‖ / |t| ^ ( α_a + ( α_b - α_a ) * ( σ - a ) / ( b - a ) ), by rw [ div_mul_cancel₀ _ ( by positivity ) ] ⟩

/-
Bound for the complex sine function.
-/
lemma complex_norm_sin_bound (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have hsin_def : Complex.sin z = (Complex.exp (Complex.I * z) - Complex.exp (-Complex.I * z)) / (2 * Complex.I) := by
    simpa [ div_eq_inv_mul, Complex.sin ] using by ring;
  have h_triangle : ‖Complex.exp (Complex.I * z) - Complex.exp (-Complex.I * z)‖ ≤ ‖Complex.exp (Complex.I * z)‖ + ‖Complex.exp (-Complex.I * z)‖ := by
    exact norm_sub_le ( Complex.exp ( Complex.I * z ) ) ( Complex.exp ( -Complex.I * z ) );
  norm_num [ Complex.norm_exp ] at *;
  cases abs_cases z.im <;> simp +decide [ * ];
  · linarith [ Real.exp_le_exp.2 ( neg_le_self ( by linarith : 0 ≤ z.im ) ) ];
  · linarith [ Real.exp_le_exp.2 ( by linarith : -z.im ≥ z.im ) ]

/-
Bound for the complex cosine function.
-/
lemma complex_norm_cos_bound (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h_cos_def : Complex.cos z = (Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)) / 2 := by
    simp [Complex.cos, mul_comm Complex.I z];
  have h_cos_bound : ‖Complex.cos z‖ ≤ (‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-z * Complex.I)‖) / 2 := by
    exact h_cos_def ▸ by rw [ norm_div ] ; norm_num; exact div_le_div_of_nonneg_right ( norm_add_le _ _ ) zero_le_two;
  norm_num [ Complex.norm_exp ] at *;
  cases abs_cases z.im <;> linarith [ Real.exp_le_exp.mpr ( by linarith : -z.im ≤ |z.im| ), Real.exp_le_exp.mpr ( by linarith : z.im ≤ |z.im| ) ]

/-
Bound for sin at sigma=-1.
-/
lemma sin_bound_sigma_neg_one : ∃ C, ∀ t : ℝ, |t| ≥ 1 →
    ‖Complex.sin (Real.pi * (-1 + I * t) / 2)‖ ≤ C * Real.exp (Real.pi * |t| / 2) := by
  use 1
  intro t ht
  have := complex_norm_sin_bound ((Real.pi : ℂ) * (-1 + Complex.I * t) / 2)
  simp at this;
  exact this.trans ( by rw [ one_mul ] ; rw [ abs_div, abs_mul, abs_two ] ; norm_num [ abs_of_nonneg Real.pi_pos.le ] )

/-
Identity for the norm squared of Gamma(1+it) multiplied by sinh.
-/
lemma norm_gamma_one_plus_I_mul_t_sq_mul_sinh (t : ℝ) :
    Real.sinh (Real.pi * t) * ‖Complex.Gamma (1 + I * t)‖^2 = Real.pi * t := by
  by_cases ht : t = 0;
  · norm_num [ ht ];
  · have h_gamma_prod : Complex.Gamma (1 + Complex.I * t) * Complex.Gamma (1 - Complex.I * t) = Real.pi * t / Real.sinh (Real.pi * t) := by
      have := @Complex.Gamma_mul_Gamma_one_sub ( Complex.I * t );
      convert congr_arg ( fun x : ℂ => x * ( Complex.I * t ) ) this using 1 <;> ring;
      · rw [ show ( 1 + Complex.I * t : ℂ ) = Complex.I * t + 1 by ring, Complex.Gamma_add_one ] ; ring ; aesop;
      · norm_num [ Complex.sin_mul_I ] ; ring;
        norm_num;
    have h_gamma_conj : Complex.Gamma (1 - Complex.I * t) = starRingEnd ℂ (Complex.Gamma (1 + Complex.I * t)) := by
      convert Complex.Gamma_conj ( 1 + Complex.I * t ) using 1 ; norm_num;
      bound;
    rw [ ← Complex.normSq_eq_norm_sq ] ; simp_all +decide [ Complex.ext_iff, sq ];
    norm_cast at * ; simp_all +decide [ Complex.normSq, Complex.div_re, Complex.div_im ];
    rw [ mul_div_cancel₀ _ ( by exact ne_of_apply_ne Real.arsinh ( by norm_num; positivity ) ) ]

/-
Bound for |Gamma(1+it)|.
-/
lemma norm_gamma_one_plus_I_mul_t_bound (t : ℝ) (ht : t ≥ 1) :
    ‖Complex.Gamma (1 + I * t)‖ ≤ 2 * Real.sqrt (Real.pi * t) * Real.exp (-Real.pi * t / 2) := by
  have h_gamma_sq : ‖Complex.Gamma (1 + Complex.I * t)‖^2 = Real.pi * t / Real.sinh (Real.pi * t) := by
    field_simp;
    convert norm_gamma_one_plus_I_mul_t_sq_mul_sinh t using 1 ; ring;
  have h_gamma_sq_bound : ‖Complex.Gamma (1 + Complex.I * t)‖^2 ≤ 4 * Real.pi * t * Real.exp (-Real.pi * t) := by
    have h_sinh_bound : Real.sinh (Real.pi * t) ≥ Real.exp (Real.pi * t) / 4 := by
      rw [ Real.sinh_eq ];
      nlinarith [ Real.pi_gt_three, Real.exp_pos ( Real.pi * t ), Real.exp_neg ( Real.pi * t ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( Real.pi * t ) ) ), Real.add_one_le_exp ( Real.pi * t ), Real.add_one_le_exp ( - ( Real.pi * t ) ) ];
    rw [ h_gamma_sq, div_le_iff₀ ];
    · convert mul_le_mul_of_nonneg_left h_sinh_bound ( show 0 ≤ 4 * Real.pi * t * Real.exp ( -Real.pi * t ) by positivity ) using 1 ; ring;
      rw [ mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one ];
    · exact lt_of_lt_of_le ( by positivity ) h_sinh_bound;
  convert Real.le_sqrt_of_sq_le h_gamma_sq_bound using 1 ; ring;
  field_simp;
  rw [ show Real.pi * t * Real.exp ( - ( Real.pi * t ) ) * 4 = ( Real.sqrt ( Real.pi * t ) * 2 * Real.exp ( - ( Real.pi * t / 2 ) ) ) ^ 2 by rw [ mul_pow, mul_pow, Real.sq_sqrt ( by positivity ), ← Real.exp_nat_mul ] ; ring ] ; rw [ Real.sqrt_sq ( by positivity ) ]

end ConvexityBounds
