/-
Integrated from Aristotle output 82b20e70-e7b2-4f83-9883-bf1148732289.
Proves a lower bound for the mean square of the partial zeta sum on the critical line.

Main result: For any N ≥ 2, ∃ c > 0, ∃ T₀ ≥ 2, ∀ T ≥ T₀,
  c * T * log N ≤ ∫₁ᵀ |Σ_{n≤N} n^{-1/2-it}|² dt

This is a KEY component for Hardy's theorem (mean square lower bound).

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace MeanSquareLowerBound

open Complex MeasureTheory Set Finset

/-- Partial sum of the Riemann zeta function: Σ_{n=1}^{N} n^{-1/2-it} -/
noncomputable def zetaPartialSum (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, (n + 1 : ℂ)^(-(1/2 : ℂ) - I * t)

/-- The sum of 1/(n+1) for n from 0 to N-1 is at least log N. -/
lemma harmonic_sum_lower_bound (N : ℕ) (hN : N ≥ 2) :
    Real.log N ≤ ∑ n ∈ Finset.range N, (1 : ℝ) / (n + 1) := by
  have h_harmonic : ∀ n : ℕ, (∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1)) ≥ Real.log (n + 1) := by
    intro n; induction' n with n ih <;> norm_num [ Finset.sum_range_succ ] at *;
    rw [ Real.log_le_iff_le_exp ( by positivity ) ] at *;
    rw [ Real.exp_add ] ; nlinarith [ inv_pos.mpr ( by linarith : 0 < ( n : ℝ ) + 1 ), mul_inv_cancel₀ ( by linarith : ( n : ℝ ) + 1 ≠ 0 ), Real.add_one_le_exp ( ( n : ℝ ) + 1 ) ⁻¹ ];
  exact le_trans ( Real.log_le_log ( by positivity ) ( by norm_num ) ) ( h_harmonic N )

/-- The integral of the squared norm of n^{-1/2-it} from 1 to T is (T-1)/n. -/
lemma diagonal_integral (n : ℕ) (hn : n ≥ 1) (T : ℝ) (hT : T ≥ 1) :
    ∫ t in Ioc 1 T, ‖(n : ℂ)^(-(1/2 : ℂ) - I * t)‖^2 = (T - 1) / n := by
  have h_norm_sq : ∀ (t : ℝ), ‖(n : ℂ) ^ (-(1/2) - Complex.I * t)‖ ^ 2 = (n : ℝ) ^ (-1 : ℝ) := by
    intro t; rw [ Complex.norm_cpow_of_ne_zero ] <;> norm_num [ hn ] ; ring;
    · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num;
    · linarith;
  simp_all +decide [ div_eq_mul_inv, Real.rpow_neg_one ]

/-- The magnitude of the cross term integral is bounded by 2/(√(nm)|log(m/n)|). -/
lemma off_diagonal_bounded (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) (hnm : n ≠ m) (T : ℝ) :
    ‖∫ t in Ioc 1 T, (n : ℂ)^(-(1/2 : ℂ) - I * t) * (m : ℂ)^(-(1/2 : ℂ) + I * t)‖
    ≤ 2 / (Real.sqrt n * Real.sqrt m * |Real.log (m / n)|) := by
  by_cases hT : T ≤ 1 <;> by_cases hmn : m = n <;> simp_all +decide [ Complex.cpow_def ];
  · positivity;
  · have h_integral : ∫ t in Set.Ioc 1 T, Complex.exp (Complex.I * t * (Real.log m - Real.log n)) = (Complex.exp (Complex.I * T * (Real.log m - Real.log n)) - Complex.exp (Complex.I * 1 * (Real.log m - Real.log n))) / (Complex.I * (Real.log m - Real.log n)) := by
      rw [ ← intervalIntegral.integral_of_le hT.le ];
      have := @integral_exp_mul_complex 1 T;
      convert @this ( Complex.I * ( Real.log m - Real.log n ) ) _ using 3 <;> norm_num [ Complex.ext_iff, Real.log_pos, hn, hm, hnm, hmn ];
      · exact ⟨ by ring, by ring ⟩;
      · exact ⟨ by ring, by ring ⟩;
      · norm_num [ Complex.log_re, Complex.log_im ];
        exact sub_ne_zero_of_ne <| fun h => hmn <| Nat.cast_injective ( Real.log_injOn_pos ( by norm_num; linarith ) ( by norm_num; linarith ) h ) ▸ rfl;
    have h_subst : ∫ t in Set.Ioc 1 T, (n : ℂ) ^ (-(1/2 : ℂ) - Complex.I * t) * (m : ℂ) ^ (-(1/2 : ℂ) + Complex.I * t) = (Complex.exp (Complex.I * T * (Real.log m - Real.log n)) - Complex.exp (Complex.I * 1 * (Real.log m - Real.log n))) / (Complex.I * (Real.log m - Real.log n)) * (n : ℂ) ^ (-(1/2 : ℂ)) * (m : ℂ) ^ (-(1/2 : ℂ)) := by
      convert congr_arg ( fun x : ℂ => x * ( n : ℂ ) ^ ( - ( 1 / 2 : ℂ ) ) * ( m : ℂ ) ^ ( - ( 1 / 2 : ℂ ) ) ) h_integral using 1;
      rw [ ← MeasureTheory.integral_mul_const, ← MeasureTheory.integral_mul_const ] ; congr ; ext ; rw [ Complex.cpow_def_of_ne_zero ( by norm_cast; linarith ), Complex.cpow_def_of_ne_zero ( by norm_cast; linarith ) ] ; ring;
      rw [ Complex.cpow_def_of_ne_zero ( by norm_cast; linarith ), Complex.cpow_def_of_ne_zero ( by norm_cast; linarith ) ] ; rw [ ← Complex.exp_add ] ; ring;
      rw [ ← Complex.exp_add, ← Complex.exp_add ] ; push_cast [ Complex.ofReal_log ( Nat.cast_nonneg _ ) ] ; ring;
    have h_triangle : ‖(Complex.exp (Complex.I * T * (Real.log m - Real.log n)) - Complex.exp (Complex.I * 1 * (Real.log m - Real.log n))) / (Complex.I * (Real.log m - Real.log n))‖ ≤ 2 / |Real.log m - Real.log n| := by
      norm_num [ Complex.norm_def, Complex.normSq ];
      norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im ];
      rw [ Real.sqrt_mul_self_eq_abs ];
      gcongr;
      exact Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith only [ sq_nonneg ( Real.cos ( T * ( Real.log m - Real.log n ) ) + Real.cos ( Real.log m - Real.log n ) ), sq_nonneg ( Real.sin ( T * ( Real.log m - Real.log n ) ) + Real.sin ( Real.log m - Real.log n ) ), Real.cos_sq' ( T * ( Real.log m - Real.log n ) ), Real.cos_sq' ( Real.log m - Real.log n ) ] ⟩;
    convert mul_le_mul h_triangle ( show ‖ ( n : ℂ ) ^ ( - ( 1 / 2 : ℂ ) ) * ( m : ℂ ) ^ ( - ( 1 / 2 : ℂ ) )‖ ≤ 1 / Real.sqrt n * 1 / Real.sqrt m from ?_ ) ( by positivity ) ( by positivity ) using 1 <;> norm_num [ Complex.norm_exp, Complex.norm_cpow_of_ne_zero, show n ≠ 0 by linarith, show m ≠ 0 by linarith ] ; ring;
    · convert congr_arg Norm.norm h_subst using 1 <;> norm_num [ Complex.norm_exp, Complex.norm_cpow_of_ne_zero, show n ≠ 0 by linarith, show m ≠ 0 by linarith ] ; ring;
      · congr! 2;
        ext; rw [ Complex.cpow_def_of_ne_zero ( by norm_cast; linarith ), Complex.cpow_def_of_ne_zero ( by norm_cast; linarith ) ] ; ring;
      · ring;
    · rw [ Real.log_div ( by positivity ) ( by positivity ) ] ; ring;
    · rw [ Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.rpow_neg ( by positivity ), Real.rpow_neg ( by positivity ) ] ; ring_nf ; norm_num

/-- **Main theorem**: For any N ≥ 2, the mean square of the partial sum
    is at least c * T * log N for large T.

    This is the partial-sum version of the mean square lower bound,
    a key ingredient for Hardy's theorem on zeta zeros on the critical line. -/
theorem partial_sum_mean_square_lower_bound (N : ℕ) (hN : N ≥ 2) :
    ∃ c : ℝ, c > 0 ∧ ∃ T₀ : ℝ, T₀ ≥ 2 ∧ ∀ T : ℝ, T ≥ T₀ →
      c * T * Real.log N ≤ ∫ t in Set.Ioc 1 T, ‖zetaPartialSum N t‖^2 := by
  have h_expand : ∀ T ≥ 1, ∫ t in Set.Ioc 1 T, ‖zetaPartialSum N t‖^2 = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ∫ t in Set.Ioc 1 T, (n + 1 : ℂ)^(-(1/2 : ℂ) - I * t) * (m + 1 : ℂ)^(-(1/2 : ℂ) + I * t) := by
    intros T hT
    have h_expand : ∀ t ∈ Set.Ioc 1 T, ‖zetaPartialSum N t‖^2 = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, (n + 1 : ℂ)^(-(1/2 : ℂ) - I * t) * (m + 1 : ℂ)^(-(1/2 : ℂ) + I * t) := by
      intro t ht
      have h_expand : ‖zetaPartialSum N t‖^2 = (∑ n ∈ Finset.range N, (n + 1 : ℂ)^(-(1/2 : ℂ) - I * t)) * (∑ m ∈ Finset.range N, (m + 1 : ℂ)^(-(1/2 : ℂ) + I * t)) := by
        have h_expand : ‖zetaPartialSum N t‖^2 = (∑ n ∈ Finset.range N, (n + 1 : ℂ)^(-(1/2 : ℂ) - I * t)) * starRingEnd ℂ (∑ n ∈ Finset.range N, (n + 1 : ℂ)^(-(1/2 : ℂ) - I * t)) := by
          rw [ Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow ];
          unfold zetaPartialSum; norm_num;
        convert h_expand using 2;
        rw [ map_sum ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ Complex.ext_iff ] ; norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def ] ; ring;
        norm_cast ; norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im ];
      rw [ h_expand, Finset.sum_mul ];
      simp +decide only [Finset.mul_sum _ _ _];
    have h_expand : ∫ t in Set.Ioc 1 T, ‖zetaPartialSum N t‖^2 = ∫ t in Set.Ioc 1 T, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, (n + 1 : ℂ)^(-(1/2 : ℂ) - I * t) * (m + 1 : ℂ)^(-(1/2 : ℂ) + I * t) := by
      convert MeasureTheory.setIntegral_congr_fun measurableSet_Ioc h_expand using 1;
      convert integral_ofReal.symm ; norm_cast;
    rw [ h_expand, MeasureTheory.integral_finset_sum ];
    · refine' Finset.sum_congr rfl fun i hi => _;
      rw [ MeasureTheory.integral_finset_sum ];
      intro j hj;
      refine' Continuous.integrableOn_Ioc _;
      refine' Continuous.mul _ _;
      · exact Continuous.cpow ( continuous_const ) ( by continuity ) ( by intro x; exact Or.inl <| by norm_cast; linarith );
      · exact Continuous.cpow ( continuous_const ) ( by continuity ) ( by intro x; exact Or.inl <| by norm_cast; linarith );
    · intro i hi;
      refine' Continuous.integrableOn_Ioc _;
      refine' continuous_finset_sum _ fun j hj => _;
      exact Continuous.mul ( Continuous.cpow ( by continuity ) ( by continuity ) <| by intro t; exact Or.inl <| by norm_cast; linarith ) ( Continuous.cpow ( by continuity ) ( by continuity ) <| by intro t; exact Or.inl <| by norm_cast; linarith );
  have h_diag : ∀ T ≥ 1, ∫ t in Set.Ioc 1 T, ‖zetaPartialSum N t‖^2 ≥ (T - 1) * Real.log N - ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, if n ≠ m then 2 / (Real.sqrt (n + 1) * Real.sqrt (m + 1) * |Real.log ((m + 1) / (n + 1))|) else 0 := by
    intros T hT
    have h_diag : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ∫ t in Set.Ioc 1 T, (n + 1 : ℂ)^(-(1/2 : ℂ) - I * t) * (m + 1 : ℂ)^(-(1/2 : ℂ) + I * t) = ∑ n ∈ Finset.range N, (T - 1) / (n + 1 : ℝ) + ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, if n ≠ m then ∫ t in Set.Ioc 1 T, (n + 1 : ℂ)^(-(1/2 : ℂ) - I * t) * (m + 1 : ℂ)^(-(1/2 : ℂ) + I * t) else 0 := by
      have h_diag : ∀ n ∈ Finset.range N, ∫ t in Set.Ioc 1 T, (n + 1 : ℂ)^(-(1/2 : ℂ) - I * t) * (n + 1 : ℂ)^(-(1/2 : ℂ) + I * t) = (T - 1) / (n + 1 : ℝ) := by
        intro n hn
        have h_diag : ∀ t ∈ Set.Ioc 1 T, (n + 1 : ℂ)^(-(1/2 : ℂ) - I * t) * (n + 1 : ℂ)^(-(1/2 : ℂ) + I * t) = (n + 1 : ℂ)^(-1 : ℂ) := by
          intro t ht; rw [ ← Complex.cpow_add _ _ _ ] ; ring ; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def ] ;
          linarith;
        rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioc h_diag, ← intervalIntegral.integral_of_le ] <;> norm_num [ hT ];
        rw [ div_eq_mul_inv, Complex.cpow_neg_one ];
      simp_all +decide [ Finset.sum_ite, Finset.filter_ne ];
      rw [ Finset.sum_congr rfl fun i hi => h_diag i ( Finset.mem_range.mp hi ) ] ; ring;
    have h_off_diag : ∀ n m : ℕ, n < N → m < N → n ≠ m → ‖∫ t in Set.Ioc 1 T, (n + 1 : ℂ)^(-(1/2 : ℂ) - I * t) * (m + 1 : ℂ)^(-(1/2 : ℂ) + I * t)‖ ≤ 2 / (Real.sqrt (n + 1) * Real.sqrt (m + 1) * |Real.log ((m + 1) / (n + 1))|) := by
      intros n m hn hm hnm;
      convert off_diagonal_bounded ( n + 1 ) ( m + 1 ) ( by linarith ) ( by linarith ) ( by simpa [ add_comm ] using hnm ) T using 1 ; norm_num;
      norm_cast;
    have h_off_diag_sum : ‖∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, if n ≠ m then ∫ t in Set.Ioc 1 T, (n + 1 : ℂ)^(-(1/2 : ℂ) - I * t) * (m + 1 : ℂ)^(-(1/2 : ℂ) + I * t) else 0‖ ≤ ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, if n ≠ m then 2 / (Real.sqrt (n + 1) * Real.sqrt (m + 1) * |Real.log ((m + 1) / (n + 1))|) else 0 := by
      refine' le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun n hn => le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun m hm => _ ) );
      split_ifs <;> simp_all +decide [ Complex.norm_exp ];
    have h_integral_bound : ∫ t in Set.Ioc 1 T, ‖zetaPartialSum N t‖^2 ≥ (T - 1) * ∑ n ∈ Finset.range N, (1 : ℝ) / (n + 1) - ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, if n ≠ m then 2 / (Real.sqrt (n + 1) * Real.sqrt (m + 1) * |Real.log ((m + 1) / (n + 1))|) else 0 := by
      have h_integral_bound : ∫ t in Set.Ioc 1 T, ‖zetaPartialSum N t‖^2 = (T - 1) * ∑ n ∈ Finset.range N, (1 : ℝ) / (n + 1) + Complex.re (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, if n ≠ m then ∫ t in Set.Ioc 1 T, (n + 1 : ℂ)^(-(1/2 : ℂ) - I * t) * (m + 1 : ℂ)^(-(1/2 : ℂ) + I * t) else 0) := by
        convert congr_arg Complex.re ( h_expand T hT ) using 1;
        rw [ h_diag ] ; norm_num [ Finset.mul_sum _ _ _, mul_comm ];
        norm_num [ div_eq_mul_inv, Complex.normSq, Complex.div_re ];
        field_simp;
      linarith [ abs_le.mp ( Complex.abs_re_le_norm ( ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, if n ≠ m then ∫ t in Set.Ioc 1 T, ( n + 1 : ℂ ) ^ ( - ( 1 / 2 : ℂ ) - Complex.I * t ) * ( m + 1 : ℂ ) ^ ( - ( 1 / 2 : ℂ ) + Complex.I * t ) else 0 ) ), h_off_diag_sum ];
    refine le_trans ?_ h_integral_bound;
    gcongr;
    · linarith;
    · convert harmonic_sum_lower_bound N hN using 1;
  obtain ⟨c, hc_pos, hc⟩ : ∃ c > 0, ∃ T₀ ≥ 2, ∀ T ≥ T₀, (T - 1) * Real.log N - ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, (if n ≠ m then 2 / (Real.sqrt (n + 1) * Real.sqrt (m + 1) * |Real.log ((m + 1) / (n + 1))|) else 0) ≥ c * T * Real.log N := by
    refine' ⟨ 1 / 2, by norm_num, 2 + ⌈2 * ( ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, if n ≠ m then 2 / ( Real.sqrt ( n + 1 ) * Real.sqrt ( m + 1 ) * |Real.log ( ( m + 1 ) / ( n + 1 ) )| ) else 0 ) / Real.log N⌉₊, _, _ ⟩ <;> norm_num;
    intro T hT; nlinarith [ Nat.le_ceil ( ( 2 * ∑ x ∈ Finset.range N, ∑ x_1 ∈ Finset.range N, if x = x_1 then 0 else 2 / ( Real.sqrt ( x + 1 ) * Real.sqrt ( x_1 + 1 ) * |Real.log ( ( x_1 + 1 ) / ( x + 1 ) )| ) ) / Real.log N ), Real.log_pos ( show ( N : ℝ ) > 1 by norm_cast ), mul_div_cancel₀ ( 2 * ∑ x ∈ Finset.range N, ∑ x_1 ∈ Finset.range N, if x = x_1 then 0 else 2 / ( Real.sqrt ( x + 1 ) * Real.sqrt ( x_1 + 1 ) * |Real.log ( ( x_1 + 1 ) / ( x + 1 ) )| ) ) ( ne_of_gt <| Real.log_pos <| show ( N : ℝ ) > 1 by norm_cast ) ] ;
  exact ⟨ c, hc_pos, hc.choose, hc.choose_spec.1, fun T hT => le_trans ( hc.choose_spec.2 T hT ) ( h_diag T ( by linarith [ hc.choose_spec.1 ] ) ) ⟩

end MeanSquareLowerBound
