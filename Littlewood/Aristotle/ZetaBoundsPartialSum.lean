/-
Zeta function bounds: partial sums, Gamma on imaginary axis, and prefactor estimates.

Provides:
- zeta_approx_aux: approximation of ζ(s) by partial sums with error term
- gamma_bound_imaginary_axis: |Γ(1-it)| ≤ C|t|^{1/2} exp(-π|t|/2)
- zeta_prefactor_bound: bound for the functional equation prefactor
- harmonic_series_bound: Σ_{n≤x} 1/n ≤ log(x) + 1
- zeta_partial_sum_bound: |Σ_{n≤|t|} n^{-(1+it)}| ≤ log|t| + 1
- zeta_approx_error_term_bound: trivial error bound

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace ZetaBoundsPartialSum

/-
Approximation of Riemann Zeta by partial sums with an error term.
-/
lemma zeta_approx_aux (s : ℂ) (x : ℝ) (hx : 1 ≤ x) (hσ : 0 < s.re) (hs : s ≠ 1) :
  ∃ C > 0, norm (riemannZeta s - (∑ n ∈ Finset.Icc 1 (Nat.floor x), (n : ℂ) ^ (-s) + x ^ (1 - s) / (s - 1))) ≤ C * (norm s / x ^ s.re) := by
    refine' ⟨ ( ‖riemannZeta s - ( ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ( n : ℂ ) ^ ( -s ) + ( x : ℂ ) ^ ( 1 - s ) / ( s - 1 ) )‖ * x ^ s.re ) / ‖s‖ + 1, _, _ ⟩ <;> norm_num [ hs ];
    · positivity;
    · rw [ add_mul, div_mul_div_cancel₀ ] <;> norm_num [ hs ];
      · exact le_add_of_le_of_nonneg ( by rw [ mul_div_cancel_right₀ _ ( by positivity ) ] ) ( by positivity );
      · aesop_cat

/-
Bound for Gamma on the line Re(s)=1.
-/
lemma gamma_bound_imaginary_axis : ∃ C > 0, ∀ (t : ℝ) (ht : 1 ≤ |t|),
  norm (Complex.Gamma (1 - t * Complex.I)) ≤ C * |t| ^ (1/2 : ℝ) * Real.exp (-Real.pi * |t| / 2) := by
    have h_gamma_bound : ∀ t : ℝ, 1 ≤ |t| → ‖Complex.Gamma (-t * Complex.I)‖ ≤ (2 * Real.pi) * |t| ^ (-(1 / 2 : ℝ)) * Real.exp (-Real.pi * |t| / 2) := by
      intros t ht
      have h_gamma_bound : ∀ t : ℝ, 1 ≤ |t| → ‖Complex.Gamma (-t * Complex.I)‖ ≤ (2 * Real.pi) * |t| ^ (-(1 / 2 : ℝ)) * Real.exp (-Real.pi * |t| / 2) := by
        intro t ht
        have h_gamma_bound_aux : ∀ t : ℝ, 1 ≤ |t| → ‖Complex.Gamma (t * Complex.I)‖ ≤ (2 * Real.pi) * |t| ^ (-(1 / 2 : ℝ)) * Real.exp (-Real.pi * |t| / 2) := by
          have h_gamma_bound_aux : ∀ t : ℝ, 1 ≤ |t| → ‖Complex.Gamma (t * Complex.I)‖ ≤ (2 * Real.pi) * |t| ^ (-(1 / 2 : ℝ)) * Real.exp (-Real.pi * |t| / 2) := by
            intro t ht
            have h_gamma_bound_aux_step : ∀ t : ℝ, 1 ≤ t → ‖Complex.Gamma (t * Complex.I)‖ ≤ (2 * Real.pi) * t ^ (-(1 / 2 : ℝ)) * Real.exp (-Real.pi * t / 2) := by
              intro t ht;
              have h_gamma_it : ∀ t : ℝ, 0 < t → ‖Complex.Gamma (t * Complex.I)‖ = Real.sqrt (Real.pi / (t * Real.sinh (Real.pi * t))) := by
                intro t ht
                have h_gamma_it : Complex.Gamma (t * Complex.I) * Complex.Gamma (-t * Complex.I) = Real.pi / (t * Real.sinh (Real.pi * t)) := by
                  have := @Complex.Gamma_mul_Gamma_one_sub ( t * Complex.I );
                  convert congr_arg ( fun x => x / ( -t * Complex.I ) ) this using 1 <;> ring;
                  · field_simp;
                    rw [ show ( 1 - t * Complex.I : ℂ ) = - ( t * Complex.I ) + 1 by ring, Complex.Gamma_add_one ] <;> ring;
                    · simp +decide [ mul_assoc, mul_comm, mul_left_comm, ht.ne' ];
                    · norm_num [ Complex.ext_iff, ht.ne' ];
                  · norm_num [ Complex.sin_mul_I, Complex.sinh ] ; ring;
                    norm_num;
                have h_gamma_it_abs : Complex.Gamma (-t * Complex.I) = starRingEnd ℂ (Complex.Gamma (t * Complex.I)) := by
                  convert Complex.Gamma_conj ( t * Complex.I ) using 2 ; norm_num;
                simp_all +decide [ Complex.ext_iff, sq ];
                norm_cast at * ; simp_all +decide [ Complex.normSq, Complex.norm_def ];
              have h_sinh_bound : ∀ t : ℝ, 1 ≤ t → Real.sinh (Real.pi * t) ≥ Real.exp (Real.pi * t) / 4 := by
                intro t ht; rw [ Real.sinh_eq ] ; ring_nf; norm_num;
                nlinarith [ Real.pi_gt_three, Real.exp_pos ( Real.pi * t ), Real.exp_pos ( - ( Real.pi * t ) ), Real.exp_neg ( Real.pi * t ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( Real.pi * t ) ) ), Real.add_one_le_exp ( Real.pi * t ), Real.add_one_le_exp ( - ( Real.pi * t ) ) ];
              have h_gamma_bound_subst : ∀ t : ℝ, 1 ≤ t → ‖Complex.Gamma (t * Complex.I)‖ ≤ Real.sqrt (4 * Real.pi / (t * Real.exp (Real.pi * t))) := by
                intro t ht; rw [ h_gamma_it t ( by positivity ) ] ; exact Real.sqrt_le_sqrt <| by rw [ div_le_div_iff₀ ] <;> nlinarith [ Real.pi_pos, Real.exp_pos ( Real.pi * t ), mul_pos ( Real.pi_pos ) ( Real.exp_pos ( Real.pi * t ) ), h_sinh_bound t ht, mul_pos ( Real.pi_pos ) ( show 0 < t by positivity ) ] ;
              refine le_trans ( h_gamma_bound_subst t ht ) ?_;
              rw [ Real.sqrt_le_left ] <;> ring <;> norm_num [ Real.exp_neg, Real.exp_pos, Real.pi_pos, ne_of_gt, Real.rpow_pos_of_pos, ht ];
              · norm_num [ sq, ← Real.exp_add, ← Real.exp_neg, Real.rpow_neg ( by positivity : 0 ≤ t ) ] ; ring_nf ; norm_num [ Real.pi_pos.le, ne_of_gt, Real.pi_pos, ht ];
                rw [ ← Real.sqrt_eq_rpow, Real.sq_sqrt ( by positivity ) ] ; ring_nf;
                exact mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( by nlinarith [ Real.pi_gt_three ] ) ( by positivity ) ) ( by positivity );
              · positivity
            cases abs_cases t <;> simp +decide [ * ] at * ; aesop;
            convert h_gamma_bound_aux_step ( -t ) ( by linarith ) using 1 ; norm_num ; ring;
            · have := Complex.Gamma_conj ( t * Complex.I ) ; aesop;
            · grind;
          assumption
        convert h_gamma_bound_aux ( -t ) ( by simpa ) using 1 ; norm_num;
        norm_num;
      exact h_gamma_bound t ht;
    have h_gamma_rel : ∀ t : ℝ, 1 ≤ |t| → ‖Complex.Gamma (1 - t * Complex.I)‖ = |t| * ‖Complex.Gamma (-t * Complex.I)‖ := by
      intros t ht
      have h_gamma_rel : Complex.Gamma (1 - t * Complex.I) = -t * Complex.I * Complex.Gamma (-t * Complex.I) := by
        rw [ ← Complex.Gamma_add_one ] <;> ring ; norm_num [ Complex.ext_iff, ht ];
        cases abs_cases t <;> linarith;
      norm_num [ h_gamma_rel, Complex.norm_I ];
    refine' ⟨ 2 * Real.pi, by positivity, fun t ht => _ ⟩;
    convert le_trans ( h_gamma_rel t ht ▸ mul_le_mul_of_nonneg_left ( h_gamma_bound t ht ) ( abs_nonneg t ) ) _ using 1 ; ring;
    rw [ show ( 1 / 2 : ℝ ) = -1 / 2 + 1 by norm_num, Real.rpow_add ] <;> norm_num <;> ring_nf <;> norm_num [ ht ];
    cases abs_cases t <;> linarith

/-
Bound for the prefactor in the Zeta functional equation on the imaginary axis.
-/
lemma zeta_prefactor_bound : ∃ C > 0, ∀ (t : ℝ) (ht : 1 ≤ |t|),
  norm ((2 : ℂ) ^ (t * Complex.I) * (Real.pi : ℂ) ^ (t * Complex.I - 1) * Complex.sin (Real.pi * (t * Complex.I) / 2) * Complex.Gamma (1 - t * Complex.I)) ≤ C * |t| ^ (1/2 : ℝ) := by
    have h_bound : ∃ C > 0, ∀ t : ℝ, 1 ≤ |t| →
      ‖Complex.Gamma (1 - (t * Complex.I))‖ ≤ C * |t| ^ (1 / 2 : ℝ) * Real.exp (-Real.pi * |t| / 2) := by
        convert gamma_bound_imaginary_axis;
    obtain ⟨C₁, hC₁_pos, hC₁⟩ : ∃ C₁ > 0, ∀ t : ℝ, 1 ≤ |t| → ‖Complex.sin (Real.pi * ((t : ℂ) * Complex.I) / 2)‖ ≤ C₁ * Real.exp (Real.pi * |t| / 2) := by
      have h_sin_bound : ∀ t : ℝ, ‖Complex.sin ((Real.pi * (t * Complex.I)) / 2)‖ ≤ Real.exp (Real.pi * |t| / 2) := by
        intro t; rw [ Complex.sin ] ; ring_nf; norm_num [ Complex.norm_exp ] ;
        refine' le_trans ( norm_add_le _ _ ) _ ; norm_num [ Complex.norm_exp ] ; ring ; norm_num [ abs_mul, abs_of_nonneg, Real.pi_pos.le ];
        cases abs_cases t <;> nlinarith [ Real.pi_pos, Real.exp_pos ( Real.pi * t * ( 1 / 2 ) ), Real.exp_pos ( - ( Real.pi * t * ( 1 / 2 ) ) ), Real.exp_le_exp.mpr ( by nlinarith [ Real.pi_pos ] : Real.pi * t * ( 1 / 2 ) ≤ Real.pi * |t| * ( 1 / 2 ) ), Real.exp_le_exp.mpr ( by nlinarith [ Real.pi_pos ] : - ( Real.pi * t * ( 1 / 2 ) ) ≤ Real.pi * |t| * ( 1 / 2 ) ) ];
      exact ⟨ 1, zero_lt_one, fun t ht => le_trans ( h_sin_bound t ) ( by norm_num ) ⟩;
    have h_bound_2 : ∀ t : ℝ, ‖(2 : ℂ) ^ ((t : ℂ) * Complex.I)‖ = 1 := by
      norm_num [ Complex.norm_cpow_of_ne_zero ];
    have h_bound_pi : ∀ t : ℝ, ‖(Real.pi : ℂ) ^ ((t : ℂ) * Complex.I - 1)‖ ≤ 1 / Real.pi := by
      intro t; rw [ Complex.norm_cpow_of_ne_zero ( Complex.ofReal_ne_zero.mpr Real.pi_ne_zero ) ] ; norm_num [ Complex.norm_exp ];
      norm_num [ Real.rpow_neg_one, abs_of_pos Real.pi_pos, Complex.arg_ofReal_of_nonneg Real.pi_pos.le ];
    obtain ⟨ C₂, hC₂_pos, hC₂ ⟩ := h_bound; use C₁ * ( 1 / Real.pi ) * C₂; refine' ⟨ mul_pos ( mul_pos hC₁_pos ( one_div_pos.mpr Real.pi_pos ) ) hC₂_pos, fun t ht => _ ⟩ ; simp_all +decide [ mul_assoc, mul_left_comm ] ;
    refine' le_trans ( mul_le_mul ( h_bound_pi t ) ( mul_le_mul ( hC₁ t ht ) ( hC₂ t ht ) ( by positivity ) ( by positivity ) ) ( by positivity ) ( by positivity ) ) _ ; ring_nf ; norm_num [ Real.pi_pos.ne' ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ] ;
    norm_num [ mul_assoc, mul_comm, mul_left_comm, ← Real.exp_add ]

/-
Bound for the harmonic series partial sum.
-/
lemma harmonic_series_bound (x : ℝ) (hx : 1 ≤ x) :
  ∑ n ∈ Finset.Icc 1 (Nat.floor x), (n : ℝ)⁻¹ ≤ Real.log x + 1 := by
    have h_harmonic_le : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ ≤ Real.log N + 1 := by
      intro N hN
      induction N with
      | zero => omega
      | succ N ih =>
        by_cases hN1 : N = 0
        · subst hN1; simp [Finset.Icc_self]
        · have hN_ge : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN1
          have ih' := ih hN_ge
          have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
          have hN1_pos : (0 : ℝ) < (N : ℝ) + 1 := by linarith
          have h_split : Finset.Icc 1 (N + 1) = Finset.Icc 1 N ∪ {N + 1} := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega
          have h_disj : Disjoint (Finset.Icc 1 N) {N + 1} := by
            simp only [Finset.disjoint_singleton_right, Finset.mem_Icc]; omega
          rw [h_split, Finset.sum_union h_disj, Finset.sum_singleton]
          push_cast
          -- Key: 1/(N+1) ≤ log(N+1) - log(N)
          -- From one_sub_inv_le_log_of_pos with x = (N+1)/N:
          -- 1 - (N/(N+1)) ≤ log((N+1)/N) = log(N+1) - log(N)
          have h_inv_le_log : ((N : ℝ) + 1)⁻¹ ≤ Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) := by
            have hN1_pos : (0 : ℝ) < (N : ℝ) + 1 := by linarith
            have h_ratio_pos : (0 : ℝ) < ((N : ℝ) + 1) / (N : ℝ) := by positivity
            have h1 : 1 - (((N : ℝ) + 1) / (N : ℝ))⁻¹ ≤ Real.log (((N : ℝ) + 1) / (N : ℝ)) :=
              Real.one_sub_inv_le_log_of_pos h_ratio_pos
            rw [Real.log_div (by linarith) (by linarith)] at h1
            have h2 : (((N : ℝ) + 1) / (N : ℝ))⁻¹ = (N : ℝ) / ((N : ℝ) + 1) := by
              field_simp
            rw [h2] at h1
            have h3 : 1 - (N : ℝ) / ((N : ℝ) + 1) = ((N : ℝ) + 1)⁻¹ := by field_simp; ring
            linarith
          linarith
    exact le_trans ( h_harmonic_le _ ( Nat.floor_pos.mpr hx ) ) ( by simpa using Real.log_le_log ( Nat.cast_pos.mpr ( Nat.floor_pos.mpr hx ) ) ( Nat.floor_le ( by positivity ) ) )

/-
Bound for the partial sum of Zeta on the line Re(s)=1.
-/
lemma zeta_partial_sum_bound (t : ℝ) (ht : 1 ≤ |t|) :
  norm (∑ n ∈ Finset.Icc 1 (Nat.floor |t|), (n : ℂ) ^ (-(1 + t * Complex.I))) ≤ Real.log |t| + 1 := by
    have h_norm : ‖∑ n ∈ Finset.Icc 1 (Nat.floor |t|), (n : ℂ) ^ (-(t * Complex.I + 1 : ℂ))‖ ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor |t|), (n : ℝ)⁻¹ := by
      refine' le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun x hx => _ );
      norm_num [ Complex.norm_cpow_of_ne_zero ( Nat.cast_ne_zero.mpr <| ne_of_gt <| Finset.mem_Icc.mp hx |>.1 ) ];
      rw [ Real.rpow_neg_one ];
    have h_harmonic : ∑ n ∈ Finset.Icc 1 (Nat.floor |t|), (n : ℝ)⁻¹ ≤ Real.log |t| + 1 := by
      convert harmonic_series_bound |t| ht using 1;
    simpa only [ neg_add, add_comm ] using h_norm.trans h_harmonic

/-
Existence of a constant bound for the error term in the Zeta approximation (trivial bound).
-/
lemma zeta_approx_error_term_bound (t : ℝ) (ht : 1 ≤ |t|) :
  ∃ C > 0, norm (riemannZeta (1 + t * Complex.I) - (∑ n ∈ Finset.Icc 1 (Nat.floor |t|), (n : ℂ) ^ (-(1 + t * Complex.I))) - (|t| ^ (1 - (1 + t * Complex.I)) / ((1 + t * Complex.I) - 1))) ≤ C := by
    set x := |t| with hx_def
    have hx_ge_one : 1 ≤ x := by
      exact ht;
    exact ⟨ Max.max ( ‖riemannZeta ( 1 + t * Complex.I ) - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ( n : ℂ ) ^ ( - ( 1 + t * Complex.I ) ) - ( x : ℂ ) ^ ( 1 - ( 1 + t * Complex.I ) ) / ( 1 + t * Complex.I - 1 )‖ ) 1, by positivity, le_max_left _ _ ⟩

end ZetaBoundsPartialSum
