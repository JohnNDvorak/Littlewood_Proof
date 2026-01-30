/-
Dirichlet series convergence infrastructure from Aristotle.

Provides summability lemmas for Dirichlet series with logarithmic weights,
Fubini-style sum swaps, and derivative bounds.

Note: The `dirichletSeriesA` and `abscissaOfConvA` definitions use the suffix "A"
to avoid conflicts with existing definitions in CoreLemmas/LandauLemma.lean.

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

namespace DirichletSeriesConv

/-
Definition of a Dirichlet series f(s) = Σ aₙ/n^s.
-/
noncomputable def dirichletSeriesA (a : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (a n : ℂ) * (n : ℂ)^(-s)

/-
Definition of the abscissa of convergence σ_c.
-/
def abscissaOfConvA (a : ℕ → ℝ) : ℝ :=
  sInf {σ : ℝ | ∀ s : ℂ, σ < s.re → Summable (fun n => (a n : ℂ) * (n : ℂ)^(-s))}

/-
Helper lemma for Landau's Lemma: Swapping sums to prove convergence at a point to the left.
-/
lemma landau_lemma_swap_sums (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (s₀ δ : ℝ) (hδ : 0 < δ)
    (h_conv : Summable (fun k : ℕ => (δ ^ k / k.factorial) * (∑' n, a n * (Real.log n) ^ k * (n : ℝ) ^ (-s₀))))
    (h_inner_conv : ∀ k, Summable (fun n => a n * (Real.log n) ^ k * (n : ℝ) ^ (-s₀))) :
    Summable (fun n => a n * (n : ℝ) ^ (-(s₀ - δ))) := by
      have h_fubini : Summable (fun (n : ℕ) => ∑' k : ℕ, (a n) * ((δ * Real.log n) ^ k) / ((Nat.factorial k) : ℝ) * (n : ℝ) ^ (-s₀ : ℝ)) := by
        have h_fubini : Summable (fun (n : ℕ) => ∑' k : ℕ, (δ ^ k / (Nat.factorial k)) * (a n) * ((Real.log n) ^ k) * (n : ℝ) ^ (-s₀ : ℝ)) := by
          have h_fubini : ∀ k : ℕ, Summable (fun (n : ℕ) => (δ ^ k / (Nat.factorial k)) * (a n) * ((Real.log n) ^ k) * (n : ℝ) ^ (-s₀ : ℝ)) := by
            exact fun k => by simpa only [ mul_assoc ] using Summable.mul_left _ ( h_inner_conv k ) ;
          have h_fubini : Summable (fun (k : ℕ) => ∑' n : ℕ, (δ ^ k / (Nat.factorial k)) * (a n) * ((Real.log n) ^ k) * (n : ℝ) ^ (-s₀ : ℝ)) := by
            convert h_conv using 2 ; simp +decide [ mul_assoc, tsum_mul_left ];
          refine' summable_of_sum_le _ _;
          exact ∑' k : ℕ, ∑' n : ℕ, δ ^ k / ( k.factorial : ℝ ) * a n * Real.log n ^ k * ( n : ℝ ) ^ ( -s₀ );
          · intro n; exact tsum_nonneg fun k => mul_nonneg ( mul_nonneg ( mul_nonneg ( div_nonneg ( pow_nonneg hδ.le _ ) ( Nat.cast_nonneg _ ) ) ( ha _ ) ) ( pow_nonneg ( Real.log_natCast_nonneg _ ) _ ) ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ;
          · intro u;
            have h_fubini : ∑ x ∈ u, ∑' k : ℕ, (δ ^ k / (Nat.factorial k)) * (a x) * ((Real.log x) ^ k) * (x : ℝ) ^ (-s₀ : ℝ) ≤ ∑' k : ℕ, ∑ x ∈ u, (δ ^ k / (Nat.factorial k)) * (a x) * ((Real.log x) ^ k) * (x : ℝ) ^ (-s₀ : ℝ) := by
              have h_fubini : ∀ {f : ℕ → ℕ → ℝ}, (∀ k, Summable (fun n => f k n)) → (∀ n, Summable (fun k => f k n)) → ∑ x ∈ u, ∑' k, f k x ≤ ∑' k, ∑ x ∈ u, f k x := by
                intros f hf_summable_k hf_summable_n
                have h_fubini : ∑ x ∈ u, ∑' k, f k x = ∑' k, ∑ x ∈ u, f k x := by
                  exact?;
                rw [h_fubini];
              apply h_fubini;
              · assumption;
              · intro n;
                have := Real.summable_pow_div_factorial ( δ * Real.log n );
                convert this.mul_left ( a n * ( n : ℝ ) ^ ( -s₀ ) ) using 2 ; ring;
            refine' le_trans h_fubini ( Summable.tsum_le_tsum _ _ _ );
            · exact fun k => Summable.sum_le_tsum ( u ) ( fun _ _ => mul_nonneg ( mul_nonneg ( mul_nonneg ( div_nonneg ( pow_nonneg hδ.le _ ) ( Nat.cast_nonneg _ ) ) ( ha _ ) ) ( pow_nonneg ( Real.log_natCast_nonneg _ ) _ ) ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ( by aesop );
            · refine' Summable.of_nonneg_of_le ( fun k => Finset.sum_nonneg fun _ _ => mul_nonneg ( mul_nonneg ( mul_nonneg ( div_nonneg ( pow_nonneg hδ.le _ ) ( Nat.cast_nonneg _ ) ) ( ha _ ) ) ( pow_nonneg ( Real.log_natCast_nonneg _ ) _ ) ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ( fun k => _ ) ‹_›;
              exact Summable.sum_le_tsum ( u ) ( fun _ _ => mul_nonneg ( mul_nonneg ( mul_nonneg ( div_nonneg ( pow_nonneg hδ.le _ ) ( Nat.cast_nonneg _ ) ) ( ha _ ) ) ( pow_nonneg ( Real.log_natCast_nonneg _ ) _ ) ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ( by aesop );
            · assumption;
        convert h_fubini using 3 ; ring;
        ac_rfl;
      have h_eq : ∀ n : ℕ, n ≥ 1 → ∑' k : ℕ, a n * ((δ * Real.log n) ^ k) / ((Nat.factorial k) : ℝ) * (n : ℝ) ^ (-s₀ : ℝ) = a n * (n : ℝ) ^ (-(s₀ - δ) : ℝ) := by
        have h_taylor : ∀ n : ℕ, n ≥ 1 → ∑' k : ℕ, (δ * Real.log n) ^ k / ((Nat.factorial k) : ℝ) = Real.exp (δ * Real.log n) := by
          norm_num [ Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div ];
        simp_all +decide [ mul_assoc, mul_div_assoc, tsum_mul_left, tsum_mul_right ];
        intro n hn; rw [ Real.rpow_def_of_pos ( by positivity ), Real.rpow_def_of_pos ( by positivity ) ] ; ring ; norm_num [ Real.exp_add, Real.exp_neg, Real.exp_log ( by positivity : 0 < ( n : ℝ ) ) ] ;
        exact Or.inl ( by rw [ ← div_eq_mul_inv, ← Real.exp_sub ] );
      rw [ ← summable_nat_add_iff 1 ] at *;
      exact h_fubini.congr fun n => h_eq _ le_add_self ▸ rfl ;

/-
If Σ a_n n^{-σ} converges, then Σ a_n log n n^{-(σ+δ)} converges for δ > 0.
-/
lemma summable_log_mul_of_summable_mul_pow (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (σ : ℝ) (h : Summable (fun n => a n * (n : ℝ)^(-σ))) (δ : ℝ) (hδ : δ > 0) :
    Summable (fun n => a n * Real.log n * (n : ℝ)^(-(σ + δ))) := by
      suffices h_rewrite : Summable (fun n => a n * (n : ℝ) ^ (-σ) * (Real.log n * (n : ℝ) ^ (-δ))) by
        convert h_rewrite using 2 ; ring ;
        by_cases hn : ‹_› = 0 <;> simp +decide [ hn, mul_assoc, ← Real.rpow_add' ] ; ring;
        exact Or.inl <| Or.inl <| by rw [ ← Real.rpow_add <| by positivity ] ; ring;
      have h_bound : ∃ C > 0, ∀ n : ℕ, n ≥ 2 → (Real.log n * (n : ℝ) ^ (-δ)) ≤ C := by
        have h_bound : ∀ n : ℕ, n ≥ 2 → (Real.log n * (n : ℝ) ^ (-δ)) ≤ 1 / (Real.exp 1 * δ) := by
          field_simp;
          intro n hn;
          rw [ Real.rpow_def_of_pos ( by positivity ) ];
          norm_num [ mul_assoc, ← Real.exp_add ];
          nlinarith [ Real.exp_pos ( - ( Real.log n * δ ) + 1 ), Real.exp_neg ( - ( Real.log n * δ ) + 1 ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( - ( Real.log n * δ ) + 1 ) ) ), Real.add_one_le_exp ( - ( Real.log n * δ ) + 1 ), Real.add_one_le_exp ( - ( - ( Real.log n * δ ) + 1 ) ), Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; linarith ) ];
        exact ⟨ _, by positivity, h_bound ⟩;
      refine' .of_nonneg_of_le ( fun n => mul_nonneg ( mul_nonneg ( ha n ) ( Real.rpow_nonneg ( Nat.cast_nonneg n ) _ ) ) ( mul_nonneg ( Real.log_natCast_nonneg n ) ( Real.rpow_nonneg ( Nat.cast_nonneg n ) _ ) ) ) ( fun n => _ ) ( h.mul_right h_bound.choose );
      rcases n with ( _ | _ | n ) <;> norm_num at *;
      · exact mul_nonneg ( mul_nonneg ( ha _ ) ( by positivity ) ) ( le_of_lt h_bound.choose_spec.1 );
      · exact mul_nonneg ( ha _ ) h_bound.choose_spec.1.le;
      · exact mul_le_mul_of_nonneg_left ( mod_cast h_bound.choose_spec.2 ( n + 2 ) ( by linarith ) ) ( mul_nonneg ( ha _ ) ( Real.rpow_nonneg ( by linarith ) _ ) )

/-
Generalization: If Σ a_n n^{-σ} converges, then Σ a_n (log n)^k n^{-(σ+δ)} converges for any k and δ > 0.
-/
lemma summable_log_pow_mul_of_summable_mul_pow (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (σ : ℝ) (h : Summable (fun n => a n * (n : ℝ)^(-σ))) (k : ℕ) (δ : ℝ) (hδ : δ > 0) :
    Summable (fun n => a n * (Real.log n)^k * (n : ℝ)^(-(σ + δ))) := by
      have h_ind : ∀ k : ℕ, ∀ δ > 0, Summable (fun n => (a n : ℝ) * (Real.log n) ^ k * (n : ℝ) ^ (-(σ + δ))) := by
        intro k hδ;
        induction' k with k ih generalizing hδ;
        · field_simp;
          intro hhδ;
          have h_compare : ∀ n : ℕ, n ≥ 1 → (a n : ℝ) * (n : ℝ) ^ (-(σ + hδ)) ≤ (a n : ℝ) * (n : ℝ) ^ (-σ) := by
            exact fun n hn => mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow_of_exponent_le ( mod_cast hn ) ( by linarith ) ) ( ha n );
          rw [ ← summable_nat_add_iff 1 ] at *;
          exact Summable.of_nonneg_of_le ( fun n => mul_nonneg ( ha _ ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ( fun n => h_compare _ le_add_self ) h;
        · intro hδ_pos;
          obtain ⟨C, hC⟩ : ∃ C > 0, ∀ n : ℕ, n ≥ 2 → (Real.log n) * (n : ℝ) ^ (-(hδ / 2)) ≤ C := by
            use 2 / hδ;
            refine' ⟨ by positivity, fun n hn => _ ⟩;
            rw [ Real.rpow_def_of_pos ( by positivity ) ];
            field_simp;
            nlinarith [ Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; linarith ), Real.log_le_sub_one_of_pos ( show ( n : ℝ ) > 0 by positivity ), Real.exp_pos ( - ( Real.log ( n : ℝ ) * hδ / 2 ) ), Real.exp_neg ( Real.log ( n : ℝ ) * hδ / 2 ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos ( Real.log ( n : ℝ ) * hδ / 2 ) ) ), Real.add_one_le_exp ( Real.log ( n : ℝ ) * hδ / 2 ), Real.add_one_le_exp ( - ( Real.log ( n : ℝ ) * hδ / 2 ) ) ];
          have h_dominate : ∀ n : ℕ, n ≥ 2 → (a n : ℝ) * (Real.log n) ^ (k + 1) * (n : ℝ) ^ (-(σ + hδ)) ≤ C * (a n : ℝ) * (Real.log n) ^ k * (n : ℝ) ^ (-(σ + hδ / 2)) := by
            intro n hn; convert mul_le_mul_of_nonneg_right ( hC.2 n hn ) ( show 0 ≤ a n * Real.log n ^ k * ( n : ℝ ) ^ ( - ( σ + hδ / 2 ) ) by exact mul_nonneg ( mul_nonneg ( ha n ) ( pow_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ) _ ) ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) using 1 ; ring;
            · norm_num [ mul_assoc, ← Real.rpow_add ( by positivity : 0 < ( n : ℝ ) ) ] ; ring;
              norm_num;
            · ring;
          rw [ ← summable_nat_add_iff 2 ];
          exact Summable.of_nonneg_of_le ( fun n => mul_nonneg ( mul_nonneg ( ha _ ) ( pow_nonneg ( Real.log_natCast_nonneg _ ) _ ) ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ( fun n => h_dominate _ ( by linarith ) ) ( by simpa [ mul_assoc ] using Summable.mul_left _ ( ih ( hδ / 2 ) ( half_pos hδ_pos ) |> Summable.comp_injective <| add_left_injective 2 ) );
      exact h_ind k δ hδ

/-
Existence of a local summable bound for the derivative of a Dirichlet series.
-/
lemma dirichletSeries_deriv_bound (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (s : ℂ) (σ : ℝ) (hσ : σ < s.re)
    (h_conv : ∀ z : ℂ, σ < z.re → Summable (fun n => (a n : ℂ) * (n : ℂ)^(-z))) :
    ∃ r > 0, ∃ b : ℕ → ℝ, Summable b ∧ ∀ z : ℂ, ‖z - s‖ < r → ∀ n, ‖(a n : ℂ) * (-Real.log n) * (n : ℂ)^(-z)‖ ≤ b n := by
      set δ := (s.re - σ) / 2 with hdelta_pos
      have hdelta_pos' : 0 < δ := by
        linarith;
      set σ' := σ + δ with hσ'_pos
      have hσ'_pos' : Summable (fun n => a n * (Real.log n) * (n : ℝ)^(-σ')) := by
        convert summable_log_mul_of_summable_mul_pow a ha ( σ + δ / 2 ) ( show Summable ( fun n : ℕ => a n * ( n : ℝ ) ^ ( - ( σ + δ / 2 ) ) ) from ?_ ) ( δ / 2 ) ( by linarith ) using 1;
        · grind;
        · have := h_conv ( σ + δ / 2 ) ( by norm_num; linarith );
          convert this.norm using 2 ; norm_cast ; norm_num [ Complex.norm_def, Complex.normSq ];
          rw [ abs_of_nonneg ( ha _ ) ] ; norm_cast ; norm_num [ Real.rpow_def_of_nonneg ] ; ring;
          split_ifs <;> simp_all +decide [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def ] ; ring;
          · norm_num [ show s.re = -σ * 3 by linarith ] at *;
            ring_nf at * ; aesop;
          · split_ifs <;> norm_num [ Complex.ext_iff ] at * ; aesop;
          · exact Or.inl ( by rw [ Real.sqrt_sq ( by positivity ) ] ; ring );
      set r := δ with hr
      have hr_pos : 0 < r := by
        exact hdelta_pos'
      have hr_bound : ∀ z : ℂ, ‖z - s‖ < r → ∀ n : ℕ, ‖(a n) * (-(Real.log n)) * (n : ℂ)^(-z)‖ ≤ a n * (Real.log n) * (n : ℝ)^(-σ') := by
        intro z hz n; by_cases hn : n = 0 <;> simp_all +decide [ Complex.norm_exp, Complex.norm_cpow_of_ne_zero ] ;
        norm_num [ abs_of_nonneg ( ha n ), Complex.norm_def, Complex.normSq, Complex.log_re, Complex.log_im ];
        rw [ Real.sqrt_mul_self ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hn ) ) ) ];
        exact mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.one_le_iff_ne_zero.mpr hn ) ( by linarith [ abs_lt.mp ( show |z.re - s.re| < ( s.re - σ ) / 2 by simpa using lt_of_le_of_lt ( Complex.abs_re_le_norm _ ) hz ) ] ) ) ( mul_nonneg ( ha n ) ( Real.log_nonneg ( mod_cast Nat.one_le_iff_ne_zero.mpr hn ) ) );
      exact ⟨ r, hr_pos, _, hσ'_pos', hr_bound ⟩

end DirichletSeriesConv
