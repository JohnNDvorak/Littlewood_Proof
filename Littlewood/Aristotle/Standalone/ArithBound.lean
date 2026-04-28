import Mathlib

/-! # Arithmetic bound for finite product lower bound

Key arithmetic inequality: exp(−K·R₀^{7/4}) ≤ (δ/(6R₀))^|S| · exp(−∑R/‖ρ‖).
The constant K = 100·(C_cnt + C_inner + 1)². -/

set_option maxHeartbeats 4000000

open Real Finset

noncomputable section

/-
For C > 0 and I > 0:
    8·C·log(96·C+12) + 56·C + 4·I ≤ 100·(C+I+1)².
-/
theorem constant_absorbs_log (C I : ℝ) (hC : 0 < C) (hI : 0 < I) :
    8 * C * Real.log (96 * C + 12) + 56 * C + 4 * I ≤ 100 * (C + I + 1) ^ 2 := by
  -- Split the inequality into two parts: $C \ge 1$ and $C < 1$.
  by_cases hC_ge_1 : C ≥ 1;
  · -- We'll use that $Real.log (96 * C + 12) ≤ 5 + Real.log C$ for $C ≥ 1$.
    have h_log_bound : Real.log (96 * C + 12) ≤ 5 + Real.log C := by
      rw [ Real.log_le_iff_le_exp, Real.exp_add, Real.exp_log ] <;> try linarith;
      have := Real.exp_one_gt_d9.le ; norm_num1 at * ; rw [ show Real.exp 5 = ( Real.exp 1 ) ^ 5 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; nlinarith [ pow_le_pow_left₀ ( by positivity ) this 5, pow_pos hC 2, pow_pos hC 3, pow_pos hC 4 ];
    nlinarith [ Real.log_le_sub_one_of_pos hC ];
  · -- For C < 1, use the bound log(96C + 12) ≤ log(108).
    have h_log_bound : Real.log (96 * C + 12) ≤ Real.log 108 := by
      exact Real.log_le_log ( by positivity ) ( by linarith );
    -- Use the bound log(108) < 5.
    have h_log_108_bound : Real.log 108 < 5 := by
      norm_num [ Real.log_lt_iff_lt_exp ];
      have := Real.exp_one_gt_d9.le ; norm_num at * ; rw [ show Real.exp 5 = ( Real.exp 1 ) ^ 5 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; nlinarith [ pow_le_pow_left₀ ( by positivity ) this 5 ];
    nlinarith [ sq_nonneg ( C + I + 1 - 1 ) ]

/-
For n ≤ C·(4R₀)^{3/2} and R₀ ≥ 1:
    n·log(12n+12) ≤ (8C·log(96C+12) + 48C)·R₀^{7/4}.
Uses log(12n+12) ≤ log((96C+12)·R₀^{3/2}) = log(96C+12) + (3/2)·log(R₀)
and log(R₀) ≤ 4·R₀^{1/4}, so (3/2)·log(R₀) ≤ 6·R₀^{1/4}.
Then n·(...) ≤ 8C·R₀^{3/2}·(log(96C+12) + 6·R₀^{1/4})
= 8C·log(96C+12)·R₀^{3/2} + 48C·R₀^{7/4}
≤ (8C·log(96C+12) + 48C)·R₀^{7/4}  since R₀^{3/2} ≤ R₀^{7/4}.
-/
theorem card_log_bound
    (C R₀ : ℝ) (hC : 0 < C) (hR₀ : 1 ≤ R₀)
    (n : ℕ) (hn : (n : ℝ) ≤ C * (4 * R₀) ^ (3 / 2 : ℝ)) :
    (n : ℝ) * Real.log (12 * ↑n + 12) ≤
      (8 * C * Real.log (96 * C + 12) + 48 * C) * R₀ ^ (7 / 4 : ℝ) := by
  -- We have n ≤ C*(4R₀)^{3/2}.
  have h_bound : (12 * n + 12 : ℝ) ≤ (96 * C + 12) * R₀^(3 / 2 : ℝ) := by
    rw [ show ( 4 * R₀ ) ^ ( 3 / 2 : ℝ ) = 4 ^ ( 3 / 2 : ℝ ) * R₀ ^ ( 3 / 2 : ℝ ) by rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] ] at hn ; norm_num at * ; nlinarith [ Real.one_le_rpow hR₀ ( by norm_num : ( 0 :ℝ ) ≤ 3/2 ) ];
  -- So n*log(12*n+12) ≤ n*(log(96*C+12) + 6*R₀^{1/4}).
  have h_log_bound : (n : ℝ) * Real.log (12 * n + 12) ≤ (n : ℝ) * (Real.log (96 * C + 12) + 6 * R₀^(1 / 4 : ℝ)) := by
    refine mul_le_mul_of_nonneg_left ?_ ( Nat.cast_nonneg _ );
    refine' le_trans ( Real.log_le_log ( by positivity ) h_bound ) _;
    rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_rpow ( by positivity ) ];
    have := Real.log_le_sub_one_of_pos ( by positivity : 0 < R₀ ^ ( 1 / 4 : ℝ ) );
    rw [ Real.log_rpow ( by positivity ) ] at this ; linarith;
  -- We have n ≤ 8*C*R₀^{3/2}.
  have h_n_bound : (n : ℝ) ≤ (8 * C) * R₀^(3 / 2 : ℝ) := by
    convert hn using 1 ; rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring;
  refine le_trans h_log_bound ?_;
  refine le_trans ( mul_le_mul_of_nonneg_right h_n_bound <| add_nonneg ( Real.log_nonneg <| by linarith ) <| by positivity ) ?_;
  ring_nf;
  norm_num [ mul_assoc, mul_left_comm, ← Real.rpow_add ( by positivity : 0 < R₀ ) ];
  exact mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_right ( Real.rpow_le_rpow_of_exponent_le hR₀ ( by norm_num ) ) ( by exact mul_nonneg ( Real.log_nonneg ( by linarith ) ) ( by norm_num ) ) ) hC.le

/-
∑_{n∈S} R/‖ρₙ‖ ≤ (4·C_inner + 8·C_cnt)·R₀^{3/2}.
Split S into inner (‖ρ‖ ≤ 2R₀) and outer (2R₀ < ‖ρ‖ ≤ 4R₀).
Inner: use hinner_bound with R₁=4R₀. Outer: R/‖ρ‖ ≤ 1, count ≤ |S|.
-/
theorem reciprocal_sum_bound
    (zeros : ℕ → ℂ) (hne : ∀ n, zeros n ≠ 0)
    (R R₀ C_cnt : ℝ) (hR₀ : 1 ≤ R₀) (hC_cnt : 0 < C_cnt)
    (hR_lo : R₀ ≤ R) (hR_hi : R ≤ 2 * R₀)
    (S : Finset ℕ) (hS_mem : ∀ n, n ∈ S ↔ ‖zeros n‖ ≤ 4 * R₀)
    (hS_card : (S.card : ℝ) ≤ C_cnt * (4 * R₀) ^ (3 / 2 : ℝ))
    (C_inner : ℝ) (hC_inner : 0 < C_inner)
    (hinner_bound : ∀ (R₁ : ℝ), 4 ≤ R₁ →
      ∃ S_inner : Finset ℕ,
        (∀ n, n ∈ S_inner ↔ ‖zeros n‖ ≤ R₁ / 2) ∧
        ∑ n ∈ S_inner, R₁ / ‖zeros n‖ ≤ C_inner * R₁ ^ (3 / 2 : ℝ)) :
    ∑ n ∈ S, R / ‖zeros n‖ ≤ (4 * C_inner + 8 * C_cnt) * R₀ ^ (3 / 2 : ℝ) := by
  obtain ⟨ S_inner, hS_inner_mem, hS_inner_bound ⟩ := hinner_bound ( 4 * R₀ ) ( by linarith ) ; simp_all +decide [ division_def ] ;
  -- For the inner part: $\sum_{n \in S \cap S_{\text{inner}}} R / \| \rho_n \| \leq \sum_{n \in S_{\text{inner}}} R / \| \rho_n \|$.
  have h_inner_sum : ∑ n ∈ S.filter (fun n => n ∈ S_inner), R / ‖zeros n‖ ≤ (1 / 2) * C_inner * (4 * R₀) ^ (3 / 2 : ℝ) := by
    have h_inner_sum : ∑ n ∈ S.filter (fun n => n ∈ S_inner), R / ‖zeros n‖ ≤ (R / (4 * R₀)) * ∑ n ∈ S_inner, (4 * R₀) / ‖zeros n‖ := by
      rw [ Finset.mul_sum _ _ _ ] ; rw [ ← Finset.sum_subset ( show S.filter ( fun n => n ∈ S_inner ) ⊆ S_inner from fun x hx => by aesop ) ] ; ring_nf;
      · norm_num [ show R₀ ≠ 0 by linarith ];
      · grind;
    norm_num [ div_eq_mul_inv ] at *;
    exact h_inner_sum.trans ( by nlinarith [ show 0 ≤ C_inner * ( 4 * R₀ ) ^ ( 3 / 2 : ℝ ) by positivity, show 0 ≤ R * ( R₀⁻¹ * ( 1 / 4 ) ) by exact mul_nonneg ( by linarith ) ( by positivity ), mul_inv_cancel_left₀ ( by positivity : R₀ ≠ 0 ) R ] );
  -- For the outer part: $\sum_{n \in S \setminus S_{\text{inner}}} R / \| \rho_n \| \leq |S| \leq C_{\text{cnt}} \cdot (4R₀)^{3/2}$.
  have h_outer_sum : ∑ n ∈ S.filter (fun n => n ∉ S_inner), R / ‖zeros n‖ ≤ C_cnt * (4 * R₀) ^ (3 / 2 : ℝ) := by
    -- Since $n \notin S_{\text{inner}}$, we have $\| \rho_n \| > 2R₀$, thus $R / \| \rho_n \| \leq 1$.
    have h_outer_bound : ∀ n ∈ S.filter (fun n => n ∉ S_inner), R / ‖zeros n‖ ≤ 1 := by
      simp +zetaDelta at *;
      exact fun n hn hn' => by rw [ div_le_iff₀ ( norm_pos_iff.mpr ( hne n ) ) ] ; linarith [ hS_mem n |>.1 hn, hS_inner_mem n |>.not.mp hn' ] ;
    refine' le_trans ( Finset.sum_le_sum h_outer_bound ) _ ; norm_num at * ; linarith [ show ( Finset.card ( Finset.filter ( fun n => n∉S_inner ) S ) :ℝ ) ≤ Finset.card S from mod_cast Finset.card_le_card <| Finset.filter_subset _ _ ] ;
  convert add_le_add h_inner_sum h_outer_sum using 1 <;> norm_num [ Real.mul_rpow, show R₀ ≥ 0 by linarith ] ; ring!;
  · rw [ Finset.sum_filter_add_sum_filter_not ];
  · ring

/-
Main theorem: exp(−100·(C+I+1)²·R₀^{7/4}) ≤ (δ/(6R₀))^|S|·exp(−∑R/‖ρ‖).
-/
theorem finite_product_arith_bound
    (zeros : ℕ → ℂ) (hne : ∀ n, zeros n ≠ 0)
    (R R₀ C_cnt : ℝ) (hR₀ : 1 ≤ R₀) (hC_cnt : 0 < C_cnt)
    (hR_lo : R₀ ≤ R) (hR_hi : R ≤ 2 * R₀)
    (S : Finset ℕ) (hS_mem : ∀ n, n ∈ S ↔ ‖zeros n‖ ≤ 4 * R₀)
    (hS_card : (S.card : ℝ) ≤ C_cnt * (4 * R₀) ^ (3 / 2 : ℝ))
    (C_inner : ℝ) (hC_inner : 0 < C_inner)
    (hinner_bound : ∀ (R₁ : ℝ), 4 ≤ R₁ →
      ∃ S_inner : Finset ℕ,
        (∀ n, n ∈ S_inner ↔ ‖zeros n‖ ≤ R₁ / 2) ∧
        ∑ n ∈ S_inner, R₁ / ‖zeros n‖ ≤ C_inner * R₁ ^ (3 / 2 : ℝ)) :
    let δ := R₀ / (2 * ↑S.card + 2)
    Real.exp (-(100 * (C_cnt + C_inner + 1) ^ 2) * R₀ ^ (7 / 4 : ℝ)) ≤
      (δ / (6 * R₀)) ^ S.card * Real.exp (-∑ n ∈ S, R / ‖zeros n‖) := by
  -- Rewrite the right-hand side using properties of exponents.
  suffices h_exp : Real.exp (-(100 * (C_cnt + C_inner + 1) ^ 2) * R₀ ^ (7 / 4 : ℝ)) ≤ Real.exp (-(↑S.card * Real.log (12 * ↑S.card + 12)) - ∑ n ∈ S, R / ‖zeros n‖) by
    convert h_exp using 1;
    rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ];
    · rw [ ← Real.exp_add, show ( R₀ / ( 2 * ↑ ( #S ) + 2 ) / ( 6 * R₀ ) ) = ( 1 / ( 12 * ↑ ( #S ) + 12 ) ) by rw [ div_div, div_eq_div_iff ] <;> ring <;> positivity ] ; norm_num ; ring;
    · positivity;
  -- Apply the card_log_bound and reciprocal_sum_bound lemmas to bound the terms.
  have h_card_log : ↑S.card * Real.log (12 * ↑S.card + 12) ≤ (8 * C_cnt * Real.log (96 * C_cnt + 12) + 48 * C_cnt) * R₀ ^ (7 / 4 : ℝ) := by
    exact card_log_bound C_cnt R₀ hC_cnt hR₀ (#S) hS_card
  have h_reciprocal_sum : ∑ n ∈ S, R / ‖zeros n‖ ≤ (4 * C_inner + 8 * C_cnt) * R₀ ^ (3 / 2 : ℝ) := by
    apply reciprocal_sum_bound zeros hne R R₀ C_cnt hR₀ hC_cnt hR_lo hR_hi S hS_mem hS_card C_inner hC_inner hinner_bound;
  -- Combine the bounds from h_card_log and h_reciprocal_sum.
  have h_combined : (8 * C_cnt * Real.log (96 * C_cnt + 12) + 48 * C_cnt + 4 * C_inner + 8 * C_cnt) * R₀ ^ (7 / 4 : ℝ) ≤ 100 * (C_cnt + C_inner + 1) ^ 2 * R₀ ^ (7 / 4 : ℝ) := by
    exact mul_le_mul_of_nonneg_right ( by nlinarith [ constant_absorbs_log C_cnt C_inner hC_cnt hC_inner ] ) ( by positivity );
  norm_num at *;
  exact le_trans ( add_le_add h_card_log ( le_trans h_reciprocal_sum ( mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow_of_exponent_le hR₀ ( show ( 3 : ℝ ) / 2 ≤ 7 / 4 by norm_num ) ) ( by positivity ) ) ) ) ( by linarith )

end