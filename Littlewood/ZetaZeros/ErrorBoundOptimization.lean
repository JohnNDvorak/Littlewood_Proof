/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Littlewood.ZetaZeros.ErrorBoundHelpers

/-!
# Optimization lemma for the PNT error bound

The key optimization argument: given the truncated explicit formula
and the zero-free region, choose T = exp(√(log x)) - 2 to obtain
the error bound |ψ(x) - x| ≤ C·x·exp(-c·√(log x)).
-/

open Real ChebyshevErrorBound

namespace ChebyshevErrorBoundOpt

/-
PROBLEM
For u ≥ 0 and c₀ > 0:
    u² · exp(-c₀ · u) ≤ (16/(c₀²·e²)) · exp(-c₀/2 · u).
    This absorbs the polynomial factor into the exponential.

PROVIDED SOLUTION
Write u²·exp(-c₀·u) = exp(-c₀/2·u) · (u²·exp(-c₀/2·u)). By sq_mul_exp_neg_le with α = c₀/2: u²·exp(-c₀/2·u) ≤ 4/((c₀/2)²·e²) = 4·4/(c₀²·e²) = 16/(c₀²·e²). So u²·exp(-c₀·u) ≤ (16/(c₀²·e²))·exp(-c₀/2·u). The key step is to split exp(-c₀·u) = exp(-c₀/2·u)·exp(-c₀/2·u) using Real.exp_add, and then multiply both sides by the u² factor.
-/
lemma term1_bound {c₀ : ℝ} (hc₀ : 0 < c₀) (u : ℝ) (hu : 0 ≤ u) :
    u ^ 2 * Real.exp (-c₀ * u) ≤
      16 / (c₀ ^ 2 * Real.exp 2) * Real.exp (-(c₀ / 2) * u) := by
        convert mul_le_mul_of_nonneg_right ( sq_mul_exp_neg_le ( show 0 < c₀ / 2 by positivity ) u hu ) ( Real.exp_nonneg ( - ( c₀ / 2 ) * u ) ) using 1 <;> ring;
        rw [ ← Real.exp_nat_mul ] ; ring

/-
PROBLEM
For u ≥ log 4 and u ≥ 0:
    u⁴ / (exp(u) - 2) ≤ (8192/e⁴) · exp(-u/2).
    This absorbs the u⁴ and truncation error into the exponential.

PROVIDED SOLUTION
For u ≥ log 4: exp(u) - 2 ≥ exp(u)/2 (by exp_sub_two_ge_half_exp). So u⁴/(exp(u)-2) ≤ u⁴/(exp(u)/2) = 2·u⁴·exp(-u). Now write exp(-u) = exp(-u/2)·exp(-u/2). So 2·u⁴·exp(-u) = 2·exp(-u/2)·(u⁴·exp(-u/2)). By pow4_mul_exp_neg_le with α = 1/2: u⁴·exp(-u/2) ≤ 256/((1/2)⁴·e⁴) = 256·16/e⁴ = 4096/e⁴. So 2·u⁴·exp(-u) ≤ 2·4096/e⁴·exp(-u/2) = 8192/e⁴·exp(-u/2) = 8192/exp(4)·exp(-(1/2)·u). Use div_le_div_of_le with appropriate manipulation for the u⁴/(exp(u)-2) step. Also need exp(u) - 2 > 0 for division (follows from exp(u) ≥ 4 > 2).
-/
lemma term2_bound (u : ℝ) (hu : Real.log 4 ≤ u) :
    u ^ 4 / (Real.exp u - 2) ≤
      8192 / Real.exp 4 * Real.exp (-(1 / 2) * u) := by
        -- By multiplying both sides of the inequality $u^4 * \exp(-u/2) \leq 4096 / \exp 4$ by 2, we get $2 * u^4 * \exp(-u/2) \leq 8192 / \exp 4$.
        have h_mul : 2 * u^4 * Real.exp (-u / 2) ≤ 8192 / Real.exp 4 := by
          convert mul_le_mul_of_nonneg_left ( pow4_mul_exp_neg_le ( show 0 < 1 / 2 by norm_num ) u ( by linarith [ Real.log_nonneg ( show ( 4 : ℝ ) ≥ 1 by norm_num ) ] ) ) zero_le_two using 1 <;> ring;
        -- By combining the inequalities from h_mul and exp_sub_two_ge_half_exp, we can conclude the proof.
        have h_combined : u^4 / (Real.exp u - 2) ≤ 2 * u^4 * Real.exp (-u) := by
          rw [ div_le_iff₀ ] <;> norm_num [ Real.exp_neg ] at *;
          · field_simp;
            nlinarith [ Real.add_one_le_exp u, Real.log_le_iff_le_exp ( by positivity ) |>.1 hu, pow_nonneg ( show 0 ≤ u by linarith [ Real.log_nonneg ( show ( 4 : ℝ ) ≥ 1 by norm_num ) ] ) 4 ];
          · exact lt_of_lt_of_le ( by norm_num [ Real.exp_log ] ) ( Real.exp_le_exp.mpr hu );
        refine le_trans h_combined ?_ ; convert mul_le_mul_of_nonneg_right h_mul ?_ using 1 ; ring_nf ; norm_num [ ← Real.exp_add ] ; ring_nf ; norm_num [ ← Real.exp_add ] ;
        · exact Or.inl ( by rw [ ← Real.exp_nat_mul ] ; ring );
        · positivity

/-
PROBLEM
The combined optimization bound.
Given c₀, A > 0, for x with log x ≥ max(4·c₀², (log 4)²):
  A·exp(-c₀·√(log x))·log(x) + A·(log x)²/(exp(√(log x))-2)
  ≤ C_large · exp(-c·√(log x))
where c = min(c₀, 1)/2 and C_large depends on A, c₀.

PROVIDED SOLUTION
Let c = min c₀ 1 / 2 and C_large = A * (16/(c₀²·e²) + 8192/e⁴). For t ≥ max(4c₀², (log 4)²), set u = √t. Then u ≥ 2c₀ and u ≥ log 4 and u ≥ 0. The bound has two terms:

Term 1: A * exp(-c₀ * u) * u² (since t = u² = (√t)² and √t = u). By term1_bound: u² * exp(-c₀ * u) ≤ 16/(c₀²·e²) * exp(-c₀/2 * u). So Term 1 ≤ A * 16/(c₀²·e²) * exp(-c₀/2 * u).

Term 2: A * u⁴ / (exp(u) - 2) (since t² = u⁴ and √t = u). By term2_bound (using u ≥ log 4): u⁴/(exp(u)-2) ≤ 8192/e⁴ * exp(-u/2). So Term 2 ≤ A * 8192/e⁴ * exp(-u/2).

Combined: ≤ A * 16/(c₀²·e²) * exp(-c₀/2 * u) + A * 8192/e⁴ * exp(-u/2).
Since c = min(c₀,1)/2 ≤ min(c₀/2, 1/2), both exp(-c₀/2*u) ≤ exp(-c*u) and exp(-u/2) ≤ exp(-c*u) (because c ≤ c₀/2 and c ≤ 1/2).

So combined ≤ (A * 16/(c₀²·e²) + A * 8192/e⁴) * exp(-c*u) = C_large * exp(-c * √t).

Key steps: use Real.sqrt_sq (for u ≥ 0), Real.sq_sqrt, exp_le_exp monotonicity, and that min(c₀,1)/2 ≤ c₀/2 and min(c₀,1)/2 ≤ 1/2.
-/
lemma combined_large_x_bound (c₀ A : ℝ) (hc₀ : 0 < c₀) (hA : 0 < A) :
    let c := min c₀ 1 / 2
    let C_large := A * (16 / (c₀ ^ 2 * Real.exp 2) + 8192 / Real.exp 4)
    ∀ (t : ℝ), t ≥ max (4 * c₀ ^ 2) ((Real.log 4) ^ 2) →
      A * Real.exp (-c₀ * Real.sqrt t) * t +
        A * t ^ 2 / (Real.exp (Real.sqrt t) - 2) ≤
      C_large * Real.exp (-c * Real.sqrt t) := by
        -- Applying the bounds from term1_bound and term2_bound.
        intro c C_large
        intro t ht
        have h_term1 : A * Real.exp (-c₀ * Real.sqrt t) * t ≤ A * 16 / (c₀ ^ 2 * Real.exp 2) * Real.exp (-c * Real.sqrt t) := by
          have h_term1 : Real.exp (-c₀ * Real.sqrt t) * t ≤ 16 / (c₀ ^ 2 * Real.exp 2) * Real.exp (-c * Real.sqrt t) := by
            have := term1_bound hc₀ ( Real.sqrt t ) ( Real.sqrt_nonneg t );
            convert this.trans _ using 1 <;> ring;
            · rw [ Real.sq_sqrt ( by nlinarith [ le_max_left ( 4 * c₀ ^ 2 ) ( Real.log 4 ^ 2 ), le_max_right ( 4 * c₀ ^ 2 ) ( Real.log 4 ^ 2 ) ] ), mul_comm ];
            · norm_num +zetaDelta at *;
              exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by cases min_cases c₀ 1 <;> nlinarith [ Real.sqrt_nonneg t, Real.sq_sqrt <| show 0 ≤ t by nlinarith ] ) <| by positivity;
          convert mul_le_mul_of_nonneg_left h_term1 hA.le using 1 <;> ring
        have h_term2 : A * t ^ 2 / (Real.exp (Real.sqrt t) - 2) ≤ A * 8192 / Real.exp 4 * Real.exp (-c * Real.sqrt t) := by
          -- Applying the bound from term2_bound.
          have h_term2 : t ^ 2 / (Real.exp (Real.sqrt t) - 2) ≤ 8192 / Real.exp 4 * Real.exp (-(1 / 2) * Real.sqrt t) := by
            convert term2_bound ( Real.sqrt t ) _ using 1;
            · rw [ show Real.sqrt t ^ 4 = ( Real.sqrt t ^ 2 ) ^ 2 by ring, Real.sq_sqrt ( by nlinarith [ le_max_left ( 4 * c₀ ^ 2 ) ( Real.log 4 ^ 2 ), le_max_right ( 4 * c₀ ^ 2 ) ( Real.log 4 ^ 2 ) ] ) ];
            · exact Real.le_sqrt_of_sq_le ( by nlinarith [ le_max_right ( 4 * c₀ ^ 2 ) ( Real.log 4 ^ 2 ) ] );
          simp_all +decide [ mul_div_assoc, mul_assoc ];
          exact h_term2.trans ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith [ show 0 ≤ Real.sqrt t by positivity, show c ≤ 1 / 2 by exact div_le_iff₀' ( by positivity ) |>.2 <| by cases min_cases c₀ 1 <;> linarith ] ) <| by positivity );
        convert add_le_add h_term1 h_term2 using 1 ; ring

/-
PROBLEM
Main optimization theorem in standalone form.
Given crude bound and large-x bound, derive the full bound for all x ≥ 2.

PROVIDED SOLUTION
Set c = min c₀ 1 / 2 and threshold = max(4*c₀²) ((log 4)²). Let C_large = A * (16/(c₀²·e²) + 8192/e⁴), and x₀ = Real.exp threshold.

Case 1: x ≥ 2 and log x ≥ threshold. Apply hexplicit to get |f x| ≤ A·x·exp(-c₀·√(log x))·log x + A·x·(log x)²/(exp(√(log x))-2). Factor out x: |f x| ≤ x · (A·exp(-c₀·√(log x))·log x + A·(log x)²/(exp(√(log x))-2)). By combined_large_x_bound with t = log x: the parenthesized expression ≤ C_large · exp(-c·√(log x)). So |f x| ≤ C_large · x · exp(-c·√(log x)).

Case 2: x ≥ 2 and log x < threshold. By hcrude: |f x| ≤ 3x. We need 3x ≤ C·x·exp(-c·√(log x)), i.e., 3 ≤ C·exp(-c·√(log x)). Since log x < threshold implies √(log x) < √threshold, exp(-c·√(log x)) > exp(-c·√threshold). So C = 3·exp(c·√threshold) works. That is, 3 ≤ C·exp(-c·√(log x)) holds for C = 3·exp(c·√threshold) since exp(-c·√(log x)) ≥ exp(-c·√threshold) (because √(log x) ≤ √threshold).

Combine: C_total = max C_large (3·exp(c·√threshold)), which is positive. Then ∃ c, C_total > 0, ∀ x ≥ 2, |f x| ≤ C_total·x·exp(-c·√(log x)).

Existence: refine ⟨c, by positivity, max C_large (3·exp(c·√threshold)), by positivity, ?_⟩.
-/
theorem optimization_main
    (f : ℝ → ℝ)
    (c₀ A : ℝ) (hc₀ : 0 < c₀) (hA : 0 < A)
    -- Crude bound for all x ≥ 1
    (hcrude : ∀ x : ℝ, 1 ≤ x → |f x| ≤ 3 * x)
    -- For x with log x ≥ threshold, the explicit formula gives:
    -- |f(x)| ≤ A·x·exp(-c₀·√(log x))·log x + A·x·(log x)²/(exp(√(log x))-2)
    (hexplicit : ∀ (x : ℝ), x ≥ 2 →
      Real.log x ≥ max (4 * c₀ ^ 2) ((Real.log 4) ^ 2) →
      |f x| ≤ A * x * Real.exp (-c₀ * (Real.log x).sqrt) * Real.log x +
              A * x * (Real.log x) ^ 2 / (Real.exp (Real.log x).sqrt - 2)) :
    ∃ c > 0, ∃ C > 0, ∀ x ≥ 2,
      |f x| ≤ C * x * Real.exp (-c * (Real.log x).sqrt) := by
        refine' ⟨ Min.min c₀ 1 / 2, _, _ ⟩ <;> norm_num;
        · grind;
        · use Max.max ( A * ( 16 / ( c₀ ^ 2 * Real.exp 2 ) + 8192 / Real.exp 4 ) ) ( 3 * Real.exp ( Min.min c₀ 1 / 2 * Real.sqrt ( Max.max ( 4 * c₀ ^ 2 ) ( Real.log 4 ^ 2 ) ) ) );
          refine' ⟨ _, fun x hx => _ ⟩;
          · positivity;
          · by_cases hlog : Real.log x ≥ max (4 * c₀^2) (Real.log 4^2);
            · refine le_trans ( hexplicit x hx hlog ) ?_;
              refine le_trans ?_ ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) <| by positivity ) <| by positivity );
              convert mul_le_mul_of_nonneg_left ( combined_large_x_bound c₀ A hc₀ hA ( Real.log x ) hlog ) ( show 0 ≤ x by positivity ) using 1 ; ring;
              ring;
            · refine le_trans ( hcrude x ( by linarith ) ) ?_;
              rw [ mul_right_comm ];
              gcongr;
              refine' le_trans _ ( mul_le_mul_of_nonneg_right ( le_max_right _ _ ) ( Real.exp_nonneg _ ) );
              norm_num [ mul_assoc, ← Real.exp_add ];
              exact mul_le_mul_of_nonneg_left ( Real.sqrt_le_sqrt <| le_of_not_ge hlog ) <| by positivity;

end ChebyshevErrorBoundOpt