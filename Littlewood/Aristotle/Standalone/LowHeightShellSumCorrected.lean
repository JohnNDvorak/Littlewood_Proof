/-
# Low-height shell sum bound

Classical low-height shell sum bound (Davenport Ch. 12 / Titchmarsh §9.6):
given an enumeration `zeros : ℕ → ℂ` of complex zeros in the critical strip
(0 < Re < 1) with zeros nonzero and local density `O(log|t|)`, the sum
`∑ 1/‖ρ‖` over "low-height far" zeros (|γ-t| > 1, |γ| < |t|/2) is `O((log|t|)²)`.
-/

import Mathlib

set_option maxHeartbeats 12800000

open Real Complex Finset

noncomputable section

/-
Zeros with bounded imaginary part form a finite set.
    Proof: cover `[-R, R]` by finitely many unit intervals centered at integers.
-/
lemma zeros_bounded_im_finite
    (f : ℕ → ℝ)
    (hfin : ∀ t : ℝ, Set.Finite {n : ℕ | |f n - t| ≤ 1})
    (R : ℝ) :
    Set.Finite {n : ℕ | |f n| ≤ R} := by
  by_contra! h;
  -- Cover `[-R, R]` by finitely many unit intervals centered at integers.
  obtain ⟨s, hs⟩ : ∃ s : Finset ℤ, {n : ℕ | abs (f n) ≤ R} ⊆ ⋃ k ∈ s, {n : ℕ | abs (f n - k) ≤ 1} := by
    use Finset.image ( fun k : ℤ => k ) ( Finset.Icc ( ⌊-R - 1⌋ ) ( ⌈R + 1⌉ ) );
    intro n hn; simp_all +decide [ abs_le ];
    exact ⟨ ⌊f n⌋, by linarith [ Int.floor_le ( f n ) ], ⟨ by exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Int.floor_le ( f n ), Int.lt_floor_add_one ( f n ), Int.floor_le ( -R ), Int.lt_floor_add_one ( -R ) ] ), by exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Int.floor_le ( f n ), Int.lt_floor_add_one ( f n ), Int.le_ceil R ] ) ⟩, by linarith [ Int.lt_floor_add_one ( f n ) ] ⟩;
  exact h ( Set.Finite.subset ( Set.Finite.biUnion ( Finset.finite_toSet s ) fun x hx => hfin x ) hs )

/-
Shell sum bound: the sum of `1/|f n|` over elements with `1 ≤ |f n| ≤ R`
    is `O((1 + log R)²)` given unit-interval density `O(1 + log|t|)`.
-/
lemma shell_sum_inv_bound
    (f : ℕ → ℝ)
    (hfin : ∀ t : ℝ, Set.Finite {n : ℕ | |f n - t| ≤ 1})
    (C : ℝ) (hCpos : 0 < C)
    (hdensity : ∀ t : ℝ, 2 ≤ |t| →
      ((hfin t).toFinset.card : ℝ) ≤ C * (1 + Real.log |t|)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset ℕ) (R : ℝ), 2 ≤ R →
      (∀ n ∈ S, 1 ≤ |f n| ∧ |f n| ≤ R) →
      (S.sum (fun n => 1 / |f n|) : ℝ) ≤ K * (1 + Real.log R) ^ 2 := by
  -- Define K as M₁ + 2C + 1.
  set M₁ := (hfin 1).toFinset.card + (hfin (-1)).toFinset.card
  set K := M₁ + 2 * C + 1
  use K;
  -- Now let's prove the bound.
  have h_bound : ∀ S : Finset ℕ, ∀ R : ℝ, 2 ≤ R → (∀ n ∈ S, 1 ≤ |f n| ∧ |f n| ≤ R) → (∑ n ∈ S, 1 / |f n|) ≤ M₁ + 2 * C * ∑ k ∈ Finset.Icc 2 ⌊R⌋₊, (1 + Real.log R) / (k : ℝ) := by
    intros S R hR hS
    have h_split : (∑ n ∈ S, 1 / |f n|) ≤ (∑ k ∈ Finset.Icc 1 ⌊R⌋₊, (∑ n ∈ S, if k ≤ |f n| ∧ |f n| < k + 1 then 1 / (k : ℝ) else 0)) := by
      have h_bound : ∀ n ∈ S, 1 / |f n| ≤ ∑ k ∈ Finset.Icc 1 ⌊R⌋₊, (if k ≤ |f n| ∧ |f n| < k + 1 then 1 / (k : ℝ) else 0) := by
        intro n hn; rw [ Finset.sum_eq_single ( Nat.floor ( |f n| ) ) ] <;> norm_num;
        · rw [ if_pos ⟨ Nat.floor_le ( abs_nonneg _ ), Nat.lt_floor_add_one _ ⟩ ] ; exact inv_anti₀ ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith [ hS n hn ] ) <| Nat.floor_le <| abs_nonneg _;
        · intro b hb₁ hb₂ hb₃ hb₄ hb₅; contrapose! hb₃;
          exact Eq.symm ( Nat.floor_eq_iff ( by positivity ) |>.2 ⟨ hb₄, hb₅ ⟩ );
        · exact fun h₁ h₂ h₃ => False.elim <| h₁ ( hS n hn |>.1 ) |> not_lt_of_ge ( Nat.floor_mono <| hS n hn |>.2 );
      exact le_trans ( Finset.sum_le_sum h_bound ) ( by rw [ Finset.sum_comm ] );
    -- For each $k \geq 2$, the count of $n \in S$ with $k \leq |f n| < k+1$ is at most $2C(1 + \log R)$.
    have h_count_bound : ∀ k ∈ Finset.Icc 2 ⌊R⌋₊, (∑ n ∈ S, if k ≤ |f n| ∧ |f n| < k + 1 then 1 else 0) ≤ 2 * C * (1 + Real.log R) := by
      intros k hk
      have h_count_bound_k : (∑ n ∈ S, if k ≤ |f n| ∧ |f n| < k + 1 then 1 else 0) ≤ (hfin k).toFinset.card + (hfin (-k)).toFinset.card := by
        have h_count_bound_k_step : ∀ n ∈ S, k ≤ |f n| ∧ |f n| < k + 1 → n ∈ (hfin k).toFinset ∨ n ∈ (hfin (-k)).toFinset := by
          simp +zetaDelta at *;
          intro n hn hk₁ hk₂; cases abs_cases ( f n - k ) <;> cases abs_cases ( f n + k ) <;> cases abs_cases ( f n ) <;> first | left; linarith | right; linarith;
        simp +zetaDelta at *;
        exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ( Finset.card_union_le _ _ );
      have := hdensity k ?_ <;> have := hdensity ( -k ) ?_ <;> norm_num at *;
      · exact le_trans ( Nat.cast_le.mpr h_count_bound_k ) ( by push_cast; nlinarith [ Real.log_nonneg ( show ( k : ℝ ) ≥ 1 by norm_cast; linarith ), Real.log_le_log ( by norm_cast; linarith ) ( show ( k : ℝ ) ≤ R by exact le_trans ( Nat.cast_le.mpr hk.2 ) ( Nat.floor_le ( by positivity ) ) ) ] );
      · lia;
      · linarith;
      · linarith;
    -- For $k = 1$, the count of $n \in S$ with $1 \leq |f n| < 2$ is at most $M₁$.
    have h_count_bound_k1 : (∑ n ∈ S, if 1 ≤ |f n| ∧ |f n| < 2 then 1 else 0) ≤ M₁ := by
      have h_count_bound_k1 : (∑ n ∈ S, if 1 ≤ |f n| ∧ |f n| < 2 then 1 else 0) ≤ (Finset.filter (fun n => |f n - 1| ≤ 1) S).card + (Finset.filter (fun n => |f n + 1| ≤ 1) S).card := by
        rw [ Finset.card_filter, Finset.card_filter ];
        simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_le_sum fun x hx => by split_ifs <;> norm_num ; cases abs_cases ( f x - 1 ) <;> cases abs_cases ( f x + 1 ) <;> cases abs_cases ( f x ) <;> linarith;
      refine le_trans h_count_bound_k1 ?_;
      exact add_le_add ( Finset.card_le_card fun x hx => by aesop ) ( Finset.card_le_card fun x hx => by aesop );
    -- Applying the bounds from h_count_bound and h_count_bound_k1 to the split sum.
    have h_apply_bounds : (∑ k ∈ Finset.Icc 1 ⌊R⌋₊, (∑ n ∈ S, if k ≤ |f n| ∧ |f n| < k + 1 then 1 / (k : ℝ) else 0)) ≤ (∑ n ∈ S, if 1 ≤ |f n| ∧ |f n| < 2 then 1 else 0) / 1 + ∑ k ∈ Finset.Icc 2 ⌊R⌋₊, (∑ n ∈ S, if k ≤ |f n| ∧ |f n| < k + 1 then 1 else 0) / (k : ℝ) := by
      rw [ Finset.Icc_eq_cons_Ioc, Finset.sum_cons ] <;> norm_num;
      · norm_num [ div_eq_mul_inv, Finset.sum_ite ];
        rfl;
      · linarith;
    refine le_trans h_split <| h_apply_bounds.trans ?_;
    gcongr;
    · simpa using Nat.cast_le.mpr h_count_bound_k1;
    · rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun x hx => by simpa only [ mul_div_assoc ] using div_le_div_of_nonneg_right ( h_count_bound x hx ) ( Nat.cast_nonneg _ ) ;
  -- Now let's bound the sum $\sum_{k=2}^{\lfloor R \rfloor} \frac{1}{k}$.
  have h_sum_bound : ∀ R : ℝ, 2 ≤ R → (∑ k ∈ Finset.Icc 2 ⌊R⌋₊, (1 : ℝ) / (k : ℝ)) ≤ 1 + Real.log R := by
    -- We'll use the fact that the sum of reciprocals of the first $n$ natural numbers is bounded above by $1 + \log n$.
    have h_harmonic_bound : ∀ n : ℕ, 2 ≤ n → (∑ k ∈ Finset.Icc 2 n, (1 : ℝ) / (k : ℝ)) ≤ 1 + Real.log n := by
      intro n hn
      have h_harmonic_bound : (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ)) ≤ 1 + Real.log n := by
        convert harmonic_le_one_add_log n using 1;
        erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ', harmonic ];
      exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc ( by norm_num ) le_rfl ) fun _ _ _ => by positivity ) h_harmonic_bound;
    exact fun R hR => le_trans ( h_harmonic_bound _ <| Nat.le_floor <| mod_cast hR ) <| by simpa using Real.log_le_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith ) <| Nat.floor_le <| by positivity;
  -- Combining the bounds, we get the desired inequality.
  have h_final_bound : ∀ S : Finset ℕ, ∀ R : ℝ, 2 ≤ R → (∀ n ∈ S, 1 ≤ |f n| ∧ |f n| ≤ R) → (∑ n ∈ S, 1 / |f n|) ≤ M₁ + 2 * C * (1 + Real.log R) ^ 2 := by
    intros S R hR hS
    specialize h_bound S R hR hS
    specialize h_sum_bound R hR
    have h_final : (∑ n ∈ S, 1 / |f n|) ≤ M₁ + 2 * C * (1 + Real.log R) * (∑ k ∈ Finset.Icc 2 ⌊R⌋₊, (1 : ℝ) / (k : ℝ)) := by
      simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] using h_bound;
    exact h_final.trans ( by nlinarith [ show 0 ≤ 2 * C * ( 1 + Real.log R ) by exact mul_nonneg ( mul_nonneg zero_le_two hCpos.le ) ( add_nonneg zero_le_one ( Real.log_nonneg ( by linarith ) ) ) ] );
  exact ⟨ by positivity, fun S R hR hS => le_trans ( h_final_bound S R hR hS ) ( by nlinarith [ show 1 ≤ ( 1 + Real.log R ) ^ 2 by exact one_le_pow₀ ( by linarith [ Real.log_nonneg ( show R ≥ 1 by linarith ) ] ) ] ) ⟩

/-
**Low-height shell sum bound** (Mathlib-only abstraction).

Given an enumeration `zeros : ℕ → ℂ` of complex zeros in the critical strip
(0 < Re(zeros n) < 1) with zeros nonzero and local density `O(log|t|)`,
the sum `∑ 1/‖ρ‖` over low-height far zeros is `O((log|t|)²)` uniformly.

Classical, standard result. Reference: Davenport Ch. 12 / Titchmarsh §9.6.1.
-/
theorem low_height_shell_sum_bound
    (zeros : ℕ → ℂ)
    (hzne : ∀ n, zeros n ≠ 0)
    (hstrip : ∀ n, 0 < (zeros n).re ∧ (zeros n).re < 1)
    (hfin : ∀ t : ℝ, Set.Finite {n : ℕ | |(zeros n).im - t| ≤ 1})
    (hdensity : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ |t| →
      ((hfin t).toFinset.card : ℝ) ≤ C * (1 + Real.log |t|)) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (t : ℝ), 2 ≤ |t| →
      Summable (fun n : {n : ℕ // ¬|(zeros n).im - t| ≤ 1 ∧
        |(zeros n).im| < |t| / 2} => 1 / ‖zeros ↑n‖) ∧
      ∑' (n : {n : ℕ // ¬|(zeros n).im - t| ≤ 1 ∧
        |(zeros n).im| < |t| / 2}), 1 / ‖zeros ↑n‖ ≤ C₂ * (Real.log |t|) ^ 2 := by
  -- Let's choose the constant $K$ from the shell_sum_inv_bound lemma.
  obtain ⟨C, hCpos, hdensity_bound⟩ := hdensity
  obtain ⟨K, hKpos, hshell⟩ := shell_sum_inv_bound (fun n => ((zeros n).im : ℝ)) (fun t => (hfin t)) C hCpos hdensity_bound;
  -- Choose $C₂ := (hfin 0).toFinset.sum (fun n => 1 / ‖zeros n‖) + K + 1 / (Real.log 2)^2 + 1$.
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ t : ℝ, 2 ≤ |t| → (∑' n : { n // ¬|(zeros n).im - t| ≤ 1 ∧ |(zeros n).im| < |t| / 2 }, 1 / ‖zeros n‖) ≤ K₀ + K * (1 + Real.log |t|)^2 := by
    -- Let $K₀$ be the sum of the reciprocals of the norms of the zeros with $|(zeros n).im| < 1$.
    obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ t : ℝ, 2 ≤ |t| → (∑' n : { n // ¬|(zeros n).im - t| ≤ 1 ∧ |(zeros n).im| < |t| / 2 ∧ |(zeros n).im| < 1 }, 1 / ‖zeros n‖) ≤ K₀ := by
      use ∑ n ∈ (hfin 0).toFinset, 1 / ‖zeros n‖ + 1;
      refine' ⟨ add_pos_of_nonneg_of_pos ( Finset.sum_nonneg fun _ _ => by positivity ) zero_lt_one, fun t ht => _ ⟩;
      rw [ tsum_eq_sum ];
      any_goals exact Finset.subtype _ ( hfin 0 |> Set.Finite.toFinset );
      · refine' le_add_of_le_of_nonneg ( _ : _ ≤ _ ) zero_le_one;
        refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
        rotate_left;
        exact Finset.image ( fun n : { n // ¬|(zeros n).im - t| ≤ 1 ∧ |(zeros n).im| < |t| / 2 ∧ |(zeros n).im| < 1 } => n.val ) ( Finset.subtype ( fun n => ¬|(zeros n).im - t| ≤ 1 ∧ |(zeros n).im| < |t| / 2 ∧ |(zeros n).im| < 1 ) ( hfin 0 |> Set.Finite.toFinset ) );
        · simp +contextual [ Finset.subset_iff ];
        · exact fun _ _ _ => by positivity;
        · rw [ Finset.sum_image ] ; aesop;
      · simp +zetaDelta at *;
        intros; linarith;
    refine' ⟨ K₀, hK₀.1, fun t ht => _ ⟩;
    -- Let $S_t$ be the set of indices $n$ such that $¬|(zeros n).im - t| ≤ 1$ and $|(zeros n).im| < |t| / 2$.
    set St := {n : ℕ | ¬|(zeros n).im - t| ≤ 1 ∧ |(zeros n).im| < |t| / 2} with hSt_def;
    -- Since $St$ is finite, we can split the sum into two parts: one over indices where $|(zeros n).im| < 1$ and one over indices where $|(zeros n).im| \geq 1$.
    have h_split_sum : ∑' n : { n // n ∈ St }, 1 / ‖zeros n‖ = ∑' n : { n // n ∈ St ∧ |(zeros n).im| < 1 }, 1 / ‖zeros n‖ + ∑' n : { n // n ∈ St ∧ 1 ≤ |(zeros n).im| }, 1 / ‖zeros n‖ := by
      have h_split_sum : ∑' n : { n // n ∈ St }, 1 / ‖zeros n‖ = ∑' n : { n // n ∈ St ∧ |(zeros n).im| < 1 }, 1 / ‖zeros n‖ + ∑' n : { n // n ∈ St ∧ 1 ≤ |(zeros n).im| }, 1 / ‖zeros n‖ := by
        have h_finite : Set.Finite St := by
          have := zeros_bounded_im_finite ( fun n => ( zeros n |> Complex.im ) ) ( fun t => hfin t ) ( |t| / 2 );
          exact this.subset fun n hn => hn.2.le
        have h_split_sum : ∑ n ∈ h_finite.toFinset, 1 / ‖zeros n‖ = ∑ n ∈ h_finite.toFinset.filter (fun n => |(zeros n).im| < 1), 1 / ‖zeros n‖ + ∑ n ∈ h_finite.toFinset.filter (fun n => 1 ≤ |(zeros n).im|), 1 / ‖zeros n‖ := by
          rw [ Finset.sum_filter, Finset.sum_filter ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext ; split_ifs <;> linarith;
        convert h_split_sum using 1;
        · rw [ tsum_eq_sum ];
          any_goals exact h_finite.toFinset.subtype _;
          · refine' Finset.sum_bij ( fun n hn => n ) _ _ _ _ <;> simp +decide [ hSt_def ];
          · simp +contextual [ hSt_def ];
        · congr! 1;
          · rw [ tsum_eq_sum ];
            any_goals exact Finset.subtype ( fun n => n ∈ St ∧ |( zeros n |> Complex.im )| < 1 ) h_finite.toFinset;
            · refine' Finset.sum_bij ( fun n hn => n ) _ _ _ _ <;> simp +contextual;
            · simp +contextual [ Finset.mem_subtype ];
          · rw [ tsum_eq_sum ];
            any_goals exact Finset.filter ( fun n => 1 ≤ |( zeros n |> Complex.im )| ) h_finite.toFinset |> Finset.subtype _;
            · refine' Finset.sum_bij ( fun n hn => n ) _ _ _ _ <;> simp +decide;
            · simp +contextual [ Finset.mem_subtype ];
      convert h_split_sum using 1;
    -- For the second part, use the shell_sum_inv_bound lemma.
    have h_second_part : ∑' n : { n // n ∈ St ∧ 1 ≤ |(zeros n).im| }, 1 / ‖zeros n‖ ≤ K * (1 + Real.log |t|)^2 := by
      have h_second_part : ∑' n : { n // n ∈ St ∧ 1 ≤ |(zeros n).im| }, 1 / ‖zeros n‖ ≤ ∑' n : { n // n ∈ St ∧ 1 ≤ |(zeros n).im| }, 1 / |(zeros n).im| := by
        refine' Summable.tsum_le_tsum _ _ _;
        · simp +zetaDelta at *;
          exact fun n hn₁ hn₂ hn₃ => inv_anti₀ ( by positivity ) ( Complex.abs_im_le_norm _ );
        · have h_finite : Set.Finite St := by
            have := zeros_bounded_im_finite ( fun n => ( zeros n |> Complex.im ) ) ( fun t => hfin t ) ( |t| / 2 );
            exact this.subset fun n hn => hn.2.le;
          refine' summable_of_ne_finset_zero _;
          exact h_finite.toFinset.subtype _ |> Finset.filter fun n => 1 ≤ |(zeros n).im|;
          simp +contextual [ hSt_def ];
        · have h_finite : Set.Finite {n : ℕ | 1 ≤ |(zeros n).im| ∧ |(zeros n).im| < |t| / 2} := by
            have := zeros_bounded_im_finite ( fun n => ( zeros n |> Complex.im ) ) ( fun t => hfin t ) ( |t| / 2 );
            exact this.subset fun x hx => hx.2.le;
          refine' summable_of_ne_finset_zero _;
          exact h_finite.toFinset.subtype _;
          simp +contextual [ hSt_def ];
      have h_second_part_finset : ∃ S : Finset ℕ, {n : ℕ | n ∈ St ∧ 1 ≤ |(zeros n).im|} = S := by
        have h_second_part_finset : Set.Finite {n : ℕ | n ∈ St ∧ 1 ≤ |(zeros n).im|} := by
          have h_second_part_finset : Set.Finite {n : ℕ | |(zeros n).im| ≤ |t| / 2} := by
            convert zeros_bounded_im_finite ( fun n => ( zeros n |> Complex.im ) ) ( fun t => hfin t ) ( |t| / 2 ) using 1;
          exact h_second_part_finset.subset fun x hx => hx.1.2.le;
        exact ⟨ h_second_part_finset.toFinset, h_second_part_finset.coe_toFinset.symm ⟩;
      obtain ⟨ S, hS ⟩ := h_second_part_finset; specialize hshell S ( |t| ) ht; simp_all +decide [ Set.ext_iff ] ;
      refine le_trans h_second_part ?_;
      convert hshell _ using 1;
      · rw [ tsum_eq_sum ];
        any_goals exact Finset.subtype ( fun n => n ∈ St ∧ 1 ≤ |( zeros n |> Complex.im )| ) S;
        · refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> simp +decide [ hS ];
          exact fun n hn => ⟨ hn, hSt_def n |>.2 <| hS n |>.2 hn |>.1, hS n |>.2 hn |>.2 ⟩;
        · simp_all +decide [ Finset.mem_subtype ];
      · exact fun n hn => ⟨ by linarith [ hS n |>.2 hn ], by linarith [ hS n |>.2 hn ] ⟩;
    refine le_trans ?_ ( add_le_add ( hK₀.2 t ht ) h_second_part );
    convert h_split_sum.le using 1;
    congr! 2;
    · exact congr_arg _ ( by ext; aesop );
    · congr! 2;
      congr! 2;
      congr! 1;
      ext; aesop;
    · congr! 1;
  refine' ⟨ K₀ / ( Real.log 2 ) ^ 2 + K * ( 1 + 1 / ( Real.log 2 ) ) ^ 2 + 1, _, _ ⟩;
  · exact add_pos_of_nonneg_of_pos ( add_nonneg ( div_nonneg hK₀.1.le ( sq_nonneg _ ) ) ( mul_nonneg hKpos.le ( sq_nonneg _ ) ) ) zero_lt_one;
  · refine' fun t ht => ⟨ _, le_trans ( hK₀.2 t ht ) _ ⟩;
    · have h_finite : Set.Finite {n : ℕ | ¬|(zeros n).im - t| ≤ 1 ∧ |(zeros n).im| < |t| / 2} := by
        have := zeros_bounded_im_finite ( fun n => ( zeros n |> Complex.im ) ) ( fun t => hfin t ) ( |t| / 2 );
        exact this.subset fun n hn => hn.2.le;
      convert h_finite.summable _;
      swap;
      exacts [ fun n => 1 / ‖zeros n‖, rfl ];
    · -- Since $|t| \geq 2$, we have $\log |t| \geq \log 2$.
      have hlog : Real.log |t| ≥ Real.log 2 := by
        exact Real.log_le_log ( by norm_num ) ht;
      refine' le_trans _ ( mul_le_mul_of_nonneg_right ( le_add_of_nonneg_right zero_le_one ) ( sq_nonneg _ ) );
      rw [ add_mul ];
      refine' add_le_add _ _;
      · rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> nlinarith [ show 0 < Real.log 2 ^ 2 by positivity, show Real.log |t| ^ 2 ≥ Real.log 2 ^ 2 by gcongr ];
      · rw [ mul_assoc ];
        exact mul_le_mul_of_nonneg_left ( by rw [ add_div', div_pow, div_mul_eq_mul_div, le_div_iff₀ ] <;> nlinarith [ Real.log_pos one_lt_two, Real.log_le_sub_one_of_pos zero_lt_two, mul_le_mul_of_nonneg_left hlog <| Real.log_nonneg one_le_two ] ) hKpos.le

end