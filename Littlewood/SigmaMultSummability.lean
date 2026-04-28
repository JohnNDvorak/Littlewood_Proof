/-
# Multiplicity-weighted summability and counting bounds

Abstract lemmas for proving summability and counting bounds for
sigma-type enumerations with multiplicity. Used to close two sorries
in HadamardFactorizationCore.lean.
-/

import Mathlib

set_option maxHeartbeats 12800000

noncomputable section

open Complex Metric Filter Set Function Topology Real Finset BigOperators

/-! ## Abstract results for sigma-type enumerations

We work with:
- `S : Type*` (base type of zeros, e.g., `xiZeroSet`)
- `w : S → ℝ` (norm function, e.g., `fun z => ‖(z : ℂ)‖`)
- `mult : S → ℕ` (multiplicity, e.g., `analyticOrderAt.toNat`)
- `e : ℕ ≃ Σ s : S, Fin (mult s)` (enumeration with multiplicity)

We prove:
1. Summability of `fun n => 1 / (w (e n).1)^2` from a counting bound
2. Existence of a Finset with counting bound for the ℕ-enumeration
-/

variable {S : Type*}

/-! ### Finiteness of the sigma-ball -/

/-
The set `{n | w((e n).1) ≤ R}` is finite when the base set `{s | w s ≤ R}` is.
-/
theorem sigma_enum_ball_finite
    (w : S → ℝ) (mult : S → ℕ)
    (e : ℕ ≃ Σ s : S, Fin (mult s))
    (R : ℝ)
    (hfin : {s : S | w s ≤ R}.Finite) :
    {n : ℕ | w (e n).1 ≤ R}.Finite := by
  -- Let's denote the set of zeros inside the ball by `σ` and show that it is finite.
  set σ := {σ : (s : S) × (Fin (mult s)) | w σ.1 ≤ R} with hσ_def
  have hσ_fin : σ.Finite := by
    have hσ_fin : (Set.image (fun σ : (s : S) × (Fin (mult s)) => σ.1) σ).Finite := by
      exact hfin.subset fun x hx => by aesop;
    convert Set.Finite.biUnion hσ_fin _;
    rotate_left;
    use fun s => { σ : ( s : S ) × Fin ( mult s ) | σ.fst = s };
    · exact fun s hs => Set.Finite.subset ( Set.toFinite ( Set.range fun i : Fin ( mult s ) => ⟨ s, i ⟩ ) ) fun x hx => by aesop;
    · ext ⟨s, i⟩; simp [hσ_def];
      exact fun _ => ⟨ i ⟩;
  exact Set.Finite.preimage ( fun n => by simp +decide ) hσ_fin

/-
Membership characterization for the sigma-ball finset.
-/
theorem sigma_enum_ball_mem
    (w : S → ℝ) (mult : S → ℕ)
    (e : ℕ ≃ Σ s : S, Fin (mult s))
    (R : ℝ)
    (hfin : {s : S | w s ≤ R}.Finite)
    (n : ℕ) :
    n ∈ (sigma_enum_ball_finite w mult e R hfin).toFinset ↔ w (e n).1 ≤ R := by
  simp +zetaDelta at *

/-! ### Cardinality bound for the sigma-ball -/

/-
The cardinality of `{n | w((e n).1) ≤ R}` is bounded by the sum of multiplicities.
-/
theorem sigma_enum_card_bound
    (w : S → ℝ) (mult : S → ℕ)
    (e : ℕ ≃ Σ s : S, Fin (mult s))
    (hmult_pos : ∀ s, 0 < mult s)
    (R : ℝ)
    (hfin : {s : S | w s ≤ R}.Finite) :
    ((sigma_enum_ball_finite w mult e R hfin).toFinset.card : ℝ) ≤
      ∑ s ∈ hfin.toFinset, (mult s : ℝ) := by
  norm_cast;
  convert Set.ncard_le_ncard ( show ( Set.image ( fun n => e n ) ( sigma_enum_ball_finite w mult e R hfin |> Set.Finite.toFinset ) ) ⊆ ( hfin.toFinset.sigma fun s => Finset.univ : Finset ( Σ s : S, Fin ( mult s ) ) ) from ?_ ) using 1;
  · rw [ Set.ncard_image_of_injective _ e.injective, Set.ncard_coe_finset ];
  · simp +decide [ Set.ncard_eq_toFinset_card' ];
    rw [ show { a : ( s : S ) × Fin ( mult s ) | w a.1 ≤ R } = ( hfin.toFinset.sigma fun s => Finset.univ : Finset ( Σ s : S, Fin ( mult s ) ) ) from ?_, Set.ncard_coe_finset ];
    · simp +decide [ Finset.card_sigma ];
    · aesop;
  · intro x hx
    aesop

/-! ### Full counting bound -/

/-
Full counting bound for the sigma-type ℕ-enumeration.
-/
theorem sigma_nat_counting_bound
    (w : S → ℝ) (mult : S → ℕ)
    (e : ℕ ≃ Σ s : S, Fin (mult s))
    (hmult_pos : ∀ s, 0 < mult s)
    (hfin : ∀ R : ℝ, {s : S | w s ≤ R}.Finite)
    (hcount : ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      (∑ s ∈ (hfin R).toFinset, (mult s : ℝ)) ≤ C * R ^ (3 / 2 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      ∃ S' : Finset ℕ,
        (∀ n, n ∈ S' ↔ w (e n).1 ≤ R) ∧
        (S'.card : ℝ) ≤ C * R ^ (3 / 2 : ℝ) := by
  cases' hcount with C hC;
  refine' ⟨ C, hC.1, fun R hR => ⟨ _, _, _ ⟩ ⟩;
  exact ( sigma_enum_ball_finite w mult e R ( hfin R ) ).toFinset;
  · exact fun n => sigma_enum_ball_mem w mult e R (hfin R) n;
  · refine' le_trans _ ( hC.2 R hR );
    convert sigma_enum_card_bound w mult e hmult_pos R ( hfin R ) using 1

/-! ### Summability of `1/w²` over the sigma-type -/

/-
Summability of `1/w(σ.1)²` over the sigma type, from a polynomial counting bound.
-/
theorem summable_sigma_inv_sq_of_counting_bound
    (w : S → ℝ) (mult : S → ℕ)
    (hw_pos : ∀ s, 0 < w s)
    (hmult_pos : ∀ s, 0 < mult s)
    (hfin : ∀ R : ℝ, {s : S | w s ≤ R}.Finite)
    (hcount : ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      (∑ s ∈ (hfin R).toFinset, (mult s : ℝ)) ≤ C * R ^ (3 / 2 : ℝ)) :
    Summable (fun σ : Σ s : S, Fin (mult s) => 1 / (w σ.1) ^ 2) := by
  -- Split the sum into two parts: one over elements where $w(s) < 1$ and one over elements where $w(s) \geq 1$.
  have h_split : Summable (fun σ : Σ s : S, Fin (mult s) => if w σ.fst < 1 then (1 / w σ.fst ^ 2 : ℝ) else 0) ∧ Summable (fun σ : Σ s : S, Fin (mult s) => if 1 ≤ w σ.fst then (1 / w σ.fst ^ 2 : ℝ) else 0) := by
    -- For the part where $w(s) \geq 1$, we use the counting bound to show that the sum is bounded.
    have h_large : Summable (fun σ : Σ s : S, Fin (mult s) => if 1 ≤ w σ.fst then (1 / w σ.fst ^ 2 : ℝ) else 0) := by
      obtain ⟨ C, hC₀, hC ⟩ := hcount;
      -- For the large part, decompose [1,∞) into dyadic shells [2^k, 2^{k+1}) for k = 0,1,2,...
      have h_shell : ∀ k : ℕ, (∑ σ ∈ Finset.filter (fun σ => 2^k ≤ w σ.fst ∧ w σ.fst < 2^(k+1)) (Finset.sigma (hfin (2^(k+1))).toFinset (fun s => Finset.filter (fun i => True) (Finset.univ : Finset (Fin (mult s))))), (1 / w σ.fst ^ 2 : ℝ)) ≤ C * 2^(3/2 : ℝ) * (1 / 2^(k/2 : ℝ)) := by
        intro k
        have h_shell_bound : (∑ σ ∈ Finset.filter (fun σ => 2^k ≤ w σ.fst ∧ w σ.fst < 2^(k+1)) (Finset.sigma (hfin (2^(k+1))).toFinset (fun s => Finset.filter (fun i => True) (Finset.univ : Finset (Fin (mult s))))), (1 / w σ.fst ^ 2 : ℝ)) ≤ (∑ s ∈ (hfin (2^(k+1))).toFinset, (mult s : ℝ)) * (1 / (2^k : ℝ) ^ 2) := by
          have h_shell_bound : ∀ s ∈ (hfin (2^(k+1))).toFinset, (∑ i ∈ Finset.filter (fun i => 2^k ≤ w s ∧ w s < 2^(k+1)) (Finset.univ : Finset (Fin (mult s))), (1 / w s ^ 2 : ℝ)) ≤ (mult s : ℝ) * (1 / (2^k : ℝ) ^ 2) := by
            intro s hs
            have h_shell_bound : ∀ i ∈ Finset.filter (fun i => 2^k ≤ w s ∧ w s < 2^(k+1)) (Finset.univ : Finset (Fin (mult s))), (1 / w s ^ 2 : ℝ) ≤ (1 / (2^k : ℝ) ^ 2) := by
              exact fun i hi => one_div_le_one_div_of_le ( sq_pos_of_pos ( pow_pos ( zero_lt_two' ℝ ) _ ) ) ( pow_le_pow_left₀ ( by positivity ) ( Finset.mem_filter.mp hi |>.2.1 ) _ );
            refine' le_trans ( Finset.sum_le_sum h_shell_bound ) _ ; norm_num;
            split_ifs <;> simp +decide [ Finset.card_univ ];
          rw [ Finset.sum_mul _ _ _ ];
          convert Finset.sum_le_sum h_shell_bound using 1;
          rw [ Finset.sum_sigma' ];
          refine' Finset.sum_bij ( fun x hx => ⟨ x.fst, x.snd ⟩ ) _ _ _ _ <;> aesop;
        refine le_trans h_shell_bound ?_;
        refine' le_trans ( mul_le_mul_of_nonneg_right ( hC ( 2 ^ ( k + 1 ) ) ( one_le_pow₀ ( by norm_num ) ) ) ( by positivity ) ) _ ; ring_nf ; norm_num;
        rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring_nf ; norm_num;
        norm_num [ Real.div_rpow, Real.rpow_mul ] ; ring_nf ; norm_num;
        rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add ] <;> norm_num ; ring_nf ; norm_num;
        norm_num [ pow_mul', ← Real.sqrt_eq_rpow ] ; ring_nf ; norm_num;
        rw [ ← Real.sqrt_div_self ] ; ring_nf ; norm_num;
        norm_num [ mul_assoc, ← mul_pow ];
      -- Summing over all shells, we get the total bound.
      have h_total : Summable (fun k : ℕ => ∑ σ ∈ Finset.filter (fun σ => 2^k ≤ w σ.fst ∧ w σ.fst < 2^(k+1)) (Finset.sigma (hfin (2^(k+1))).toFinset (fun s => Finset.filter (fun i => True) (Finset.univ : Finset (Fin (mult s))))), (1 / w σ.fst ^ 2 : ℝ)) := by
        refine' Summable.of_nonneg_of_le ( fun k => Finset.sum_nonneg fun _ _ => one_div_nonneg.2 ( sq_nonneg _ ) ) ( fun k => h_shell k ) _;
        refine' Summable.mul_left _ _;
        -- Recognize that the series $\sum_{k=0}^{\infty} \frac{1}{2^{k/2}}$ is a geometric series with common ratio $1/\sqrt{2}$.
        have h_geo_series : Summable (fun k : ℕ => (1 / Real.sqrt 2) ^ k) := by
          exact summable_geometric_of_lt_one ( by positivity ) ( by rw [ div_lt_iff₀ ] <;> norm_num [ Real.lt_sqrt ] );
        convert h_geo_series using 2 ; norm_num [ Real.sqrt_eq_rpow, ← Real.rpow_mul ];
        rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> ring ; norm_num;
      refine' summable_of_sum_le _ _;
      exact ∑' k : ℕ, ∑ σ ∈ Finset.filter ( fun σ => 2 ^ k ≤ w σ.fst ∧ w σ.fst < 2 ^ ( k + 1 ) ) ( Finset.sigma ( hfin ( 2 ^ ( k + 1 ) ) |> Set.Finite.toFinset ) fun s => Finset.filter ( fun i => True ) ( Finset.univ : Finset ( Fin ( mult s ) ) ) ), ( 1 / w σ.fst ^ 2 : ℝ );
      · exact fun _ => by positivity;
      · intro u
        have h_sum_le : ∑ x ∈ u, (if 1 ≤ w x.fst then 1 / w x.fst ^ 2 else 0) ≤ ∑ k ∈ Finset.range (Nat.log 2 (⌈(∑ x ∈ u, w x.fst)⌉₊) + 1), ∑ σ ∈ Finset.filter (fun σ => 2^k ≤ w σ.fst ∧ w σ.fst < 2^(k+1)) (Finset.sigma (hfin (2^(k+1))).toFinset (fun s => Finset.filter (fun i => True) (Finset.univ : Finset (Fin (mult s))))), (1 / w σ.fst ^ 2 : ℝ) := by
          have h_sum_le : ∀ x ∈ u, (if 1 ≤ w x.fst then 1 / w x.fst ^ 2 else 0) ≤ ∑ k ∈ Finset.range (Nat.log 2 (⌈(∑ x ∈ u, w x.fst)⌉₊) + 1), (if 2^k ≤ w x.fst ∧ w x.fst < 2^(k+1) then 1 / w x.fst ^ 2 else 0) := by
            intro x hx
            by_cases h : 1 ≤ w x.fst;
            · have h_log : ∃ k ∈ Finset.range (Nat.log 2 (⌈(∑ x ∈ u, w x.fst)⌉₊) + 1), 2^k ≤ w x.fst ∧ w x.fst < 2^(k+1) := by
                refine' ⟨ Nat.log 2 ⌊w x.fst⌋₊, _, _, _ ⟩ <;> norm_num;
                · exact Nat.log_mono_right ( Nat.floor_le_ceil _ |> le_trans <| Nat.ceil_mono <| Finset.single_le_sum ( fun a _ => le_of_lt <| hw_pos a.fst ) hx );
                · exact le_trans ( mod_cast Nat.pow_log_le_self 2 ( Nat.ne_of_gt ( Nat.floor_pos.mpr h ) ) ) ( Nat.floor_le ( le_of_lt ( hw_pos _ ) ) );
                · have := Nat.lt_pow_succ_log_self ( by norm_num : ( 1 : ℕ ) < 2 ) ⌊w x.fst⌋₊;
                  exact lt_of_lt_of_le ( Nat.lt_floor_add_one _ ) ( mod_cast this );
              obtain ⟨ k, hk₁, hk₂, hk₃ ⟩ := h_log; rw [ Finset.sum_eq_add_sum_diff_singleton hk₁ ] ; simp +decide [ hk₂, hk₃, h ] ;
              exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity;
            · simp [h];
              exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity;
          refine' le_trans ( Finset.sum_le_sum h_sum_le ) _;
          rw [ Finset.sum_comm ];
          refine' Finset.sum_le_sum fun k hk => _;
          rw [ ← Finset.sum_filter ];
          refine' Finset.sum_le_sum_of_subset_of_nonneg _ fun _ _ _ => one_div_nonneg.2 ( sq_nonneg _ );
          simp +contextual [ Finset.subset_iff ];
          exact fun x hx₁ hx₂ hx₃ => le_of_lt hx₃;
        exact h_sum_le.trans ( Summable.sum_le_tsum ( Finset.range _ ) ( fun _ _ => Finset.sum_nonneg fun _ _ => one_div_nonneg.2 ( sq_nonneg _ ) ) h_total );
    refine' ⟨ _, h_large ⟩;
    refine' summable_of_ne_finset_zero _;
    exact Finset.sigma ( hfin 1 |> Set.Finite.toFinset ) fun s => Finset.univ;
    simp +contextual;
    intros; linarith;
  convert h_split.1.add h_split.2 using 2 ; aesop

/-! ### Transfer summability to ℕ via equivalence -/

/-
Transfer summability from sigma type to ℕ via an equivalence.
-/
theorem summable_sigma_nat_via_equiv
    (w : S → ℝ) (mult : S → ℕ)
    (e : ℕ ≃ Σ s : S, Fin (mult s))
    (hσ : Summable (fun σ : Σ s : S, Fin (mult s) => 1 / (w σ.1) ^ 2)) :
    Summable (fun n => 1 / (w (e n).1) ^ 2) := by
  exact hσ.comp_injective e.injective

end