/-
# Shell sum bound on near-height far zeros

Classical near-height shell sum bound (Davenport Ch. 12 / Titchmarsh §9.6):
given an enumeration `γ : ℕ → ℝ` of imaginary parts of zeros with local density
`O(log|t|)`, the sum `∑ 1/|γ-t|` over "near-height far" zeros (|γ-t| > 1, |γ-t| ≤ 2|t|)
is `O((log|t|)²)`.

## Proof sketch

Shell decomposition: group far zeros by integer distance k = ⌊|γ-t|⌋ ≥ 1.
- Shell k has at most `C·log(|t|+k)` zeros by the density hypothesis.
- Each zero in shell k contributes `≤ 1/k`.
- Sum over k: `∑_{k=1}^{2|t|} C·log(|t|+k)/k ≤ C·log(3|t|)·H_{2|t|} = O(log²|t|)`.

## Correction from original statement

The original theorem statement had condition `|t|/2 ≤ |γ n|` (lower bound only),
which makes the sum diverge for any enumeration with O(log k) zeros near height k.
Counterexample: γ(n) = n has at most 3 zeros in any unit interval, but
∑_{n ≥ |t|/2, |n-t|>1} 1/|n-t| ≥ ∑_{k=2}^∞ 1/k = ∞.

The corrected version adds the upper bound `|γ n - t| ≤ 2·|t|` (restricting to
zeros within distance 2|t| of t), making the sum finite and O(log²|t|).
The density hypothesis is also extended to all centers (using `|s| + 2` to handle
centers near the origin where `log |s|` is not useful).

## Mathlib ingredients used

- `harmonic`, `harmonic_le_one_add_log`
- `Finset.sum_le_sum`, `Finset.sum_biUnion`
- `Real.log_le_log`, `Real.log_nonneg`
-/

import Mathlib

set_option maxHeartbeats 12800000

open Real Finset

/-! ### Original (false) theorem — commented out

The original formulation is false because the subtype
`{n : ℕ // ¬|γ n - t| ≤ 1 ∧ |t| / 2 ≤ |γ n|}` can be infinite and the
sum `∑' 1/|γ n - t|` diverges in general (see module docstring above).

```
theorem near_height_shell_sum_bound_ORIGINAL
    (γ : ℕ → ℝ)
    (hfin : ∀ t : ℝ, Set.Finite {n : ℕ | |γ n - t| ≤ 1})
    (hdensity : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ |t| →
      ((hfin t).toFinset.card : ℝ) ≤ C * (1 + Real.log |t|)) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (t : ℝ), 2 ≤ |t| →
      Summable (fun n : {n : ℕ // ¬|γ n - t| ≤ 1 ∧ |t| / 2 ≤ |γ n|} =>
        1 / |γ ↑n - t|) ∧
      ∑' (n : {n : ℕ // ¬|γ n - t| ≤ 1 ∧ |t| / 2 ≤ |γ n|}),
        1 / |γ ↑n - t| ≤ C₁ * (Real.log |t|) ^ 2 := by
  sorry
```
-/

/-! ### Helper lemmas -/

/-
Shell sum bound via fiber decomposition and harmonic numbers.

Given a finset `S` with a "shell" function `f : S → {1,..,K}`,
if each shell has at most `D` elements and each element `n` contributes
at most `1/f(n)`, then the total sum is at most `D · H_K`.
-/
lemma shell_sum_le_harmonic (S : Finset ℕ) (g : ℕ → ℝ) (f : ℕ → ℕ)
    (D : ℝ) (K : ℕ)
    (hg_nn : ∀ n ∈ S, 0 ≤ g n)
    (hg_bound : ∀ n ∈ S, g n ≤ ((f n : ℝ))⁻¹)
    (hf_pos : ∀ n ∈ S, 1 ≤ f n)
    (hf_le : ∀ n ∈ S, f n ≤ K)
    (hD_nn : 0 ≤ D)
    (hD_bound : ∀ k, 1 ≤ k → k ≤ K →
      ((S.filter (fun n => f n = k)).card : ℝ) ≤ D) :
    S.sum g ≤ D * (harmonic K : ℝ) := by
  -- By decomposing S by the fibers of f, we can rewrite the sum as a double sum.
  have h_decomp : S.sum g ≤ ∑ k ∈ Finset.Icc 1 K, ∑ n ∈ S.filter (fun n => f n = k), (k : ℝ)⁻¹ := by
    have h_decomp : S.sum g ≤ ∑ n ∈ S, (↑(f n))⁻¹ := by
      exact Finset.sum_le_sum hg_bound;
    refine le_trans h_decomp ?_;
    simp +decide only [sum_filter];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
  simp_all +decide [ Finset.sum_filter, harmonic_eq_sum_Icc ];
  exact h_decomp.trans ( by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_right ( hD_bound x ( Finset.mem_Icc.mp hx |>.1 ) ( Finset.mem_Icc.mp hx |>.2 ) ) ( inv_nonneg.mpr ( Nat.cast_nonneg _ ) ) )

/-
For `x ≥ 2`, `1 + log(3x + 3) ≤ 6 * log x`.
-/
lemma one_add_log_le_mul_log (x : ℝ) (hx : 2 ≤ x) :
    1 + Real.log (3 * x + 3) ≤ 6 * Real.log x := by
  rw [ ← Real.log_rpow, ← Real.log_exp 1, ← Real.log_mul, Real.log_le_log_iff ] <;> norm_num <;> try positivity;
  have := Real.exp_one_lt_d9.le ; norm_num at * ; nlinarith [ pow_le_pow_left₀ ( by positivity ) hx 5 ] ;

/-
For `x ≥ 2`, `1 + log(2x) ≤ 4 * log x`.
-/
lemma one_add_log_2x_le (x : ℝ) (hx : 2 ≤ x) :
    1 + Real.log (2 * x) ≤ 4 * Real.log x := by
  rw [ Real.log_mul ] <;> try linarith;
  have := Real.log_two_gt_d9 ; norm_num at * ; linarith [ Real.log_le_log ( by norm_num ) hx ]

/-
Shell count bound: zeros in shell `k` around `t` are covered by two
unit-interval density counts.
-/
lemma shell_count_le_density (γ : ℕ → ℝ) (t : ℝ) (k : ℕ)
    (hfin : ∀ t : ℝ, Set.Finite {n : ℕ | |γ n - t| ≤ 1})
    (S : Finset ℕ) (hk : 1 ≤ k)
    (hS : ∀ n ∈ S, ⌊|γ n - t|⌋₊ = k) :
    S.card ≤ (hfin (t + ↑k + 1/2)).toFinset.card +
             (hfin (t - ↑k - 1/2)).toFinset.card := by
  refine' le_trans ( Finset.card_le_card _ ) _;
  exact ( hfin ( t + k + 1 / 2 ) |> Set.Finite.toFinset ) ∪ ( hfin ( t - k - 1 / 2 ) |> Set.Finite.toFinset );
  · intro n hn; specialize hS n hn; by_cases h : γ n - t ≥ 0 <;> by_cases h' : γ n - t < 0 <;> simp_all +decide [ Nat.floor_eq_iff, abs_of_nonpos, abs_of_nonneg ] ;
    · linarith;
    · exact Or.inl ( abs_le.mpr ⟨ by norm_num; linarith, by norm_num; linarith ⟩ );
    · exact Or.inr ( abs_le.mpr ⟨ by norm_num; cases abs_cases ( γ n - t ) <;> linarith, by norm_num; cases abs_cases ( γ n - t ) <;> linarith ⟩ );
  · exact Finset.card_union_le _ _

/-
Uniform shell density bound: for each shell k ∈ {1,..,⌊2|t|⌋₊}, the number of
elements in that shell is at most 2C(1 + log(3|t| + 3)).
-/
lemma shell_density_uniform_bound (γ : ℕ → ℝ) (t : ℝ) (C : ℝ)
    (hfin : ∀ t : ℝ, Set.Finite {n : ℕ | |γ n - t| ≤ 1})
    (hdens : ∀ s : ℝ, ((hfin s).toFinset.card : ℝ) ≤ C * (1 + Real.log (|s| + 2)))
    (hC : 0 < C) (ht : 2 ≤ |t|)
    (S : Finset ℕ) (k : ℕ) (hk : 1 ≤ k) (hk_le : k ≤ ⌊2 * |t|⌋₊)
    (hSk : ∀ n ∈ S, ⌊|γ n - t|⌋₊ = k) :
    (S.card : ℝ) ≤ 2 * C * (1 + Real.log (3 * |t| + 3)) := by
  -- Applying the lemma shell_count_le_density, we get S.card ≤ (hfin (t + k + 1/2)).toFinset.card + (hfin (t - k - 1/2)).toFinset.card.
  have h_card_le : (S.card : ℝ) ≤ (hfin (t + k + 1 / 2)).toFinset.card + (hfin (t - k - 1 / 2)).toFinset.card := by
    exact_mod_cast shell_count_le_density γ t k hfin S hk hSk;
  refine le_trans h_card_le <| le_trans ( add_le_add ( hdens _ ) ( hdens _ ) ) ?_;
  -- Applying the inequality $|t + k + 1/2| + 2 \leq 3|t| + 3$ and $|t - k - 1/2| + 2 \leq 3|t| + 3$.
  have h_ineq : |t + k + 1 / 2| + 2 ≤ 3 * |t| + 3 ∧ |t - k - 1 / 2| + 2 ≤ 3 * |t| + 3 := by
    constructor <;> cases abs_cases ( t + k + 1 / 2 ) <;> cases abs_cases ( t - k - 1 / 2 ) <;> cases abs_cases t <;> linarith [ show ( k : ℝ ) ≤ 2 * |t| by exact le_trans ( Nat.cast_le.mpr hk_le ) ( Nat.floor_le ( by positivity ) ) ];
  nlinarith [ Real.log_le_log ( by positivity ) h_ineq.1, Real.log_le_log ( by positivity ) h_ineq.2 ]

/-! ### Main corrected theorem -/

/-
**Near-height shell sum bound** (corrected formulation).

Given an enumeration `γ : ℕ → ℝ` of imaginary parts with local density `O(log|t|)`,
the sum `∑ 1/|γ-t|` over any finite set of indices with `1 < |γ-t| ≤ 2|t|`
is `O((log|t|)²)` uniformly.

Compared to the original statement:
- The condition `|t|/2 ≤ |γ n|` is replaced by `|γ n - t| ≤ 2 * |t|`
  (an upper bound on distance, making the sum finite).
- The density hypothesis is extended to all centers `s` (using `|s| + 2`).
- The conclusion uses `Finset.sum` (the sum is over a finite set).

Reference: Davenport Ch. 12 / Titchmarsh §9.6.1.
-/
theorem near_height_shell_sum_bound
    (γ : ℕ → ℝ)
    (hfin : ∀ t : ℝ, Set.Finite {n : ℕ | |γ n - t| ≤ 1})
    (hdensity : ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ,
      ((hfin s).toFinset.card : ℝ) ≤ C * (1 + Real.log (|s| + 2))) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (t : ℝ), 2 ≤ |t| →
      ∀ (S : Finset ℕ),
      (∀ n ∈ S, 1 < |γ n - t|) →
      (∀ n ∈ S, |γ n - t| ≤ 2 * |t|) →
      S.sum (fun n => 1 / |γ n - t|) ≤ C₁ * (Real.log |t|) ^ 2 := by
  obtain ⟨ C, hC₀, hC ⟩ := hdensity; use 48 * C; refine' ⟨ _, fun t ht S hS₁ hS₂ ↦ _ ⟩ <;> norm_num [ hC₀ ];
  -- Apply shell_sum_le_harmonic with:
  set D := 2 * C * (1 + Real.log (3 * |t| + 3))
  set K := Nat.floor (2 * |t|)
  have hshell : S.sum (fun n => 1 / |γ n - t|) ≤ D * (harmonic K : ℝ) := by
    apply shell_sum_le_harmonic S (fun n => 1 / |γ n - t|) (fun n => Nat.floor (|γ n - t|)) D K (by
    exact fun n hn => one_div_nonneg.2 <| abs_nonneg _) (by
    exact fun n hn => by simpa using inv_anti₀ ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| le_of_lt <| hS₁ n hn ) <| Nat.floor_le <| abs_nonneg _;) (by
    exact fun n hn => Nat.floor_pos.mpr ( le_of_lt ( hS₁ n hn ) )) (by
    exact fun n hn => Nat.floor_mono <| hS₂ n hn) (by
    exact mul_nonneg ( mul_nonneg zero_le_two hC₀.le ) ( add_nonneg zero_le_one ( Real.log_nonneg ( by linarith [ abs_nonneg t ] ) ) )) (by
    intros k hk₁ hk₂; have := shell_density_uniform_bound γ t C hfin hC hC₀ ht; aesop;);
  -- Use the bounds on `harmonic K` and `D`.
  have hbound : D * (harmonic K : ℝ) ≤ 2 * C * (1 + Real.log (3 * |t| + 3)) * (1 + Real.log (2 * |t|)) := by
    gcongr;
    · exact mul_nonneg ( mul_nonneg zero_le_two hC₀.le ) ( add_nonneg zero_le_one ( Real.log_nonneg ( by linarith ) ) );
    · exact le_trans ( harmonic_le_one_add_log _ ) ( by simpa using Real.log_le_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith ) <| Nat.floor_le <| by positivity );
  -- Use the bounds on `1 + log(3 * |t| + 3)` and `1 + log(2 * |t|)`.
  have hlog_bounds : (1 + Real.log (3 * |t| + 3)) * (1 + Real.log (2 * |t|)) ≤ 6 * Real.log |t| * 4 * Real.log |t| := by
    have hlog_bounds : 1 + Real.log (3 * |t| + 3) ≤ 6 * Real.log |t| ∧ 1 + Real.log (2 * |t|) ≤ 4 * Real.log |t| := by
      exact ⟨ one_add_log_le_mul_log _ ht, one_add_log_2x_le _ ht ⟩;
    nlinarith [ show 0 ≤ 1 + Real.log ( 3 * |t| + 3 ) by exact add_nonneg zero_le_one ( Real.log_nonneg ( by linarith [ abs_nonneg t ] ) ), show 0 ≤ 1 + Real.log ( 2 * |t| ) by exact add_nonneg zero_le_one ( Real.log_nonneg ( by linarith [ abs_nonneg t ] ) ) ];
  norm_num +zetaDelta at * ; nlinarith [ show 0 ≤ C by positivity ] ;

/-
**Multiplicity-weighted near-height shell sum bound.**

Given an enumeration `γ : ℕ → ℝ` of imaginary parts and a non-negative
weight `m : ℕ → ℝ` (typically a multiplicity) with uniform upper bound
`m n ≤ M`, the weighted shell sum `∑ m n / |γ n - t|` over near-height
far zeros is `O(M · log²|t|)`.

Reduction: `m n / |γ n - t| ≤ M / |γ n - t|`, then apply
`near_height_shell_sum_bound` to `1/|γ n - t|` and scale by `M`.
-/
theorem near_height_shell_sum_bound_weighted
    (γ : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hfin : ∀ t : ℝ, Set.Finite {n : ℕ | |γ n - t| ≤ 1})
    (hdensity : ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ,
      ((hfin s).toFinset.card : ℝ) ≤ C * (1 + Real.log (|s| + 2))) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (t : ℝ), 2 ≤ |t| →
      ∀ (S : Finset ℕ) (m : ℕ → ℝ),
      (∀ n ∈ S, 0 ≤ m n) →
      (∀ n ∈ S, m n ≤ M) →
      (∀ n ∈ S, 1 < |γ n - t|) →
      (∀ n ∈ S, |γ n - t| ≤ 2 * |t|) →
      S.sum (fun n => m n / |γ n - t|) ≤ C₁ * M * (Real.log |t|) ^ 2 := by
  obtain ⟨C₁, hC₁_pos, hbound⟩ := near_height_shell_sum_bound γ hfin hdensity
  refine ⟨C₁, hC₁_pos, ?_⟩
  intro t ht S m hm_nn hm_le hS₁ hS₂
  have h_unweighted := hbound t ht S hS₁ hS₂
  have h_pointwise : ∀ n ∈ S, m n / |γ n - t| ≤ M * (1 / |γ n - t|) := by
    intro n hn
    have hpos : 0 < |γ n - t| := lt_trans zero_lt_one (hS₁ n hn)
    rw [mul_one_div, div_le_div_iff₀ hpos hpos]
    exact mul_le_mul_of_nonneg_right (hm_le n hn) hpos.le
  calc S.sum (fun n => m n / |γ n - t|)
      ≤ S.sum (fun n => M * (1 / |γ n - t|)) :=
        Finset.sum_le_sum h_pointwise
    _ = M * S.sum (fun n => 1 / |γ n - t|) := by rw [← Finset.mul_sum]
    _ ≤ M * (C₁ * (Real.log |t|) ^ 2) :=
        mul_le_mul_of_nonneg_left h_unweighted hM
    _ = C₁ * M * (Real.log |t|) ^ 2 := by ring

/-! ### Aristotle-proved abstract density bounds (job 58a331f3, 2026-04-18) -/

/-
Shell-sum helper: given a finset `S` of natural numbers and a function
`f : ℕ → ℕ` with `1 ≤ f n` and `f n ≤ K` for all `n ∈ S`, and with at most
`D` elements per shell `{n | f n = k}`, we have
`∑_{n∈S} 1/f(n) ≤ D * H_K` where `H_K` is the K-th harmonic number.

Aristotle-proved (job 58a331f3) — sister of `shell_sum_le_harmonic` above
with a flat per-shell density bound and no upper-bound function `g`.
-/
lemma shell_sum_le_harmonic_mul_density
    (S : Finset ℕ) (f : ℕ → ℕ) (K : ℕ) (D : ℝ)
    (hD : 0 ≤ D)
    (hf_pos : ∀ n ∈ S, 1 ≤ f n)
    (hf_le : ∀ n ∈ S, f n ≤ K)
    (hdensity : ∀ k : ℕ, 1 ≤ k → k ≤ K →
      ((S.filter (fun n => f n = k)).card : ℝ) ≤ D) :
    S.sum (fun n => (1 : ℝ) / (f n : ℝ)) ≤ D * (harmonic K : ℝ) := by
  have h_union : ∑ n ∈ S, (1 / (f n : ℝ)) = ∑ k ∈ Finset.Icc 1 K, ∑ n ∈ S.filter (fun n => f n = k), (1 / (f n : ℝ)) := by
    rw [← Finset.sum_biUnion]
    · rcongr n; aesop
    · exact?
  have h_shell_bound : ∀ k ∈ Finset.Icc 1 K, ∑ n ∈ S.filter (fun n => f n = k), (1 / (f n : ℝ)) ≤ D * (1 / (k : ℝ)) := by
    intros k hk; rw [Finset.sum_congr rfl fun x hx => by rw [show f x = k from Finset.mem_filter.mp hx |>.2]];
    simpa [mul_comm] using mul_le_mul_of_nonneg_right (hdensity k (Finset.mem_Icc.mp hk |>.1) (Finset.mem_Icc.mp hk |>.2)) (by positivity);
  convert Finset.sum_le_sum h_shell_bound using 1
  norm_num [← Finset.mul_sum _ _ _, harmonic]
  exact Or.inl (by erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num [Finset.sum_range_succ'])

/-
Per-shell density: if `⌊|γ n|⌋ = k` then n is in the density ball at ±k.
Aristotle-proved (job 58a331f3).
-/
lemma floor_abs_density_bound
    (γ : ℕ → ℝ)
    (hfin : ∀ t : ℝ, Set.Finite {n : ℕ | |γ n - t| ≤ 1})
    (C : ℝ) (hC : 0 < C)
    (hdensity : ∀ s : ℝ, ((hfin s).toFinset.card : ℝ) ≤ C * (1 + Real.log (|s| + 2)))
    (S : Finset ℕ) (k : ℕ) (hk : 1 ≤ k) :
    ((S.filter (fun n => ⌊|γ n|⌋₊ = k)).card : ℝ) ≤
      2 * C * (1 + Real.log (↑k + 2)) := by
  have h_filter_subset : (S.filter (fun n => Nat.floor (abs (γ n)) = k)) ⊆ (hfin (k : ℝ)).toFinset ∪ (hfin (-k : ℝ)).toFinset := by
    norm_num [Finset.subset_iff, Nat.floor_eq_iff, abs_le] at *
    intro n hn hk₁ hk₂; cases abs_cases (γ n) <;> first | left; constructor <;> linarith | right; constructor <;> linarith
  refine' le_trans _ (le_trans (add_le_add (hdensity k) (hdensity (-k))) _)
  · exact_mod_cast le_trans (Finset.card_le_card h_filter_subset) (Finset.card_union_le _ _)
  · norm_num [abs_of_nonneg, add_nonneg]; ring_nf; norm_num

/-
**0-pivot reciprocal sum bound** (Aristotle-proved, job 58a331f3).

Given `γ : ℕ → ℝ` with local density `O(log)`, for any finset `S` of indices
with `1 < |γ n|` and `|γ n| ≤ R`, we have `∑_{n∈S} 1/|γ n| ≤ C'·(log R)²`.
-/
theorem density_sum_reciprocal_gamma_abstract
    (γ : ℕ → ℝ)
    (hfin : ∀ t : ℝ, Set.Finite {n : ℕ | |γ n - t| ≤ 1})
    (hdensity : ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ,
      ((hfin s).toFinset.card : ℝ) ≤ C * (1 + Real.log (|s| + 2))) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ R : ℝ, 2 ≤ R →
      ∀ S : Finset ℕ,
      (∀ n ∈ S, 1 < |γ n|) →
      (∀ n ∈ S, |γ n| ≤ R) →
      S.sum (fun n => 1 / |γ n|) ≤ C' * (Real.log R) ^ 2 := by
  obtain ⟨C, hC₀, hdensity⟩ := hdensity
  refine' ⟨4 * C * 5 ^ 2, by positivity, fun R hR S hS₁ hS₂ => _⟩
  have h_shell_sum : S.sum (fun n => (1 : ℝ) / (⌊|γ n|⌋₊ : ℝ)) ≤ 2 * C * (1 + Real.log (R + 2)) * (harmonic ⌊R⌋₊ : ℝ) := by
    have h_shell_sum : ∀ k : ℕ, 1 ≤ k → k ≤ ⌊R⌋₊ → ((S.filter (fun n => ⌊|γ n|⌋₊ = k)).card : ℝ) ≤ 2 * C * (1 + Real.log (R + 2)) := by
      intros k hk₁ hk₂
      refine' le_trans _ (mul_le_mul_of_nonneg_left (show 1 + Real.log (R + 2) ≥ 1 + Real.log (k + 2) by gcongr; linarith [Nat.floor_le (show 0 ≤ R by linarith), show (k : ℝ) ≤ ⌊R⌋₊ by norm_cast]) (by positivity))
      convert floor_abs_density_bound γ hfin C hC₀ hdensity S k hk₁ using 1
    convert shell_sum_le_harmonic_mul_density S (fun n => ⌊|γ n|⌋₊) ⌊R⌋₊ (2 * C * (1 + Real.log (R + 2))) (by exact mul_nonneg (mul_nonneg zero_le_two hC₀.le) (add_nonneg zero_le_one (Real.log_nonneg (by linarith)))) _ _ _ using 1
    · exact fun n hn => Nat.floor_pos.mpr (le_of_lt (hS₁ n hn))
    · exact fun n hn => Nat.floor_mono <| hS₂ n hn
    · convert h_shell_sum using 1
  have h_harmonic_bound : (harmonic ⌊R⌋₊ : ℝ) ≤ 1 + Real.log R := by
    convert harmonic_floor_le_one_add_log R (by linarith) using 1
  have h_combined : S.sum (fun n => (1 : ℝ) / |γ n|) ≤ 2 * C * (1 + Real.log (R + 2)) * (1 + Real.log R) := by
    refine le_trans ?_ (h_shell_sum.trans ?_)
    · exact Finset.sum_le_sum fun n hn => one_div_le_one_div_of_le (Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith [hS₁ n hn]) <| Nat.floor_le <| by positivity
    · exact mul_le_mul_of_nonneg_left h_harmonic_bound <| mul_nonneg (mul_nonneg zero_le_two hC₀.le) <| add_nonneg zero_le_one <| Real.log_nonneg <| by linarith
  have h_log_bounds : 1 + Real.log (R + 2) ≤ 5 * Real.log R ∧ 1 + Real.log R ≤ 5 * Real.log R := by
    constructor <;> rw [← Real.log_rpow, Real.le_log_iff_exp_le] <;> norm_num <;> try positivity
    · rw [Real.exp_add, Real.exp_log (by positivity)]
      have := Real.exp_one_lt_d9.le; norm_num1 at *; nlinarith [pow_le_pow_left₀ (by positivity) hR 4, pow_le_pow_left₀ (by positivity) hR 5]
    · rw [Real.exp_add, Real.exp_log (by positivity)]
      exact le_trans (mul_le_mul_of_nonneg_right (Real.exp_one_lt_d9.le) (by positivity)) (by norm_num; nlinarith [pow_le_pow_left₀ (by positivity) hR 4])
  nlinarith [show 0 ≤ C * Real.log R by exact mul_nonneg hC₀.le (Real.log_nonneg (by linarith))]

/-
**Shifted reciprocal sum bound** (Aristotle-proved, job 58a331f3).

Given `γ : ℕ → ℝ` with local density `O(log)`, for any finset `S` of indices
with `1 < |γ n - t|` and `|γ n| ≤ 2|t| + 2`,
we have `∑_{n∈S} 1/|γ n - t| ≤ C'·(log|t|)²`.
-/
theorem density_sum_reciprocal_shifted_abstract
    (γ : ℕ → ℝ)
    (hfin : ∀ t : ℝ, Set.Finite {n : ℕ | |γ n - t| ≤ 1})
    (hdensity : ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ,
      ((hfin s).toFinset.card : ℝ) ≤ C * (1 + Real.log (|s| + 2))) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ t : ℝ, 2 ≤ |t| →
      ∀ S : Finset ℕ,
      (∀ n ∈ S, 1 < |γ n - t|) →
      (∀ n ∈ S, |γ n| ≤ 2 * |t| + 2) →
      S.sum (fun n => 1 / |γ n - t|) ≤ C' * (Real.log |t|) ^ 2 := by
  obtain ⟨C, hC_pos, hC_density⟩ := hdensity
  use 60 * C
  refine' ⟨by positivity, _⟩
  intros t ht S hS1 hS2
  have hshell : ∀ k : ℕ, 1 ≤ k → k ≤ Nat.floor (3 * |t| + 2) → ((S.filter (fun n => ⌊|γ n - t|⌋₊ = k)).card : ℝ) ≤ 2 * C * (1 + Real.log (4 * |t| + 4)) := by
    intros k hk1 hk2
    have hshell : ((S.filter (fun n => ⌊|γ n - t|⌋₊ = k)).card : ℝ) ≤ (hfin (t + k)).toFinset.card + (hfin (t - k)).toFinset.card := by
      refine' mod_cast le_trans (Finset.card_le_card _) (Finset.card_union_le _ _)
      intro n hn; simp_all +decide [Nat.floor_eq_iff]
      cases abs_cases (γ n - t) <;> cases abs_cases (γ n - (t + k)) <;> cases abs_cases (γ n - (t - k)) <;> first | left; linarith | right; linarith
    refine le_trans hshell ?_
    refine le_trans (add_le_add (hC_density (t + k)) (hC_density (t - k))) ?_
    have h_bounds : |t + k| + 2 ≤ 4 * |t| + 4 ∧ |t - k| + 2 ≤ 4 * |t| + 4 := by
      constructor <;> cases abs_cases (t + k) <;> cases abs_cases (t - k) <;> cases abs_cases t <;> linarith [show (k : ℝ) ≤ 3 * |t| + 2 by exact le_trans (Nat.cast_le.mpr hk2) (Nat.floor_le (by positivity))]
    nlinarith [Real.log_le_log (by positivity) h_bounds.1, Real.log_le_log (by positivity) h_bounds.2]
  have hsum : ∑ n ∈ S, 1 / |γ n - t| ≤ 2 * C * (1 + Real.log (4 * |t| + 4)) * (harmonic (Nat.floor (3 * |t| + 2))) := by
    have hsum : ∑ n ∈ S, 1 / |γ n - t| ≤ ∑ k ∈ Finset.Icc 1 (Nat.floor (3 * |t| + 2)), ((S.filter (fun n => ⌊|γ n - t|⌋₊ = k)).card : ℝ) * (1 / k) := by
      have hsum : ∑ n ∈ S, 1 / |γ n - t| ≤ ∑ k ∈ Finset.Icc 1 (Nat.floor (3 * |t| + 2)), ∑ n ∈ S.filter (fun n => ⌊|γ n - t|⌋₊ = k), 1 / |γ n - t| := by
        rw [← Finset.sum_biUnion]
        · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => one_div_nonneg.mpr <| abs_nonneg _
          intro n hn; specialize hS1 n hn; specialize hS2 n hn; simp_all +decide [Nat.floor_le]
          exact ⟨by linarith, Nat.floor_mono <| by cases abs_cases (γ n - t) <;> cases abs_cases (γ n) <;> cases abs_cases t <;> linarith⟩
        · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop
      refine le_trans hsum ?_
      gcongr
      rename_i k hk
      exact le_trans (Finset.sum_le_sum fun x hx => one_div_le_one_div_of_le (by norm_cast; linarith [Finset.mem_Icc.mp hk]) <| show |γ x - t| ≥ k from Nat.floor_le (abs_nonneg _) |> le_trans (mod_cast by aesop)) <| by norm_num
    refine le_trans hsum ?_
    refine' le_trans (Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hshell k (Finset.mem_Icc.mp hk |>.1) (Finset.mem_Icc.mp hk |>.2)) (by positivity)) _
    norm_num [← Finset.mul_sum _ _ _, harmonic]
    erw [Finset.sum_Ico_eq_sub _ _] <;> norm_num [Finset.sum_range_succ']
  have hharmonic : harmonic (Nat.floor (3 * |t| + 2)) ≤ 1 + Real.log (3 * |t| + 2) := by
    convert harmonic_floor_le_one_add_log (3 * |t| + 2) using 1
    exact ⟨fun h => fun _ => h, fun h => h (by linarith)⟩
  have hlog_bound : 1 + Real.log (4 * |t| + 4) ≤ 6 * Real.log |t| ∧ 1 + Real.log (3 * |t| + 2) ≤ 5 * Real.log |t| := by
    constructor <;> rw [← Real.log_rpow, Real.le_log_iff_exp_le] <;> norm_cast <;> try positivity
    · rw [Real.exp_add, Real.exp_log (by positivity)]
      have := Real.exp_one_lt_d9.le; norm_num1 at *; nlinarith [pow_le_pow_left₀ (by positivity) ht 5, pow_le_pow_left₀ (by positivity) ht 6]
    · rw [Real.exp_add, Real.exp_log (by positivity)]
      have := Real.exp_one_lt_d9.le; norm_num1 at *; nlinarith [pow_le_pow_left₀ (by positivity) ht 4, pow_le_pow_left₀ (by positivity) ht 5]
  refine le_trans hsum ?_
  refine le_trans (mul_le_mul_of_nonneg_left hharmonic <| by exact mul_nonneg (mul_nonneg zero_le_two hC_pos.le) <| by linarith [Real.log_nonneg <| show 1 ≤ 4 * |t| + 4 by linarith]) ?_
  convert mul_le_mul (mul_le_mul_of_nonneg_left hlog_bound.1 (show 0 ≤ 2 * C by positivity)) hlog_bound.2 (by exact add_nonneg zero_le_one (Real.log_nonneg (by linarith))) (by nlinarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ |t|)]) using 1; ring