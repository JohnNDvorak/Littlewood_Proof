import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.PringsheimBinomialRearrangement

open scoped BigOperators

/--
Finite binomial reindexing for Landau/Pringsheim-type arguments.

This is the algebraic rearrangement behind the shifted-radius partial-sum bound:

`Σ_{n < N} aₙ (R+t)^n = Σ_{k < N} t^k Σ_{n < N} aₙ * choose(n,k) * R^(n-k)`.

The proof is purely finite/combinatorial and does not use any asymptotics.
-/
theorem sum_range_mul_add_pow_reindex
    (a : ℕ → ℝ) (R t : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, a n * (R + t) ^ n) =
      ∑ k ∈ Finset.range N, t ^ k *
        (∑ n ∈ Finset.range N, a n * ((Nat.choose n k : ℝ) * R ^ (n - k))) := by
  calc
    (∑ n ∈ Finset.range N, a n * (R + t) ^ n)
        = ∑ n ∈ Finset.range N,
            ∑ k ∈ Finset.range (n + 1),
              a n * ((Nat.choose n k : ℝ) * t ^ k * R ^ (n - k)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [add_comm R t, add_pow, Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
    _ = ∑ n ∈ Finset.range N,
          ∑ k ∈ Finset.range N,
            if k ≤ n then a n * ((Nat.choose n k : ℝ) * t ^ k * R ^ (n - k)) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          have hnlt : n < N := Finset.mem_range.mp hn
          have hfilter :
              (Finset.range N).filter (fun k : ℕ => k ≤ n) = Finset.range (n + 1) := by
            ext k
            constructor
            · intro hk
              simp only [Finset.mem_filter, Finset.mem_range] at hk
              simpa [Finset.mem_range] using (Nat.lt_succ_of_le hk.2)
            · intro hk
              have hklt : k < n + 1 := by
                simpa [Finset.mem_range] using hk
              have hkle : k ≤ n := Nat.le_of_lt_succ hklt
              have hkltN : k < N := lt_of_le_of_lt hkle hnlt
              simp [Finset.mem_filter, Finset.mem_range, hkltN, hkle]
          calc
            (∑ k ∈ Finset.range (n + 1), a n * ((Nat.choose n k : ℝ) * t ^ k * R ^ (n - k)))
                = ∑ k ∈ (Finset.range N).filter (fun k : ℕ => k ≤ n),
                    a n * ((Nat.choose n k : ℝ) * t ^ k * R ^ (n - k)) := by
                  rw [hfilter]
            _ = ∑ k ∈ Finset.range N,
                  if k ≤ n then a n * ((Nat.choose n k : ℝ) * t ^ k * R ^ (n - k)) else 0 := by
                  rw [Finset.sum_filter]
    _ = ∑ k ∈ Finset.range N,
          ∑ n ∈ Finset.range N,
            if k ≤ n then a n * ((Nat.choose n k : ℝ) * t ^ k * R ^ (n - k)) else 0 := by
          exact Finset.sum_comm
    _ = ∑ k ∈ Finset.range N,
          t ^ k * (∑ n ∈ Finset.range N, a n * ((Nat.choose n k : ℝ) * R ^ (n - k))) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          calc
            (∑ n ∈ Finset.range N,
                if k ≤ n then a n * ((Nat.choose n k : ℝ) * t ^ k * R ^ (n - k)) else 0)
                = ∑ n ∈ Finset.range N,
                    a n * ((Nat.choose n k : ℝ) * t ^ k * R ^ (n - k)) := by
                      refine Finset.sum_congr rfl ?_
                      intro n hn
                      by_cases hkn : k ≤ n
                      · simp [hkn]
                      · have hchoose : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt (lt_of_not_ge hkn)
                        simp [hkn, hchoose]
            _ = ∑ n ∈ Finset.range N,
                  t ^ k * (a n * ((Nat.choose n k : ℝ) * R ^ (n - k))) := by
                    refine Finset.sum_congr rfl ?_
                    intro n hn
                    ring
            _ = t ^ k * (∑ n ∈ Finset.range N, a n * ((Nat.choose n k : ℝ) * R ^ (n - k))) := by
                    rw [Finset.mul_sum]

/--
Ordered comparison form of `sum_range_mul_add_pow_reindex`.

If the reindexed inner sums admit bounds `b k`, then the original shifted
partial sum is bounded by the corresponding weighted `b`-sum.
-/
theorem sum_range_mul_add_pow_le_of_inner_le
    (a b : ℕ → ℝ) (R t : ℝ) (N : ℕ)
    (ht : 0 ≤ t)
    (hinner :
      ∀ k : ℕ,
        k < N →
          (∑ n ∈ Finset.range N, a n * ((Nat.choose n k : ℝ) * R ^ (n - k))) ≤ b k) :
    (∑ n ∈ Finset.range N, a n * (R + t) ^ n)
      ≤ ∑ k ∈ Finset.range N, t ^ k * b k := by
  rw [sum_range_mul_add_pow_reindex a R t N]
  refine Finset.sum_le_sum ?_
  intro k hk
  have hklt : k < N := Finset.mem_range.mp hk
  have hpow_nonneg : 0 ≤ t ^ k := pow_nonneg ht k
  exact mul_le_mul_of_nonneg_left (hinner k hklt) hpow_nonneg

end Aristotle.Standalone.PringsheimBinomialRearrangement
