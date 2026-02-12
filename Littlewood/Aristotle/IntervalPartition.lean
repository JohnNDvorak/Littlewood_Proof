/- 
Finite interval-partition lemmas for set integrals on `Ioc`.

These lemmas are lightweight infrastructure for decomposing
`∫ t in Ioc a b, f t` across adjacent breakpoints.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.IntervalPartition

open MeasureTheory Set

/-- Split a set integral across a single adjacent breakpoint. -/
theorem integral_split_at (f : ℝ → ℝ) (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (hf1 : IntegrableOn f (Set.Ioc a b)) (hf2 : IntegrableOn f (Set.Ioc b c)) :
    ∫ t in Set.Ioc a c, f t ∂volume =
      ∫ t in Set.Ioc a b, f t ∂volume + ∫ t in Set.Ioc b c, f t ∂volume := by
  have h_union := setIntegral_union (Ioc_disjoint_Ioc_of_le (le_refl b))
    measurableSet_Ioc hf1 hf2
  rw [Ioc_union_Ioc_eq_Ioc hab hbc] at h_union
  exact h_union

private lemma bp_zero_le (bp : ℕ → ℝ) :
    ∀ N : ℕ, (∀ k, k < N → bp k ≤ bp (k + 1)) → bp 0 ≤ bp N
  | 0, _ => le_rfl
  | N + 1, h => by
      have h_prev : bp 0 ≤ bp N := bp_zero_le bp N (fun k hk =>
        h k (Nat.lt_trans hk (Nat.lt_succ_self N)))
      exact le_trans h_prev (h N (Nat.lt_succ_self N))

/-- Integrability of `f` on the whole interval from integrability on adjacent blocks. -/
theorem integrableOn_split_finitely (f : ℝ → ℝ) (bp : ℕ → ℝ) :
    ∀ N : ℕ,
      (∀ k, k < N → bp k ≤ bp (k + 1)) →
      (∀ k, k < N → IntegrableOn f (Set.Ioc (bp k) (bp (k + 1)))) →
      IntegrableOn f (Set.Ioc (bp 0) (bp N))
  | 0, _, _ => by
      simpa using (integrableOn_empty : IntegrableOn f (∅ : Set ℝ))
  | N + 1, h_mono, h_int => by
      have h_monoN : ∀ k, k < N → bp k ≤ bp (k + 1) := by
        intro k hk
        exact h_mono k (Nat.lt_trans hk (Nat.lt_succ_self N))
      have h_intN : ∀ k, k < N → IntegrableOn f (Set.Ioc (bp k) (bp (k + 1))) := by
        intro k hk
        exact h_int k (Nat.lt_trans hk (Nat.lt_succ_self N))
      have h_left : IntegrableOn f (Set.Ioc (bp 0) (bp N)) :=
        integrableOn_split_finitely f bp N h_monoN h_intN
      have h_right : IntegrableOn f (Set.Ioc (bp N) (bp (N + 1))) :=
        h_int N (Nat.lt_succ_self N)
      have h_union : IntegrableOn f
          ((Set.Ioc (bp 0) (bp N)) ∪ Set.Ioc (bp N) (bp (N + 1))) :=
        h_left.union h_right
      have h0N : bp 0 ≤ bp N := bp_zero_le bp N h_monoN
      have hN : bp N ≤ bp (N + 1) := h_mono N (Nat.lt_succ_self N)
      have h_set :
          (Set.Ioc (bp 0) (bp N)) ∪ Set.Ioc (bp N) (bp (N + 1))
            = Set.Ioc (bp 0) (bp (N + 1)) :=
        Ioc_union_Ioc_eq_Ioc h0N hN
      simpa [h_set] using h_union

private noncomputable def blockInt (f : ℝ → ℝ) (bp : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∫ t in Set.Ioc (bp k) (bp (k + 1)), f t ∂volume

/-- Split a set integral along finitely many adjacent breakpoints. -/
theorem integral_split_finitely (f : ℝ → ℝ) (bp : ℕ → ℝ) :
    ∀ N : ℕ,
      (∀ k, k < N → bp k ≤ bp (k + 1)) →
      (∀ k, k < N → IntegrableOn f (Set.Ioc (bp k) (bp (k + 1)))) →
      ∫ t in Set.Ioc (bp 0) (bp N), f t ∂volume
        = Finset.sum (Finset.range N) (fun k => blockInt f bp k)
  | 0, _, _ => by
      simp
  | N + 1, h_mono, h_int => by
      have h_monoN : ∀ k, k < N → bp k ≤ bp (k + 1) := by
        intro k hk
        exact h_mono k (Nat.lt_trans hk (Nat.lt_succ_self N))
      have h_intN : ∀ k, k < N → IntegrableOn f (Set.Ioc (bp k) (bp (k + 1))) := by
        intro k hk
        exact h_int k (Nat.lt_trans hk (Nat.lt_succ_self N))
      have h_left_int : IntegrableOn f (Set.Ioc (bp 0) (bp N)) :=
        integrableOn_split_finitely f bp N h_monoN h_intN
      have h_right_int : IntegrableOn f (Set.Ioc (bp N) (bp (N + 1))) :=
        h_int N (Nat.lt_succ_self N)
      have h0N : bp 0 ≤ bp N := bp_zero_le bp N h_monoN
      have hN : bp N ≤ bp (N + 1) := h_mono N (Nat.lt_succ_self N)
      have h_split :
          ∫ t in Set.Ioc (bp 0) (bp (N + 1)), f t ∂volume =
            ∫ t in Set.Ioc (bp 0) (bp N), f t ∂volume +
              ∫ t in Set.Ioc (bp N) (bp (N + 1)), f t ∂volume :=
        integral_split_at f (bp 0) (bp N) (bp (N + 1)) h0N hN h_left_int h_right_int
      calc
        ∫ t in Set.Ioc (bp 0) (bp (N + 1)), f t ∂volume
            = ∫ t in Set.Ioc (bp 0) (bp N), f t ∂volume +
                ∫ t in Set.Ioc (bp N) (bp (N + 1)), f t ∂volume := h_split
        _ = Finset.sum (Finset.range N) (fun k => blockInt f bp k) + blockInt f bp N := by
              rw [integral_split_finitely f bp N h_monoN h_intN]
              rfl
        _ = Finset.sum (Finset.range (N + 1)) (fun k => blockInt f bp k) := by
              rw [Finset.sum_range_succ]

end Aristotle.IntervalPartition
