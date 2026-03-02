/-
Abel summation (summation by parts) and alternating series bound.

KEY RESULTS:
  abel_summation: ∑_{k=0}^{n} f(k)*g(k) = F(n)*g(n) - ∑_{k=0}^{n-1} F(k)*(g(k+1)-g(k))
  alternating_sum_le_last: |∑_{k=0}^{n} (-1)^k * a_k| ≤ a_n for monotone nonneg a

These are needed for the Hardy first moment analysis: VdC per-mode gives T^{3/4}
(insufficient), but the alternating sign structure from stationary phase gives
cos(πn²) = (-1)^n, and this bound brings the total down to T^{1/4}.

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace AbelSummation

open Finset

/-- Partial sum F(n) = ∑_{k=0}^{n} f(k). -/
def partialSum (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), f k

@[simp] lemma partialSum_zero (f : ℕ → ℝ) : partialSum f 0 = f 0 := by
  simp [partialSum]

lemma partialSum_succ (f : ℕ → ℝ) (n : ℕ) :
    partialSum f (n + 1) = partialSum f n + f (n + 1) := by
  simp [partialSum, Finset.sum_range_succ]

/-- The two-term recurrence: S(n+2) = S(n) + (-1)^{n+1}·a(n+1) + (-1)^{n+2}·a(n+2).
    Simplifies to S(n+2) = S(n) + (-1)^n·(a(n+2) - a(n+1)). -/
private lemma alternating_sum_step (a : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 3), (-1 : ℝ) ^ k * a k =
    (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * a k) +
    (-1 : ℝ) ^ n * (a (n + 2) - a (n + 1)) := by
  rw [show n + 3 = (n + 2) + 1 from by omega, Finset.sum_range_succ,
      show n + 2 = (n + 1) + 1 from by omega, Finset.sum_range_succ]
  ring

/-- Alternating partial sum bound:
    |∑_{k=0}^{n} (-1)^k * a_k| ≤ a_n
    when a is monotone increasing and nonneg.

    Proof by strong induction with step 2:
    |S(n+2)| = |S(n) + (-1)^n (a(n+2)-a(n+1))|
             ≤ |S(n)| + (a(n+2)-a(n+1))   [triangle, monotone]
             ≤ a(n) + a(n+2) - a(n+1)       [IH]
             ≤ a(n+2)                         [a(n) ≤ a(n+1)] -/
theorem alternating_sum_le_last (a : ℕ → ℝ)
    (h_nonneg : ∀ k, 0 ≤ a k)
    (h_mono : Monotone a) (n : ℕ) :
    |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * a k| ≤ a n := by
  induction n using Nat.strongRec' with
  | _ n ih =>
    match n with
    | 0 =>
      simp only [show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one, pow_zero, one_mul]
      exact le_of_eq (abs_of_nonneg (h_nonneg 0))
    | 1 =>
      simp only [show (1 : ℕ) + 1 = 2 from rfl, Finset.sum_range_succ,
        Finset.sum_range_zero, pow_zero, one_mul, pow_one, neg_one_mul, zero_add]
      -- Goal: |a 0 + -a 1| ≤ a 1
      rw [show a 0 + -a 1 = -(a 1 - a 0) from by ring, abs_neg,
          abs_of_nonneg (sub_nonneg.mpr (h_mono (by omega)))]
      linarith [h_nonneg 0]
    | n + 2 =>
      rw [alternating_sum_step]
      calc |∑ k ∈ range (n + 1), (-1 : ℝ) ^ k * a k + (-1 : ℝ) ^ n * (a (n + 2) - a (n + 1))|
          ≤ |∑ k ∈ range (n + 1), (-1 : ℝ) ^ k * a k| + |(-1 : ℝ) ^ n * (a (n + 2) - a (n + 1))| :=
            abs_add_le _ _
        _ ≤ a n + (a (n + 2) - a (n + 1)) := by
            have h1 := ih n (by omega)
            have h2 : |(-1 : ℝ) ^ n * (a (n + 2) - a (n + 1))| = a (n + 2) - a (n + 1) := by
              rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
                  abs_of_nonneg (sub_nonneg.mpr (h_mono (by omega)))]
            linarith
        _ ≤ a (n + 2) := by linarith [h_mono (show n ≤ n + 1 from by omega)]

/-- Reindexing identity: ∑_{j<n+1} (-1)^(n-j) a(j) = (-1)^n · ∑_{j<n+1} (-1)^j a(j).
    Since (-1)^(n-j) = (-1)^n · (-1)^(-j) = (-1)^n · (-1)^j for natural exponents. -/
private lemma alternating_sum_reverse_sign (a : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - j) * a j =
    (-1 : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * a j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj_le : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← mul_assoc, ← pow_add, show n + j = (n - j) + 2 * j from by omega,
      pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

theorem alternating_antitone_sum_le_first (a : ℕ → ℝ)
    (h_nonneg : ∀ k, 0 ≤ a k)
    (h_anti : Antitone a) (n : ℕ) :
    |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * a k| ≤ a 0 := by
  -- Define reversed sequence b(k) = a(n-k). Then b is monotone nonneg.
  set b : ℕ → ℝ := fun k => a (n - k) with hb_def
  have hb_mono : Monotone b := fun i j hij => h_anti (Nat.sub_le_sub_left hij n)
  have hb_nonneg : ∀ k, 0 ≤ b k := fun k => h_nonneg _
  -- alternating_sum_le_last gives |∑_{k<n+1} (-1)^k b(k)| ≤ b(n) = a(0)
  have h_last := alternating_sum_le_last b hb_nonneg hb_mono n
  simp only [hb_def, Nat.sub_self] at h_last
  -- h_last : |∑_{k<n+1} (-1)^k a(n-k)| ≤ a 0
  -- Use sum_range_reflect to reindex: ∑_{k<n+1} f(n-k) = ∑_{k<n+1} f(k)
  -- where f(k) = (-1)^k * a(n-k)... but that doesn't directly help.
  -- Instead, directly rewrite ∑(-1)^k a(n-k) using the reverse sign lemma.
  -- sum_range_reflect gives: ∑_{j<m} f(m-1-j) = ∑_{j<m} f(j)
  -- With m = n+1, f(j) = (-1)^(n-j) * a(j):
  -- ∑_{j<n+1} (-1)^(n-(n-j)) * a(n-j) = ∑_{j<n+1} (-1)^(n-j) * a(j)
  -- LHS = ∑_{j<n+1} (-1)^j * a(n-j) (since n-(n-j) = j for j ≤ n)
  -- So: ∑_{j<n+1} (-1)^j a(n-j) = ∑_{j<n+1} (-1)^(n-j) a(j)
  --                                = (-1)^n · ∑_{j<n+1} (-1)^j a(j)
  -- Therefore |∑(-1)^j a(j)| = |(-1)^n · ∑(-1)^j a(j)| = |∑(-1)^j a(n-j)| ≤ a 0
  have h_reflect : ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * a (n - j)
      = ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - j) * a j := by
    rw [← Finset.sum_range_reflect (fun j => (-1 : ℝ) ^ (n - j) * a j) (n + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hj_le : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    show (-1 : ℝ) ^ j * a (n - j) = (-1 : ℝ) ^ (n - (n - j)) * a (n - j)
    rw [Nat.sub_sub_self hj_le]
  rw [h_reflect, alternating_sum_reverse_sign] at h_last
  rwa [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at h_last

end AbelSummation
