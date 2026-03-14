/-
Abel summation (summation by parts) and alternating series bound.

KEY RESULTS:
  abel_summation_by_parts: ∑_{k=0}^{n} a(k)·b(k) = A(n)·b(n) - ∑_{k=0}^{n-1} A(k)·(b(k+1)-b(k))
  abel_summation_bound: |∑ a(k)·b(k)| ≤ C·b(0) for |A(k)| ≤ C, b nonneg antitone
  abel_bound_from_one: shifted version starting from index 1
  alternating_sum_le_last: |∑_{k=0}^{n} (-1)^k * a_k| ≤ a_n for monotone nonneg a
  alternating_antitone_sum_le_first: |∑ (-1)^k a_k| ≤ a_0 for antitone nonneg a

Applications:
- Hardy first moment: alternating sign structure from cos(πn²) = (-1)^n
- Siegel wall polynomial mismatch: exponential sum × monotone amplitude
- Dirichlet-type sums: bounded partial sums × decaying amplitude

SORRY COUNT: 0

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

/-! ## General Abel summation by parts

The classical identity: ∑_{k=0}^{n} a(k)·b(k) = A(n)·b(n) - ∑_{k=0}^{n-1} A(k)·(b(k+1)-b(k))
where A(k) = ∑_{j=0}^{k} a(j).

This is the discrete analogue of integration by parts. Combined with bounds on the
partial sums A(k), it gives the Abel summation bound:
  |∑ a(k)·b(k)| ≤ max_k |A(k)| · b(0)
when b is nonneg and antitone.

Applications:
- Bounding Dirichlet-type sums Σ a(n)·n^{-s} when partial sums A(N) are bounded
- Polynomial mismatch in the Siegel wall argument (exponential sum × monotone amplitude)
- Converting VdC exponential sum bounds into L-function estimates

Reference: Apostol, Introduction to Analytic Number Theory, Theorem 4.2.
-/

/-- **Abel summation by parts** (summation-by-parts identity):
    ∑_{k=0}^{n} a(k)·b(k) = A(n)·b(n) - ∑_{k=0}^{n-1} A(k)·(b(k+1) - b(k))
    where A(k) = ∑_{j=0}^{k} a(j).

    This is the discrete analogue of integration by parts ∫ u dv = uv - ∫ v du.
    PROVED by induction on n. -/
theorem abel_summation_by_parts (a b : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), a k * b k =
      (∑ k ∈ Finset.range (n + 1), a k) * b n -
        ∑ k ∈ Finset.range n,
          (∑ j ∈ Finset.range (k + 1), a j) * (b (k + 1) - b k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have lhs_expand : ∑ k ∈ Finset.range (n + 2), a k * b k =
        (∑ k ∈ Finset.range (n + 1), a k * b k) + a (n + 1) * b (n + 1) :=
      Finset.sum_range_succ _ _
    have rhs_sum_expand : ∑ k ∈ Finset.range (n + 1),
        (∑ j ∈ Finset.range (k + 1), a j) * (b (k + 1) - b k) =
      (∑ k ∈ Finset.range n,
        (∑ j ∈ Finset.range (k + 1), a j) * (b (k + 1) - b k)) +
        (∑ j ∈ Finset.range (n + 1), a j) * (b (n + 1) - b n) :=
      Finset.sum_range_succ _ _
    have a_expand : ∑ k ∈ Finset.range (n + 2), a k =
        (∑ k ∈ Finset.range (n + 1), a k) + a (n + 1) :=
      Finset.sum_range_succ _ _
    rw [show n + 1 + 1 = n + 2 from by omega]
    rw [lhs_expand, ih, rhs_sum_expand, a_expand]
    ring

/-- **Abel summation bound**: if partial sums |A(k)| ≤ C for all k ≤ n and
    b is nonneg antitone, then |∑_{k=0}^{n} a(k)·b(k)| ≤ C·b(0).

    Proof: from the Abel identity,
      |A(n)·b(n) - ∑ A(k)·Δb(k)| ≤ C·b(n) + C·∑|Δb(k)|
                                    = C·b(n) + C·(b(0) - b(n))  [telescoping]
                                    = C·b(0).

    This is the key tool for converting exponential sum bounds into
    Dirichlet series estimates. PROVED from `abel_summation_by_parts`. -/
theorem abel_summation_bound (a b : ℕ → ℝ) (n : ℕ) (C : ℝ)
    (h_partial : ∀ k ≤ n, |∑ j ∈ Finset.range (k + 1), a j| ≤ C)
    (h_nonneg : ∀ k ≤ n, 0 ≤ b k)
    (h_anti : ∀ k < n, b (k + 1) ≤ b k) :
    |∑ k ∈ Finset.range (n + 1), a k * b k| ≤ C * b 0 := by
  rw [abel_summation_by_parts]
  -- Bound the A(n)·b(n) term
  have h1 : |(∑ k ∈ Finset.range (n + 1), a k) * b n| ≤ C * b n := by
    rw [abs_mul, abs_of_nonneg (h_nonneg n le_rfl)]
    exact mul_le_mul_of_nonneg_right (h_partial n le_rfl) (h_nonneg n le_rfl)
  -- Bound the Abel correction sum using telescoping
  have h2 : |∑ k ∈ Finset.range n,
      (∑ j ∈ Finset.range (k + 1), a j) * (b (k + 1) - b k)| ≤
      C * (b 0 - b n) := by
    calc |∑ k ∈ Finset.range n,
          (∑ j ∈ Finset.range (k + 1), a j) * (b (k + 1) - b k)|
        ≤ ∑ k ∈ Finset.range n,
          |(∑ j ∈ Finset.range (k + 1), a j) * (b (k + 1) - b k)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ Finset.range n,
          |∑ j ∈ Finset.range (k + 1), a j| * |b (k + 1) - b k| := by
          congr 1; ext k; exact abs_mul _ _
      _ ≤ ∑ k ∈ Finset.range n, C * (b k - b (k + 1)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' : k < n := Finset.mem_range.mp hk
          have h_diff : b (k + 1) - b k ≤ 0 := sub_nonpos.mpr (h_anti k hk')
          rw [abs_of_nonpos h_diff, neg_sub]
          exact mul_le_mul_of_nonneg_right
            (h_partial k (le_of_lt hk')) (sub_nonneg.mpr (h_anti k hk'))
      _ = C * ∑ k ∈ Finset.range n, (b k - b (k + 1)) := by rw [← Finset.mul_sum]
      _ = C * (b 0 - b n) := by rw [Finset.sum_range_sub']
  -- Combine via triangle inequality
  calc |(∑ k ∈ Finset.range (n + 1), a k) * b n -
        ∑ k ∈ Finset.range n,
          (∑ j ∈ Finset.range (k + 1), a j) * (b (k + 1) - b k)|
      ≤ |(∑ k ∈ Finset.range (n + 1), a k) * b n| +
        |∑ k ∈ Finset.range n,
          (∑ j ∈ Finset.range (k + 1), a j) * (b (k + 1) - b k)| :=
        abs_sub _ _
    _ ≤ C * b n + C * (b 0 - b n) := add_le_add h1 h2
    _ = C * b 0 := by ring

/-- Corollary: Abel bound with explicit partial sum function.
    If S(k) = ∑_{j=0}^{k} a(j) satisfies |S(k)| ≤ C and b is nonneg antitone,
    then |∑ a(k)·b(k)| ≤ C·b(0). -/
theorem abel_bound_with_partialSum (a b : ℕ → ℝ) (n : ℕ) (C : ℝ)
    (h_partial : ∀ k ≤ n, |partialSum a k| ≤ C)
    (h_nonneg : ∀ k ≤ n, 0 ≤ b k)
    (h_anti : ∀ k < n, b (k + 1) ≤ b k) :
    |∑ k ∈ Finset.range (n + 1), a k * b k| ≤ C * b 0 := by
  exact abel_summation_bound a b n C
    (fun k hk => by exact h_partial k hk)
    h_nonneg h_anti

/-- Abel bound for Dirichlet-type sums: if the oscillatory partial sums
    A(k) = ∑_{j ≤ k} a(j) satisfy |A(k)| ≤ C, and the amplitude b(k) = k^{-α}
    for some α > 0, then |∑_{k=1}^{N} a(k)·b(k)| ≤ C·b(1) = C.

    More generally: for any bounded partial sums and nonneg antitone amplitude
    starting from index 1. PROVED from `abel_summation_bound` via shift. -/
theorem abel_bound_from_one (a b : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (C : ℝ)
    (h_partial : ∀ k, 1 ≤ k → k ≤ n →
      |∑ j ∈ Finset.range k, a (j + 1)| ≤ C)
    (h_nonneg : ∀ k, 1 ≤ k → k ≤ n → 0 ≤ b k)
    (h_anti : ∀ k, 1 ≤ k → k < n → b (k + 1) ≤ b k) :
    |∑ k ∈ Finset.range n, a (k + 1) * b (k + 1)| ≤ C * b 1 := by
  -- Shift: let a'(k) = a(k+1), b'(k) = b(k+1)
  set a' : ℕ → ℝ := fun k => a (k + 1) with ha'_def
  set b' : ℕ → ℝ := fun k => b (k + 1) with hb'_def
  have h_eq : ∑ k ∈ Finset.range n, a (k + 1) * b (k + 1) =
      ∑ k ∈ Finset.range n, a' k * b' k := by rfl
  rw [h_eq]
  -- Apply abel_summation_bound with n replaced by n-1
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [hm]
  apply abel_summation_bound a' b' m C
  · intro k hk
    rw [ha'_def]
    exact h_partial (k + 1) (by omega) (by omega)
  · intro k hk
    exact h_nonneg (k + 1) (by omega) (by omega)
  · intro k hk
    exact h_anti (k + 1) (by omega) (by omega)

end AbelSummation
