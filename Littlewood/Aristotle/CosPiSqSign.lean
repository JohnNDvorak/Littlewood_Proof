/-
Arithmetic lemmas for the alternating sign structure in the Hardy first moment.

KEY RESULTS:
  cos_pi_mul_nat_sq: cos(π·n²) = (-1)^n for n : ℕ
  neg_one_pow_nat_sq: (-1)^(n²) = (-1)^n for n : ℕ
  alternating_sqrt_sum_bound: |∑_{k=0}^{n} (-1)^k · √(k+1)| ≤ √(n+1)

The first result is the key sign identity:
  Stationary phase of the n-th mode in the Hardy Z first moment gives
  cos(θ(t₀) - t₀·log(n+1)) ≈ cos(π·n²) = (-1)^n, producing an
  alternating sum. Combined with Abel summation (AbelSummation.lean),
  the total is O(√N) instead of O(N^{3/2}), breaking the T^{3/4} barrier.

DEPENDENCIES: AbelSummation.lean (for alternating_sqrt_sum_bound)
Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.AbelSummation

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CosPiSqSign

open Finset Real

/-- (-1)^(n²) = (-1)^n for natural numbers.
    Key fact: n² = n·n, so (-1)^(n²) = ((-1)^n)^n.
    Since (-1)^n ∈ {1, -1}, raising to the n-th power preserves the value. -/
theorem neg_one_pow_nat_sq (n : ℕ) : (-1 : ℝ) ^ (n ^ 2) = (-1 : ℝ) ^ n := by
  rw [sq, pow_mul]
  -- Goal: ((-1 : ℝ) ^ n) ^ n = (-1 : ℝ) ^ n
  rcases n.even_or_odd with h | h <;> simp [h.neg_one_pow]

/-- cos(π · n²) = (-1)^n for n : ℕ.
    The key sign identity for Hardy's first moment analysis:
    the stationary phase value cos(πn²) alternates in sign. -/
theorem cos_pi_mul_nat_sq (n : ℕ) : Real.cos (Real.pi * (n : ℝ) ^ 2) = (-1 : ℝ) ^ n := by
  rw [show Real.pi * (n : ℝ) ^ 2 = ((n ^ 2 : ℕ) : ℝ) * Real.pi from by push_cast; ring]
  rw [Real.cos_nat_mul_pi, neg_one_pow_nat_sq]

/-- cos(π · (n+1)²) = (-1)^(n+1) for n : ℕ.
    Shifted version for the sum starting at n=0. -/
theorem cos_pi_mul_succ_sq (n : ℕ) :
    Real.cos (Real.pi * ((n : ℝ) + 1) ^ 2) = (-1 : ℝ) ^ (n + 1) := by
  rw [show Real.pi * ((n : ℝ) + 1) ^ 2 = (((n + 1) ^ 2 : ℕ) : ℝ) * Real.pi from by
    push_cast; ring]
  rw [Real.cos_nat_mul_pi, neg_one_pow_nat_sq]

/-- The alternating sum of √(k+1) is bounded by √(n+1).
    Direct consequence of alternating_sum_le_last from AbelSummation.lean
    with a(k) = √(k+1), which is monotone and nonneg.

    This is the key bound that reduces the Hardy first moment from
    O(T^{3/4}) (naive) to O(T^{1/4}) (alternating sign). -/
theorem alternating_sqrt_sum_bound (n : ℕ) :
    |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * Real.sqrt (↑k + 1)| ≤
      Real.sqrt (↑n + 1) := by
  exact AbelSummation.alternating_sum_le_last
    (fun k => Real.sqrt (↑k + 1))
    (fun k => Real.sqrt_nonneg _)
    (fun a b hab => Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_right hab 1))
    n

/-- The sum ∑_{k=0}^{n} (-1)^k · √(k+1) · c for constant c ≥ 0
    is bounded by c · √(n+1). -/
theorem alternating_sqrt_sum_const_bound (n : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (c * Real.sqrt (↑k + 1))| ≤
      c * Real.sqrt (↑n + 1) := by
  have hrw : ∀ k ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ k * (c * Real.sqrt (↑k + 1)) =
      c * ((-1 : ℝ) ^ k * Real.sqrt (↑k + 1)) := by
    intros; ring
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (alternating_sqrt_sum_bound n) hc

end CosPiSqSign
