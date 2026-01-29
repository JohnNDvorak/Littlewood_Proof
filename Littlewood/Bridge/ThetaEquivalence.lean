/-
# Theta Definition Equivalence Bridge

Connects ThetaLinearBoundV2's `theta : ℕ → ℝ` to ThetaLinearBound's `theta : ℝ → ℝ`.

Key insight: both sum `log p` over primes `p ≤ n`, just using different finset
representations:
- ThetaLinearBound: `∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), log p`  (ℝ → ℝ)
- ThetaLinearBoundV2: `∑ p ∈ (Finset.range (n+1)).filter Nat.Prime, log p`  (ℕ → ℝ)

Since `Nat.primesBelow (n+1) = (Finset.range (n+1)).filter Nat.Prime` and `⌊(n:ℝ)⌋₊ = n`,
the definitions agree on natural numbers.

This bridge enables closing the 2 sorries in ThetaLinearBound.lean using
ThetaLinearBoundV2's sorry-free proofs.

Co-authored-by: Claude <noreply@anthropic.com>
-/

import Littlewood.Aristotle.ThetaLinearBound
import Littlewood.Aristotle.ThetaLinearBoundV2

open scoped BigOperators Real

noncomputable section

/-! ## Finset Equivalence -/

/-- `Nat.primesBelow (n+1)` equals `(Finset.range (n+1)).filter Nat.Prime` -/
theorem primesBelow_eq_range_filter (n : ℕ) :
    Nat.primesBelow (n + 1) = (Finset.range (n + 1)).filter Nat.Prime := by
  ext p
  simp [Nat.primesBelow, Finset.mem_filter, Finset.mem_range]

/-! ## Definition Equivalence -/

/-- ThetaLinearBound.theta on a natural number equals ThetaLinearBoundV2.theta -/
theorem theta_eq_at_nat (n : ℕ) :
    ThetaLinearBound.theta (n : ℝ) = ThetaLinearBoundV2.theta n := by
  unfold ThetaLinearBound.theta ThetaLinearBoundV2.theta
  congr 1
  have : ⌊(n : ℝ)⌋₊ = n := Nat.floor_natCast n
  rw [this, primesBelow_eq_range_filter]

/-! ## Central Binomial Equivalence -/

/-- `Nat.centralBinom n = Nat.choose (2*n) n` -/
theorem centralBinom_eq_choose (n : ℕ) :
    Nat.centralBinom n = Nat.choose (2 * n) n := by
  simp [Nat.centralBinom]

/-- The prime finset difference equals the Ioc filter -/
theorem primesBelow_sdiff_eq_Ioc_filter (n : ℕ) :
    (Nat.primesBelow (2 * n + 1)) \ (Nat.primesBelow (n + 1)) =
    (Finset.Ioc n (2 * n)).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_sdiff, Nat.primesBelow, Finset.mem_filter, Finset.mem_range,
    Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hp_lt, hp_prime⟩, hp_not⟩
    refine ⟨⟨?_, ?_⟩, hp_prime⟩
    · by_contra h
      push_neg at h
      exact hp_not ⟨Nat.lt_succ_of_le h, hp_prime⟩
    · omega
  · rintro ⟨⟨hp_gt, hp_le⟩, hp_prime⟩
    exact ⟨⟨by omega, hp_prime⟩, fun ⟨h, _⟩ => by omega⟩

/-! ## Transferred Theorems -/

/-- Close ThetaLinearBound's prod_primes sorry using V2's proof -/
theorem prod_primes_from_V2 (n : ℕ) :
    ∏ p ∈ (Nat.primesBelow (2 * n + 1)) \ (Nat.primesBelow (n + 1)), p ∣
    Nat.centralBinom n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.primesBelow, Nat.centralBinom]
  · rw [centralBinom_eq_choose, primesBelow_sdiff_eq_Ioc_filter]
    exact ThetaLinearBoundV2.prod_primes_divides_centralBinom n hn

/-- Close ThetaLinearBound's theta_two_mul_sub_theta_le sorry using V2's proof -/
theorem theta_two_mul_sub_from_V2 (n : ℕ) :
    ThetaLinearBound.theta (2 * n) - ThetaLinearBound.theta n ≤ 2 * n * Real.log 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ThetaLinearBound.theta, Nat.primesBelow]
  · rw [show (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) from by push_cast; ring]
    rw [theta_eq_at_nat, theta_eq_at_nat]
    have := ThetaLinearBoundV2.theta_two_mul_sub_theta_le n hn
    convert this using 1
    push_cast; ring

end
