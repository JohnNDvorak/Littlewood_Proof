/-
Derived RS sign-structure consequences from the atomic per-block signed input.

This file adds no new axioms/sorries; it repackages the current atomic
`per_block_signed_bound` statement into reusable corollaries.
-/

import Mathlib
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.RSBlockDecomposition

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.RSSignStructure

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

/-- Extract the local per-block signed approximation component from
`RSBlockDecomposition.per_block_signed_bound`. -/
theorem per_block_signed_centered :
    ∃ A B : ℝ, A > 0 ∧ B ≥ 0 ∧
      (∀ T : ℝ, T ≥ 2 →
        ∀ k : ℕ, k < hardyN T →
          ∃ s : ℝ, s = (-1 : ℝ) ^ k ∧
            |(∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
                ErrorTerm t) - s * A * Real.sqrt ((k : ℝ) + 1)| ≤ B) := by
  rcases Aristotle.RSBlockDecomposition.per_block_signed_bound with
    ⟨A, B, hA, hB, hlocal, _hglobal⟩
  exact ⟨A, B, hA, hB, hlocal⟩

/-- Extract the global alternating-sqrt decomposition component from
`RSBlockDecomposition.per_block_signed_bound`. -/
theorem global_alternating_decomposition :
    ∃ A B : ℝ, A > 0 ∧ B ≥ 0 ∧
      (∀ T : ℝ, T ≥ 2 →
        ∃ N : ℕ,
          ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
          |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + B) := by
  rcases Aristotle.RSBlockDecomposition.per_block_signed_bound with
    ⟨A, B, hA, hB, _hlocal, hglobal⟩
  exact ⟨A, B, hA, hB, hglobal⟩

/-- The signed per-block approximation implies a coarse absolute per-block
bound of size `A*sqrt(k+1) + B`. -/
theorem per_block_abs_bound_from_signed :
    ∃ A B : ℝ, A > 0 ∧ B ≥ 0 ∧
      (∀ T : ℝ, T ≥ 2 →
        ∀ k : ℕ, k < hardyN T →
          |∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t|
            ≤ A * Real.sqrt ((k : ℝ) + 1) + B) := by
  rcases per_block_signed_centered with ⟨A, B, hA, hB, hlocal⟩
  refine ⟨A, B, hA, hB, ?_⟩
  intro T hT k hk
  rcases hlocal T hT k hk with ⟨s, hs, hclose⟩
  let I : ℝ := ∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t
  let y : ℝ := s * A * Real.sqrt ((k : ℝ) + 1)

  have htri : |I| ≤ |I - y| + |y| := by
    have h := norm_add_le (I - y) y
    simpa [I, y, Real.norm_eq_abs, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

  have hsabs : |s| = 1 := by
    rw [hs]
    simp

  have hy_nonneg : 0 ≤ A * Real.sqrt ((k : ℝ) + 1) := by
    exact mul_nonneg (le_of_lt hA) (Real.sqrt_nonneg _)

  have hy_abs : |y| = A * Real.sqrt ((k : ℝ) + 1) := by
    calc
      |y| = |s| * |A * Real.sqrt ((k : ℝ) + 1)| := by
              simp [y, abs_mul, mul_assoc]
      _ = 1 * |A * Real.sqrt ((k : ℝ) + 1)| := by rw [hsabs]
      _ = |A * Real.sqrt ((k : ℝ) + 1)| := by ring
      _ = A * Real.sqrt ((k : ℝ) + 1) := by
            exact abs_of_nonneg hy_nonneg

  have hclose' : |I - y| ≤ B := by
    simpa [I, y] using hclose

  have : |I| ≤ B + A * Real.sqrt ((k : ℝ) + 1) := by
    linarith [htri, hclose', hy_abs]

  linarith

end Aristotle.RSSignStructure
