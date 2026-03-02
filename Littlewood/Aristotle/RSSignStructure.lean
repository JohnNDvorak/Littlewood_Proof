/-
Derived RS sign-structure consequences from the atomic per-block signed input.

This file adds no new axioms/sorries; it repackages the current atomic
`per_block_signed_bound` statement into reusable corollaries.

NOTE (2026-03): `per_block_signed_centered` and `per_block_abs_bound_from_signed`
were removed — they extracted the local clause which was false and has been
deleted from `PerBlockSignedBoundHyp`. They had no downstream consumers.
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

/-- Extract the global alternating-sqrt decomposition component from
`RSBlockDecomposition.per_block_signed_bound`. -/
theorem global_alternating_decomposition :
    Aristotle.RSBlockDecomposition.PerBlockSignedBoundHyp →
    ∃ A B : ℝ, A > 0 ∧ B ≥ 0 ∧
      (∀ T : ℝ, T ≥ 2 →
        ∃ N : ℕ,
          ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
          |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + B) := by
  intro hyp
  rcases Aristotle.RSBlockDecomposition.per_block_signed_bound hyp with
    ⟨A, B, hA, hB, hglobal⟩
  exact ⟨A, B, hA, hB, hglobal⟩

end Aristotle.RSSignStructure
