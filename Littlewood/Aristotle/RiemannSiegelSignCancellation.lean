/- 
Abstract sign-cancellation route for a `T^(1/4)` first-moment bound.

This module isolates the finite-dimensional Abel-summation step:
if an integral admits an alternating-`√(n+1)` decomposition with
index `N(T) ≲ T^(1/2)`, then the integral is `O(T^(1/4))`.
-/

import Mathlib
import Littlewood.Aristotle.CosPiSqSign
import Littlewood.Aristotle.HardyZFirstMoment

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace RiemannSiegelSignCancellation

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

/-- Abstract sign-cancellation criterion:
if `∫ E` is controlled by an alternating `√(n+1)` sum with `N(T) ≤ T^(1/2)`,
then `∫ E = O(T^(1/4))`. -/
theorem firstMoment_quarter_of_alternatingSqrt
    (E : ℝ → ℝ)
    (hdecomp :
      ∃ A B : ℝ, A > 0 ∧ B ≥ 0 ∧
        ∀ T : ℝ, T ≥ 2 →
          ∃ N : ℕ,
            ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
            |∫ t in Ioc 1 T, E t|
              ≤ A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + B) :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, E t| ≤ C * T ^ (1 / 4 : ℝ) := by
  rcases hdecomp with ⟨A, B, hA, hB, hdecompT⟩
  refine ⟨A + B, by linarith, ?_⟩
  intro T hT
  rcases hdecompT T hT with ⟨N, hN, hI⟩
  have hAlt :
      |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| ≤
        Real.sqrt ((N : ℝ) + 1) := by
    simpa [Nat.cast_add, Nat.cast_one] using CosPiSqSign.alternating_sqrt_sum_bound N
  have hSqrtN :
      Real.sqrt ((N : ℝ) + 1) ≤ T ^ (1 / 4 : ℝ) := by
    have hsqrt_le : Real.sqrt ((N : ℝ) + 1) ≤ Real.sqrt (T ^ (1 / 2 : ℝ)) :=
      Real.sqrt_le_sqrt hN
    have hTnn : 0 ≤ T := by linarith
    calc
      Real.sqrt ((N : ℝ) + 1) ≤ Real.sqrt (T ^ (1 / 2 : ℝ)) := hsqrt_le
      _ = (T ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
      _ = T ^ ((1 / 2 : ℝ) * (1 / 2 : ℝ)) := by
            rw [← Real.rpow_mul hTnn]
      _ = T ^ (1 / 4 : ℝ) := by ring_nf
  have hPow_ge_one : (1 : ℝ) ≤ T ^ (1 / 4 : ℝ) := by
    have hT1 : (1 : ℝ) ≤ T := by linarith
    exact Real.one_le_rpow hT1 (by norm_num)
  have hBmul : B ≤ B * T ^ (1 / 4 : ℝ) := by
    calc
      B = B * 1 := by ring
      _ ≤ B * T ^ (1 / 4 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hPow_ge_one hB
  calc
    |∫ t in Ioc 1 T, E t|
        ≤ A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + B := hI
    _ ≤ A * Real.sqrt ((N : ℝ) + 1) + B := by
          exact add_le_add (mul_le_mul_of_nonneg_left hAlt (le_of_lt hA)) le_rfl
    _ ≤ A * T ^ (1 / 4 : ℝ) + B := by
          exact add_le_add (mul_le_mul_of_nonneg_left hSqrtN (le_of_lt hA)) le_rfl
    _ ≤ A * T ^ (1 / 4 : ℝ) + B * T ^ (1 / 4 : ℝ) := by
          exact add_le_add_right hBmul _
    _ = (A + B) * T ^ (1 / 4 : ℝ) := by ring

/-- Specialization of `firstMoment_quarter_of_alternatingSqrt` to
`HardyEstimatesPartial.ErrorTerm`. -/
theorem errorTerm_firstMoment_quarter_of_alternatingSqrt
    (hdecomp :
      ∃ A B : ℝ, A > 0 ∧ B ≥ 0 ∧
        ∀ T : ℝ, T ≥ 2 →
          ∃ N : ℕ,
            ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
            |∫ t in Ioc 1 T, ErrorTerm t|
              ≤ A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + B) :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, ErrorTerm t| ≤ C * T ^ (1 / 4 : ℝ) := by
  simpa using firstMoment_quarter_of_alternatingSqrt ErrorTerm hdecomp

end RiemannSiegelSignCancellation
