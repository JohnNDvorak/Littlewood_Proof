/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.PrimeCounting
import Littlewood.Basic.ChebyshevFunctions

/-!
# Prime Counting Helper Lemmas

Wrappers and extensions for Mathlib's prime counting infrastructure.

## Main Results (from Mathlib)

* `Nat.monotone_primeCounting` : π is monotone
* `Nat.tendsto_primeCounting` : π → ∞ as n → ∞

## Additional Results

* `chebyshevPsi_nonneg` : ψ(x) ≥ 0
* `chebyshevTheta_nonneg` : θ(x) ≥ 0
-/

open Nat Filter Topology

namespace Littlewood.Development.PrimeHelpers

/-- Wrapper: π is monotone (from Mathlib) -/
theorem primeCounting_mono : Monotone Nat.primeCounting :=
  Nat.monotone_primeCounting

/-- Wrapper: π → ∞ (from Mathlib) -/
theorem primeCounting_tendsto_atTop :
    Tendsto Nat.primeCounting atTop atTop :=
  Nat.tendsto_primeCounting

/-- ψ(x) ≥ 0 since it's a sum of non-negative von Mangoldt values -/
theorem chebyshevPsi_nonneg (x : ℝ) : 0 ≤ chebyshevPsi x := by
  unfold chebyshevPsi
  apply Finset.sum_nonneg
  intro i _
  exact ArithmeticFunction.vonMangoldt_nonneg

/-- θ(x) ≥ 0 since it's a sum of non-negative log primes -/
theorem chebyshevTheta_nonneg (x : ℝ) : 0 ≤ chebyshevTheta x := by
  unfold chebyshevTheta
  apply Finset.sum_nonneg
  intro i hi
  simp only [Finset.mem_filter] at hi
  exact Real.log_nonneg (Nat.one_le_cast.mpr (Nat.Prime.one_le hi.2))

/-- ψ is monotone: if x ≤ y then ψ(x) ≤ ψ(y) -/
theorem chebyshevPsi_mono : Monotone chebyshevPsi := by
  intro x y hxy
  unfold chebyshevPsi
  have hsub : Finset.Icc 1 (Nat.floor x) ⊆ Finset.Icc 1 (Nat.floor y) := by
    intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    exact ⟨hi.1, le_trans hi.2 (Nat.floor_mono hxy)⟩
  calc ∑ i ∈ Finset.Icc 1 (Nat.floor x), ArithmeticFunction.vonMangoldt i
      ≤ ∑ i ∈ Finset.Icc 1 (Nat.floor y), ArithmeticFunction.vonMangoldt i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)

/-- θ is monotone: if x ≤ y then θ(x) ≤ θ(y) -/
theorem chebyshevTheta_mono : Monotone chebyshevTheta := by
  intro x y hxy
  unfold chebyshevTheta
  have hsub : (Finset.Icc 1 (Nat.floor x)).filter Nat.Prime ⊆
              (Finset.Icc 1 (Nat.floor y)).filter Nat.Prime := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_Icc] at hi ⊢
    exact ⟨⟨hi.1.1, le_trans hi.1.2 (Nat.floor_mono hxy)⟩, hi.2⟩
  calc ∑ i ∈ (Finset.Icc 1 (Nat.floor x)).filter Nat.Prime, Real.log i
      ≤ ∑ i ∈ (Finset.Icc 1 (Nat.floor y)).filter Nat.Prime, Real.log i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro i hi _
        simp only [Finset.mem_filter] at hi
        exact Real.log_nonneg (Nat.one_le_cast.mpr (Nat.Prime.one_le hi.2))

end Littlewood.Development.PrimeHelpers
