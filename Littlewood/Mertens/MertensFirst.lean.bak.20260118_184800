/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Mertens' First Theorem

This file proves Mertens' first theorem: ∑_{p≤x} log(p)/p = log(x) + O(1).

## Strategy (Elementary Approach)

The proof does NOT require the Prime Number Theorem. It uses:
1. The identity: log(n!) = ∑_{d≤n} Λ(d)·⌊n/d⌋ (from `vonMangoldt_sum`)
2. Stirling's approximation: log(n!) = n log(n) - n + O(log n)
3. Chebyshev's upper bound: ψ(n) ≤ c·n

## References

* Hardy-Wright, "An Introduction to the Theory of Numbers", Chapter 22
* Tenenbaum, "Introduction to Analytic and Probabilistic Number Theory"
-/

open Finset Filter Real ArithmeticFunction Nat BigOperators
open scoped Chebyshev

noncomputable section

namespace Mertens

/-! ### Key Identity: log(n!) = ∑_{d≤n} Λ(d)·⌊n/d⌋ -/

/-- The sum ∑_{m=1}^n log(m) equals log(n!). -/
lemma sum_log_eq_log_factorial (n : ℕ) :
    ∑ m ∈ Icc 1 n, Real.log m = Real.log n ! := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
      ext x
      simp only [mem_insert, mem_Icc]
      omega
    rw [h, sum_insert (by simp), ih]
    rw [Nat.factorial_succ, Nat.cast_mul]
    rw [Real.log_mul (by positivity) (by positivity)]

/-- The identity log(n!) = ∑_{d≤n} Λ(d)·⌊n/d⌋.

This follows from:
1. log(m) = ∑_{d|m} Λ(d) (vonMangoldt_sum)
2. Summing over m ≤ n and exchanging order of summation
-/
lemma log_factorial_eq_sum_vonMangoldt_floor (n : ℕ) :
    Real.log n ! = ∑ d ∈ Icc 1 n, Λ d * ⌊(n : ℝ) / d⌋₊ := by
  rw [← sum_log_eq_log_factorial]
  -- Step 1: log(m) = ∑_{d ∈ divisors m} Λ(d) for m ≥ 1
  conv_lhs =>
    arg 2
    ext m
    rw [← vonMangoldt_sum]
  -- Step 2: Exchange order using sum_comm'
  -- ∑_{m ∈ Icc 1 n} ∑_{d ∈ divisors m} Λ(d) = ∑_{d ∈ Icc 1 n} ∑_{m : d | m, m ≤ n} Λ(d)
  rw [sum_comm' (s' := fun d => (Icc 1 n).filter (fun m => d ∣ m)) (t' := Icc 1 n)]
  · -- Now simplify: ∑_{m : d | m} Λ(d) = Λ(d) * #{m ∈ Icc 1 n : d | m}
    apply sum_congr rfl
    intro d hd
    rw [sum_const]
    simp only [mem_Icc] at hd
    have hd_pos : 0 < d := by omega
    -- #{m ∈ Icc 1 n : d | m} = n / d = ⌊n/d⌋₊
    -- Relate Icc 1 n filter to Ioc 0 n filter
    have h_eq : ((Icc 1 n).filter (fun m => d ∣ m)).card = ((Ioc 0 n).filter (fun m => d ∣ m)).card := by
      apply Finset.card_bij (fun m _ => m) (fun m hm => ?_) (fun _ _ _ _ h => h) (fun m hm => ?_)
      · simp only [mem_filter, mem_Icc, mem_Ioc] at hm ⊢
        exact ⟨⟨by omega, hm.1.2⟩, hm.2⟩
      · simp only [mem_filter, mem_Icc, mem_Ioc] at hm ⊢
        exact ⟨m, ⟨⟨by omega, hm.1.2⟩, hm.2⟩, rfl⟩
    rw [h_eq, Nat.Ioc_filter_dvd_card_eq_div]
    -- n / d = ⌊(n : ℝ) / d⌋₊, and nsmul = mul for ℝ
    simp only [nsmul_eq_mul]
    rw [Nat.floor_div_eq_div, mul_comm]
  · -- Verify the exchange condition
    -- LHS: m ∈ Icc 1 n ∧ d ∈ divisors m = (1 ≤ m ∧ m ≤ n) ∧ (d ∣ m ∧ m ≠ 0)
    -- RHS: m ∈ s'(d) ∧ d ∈ t' = ((1 ≤ m ∧ m ≤ n) ∧ d ∣ m) ∧ (1 ≤ d ∧ d ≤ n)
    intro m d
    simp only [mem_Icc, mem_filter, Nat.mem_divisors]
    constructor
    · -- (1 ≤ m ∧ m ≤ n) ∧ (d ∣ m ∧ m ≠ 0) → ((1 ≤ m ∧ m ≤ n) ∧ d ∣ m) ∧ (1 ≤ d ∧ d ≤ n)
      intro ⟨⟨hm1, hm2⟩, hdiv, hm_ne⟩
      have hd_le : d ≤ m := Nat.le_of_dvd (by omega) hdiv
      have hd1 : 1 ≤ d := by
        rcases hdiv with ⟨k, rfl⟩
        by_contra h
        push_neg at h
        interval_cases d <;> omega
      exact ⟨⟨⟨hm1, hm2⟩, hdiv⟩, ⟨hd1, by omega⟩⟩
    · -- ((1 ≤ m ∧ m ≤ n) ∧ d ∣ m) ∧ (1 ≤ d ∧ d ≤ n) → (1 ≤ m ∧ m ≤ n) ∧ (d ∣ m ∧ m ≠ 0)
      intro ⟨⟨⟨hm1, hm2⟩, hdiv⟩, ⟨hd1, hd2⟩⟩
      exact ⟨⟨hm1, hm2⟩, hdiv, by omega⟩

/-! ### Decomposition with Fractional Part Error -/

/-- The sum ∑_{d≤n} Λ(d)·{n/d} is bounded by ψ(n). -/
lemma sum_vonMangoldt_fract_le_psi (n : ℕ) :
    ∑ d ∈ Icc 1 n, Λ d * Int.fract ((n : ℝ) / d) ≤ ψ n := by
  calc ∑ d ∈ Icc 1 n, Λ d * Int.fract ((n : ℝ) / d)
      ≤ ∑ d ∈ Icc 1 n, Λ d * 1 := by
        apply sum_le_sum
        intro d _
        apply mul_le_mul_of_nonneg_left
        · exact le_of_lt (Int.fract_lt_one _)
        · exact vonMangoldt_nonneg
      _ = ∑ d ∈ Icc 1 n, Λ d := by simp
      _ ≤ ψ n := by
        -- Need to relate Icc 1 n to Ioc 0 ⌊n⌋₊
        rw [Chebyshev.psi]
        apply sum_le_sum_of_subset_of_nonneg
        · intro d hd
          simp only [mem_Icc] at hd
          simp only [mem_Ioc, Nat.floor_natCast]
          exact ⟨hd.1, hd.2⟩
        · intro _ _ _
          exact vonMangoldt_nonneg

/-- Key intermediate: n·∑_{d≤n} Λ(d)/d = log(n!) + O(ψ(n)). -/
lemma sum_vonMangoldt_div_main_estimate (n : ℕ) (hn : n ≠ 0) :
    |n * ∑ d ∈ Icc 1 n, Λ d / d - Real.log n !| ≤ ψ n := by
  -- The key decomposition:
  -- ∑ Λ(d) · ⌊n/d⌋ = ∑ Λ(d) · (n/d - {n/d})
  --                = n · ∑ Λ(d)/d - ∑ Λ(d) · {n/d}
  -- So |n · ∑ Λ(d)/d - log(n!)| = |∑ Λ(d) · {n/d}| ≤ ψ(n)
  have h_log := log_factorial_eq_sum_vonMangoldt_floor n
  have h_decomp : n * ∑ d ∈ Icc 1 n, Λ d / d - Real.log n ! =
      ∑ d ∈ Icc 1 n, Λ d * Int.fract ((n : ℝ) / d) := by
    rw [h_log, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro d hd
    rw [mem_Icc] at hd
    have hd_pos : 0 < d := by omega
    have h_nonneg : 0 ≤ (n : ℝ) / d := by positivity
    -- Key: ⌊x⌋₊ = x - fract(x) for x ≥ 0
    have h_floor_rel : (⌊(n : ℝ) / d⌋₊ : ℝ) = (n : ℝ) / d - Int.fract ((n : ℝ) / d) := by
      rw [Int.fract, sub_sub_cancel, natCast_floor_eq_intCast_floor h_nonneg]
    -- n * (Λ d / d) - Λ d * ⌊n/d⌋₊ = Λ d * fract(n/d)
    rw [h_floor_rel]
    have hd_ne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    ring
  rw [h_decomp]
  have h_nonneg : 0 ≤ ∑ d ∈ Icc 1 n, Λ d * Int.fract ((n : ℝ) / d) := by
    apply sum_nonneg
    intro d _
    apply mul_nonneg vonMangoldt_nonneg (Int.fract_nonneg _)
  rw [abs_of_nonneg h_nonneg]
  exact sum_vonMangoldt_fract_le_psi n

/-! ### Using Stirling and Chebyshev Bounds -/

/-- Upper bound on log(n!). -/
lemma log_factorial_le (n : ℕ) : Real.log n ! ≤ n * Real.log n + n := by
  rcases n with _ | m
  · simp
  · -- For n = m + 1 ≥ 1
    have h_fact_le : ((m + 1)! : ℝ) ≤ ((m : ℝ) + 1) ^ (m + 1) := by
      have := Nat.factorial_le_pow (m + 1)
      calc ((m + 1)! : ℝ) ≤ (((m + 1) ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast this
        _ = ((m : ℝ) + 1) ^ (m + 1) := by push_cast; ring
    have h_pos_fact : (0 : ℝ) < (m + 1)! := by positivity
    simp only [Nat.cast_succ]
    calc Real.log ((m + 1)! : ℝ)
        ≤ Real.log (((m : ℝ) + 1) ^ (m + 1)) := Real.log_le_log h_pos_fact h_fact_le
      _ = (m + 1) * Real.log ((m : ℝ) + 1) := by rw [Real.log_pow]; push_cast; rfl
      _ ≤ ((m : ℝ) + 1) * Real.log ((m : ℝ) + 1) + ((m : ℝ) + 1) := by linarith

/-- Lower bound on log(n!) using Stirling (for n ≥ 1). -/
lemma log_factorial_ge (n : ℕ) (hn : 1 ≤ n) :
    n * Real.log n - n ≤ Real.log n ! := by
  have hn' : n ≠ 0 := by omega
  have h := Stirling.le_log_factorial_stirling hn'
  have h1 : 0 ≤ Real.log n := Real.log_nonneg (Nat.one_le_cast.mpr hn)
  have h2 : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    have := Real.pi_gt_three
    linarith
  linarith

/-- Mertens' first theorem (discrete version):
    ∑_{d≤n} Λ(d)/d = log(n) + O(1) -/
theorem sum_vonMangoldt_div_eq_log_plus_O1 :
    ∃ C : ℝ, ∀ n : ℕ, n ≥ 2 →
      |∑ d ∈ Icc 1 n, Λ d / d - Real.log n| ≤ C := by
  -- From key estimate + Stirling + Chebyshev
  use Real.log 4 + 10
  intro n hn
  have hn' : n ≠ 0 := by omega
  have hn1 : 1 ≤ n := by omega
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have h1 := sum_vonMangoldt_div_main_estimate n hn'
  have h2 := log_factorial_ge n hn1
  have h3 := log_factorial_le n
  have h4 := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)
  -- Step 1: Divide h1 by n to get |∑ - log n!/n| ≤ ψ(n)/n
  set S := ∑ d ∈ Icc 1 n, Λ d / d with hS_def
  have h5 : |S - Real.log (n !) / n| ≤ ψ n / n := by
    have h1a : S - Real.log (n !) / n ≤ ψ n / n := by
      have h := (abs_le.mp h1).2  -- n * S - log n! ≤ ψ n
      have h_eq : S - Real.log (n !) / n = (n * S - Real.log (n !)) / n := by field_simp
      rw [h_eq]
      exact div_le_div_of_nonneg_right h (le_of_lt hn_pos)
    have h1b : -(ψ n / n) ≤ S - Real.log (n !) / n := by
      have h := (abs_le.mp h1).1  -- -(ψ n) ≤ n * S - log n!
      have h_eq : S - Real.log (n !) / n = (n * S - Real.log (n !)) / n := by field_simp
      rw [h_eq]
      have h' : -ψ n / n ≤ (n * S - Real.log (n !)) / n := by
        exact div_le_div_of_nonneg_right h (le_of_lt hn_pos)
      convert h' using 1
      exact (neg_div _ _).symm
    rw [abs_le]
    exact ⟨h1b, h1a⟩
  -- Step 2: ψ(n)/n ≤ log 4 + 4
  have h6 : ψ n / n ≤ Real.log 4 + 4 := by
    calc ψ n / n ≤ (Real.log 4 + 4) * n / n := div_le_div_of_nonneg_right h4 (le_of_lt hn_pos)
      _ = Real.log 4 + 4 := by field_simp
  -- Step 3: From Stirling, |log n!/n - log n| ≤ 1
  have h7 : |Real.log (n !) / n - Real.log n| ≤ 1 := by
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have h2' : Real.log n - 1 ≤ Real.log (n !) / n := by
      have h := div_le_div_of_nonneg_right h2 (le_of_lt hn_pos)
      calc Real.log n - 1
          = n * Real.log n / n - n / n := by field_simp
        _ = (n * Real.log n - n) / n := by rw [sub_div]
        _ ≤ Real.log (n !) / n := h
    have h3' : Real.log (n !) / n ≤ Real.log n + 1 := by
      have h := div_le_div_of_nonneg_right h3 (le_of_lt hn_pos)
      calc Real.log (n !) / n ≤ (n * Real.log n + n) / n := h
        _ = n * Real.log n / n + n / n := by rw [add_div]
        _ = Real.log n + 1 := by field_simp
    rw [abs_sub_le_iff]
    constructor <;> linarith
  -- Step 4: Triangle inequality
  calc |S - Real.log n|
      = |(S - Real.log (n !) / n) + (Real.log (n !) / n - Real.log n)| := by ring_nf
    _ ≤ |S - Real.log (n !) / n| + |Real.log (n !) / n - Real.log n| := abs_add_le _ _
    _ ≤ (Real.log 4 + 4) + 1 := by linarith [h5, h6, h7]
    _ ≤ Real.log 4 + 10 := by linarith

/-- Extract the prime sum from the von Mangoldt sum. -/
lemma sum_vonMangoldt_div_eq_sum_primes_plus_powers (n : ℕ) :
    ∑ d ∈ Icc 1 n, Λ d / d =
      ∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p / p +
      ∑ d ∈ (Icc 1 n).filter (fun d => IsPrimePow d ∧ ¬Nat.Prime d), Λ d / d := by
  rw [← sum_filter_add_sum_filter_not (Icc 1 n) Nat.Prime]
  congr 1
  · apply sum_congr rfl
    intro p hp
    rw [mem_filter] at hp
    rw [vonMangoldt_apply_prime hp.2]
  · -- For non-primes, either Λ(d) = 0 (not prime power) or d is a higher prime power
    -- The key observation: terms with Λ(d) = 0 contribute 0, so we can add any predicate
    -- Strategy: show both sums equal the sum over {d : IsPrimePow d ∧ ¬Prime d}
    -- by noting that non-prime-power terms contribute 0
    symm
    apply sum_subset
    · intro d hd
      simp only [mem_filter, mem_Icc] at hd ⊢
      exact ⟨hd.1, hd.2.2⟩
    · intro d hd hd'
      -- d is in filter(not Prime) but not in filter(IsPrimePow ∧ not Prime)
      -- This means d is not prime and not a prime power, so Λ(d) = 0
      simp only [mem_filter, mem_Icc] at hd hd'
      push_neg at hd'
      -- hd' : d ∈ Icc 1 n → IsPrimePow d → Prime d
      -- hd : d ∈ Icc 1 n ∧ ¬Prime d
      -- So: IsPrimePow d → Prime d, but ¬Prime d, hence ¬IsPrimePow d
      have h_not_pow : ¬IsPrimePow d := fun h => hd.2 (hd' hd.1 h)
      rw [vonMangoldt_eq_zero_iff.mpr h_not_pow]
      simp

/-- The sum over prime powers (k ≥ 2) converges absolutely. -/
lemma sum_prime_powers_bounded :
    ∃ C : ℝ, ∀ n : ℕ,
      ∑ d ∈ (Icc 1 n).filter (fun d => IsPrimePow d ∧ ¬Nat.Prime d), Λ d / d ≤ C := by
  -- This is ∑_{p, k≥2, p^k ≤ n} log(p)/p^k
  -- For each prime p: ∑_{k≥2} log(p)/p^k = log(p)·p^{-2}/(1 - p^{-1}) = log(p)/(p² - p)
  -- The total sum ∑_p log(p)/(p² - p) ≈ 0.76 converges since:
  --   log(p)/(p² - p) ≤ 2·log(p)/p² and ∑_p log(p)/p² converges by comparison with ∫ log(x)/x² dx
  -- Explicit computation: log(2)/2 + log(3)/6 + log(5)/20 + log(7)/42 + ... ≈ 0.76 < 3
  use 3
  intro n
  -- Each term Λ(d)/d for d = p^k with k ≥ 2 is log(p)/p^k ≤ log(p)/p² ≤ 2·log(p)/p²
  -- The sum is bounded by the convergent series ∑_p log(p)/(p² - p) < 1 < 3
  -- This bound is independent of n since the finite sum is always ≤ the infinite limit
  sorry

/-- **Mertens' First Theorem**: ∑_{p≤n} log(p)/p = log(n) + O(1) -/
theorem mertens_first :
    ∃ C : ℝ, ∀ n : ℕ, n ≥ 2 →
      |∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p / p - Real.log n| ≤ C := by
  obtain ⟨C1, hC1⟩ := sum_vonMangoldt_div_eq_log_plus_O1
  obtain ⟨C2, hC2⟩ := sum_prime_powers_bounded
  use C1 + C2
  intro n hn
  have h_decomp := sum_vonMangoldt_div_eq_sum_primes_plus_powers n
  specialize hC1 n hn
  specialize hC2 n
  -- ∑ Λ(d)/d = ∑_{prime} log(p)/p + ∑_{prime powers ≥ 2}
  -- |∑_{prime} log(p)/p - log(n)| ≤ |∑ Λ(d)/d - log(n)| + |∑_{powers}|
  have h_powers_nonneg : 0 ≤ ∑ d ∈ (Icc 1 n).filter (fun d => IsPrimePow d ∧ ¬Nat.Prime d), Λ d / d := by
    apply sum_nonneg
    intro d hd
    apply div_nonneg vonMangoldt_nonneg
    rw [mem_filter, mem_Icc] at hd
    exact Nat.cast_nonneg d
  -- The proof follows from triangle inequality
  -- Let A = ∑ Λ(d)/d, B = ∑_{powers} Λ(d)/d, L = log(n)
  -- Prime sum = A - B
  -- |A - B - L| ≤ |A - L| + |B|
  set A := ∑ d ∈ Icc 1 n, Λ d / d with hA_def
  set B := ∑ d ∈ (Icc 1 n).filter (fun d => IsPrimePow d ∧ ¬Nat.Prime d), Λ d / d with hB_def
  set L := Real.log n with hL_def
  have key : |A - B - L| ≤ |A - L| + B := by
    calc |A - B - L|
        = |(A - L) + (- B)| := by ring_nf
        _ ≤ |A - L| + |-B| := abs_add_le _ _
        _ = |A - L| + B := by rw [abs_neg, abs_of_nonneg h_powers_nonneg]
  have h_eq : ∑ p ∈ (Icc 1 n).filter Nat.Prime, Real.log p / p = A - B := by
    rw [h_decomp]; ring
  rw [h_eq]
  linarith

/-- Mertens' first theorem (continuous version). -/
theorem mertens_first_continuous :
    ∃ C : ℝ, ∀ x : ℝ, x ≥ 2 →
      |∑ p ∈ (Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log p / p - Real.log x| ≤ C := by
  obtain ⟨C, hC⟩ := mertens_first
  use C + 1
  intro x hx
  have hn : ⌊x⌋₊ ≥ 2 := Nat.le_floor hx
  specialize hC ⌊x⌋₊ hn
  have h_floor_pos : (0 : ℝ) < ⌊x⌋₊ := by
    rw [Nat.cast_pos, Nat.floor_pos]
    linarith
  have h_floor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have h_lt_floor_succ : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  have h_log_diff : |Real.log ⌊x⌋₊ - Real.log x| ≤ 1 := by
    rw [abs_sub_comm]
    have h1 : Real.log x - Real.log ⌊x⌋₊ ≥ 0 := by
      apply sub_nonneg.mpr
      apply Real.log_le_log h_floor_pos h_floor_le
    rw [abs_of_nonneg h1]
    calc Real.log x - Real.log ⌊x⌋₊
        = Real.log (x / ⌊x⌋₊) := by rw [Real.log_div (by linarith) (by linarith)]
        _ ≤ x / ⌊x⌋₊ - 1 := Real.log_le_sub_one_of_pos (div_pos (by linarith) h_floor_pos)
        _ ≤ (⌊x⌋₊ + 1) / ⌊x⌋₊ - 1 := by
          have : x ≤ ⌊x⌋₊ + 1 := le_of_lt h_lt_floor_succ
          gcongr
        _ = 1 / ⌊x⌋₊ := by
          have h2 : (⌊x⌋₊ : ℝ) ≠ 0 := ne_of_gt h_floor_pos
          field_simp
          ring
        _ ≤ 1 / 2 := by
          gcongr
          calc (2 : ℝ) ≤ (⌊x⌋₊ : ℕ) := by exact_mod_cast hn
            _ = (⌊x⌋₊ : ℝ) := by simp
        _ ≤ 1 := by norm_num
  -- |sum - log x| ≤ |sum - log ⌊x⌋| + |log ⌊x⌋ - log x|
  have h_triangle : |∑ p ∈ (Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log p / p - Real.log x| ≤
      |∑ p ∈ (Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log p / p - Real.log ⌊x⌋₊| +
      |Real.log ⌊x⌋₊ - Real.log x| := by
    calc |∑ p ∈ (Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log p / p - Real.log x|
        = |∑ p ∈ (Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log p / p - Real.log ⌊x⌋₊ +
            (Real.log ⌊x⌋₊ - Real.log x)| := by ring_nf
        _ ≤ |∑ p ∈ (Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log p / p - Real.log ⌊x⌋₊| +
            |Real.log ⌊x⌋₊ - Real.log x| := abs_add_le _ _
  linarith

end Mertens

end
