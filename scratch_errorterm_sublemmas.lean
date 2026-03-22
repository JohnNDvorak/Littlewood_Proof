/-
  scratch_errorterm_sublemmas.lean
  Agent 3 (iteration 4) — 2026-03-16

  AXLE-verified Mathlib-only sub-lemmas for closing the two sorrys in
  errorTerm_first_moment_sqrt (RSExpansionProof.lean):

  Sorry 1 (line 4547): block_sum_sqrt_bound — standalone, currently unused
  Sorry 2 (line 4668): h_mid — the live sorry in the main proof

  Strategy for h_mid:
    1. integral_split_finitely decomposes ∫_{hs0}^{hsK} into ∑_{k<K} ∫_{block_k}
    2. Rewrite as ∑ (-1)^k * b(k) where b(k) = (-1)^k * ∫_{block_k} ET ≥ 0
       (sign pattern from signed_block_integral_nonneg)
    3. Apply alt_sum_approx_mono with M_fn monotone envelope, δ constant error
    4. Result: |∑| ≤ M(K-1) + K*δ ≤ (C_1 + δ)*√T

  The commented-out draft (lines 4745–4880) has this approach fully sketched
  with three remaining sorrys at lines 4862, 4877, 4879. The live proof
  (lines 4549–4767) simplifies the constant handling but has the sorry at 4668.

  All lemmas below are AXLE-verified (import Mathlib only).
-/
import Mathlib

/-! ### A. Monotonicity of √(k+2) envelope -/

/-- C * √(k+2) is monotone in k for C ≥ 0. -/
theorem sqrt_plus_two_monotone (C : ℝ) (hC : 0 ≤ C) :
    Monotone (fun k : ℕ => C * Real.sqrt ((k : ℝ) + 2)) := by
  intro a b hab
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_right hab 2))
    hC

/-! ### B. √(K+2) ≤ √T from K ≤ √T and T ≥ 4 -/

/-- When K ≤ √T and T ≥ 4, we have √(K+2) ≤ √T. -/
theorem sqrt_K2_le_sqrt_T (K : ℕ) (T : ℝ) (hT4 : 4 ≤ T)
    (hK : (K : ℝ) ≤ Real.sqrt T) :
    Real.sqrt ((K : ℝ) + 2) ≤ Real.sqrt T := by
  apply Real.sqrt_le_sqrt
  have hSqT2 : Real.sqrt T + 2 ≤ T := by
    have : Real.sqrt T ≤ T - 2 := by
      rw [← Real.sqrt_sq (by linarith : (0:ℝ) ≤ T - 2)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith
  linarith

/-- When K ≤ √T and T ≥ 4, we have √(K+1) ≤ √T. -/
theorem sqrt_K1_le_sqrt_T (K : ℕ) (T : ℝ) (hT : 4 ≤ T)
    (hK : (K : ℝ) ≤ Real.sqrt T) :
    Real.sqrt ((K : ℝ) + 1) ≤ Real.sqrt T := by
  apply Real.sqrt_le_sqrt
  have : Real.sqrt T + 1 ≤ T := by
    have : Real.sqrt T ≤ T - 1 := by
      rw [← Real.sqrt_sq (show (0:ℝ) ≤ T - 1 by nlinarith)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith
  linarith

/-- √(√T + 2) ≤ √T for T ≥ 4. -/
theorem sqrt_sqrt_plus_two_le (T : ℝ) (hT : 4 ≤ T) :
    Real.sqrt (Real.sqrt T + 2) ≤ Real.sqrt T := by
  apply Real.sqrt_le_sqrt
  have h1 : Real.sqrt T ≤ T - 2 := by
    rw [← Real.sqrt_sq (show (0:ℝ) ≤ T - 2 by nlinarith)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  linarith

/-! ### C. Constant absorption: c ≤ c * T^(1/2) for T ≥ 1 -/

/-- A nonneg constant is absorbed by T^(1/2) when T ≥ 1. -/
theorem const_le_const_mul_rpow_half (c : ℝ) (hc : 0 ≤ c) (T : ℝ) (hT : 1 ≤ T) :
    c ≤ c * T ^ ((1:ℝ)/2) := by
  calc c = c * 1 := (mul_one c).symm
    _ ≤ c * T ^ ((1:ℝ)/2) := by
      gcongr
      calc (1:ℝ) = (1:ℝ) ^ ((1:ℝ)/2) := by simp
        _ ≤ T ^ ((1:ℝ)/2) := by
          exact Real.rpow_le_rpow (by norm_num) hT (by norm_num)

/-! ### D. K*δ ≤ δ*√T from K ≤ √T -/

/-- K * δ ≤ δ * √T when K ≤ √T and δ ≥ 0. -/
theorem nat_le_sqrt_mul_const (K : ℕ) (T δ : ℝ) (hδ : 0 ≤ δ)
    (hK : (K : ℝ) ≤ Real.sqrt T) :
    (K : ℝ) * δ ≤ δ * Real.sqrt T := by
  rw [mul_comm]; exact mul_le_mul_of_nonneg_left hK hδ

/-! ### E. Combined mid-section bound -/

/-- The combine step for h_mid: C*√(K+1) + K*δ ≤ (C+δ)*√T. -/
theorem block_mid_combine (C δ : ℝ) (K : ℕ) (T : ℝ)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hK_sqrt : (K : ℝ) ≤ Real.sqrt T)
    (hK1_sqrt : Real.sqrt ((K:ℝ) + 1) ≤ Real.sqrt T) :
    C * Real.sqrt ((K:ℝ) + 1) + (K : ℝ) * δ ≤ (C + δ) * Real.sqrt T := by
  have h1 : C * Real.sqrt ((K:ℝ) + 1) ≤ C * Real.sqrt T :=
    mul_le_mul_of_nonneg_left hK1_sqrt hC
  have h2 : (K : ℝ) * δ ≤ δ * Real.sqrt T := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left hK_sqrt hδ
  linarith [mul_comm δ (Real.sqrt T)]

/-! ### F. Finset range rewrite for K > 0 -/

theorem finset_range_pred_succ (K : ℕ) (hK : 0 < K) :
    Finset.range K = Finset.range ((K - 1) + 1) := by
  congr 1; omega

/-! ### G. Sum of √(k+2) fallback bound (triangle inequality path) -/

/-- Fallback: ∑_{k<K} √(k+2) ≤ K * √(K+2). Only needed if alternation fails. -/
theorem sum_sqrt_le_mul_sqrt (K : ℕ) :
    ∑ k ∈ Finset.range K, Real.sqrt ((k:ℝ) + 2) ≤
    (K : ℝ) * Real.sqrt ((K:ℝ) + 2) := by
  calc ∑ k ∈ Finset.range K, Real.sqrt ((k:ℝ) + 2)
      ≤ ∑ k ∈ Finset.range K, Real.sqrt ((K:ℝ) + 2) := by
        apply Finset.sum_le_sum; intro k hk
        apply Real.sqrt_le_sqrt
        have := Finset.mem_range.mp hk
        exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt this) 2
    _ = (K : ℝ) * Real.sqrt ((K:ℝ) + 2) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-! ### H. Real.sqrt = rpow conversion -/

theorem sqrt_eq_rpow_half (x : ℝ) :
    Real.sqrt x = x ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow x

/-! ### Analysis of the two sorrys

## Sorry 1: block_sum_sqrt_bound (line 4547)
  Statement: ∃ C_S > 0, ∀ K, 0 < K → |∑_{k<K} ∫_{block} ET| ≤ C_S * √(K+1)
  Status: STANDALONE, not referenced by the live proof.
  Approach: Same as h_mid — rewrite as alternating sum, apply alt_sum_approx_mono.
  Difficulty: MODERATE. Needs signed_block_integral_nonneg + monotone envelope.

## Sorry 2: h_mid (line 4668)
  Statement: |∫ hs0..hsK, ET| ≤ C_bl * √T + C₂
  Status: LIVE sorry blocking errorTerm_first_moment_sqrt.
  Approach:
    1. Use integral_split_finitely to get ∑_{k<K} ∫_{block_k} ET
    2. Rewrite as ∑ (-1)^k * b(k) using signed_block_integral_nonneg
    3. Apply alt_sum_approx_mono (already proved in file)
    4. Get bound M_fn(K-1) + K*δ
    5. Use sub-lemmas B, D, E above to reduce to (C1+δ)*√T
    6. Absorb into C_bl * √T + C₂

  Key blocker: The live proof uses constants C_bl and C₂ from
  error_block_integral_bound and rs_block_interpolation respectively.
  The draft uses M_fn (a more complex envelope based on rsPsi integrals)
  and δ (a compound constant). Agent 1 needs to choose which constant
  framework to use and wire accordingly.

  Recommended path: Follow the commented-out draft (lines 4836-4856)
  which already has the correct structure. The sub-lemmas above provide
  the final combine step (E) and sqrt chain (B, C, D).
-/
