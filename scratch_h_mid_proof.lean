/-
# Scratch: h_mid proof strategy for errorTerm_first_moment_sqrt
# Agent 3, iteration 5 — 2026-03-16

## Target sorry
RSExpansionProof.lean:4649 — the live sorry:
  have h_mid : |∫ t in Ioc (hardyStart 0) (hardyStart K), ErrorTerm t| ≤
      C_bl * Real.sqrt T + C₂ := by
    sorry

## Diagnosis
The live sorry needs `C_bl * √T + C₂`, but the correct proof (commented-out draft at
lines 4749-4884) uses `M_fn(K-1) + K*δ` which then gets absorbed into `C_E * √T` at
the final combine step. The live version's constant mismatch means the sorry cannot be
filled as-is — it needs the COMMENTED-OUT version's approach instead.

## Recommended fix: Replace live proof with commented-out version
The commented-out version (lines 4749-4884) has the MID block FULLY PROVED at lines
4840-4860, but three remaining sorrys:

1. **TAIL (line 4866)**: sign-monotonicity for partial block integral
   Needs: |∫_{hsK}^T ET| ≤ C_bl * √(K+2)
   This follows from signed_block_integral_nonneg + the interpolation bound
   (rs_block_interpolation). The live version's h_tail (lines 4577-4591) already
   proves this correctly. SOLUTION: copy live h_tail proof.

2. **COMBINE (line 4881)**: rpow arithmetic
   Needs: (M₀+2)*hs0 + (M_fn(K-1) + K*δ) + C_bl*√(K+2) ≤ C_E * T^{1/2}
   SOLUTION: Use combine_bound (proved below) to show M_fn(K-1) + K*δ ≤ const*√T,
   then the rest is O(1) absorbed via T^{1/2} ≥ 1.

3. **SMALL-T (line 4883)**: T ∈ [2, 2π)
   SOLUTION: Copy the live version's small-T case (lines 4713-4748) verbatim.

## Verified sub-lemmas (AXLE-checked)
-/

import Mathlib

/-! ## Part 1: combine_bound — rpow arithmetic for the final combine step

Given:
- M_fn(k) ≤ C_bound * √(k+2) (block integral size bound)
- K ≤ √T (block count bound)
- δ > 0 (universal approximation error)

Proves: M_fn(K-1) + K*δ ≤ (2*C_bound + δ + 1) * √T

Key ideas:
- M_fn(K-1) ≤ C_bound * √(K+1) ≤ C_bound * √(√T+2) ≤ 2*C_bound*√T
  via √(√T+2) ≤ √(3√T) = √3·√(√T) ≤ 2·√T
- K*δ ≤ √T * δ
-/
section FinalCombine

theorem combine_bound (K : ℕ) (T : ℝ) (hT : 2 ≤ T) (hK : (K : ℝ) ≤ Real.sqrt T)
    (M_fn : ℕ → ℝ) (δ C_bound : ℝ) (hδ_pos : 0 < δ)
    (hM_le : ∀ k, M_fn k ≤ C_bound * Real.sqrt ((k : ℝ) + 2))
    (hCb_pos : 0 < C_bound) :
    M_fn (K - 1) + (K : ℝ) * δ ≤ (C_bound * 2 + δ + 1) * Real.sqrt T := by
  have hT_pos : (0 : ℝ) < T := by linarith
  have hSqrt_pos : (0 : ℝ) < Real.sqrt T := Real.sqrt_pos.mpr hT_pos
  have hSqrt_ge1 : (1 : ℝ) ≤ Real.sqrt T := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
  have hSqrt_le_T : Real.sqrt T ≤ T := by
    have : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt (le_of_lt hT_pos)
    nlinarith [hSqrt_ge1]
  have hM : M_fn (K - 1) ≤ C_bound * Real.sqrt (Real.sqrt T + 2) := by
    calc M_fn (K - 1) ≤ C_bound * Real.sqrt (((K - 1 : ℕ) : ℝ) + 2) := hM_le _
      _ ≤ C_bound * Real.sqrt ((K : ℝ) + 2) := by
          gcongr; push_cast; exact_mod_cast Nat.sub_le K 1
      _ ≤ C_bound * Real.sqrt (Real.sqrt T + 2) := by gcongr
  have h_sqrt_bound : Real.sqrt (Real.sqrt T + 2) ≤ 2 * Real.sqrt T := by
    calc Real.sqrt (Real.sqrt T + 2)
        ≤ Real.sqrt (3 * Real.sqrt T) := by
          apply Real.sqrt_le_sqrt; linarith [hSqrt_ge1]
      _ = Real.sqrt 3 * Real.sqrt (Real.sqrt T) := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
      _ ≤ 2 * Real.sqrt (Real.sqrt T) := by
          gcongr
          calc Real.sqrt 3 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
            _ = 2 := by rw [show (4:ℝ) = 2^2 from by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ 2 * Real.sqrt T := mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt hSqrt_le_T) (by norm_num)
  have hKd : (K : ℝ) * δ ≤ Real.sqrt T * δ :=
    mul_le_mul_of_nonneg_right hK (le_of_lt hδ_pos)
  calc M_fn (K - 1) + (K : ℝ) * δ
      ≤ C_bound * (2 * Real.sqrt T) + Real.sqrt T * δ := by
        have : C_bound * Real.sqrt (Real.sqrt T + 2) ≤ C_bound * (2 * Real.sqrt T) :=
          mul_le_mul_of_nonneg_left h_sqrt_bound (le_of_lt hCb_pos)
        linarith
    _ = (C_bound * 2 + δ) * Real.sqrt T := by ring
    _ ≤ (C_bound * 2 + δ + 1) * Real.sqrt T := by linarith [hSqrt_pos]

end FinalCombine

/-! ## Part 2: alt_sum_approx_mono structure

The key algebraic lemma (already proved in RSExpansionProof at line 3404):

  |∑_{k<n+1} (-1)^k b(k)| ≤ M_fn(n) + (n+1)·δ

where b approximates monotone M_fn with error δ.

Proof structure:
1. Split: (-1)^k b(k) = (-1)^k M(k) + (-1)^k (b(k)-M(k))
2. Triangle: |∑ ...| ≤ |∑ (-1)^k M(k)| + |∑ (-1)^k (b(k)-M(k))|
3. First term ≤ M(n) by alt_sum_mono_le (monotone alternating bound)
4. Second term ≤ (n+1)δ by triangle + |(-1)^k| = 1 + |b(k)-M(k)| ≤ δ

This is verified with the axiom stub below.
-/
section AltSumApproxMono

-- Axiom stub for the monotone alternating sum bound (proved in project)
axiom alt_sum_mono_le_axiom (M_fn : ℕ → ℝ) (hM_nn : ∀ k, 0 ≤ M_fn k)
    (hM_mono : Monotone M_fn) (n : ℕ) :
    |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * M_fn k| ≤ M_fn n

theorem alt_sum_approx_mono_standalone (b M_fn : ℕ → ℝ) (δ : ℝ) (_hδ : 0 ≤ δ)
    (hM_nn : ∀ k, 0 ≤ M_fn k) (hM_mono : Monotone M_fn)
    (h_approx : ∀ k, |b k - M_fn k| ≤ δ) (n : ℕ) :
    |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * b k| ≤ M_fn n + (↑n + 1) * δ := by
  have h_split : ∀ k, (-1 : ℝ) ^ k * b k =
      (-1 : ℝ) ^ k * M_fn k + (-1 : ℝ) ^ k * (b k - M_fn k) := by intro k; ring
  simp_rw [h_split, Finset.sum_add_distrib]
  calc |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * M_fn k +
        ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (b k - M_fn k)|
      ≤ |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * M_fn k| +
        |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (b k - M_fn k)| := abs_add_le _ _
    _ ≤ M_fn n + ∑ k ∈ Finset.range (n + 1), δ := by
        gcongr
        · exact alt_sum_mono_le_axiom M_fn hM_nn hM_mono n
        · calc |∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (b k - M_fn k)|
              ≤ ∑ k ∈ Finset.range (n + 1), |(-1 : ℝ) ^ k * (b k - M_fn k)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ k ∈ Finset.range (n + 1), δ := by
                gcongr with k _
                rw [abs_mul, show |(-1 : ℝ) ^ k| = 1 from by simp [abs_pow, abs_neg, abs_one]]
                simp; exact h_approx k
    _ = M_fn n + (↑n + 1) * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

end AltSumApproxMono

/-! ## Part 3: Assembly plan for closing the live sorry

### Step 1: Uncomment lines 4749-4884
The commented-out version has the correct proof structure with:
- b(k), M_fn(k), δ, h_approx all defined and verified
- MID block fully proved via alt_sum_approx_mono
- HEAD block fully proved

### Step 2: Fix TAIL sorry (line 4866)
Replace with the working h_tail from lines 4577-4591 (adjust target bound).
The live version proves |∫_{hsK}^T ET| ≤ C_bl*√(K+2) + C₂ using rs_block_interpolation.

### Step 3: Fix COMBINE sorry (line 4881)
Use combine_bound to show:
  M_fn(K-1) + K*δ ≤ (8π + δ + 1) * √T    [C_bound = 4π]
Then:
  head + mid + tail
  ≤ (M₀+2)*hs0 + (8π+δ+1)*√T + C_bl*√(K+2) + C₂
  ≤ (M₀+2)*hs0 + (8π+δ+1)*√T + (C_bl+C₂)*√T    [√(K+2) ≤ √T, C₂ ≤ C₂*√T]
  ≤ ((M₀+2)*hs0 + 8π + δ + 1 + C_bl + C₂ + 1) * √T
  = C_E * √T  (redefine C_E)

### Step 4: Fix SMALL-T sorry (line 4883)
Copy lines 4713-4748 from live version (already working).

### Step 5: Delete duplicate code
Remove the first (live) version of errorTerm_first_moment_sqrt and keep only the
uncommented second version.

### Constants
- C_E := (M₀+2)*hs0 + 8π + δ + C_bl + C₂ + 2
  where δ = C_bl*√2 + 4π√2 + 3π (from line 4778)
- This is a universal positive constant depending only on hardyZ, error_block_integral_bound,
  and rs_block_interpolation.
-/
