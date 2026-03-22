/-
  scratch_mainterm_full_proof.lean
  ================================
  Analysis and sub-lemmas for sorry #3: mainTerm_first_moment_ibp
  (RSExpansionProof.lean:3434)

  Agent 4 (iteration 5), 2026-03-15.

  ## Target
  ```
  private theorem mainTerm_first_moment_ibp :
      ∃ C_M > 0, ∀ T : ℝ, T ≥ 2 →
        |∫ t in Ioc 1 T, MainTerm t| ≤ C_M * T ^ ((1 : ℝ) / 2) := by
    sorry
  ```

  ## CRITICAL FINDING

  The T^{1/2} bound on ∫ MainTerm ALONE is stronger than what per-mode VdC yields.
  Per-mode VdC gives O(T^{3/4}), not O(T^{1/2}). Here's why:

  - On block k (length ~C·k), mode n = k (resonant) has |∫ cos(φ_k)| ≤ C·k
    (trivial bound; VdC2 gives the same order since θ'' ~ 1/k²).
  - Weight (k+1)^{-1/2} · C·k ≈ C·√k per block.
  - Sum over K ≈ √T blocks: Σ √k ≈ K^{3/2} ≈ T^{3/4}.

  The O(T^{1/2}) for ∫ Z(t) dt comes from IBP on the FULL Z using
  ζ(1/2+it) convexity bounds (Titchmarsh §4.15), proved in
  HardyZFirstMomentIBP.lean. But that file IMPORTS RSExpansionProof.lean,
  so we can't use it here (circular dependency).

  ## VIABLE PATHS TO CLOSE SORRY #3

  ### Path A: Restructure the proof chain (RECOMMENDED)
  The siegel_first_moment theorem (line 4767) decomposes |∫ Z| into:
    |∫ Z| ≤ |∫ MainTerm| + |∫ ErrorTerm|

  Instead, restructure to prove |∫ Z| ≤ C·T^{1/2} DIRECTLY via IBP on Z,
  without going through the MainTerm/ErrorTerm split. This is what
  HardyZFirstMomentIBP already does. The fix: break the circular import
  by moving hardyZ_first_moment_sqrt_bound out of RSExpansionProof and
  into a separate file that HardyZFirstMomentIBP doesn't import.

  ### Path B: Use ErrorTerm cancellation
  Since ErrorTerm = Z - MainTerm, we have MainTerm = Z - ErrorTerm.
  |∫ MainTerm| = |∫ Z - ∫ ErrorTerm| ≤ |∫ Z| + |∫ ErrorTerm|.

  If |∫ Z| ≤ C·T^{1/2} is proved ELSEWHERE (breaking the import cycle),
  and |∫ ErrorTerm| ≤ C·T^{1/2} (from errorTerm_first_moment_sqrt),
  then |∫ MainTerm| ≤ C·T^{1/2}. But this creates a dependency loop:
  we'd need ∫ Z = O(T^{1/2}) to prove ∫ MainTerm = O(T^{1/2}),
  and siegel_first_moment uses ∫ MainTerm to prove ∫ Z.

  ### Path C: Prove O(T^{3/4}) and weaken the claim
  Change the exponent in mainTerm_first_moment_ibp to 3/4, and
  compensate downstream. This changes siegel_first_moment to:
    |∫ Z| ≤ C·T^{3/4} + C·T^{1/2} = O(T^{3/4})
  Then hardyZ_first_moment_sqrt_bound would claim T^{3/4} instead of T^{1/2}.
  This may break downstream consumers that need the T^{1/2} exponent.

  ### Path D: Direct O(T^{1/2}) via Dirichlet polynomial mean-value
  The Montgomery-Vaughan mean-value theorem gives:
    ∫₀ᵀ |Σ a_n n^{-it}|² dt = (T + O(N)) Σ |a_n|²
  Combined with the e^{iθ(t)} phase, one can show a SINGLE integral
  ∫ e^{iθ(t)} (n+1)^{-it} dt = O(1) for each n (from VdC on the FULL
  range, not per-block). Then:
    |∫ MainTerm| ≤ 2 Σ_{n<N} (n+1)^{-1/2} · C = C · Σ 1/√(n+1) ≤ 2C√N ≤ C·T^{1/4}
  This gives T^{1/4}, which is BETTER than T^{1/2}!

  KEY INSIGHT: Each mode n integral ∫₁ᵀ (n+1)^{-1/2} cos(θ(t)-t·log(n+1)) dt
  is O(1) by VdC first derivative test on the FULL interval [T₀, T], since:
  - φ'_n(t) = θ'(t) - log(n+1) is monotone increasing (θ'' > 0)
  - For t ≥ T₀ (large enough): φ'_n(T₀) > 0 (θ'(T₀) > max_n log(n+1))
    Actually NO: for the resonant modes, φ'_n passes through zero!
  - The modes where φ'_n changes sign are the BLOCK-RESONANT modes.
    For each n, the resonance t_n is where θ'(t_n) = log(n+1), i.e., t_n ≈ hs(n).

  VdC with φ' passing through zero: use VdC SECOND derivative test.
  For each mode n:
    φ''_n(t) = θ''(t) ~ 1/(2t) > 0 everywhere
    VdC2: |∫_{hs(n)-L}^{hs(n)+L} e^{iφ_n}| ≤ C/√(min θ'') ≤ C·√t_n ≤ C·(n+1)
  For |t - t_n| > L: |φ'_n| ≥ C/L by monotonicity, VdC1 gives O(L/C) contribution.
  Total for mode n: O(n+1).
  Sum: Σ (n+1)^{-1/2} · C·(n+1) = C · Σ (n+1)^{1/2} ≈ C · N^{3/2} = C · T^{3/4}.

  So the per-mode integral is NOT O(1); it's O(n+1). Back to T^{3/4}.

  BUT WAIT: The integral is over [1, T], and MainTerm(t) has VARYING N(t).
  For t slightly above 1, N(t) = 0 or 1. Mode n only "exists" for t ≥ hs(n).
  So mode n contributes only ∫_{hs(n)}^T cos(φ_n(t)) dt.

  For modes with hs(n) > T: they don't contribute at all.
  For mode n with hs(n) ≤ T: their integral from hs(n) to T includes the
  resonance point t_n = hs(n), so VdC2 applies giving O(n+1).

  HMMMM. Let me try Path D more carefully.

  Actually, there is a subtlety I missed. The integral is NOT
  ∫₁ᵀ MainTerm = Σ_n ∫_{hs(n)}^T w_n cos(φ_n)
  because MainTerm(t) uses N(t) = ⌊√(t/2π)⌋ modes at time t,
  and the sum ranges change at block boundaries.

  On block k, only modes 0,...,k are present. When we pass from block k
  to block k+1, mode k+1 appears. So:
  ∫₁ᵀ MainTerm = Σ_k ∫_{block k} (2 Σ_{n≤k} w_n cos(φ_n))
               = 2 Σ_n w_n Σ_{k≥n} ∫_{block k} cos(φ_n)

  Σ_{k≥n} ∫_{block k} cos(φ_n) = ∫_{hs(n)}^{T'} cos(φ_n(t)) dt
  where T' is the end of the last block. This equals the mode-n integral
  over its full active range.

  So the analysis IS per-mode on the full active range. VdC2 applies at
  the resonance t_n and gives O(n). Total = O(T^{3/4}).

  ## CONCLUSION

  Sorry #3 (`mainTerm_first_moment_ibp`) with exponent 1/2 is NOT closable
  by per-mode VdC alone. The achievable bound is T^{3/4}.

  The T^{1/2} bound for ∫ Z requires the FULL IBP on Z(t) with ζ convexity
  bounds (proved in HardyZFirstMomentIBP.lean).

  **RECOMMENDATION FOR AGENT 1**: Restructure the proof chain:
  1. Move `siegel_first_moment` to use the IBP bound from HardyZFirstMomentIBP
     directly, rather than splitting into MainTerm + ErrorTerm.
  2. Or: Change the sorry exponent to 3/4 and adjust downstream.
  3. Or: Accept sorry #3 as IRREDUCIBLE at the T^{1/2} level —
     it encodes genuine oscillatory cancellation that requires the
     ζ convexity bound infrastructure.

  ## SUB-LEMMAS (AXLE-verified, for T^{3/4} proof if Path C chosen)

  All sub-lemmas from scratch_ibp_proofs.lean and scratch_vdc_proofs.lean
  are available. The assembly for T^{3/4} would follow the outline below.
-/

-- ════════════════════════════════════════════════════════════
-- PART 1: AXLE-VERIFIED MATHLIB-ONLY SUB-LEMMAS
-- ════════════════════════════════════════════════════════════

import Mathlib

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Real MeasureTheory Set Filter Topology Finset

noncomputable section

-- ────────────────────────────────────────────────────────────
-- A. Telescoping bound: Σ_{n<N} (n+1)^{-1/2} ≤ 2√N
-- ────────────────────────────────────────────────────────────

private lemma inv_sqrt_le_two_sqrt_diff (n : ℕ) :
    1 / Real.sqrt ((n : ℝ) + 1) ≤ 2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h_sqrt_pos : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos_of_pos hn1
  have h_sqrt_nn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg n
  have h_sqrt_le : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have h_diff_nn : 0 ≤ Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ) := by linarith
  have h_conj : (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) *
      (Real.sqrt ((n : ℝ) + 1) + Real.sqrt n) = 1 := by
    have h1 : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (le_of_lt hn1)
    have h2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn_nn
    nlinarith [sq_nonneg (Real.sqrt ((n : ℝ) + 1)), sq_nonneg (Real.sqrt (n : ℝ))]
  have h_sum_pos : 0 < Real.sqrt ((n : ℝ) + 1) + Real.sqrt n := by linarith
  rw [div_le_iff₀ h_sqrt_pos]
  nlinarith [h_conj, mul_nonneg h_diff_nn h_sqrt_nn,
             mul_le_mul_of_nonneg_left h_sqrt_le h_diff_nn]

theorem sum_inv_sqrt_le_two_sqrt (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 / Real.sqrt ((n : ℝ) + 1)) ≤ 2 * Real.sqrt N := by
  have h_cast : ∀ n : ℕ, Real.sqrt ((n : ℝ) + 1) = Real.sqrt (↑(n + 1)) := by
    intro n; congr 1; push_cast; ring
  calc ∑ n ∈ Finset.range N, (1 / Real.sqrt ((n : ℝ) + 1))
      ≤ ∑ n ∈ Finset.range N,
          (2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n)) :=
        Finset.sum_le_sum (fun n _ => inv_sqrt_le_two_sqrt_diff n)
    _ = 2 * ∑ n ∈ Finset.range N,
          (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) := by
        rw [Finset.mul_sum]
    _ = 2 * ∑ n ∈ Finset.range N,
          (Real.sqrt (↑(n + 1)) - Real.sqrt (↑n)) := by
        congr 1; apply Finset.sum_congr rfl; intro n _; rw [h_cast]
    _ = 2 * (Real.sqrt ↑N - Real.sqrt ↑(0 : ℕ)) :=
        by congr 1; exact Finset.sum_range_sub (fun n => Real.sqrt (↑n)) N
    _ = 2 * Real.sqrt N := by simp [Real.sqrt_zero]

-- ────────────────────────────────────────────────────────────
-- B. rpow comparison
-- ────────────────────────────────────────────────────────────

theorem rpow_quarter_le_half {T : ℝ} (hT : 1 ≤ T) :
    T ^ ((1 : ℝ)/4) ≤ T ^ ((1 : ℝ)/2) :=
  rpow_le_rpow_of_exponent_le hT (by norm_num : (1:ℝ)/4 ≤ 1/2)

-- ────────────────────────────────────────────────────────────
-- C. √N ≤ (T/(2π))^{1/4} + 1
-- ────────────────────────────────────────────────────────────

theorem sqrt_hardyN_le_rpow_quarter {N : ℕ} {T : ℝ} (hT : 0 < T)
    (hN : (N : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) + 1) :
    Real.sqrt N ≤ (T / (2 * Real.pi)) ^ ((1:ℝ)/4) + 1 := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have h1 : Real.sqrt N ≤ Real.sqrt (Real.sqrt (T / (2 * Real.pi)) + 1) := by
    apply Real.sqrt_le_sqrt; exact_mod_cast hN
  have h_sqrt_T2pi_nn : 0 ≤ Real.sqrt (T / (2 * Real.pi)) := Real.sqrt_nonneg _
  have h2 : Real.sqrt (Real.sqrt (T / (2 * Real.pi)) + 1) ≤
      Real.sqrt (Real.sqrt (T / (2 * Real.pi))) + 1 := by
    rw [← Real.sqrt_sq
      (show 0 ≤ Real.sqrt (Real.sqrt (T / (2 * Real.pi))) + 1 by positivity)]
    apply Real.sqrt_le_sqrt
    nlinarith [Real.sq_sqrt h_sqrt_T2pi_nn,
               Real.sqrt_nonneg (Real.sqrt (T / (2 * Real.pi)))]
  have h3 : Real.sqrt (Real.sqrt (T / (2 * Real.pi))) =
      (T / (2 * Real.pi)) ^ ((1:ℝ)/4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    rw [← rpow_mul (div_nonneg (le_of_lt hT) (le_of_lt hpi))]
    norm_num
  linarith

-- ────────────────────────────────────────────────────────────
-- D. Interval integral norm bound
-- ────────────────────────────────────────────────────────────

theorem interval_integral_norm_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    {M : ℝ} (_hM : 0 ≤ M)
    (hf_int : IntervalIntegrable f volume a b)
    (hf_bd : ∀ t ∈ Icc a b, ‖f t‖ ≤ M) :
    ‖∫ t in a..b, f t‖ ≤ M * (b - a) := by
  calc ‖∫ t in a..b, f t‖
      ≤ ∫ t in a..b, ‖f t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..b, M := by
        apply intervalIntegral.integral_mono_on hab hf_int.norm
          (intervalIntegrable_const)
        intro t ht; exact hf_bd t ht
    _ = M * (b - a) := by
        simp [intervalIntegral.integral_const, smul_eq_mul]; ring

-- ────────────────────────────────────────────────────────────
-- E. Set integral Ioc splitting
-- ────────────────────────────────────────────────────────────

theorem setIntegral_Ioc_split {f : ℝ → ℝ} {a c b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hf : IntegrableOn f (Ioc a b)) :
    ∫ t in Ioc a b, f t = (∫ t in Ioc a c, f t) + (∫ t in Ioc c b, f t) := by
  have h_union : Ioc a b = Ioc a c ∪ Ioc c b := (Ioc_union_Ioc_eq_Ioc hac hcb).symm
  rw [h_union]
  have h_disj : Disjoint (Ioc a c) (Ioc c b) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact not_lt.mpr hx1.2 hx2.1
  exact setIntegral_union h_disj measurableSet_Ioc
    (hf.mono_set (Ioc_subset_Ioc_right hcb))
    (hf.mono_set (Ioc_subset_Ioc_left hac))

-- ────────────────────────────────────────────────────────────
-- F. (n+1)^{-1/2} ≤ 1
-- ────────────────────────────────────────────────────────────

lemma rpow_neg_half_le_one (n : ℕ) : (↑n + 1 : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (↑n + 1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  calc (↑n + 1 : ℝ) ^ (-(1/2 : ℝ))
      ≤ (1 : ℝ) ^ (-(1/2 : ℝ)) := by
        apply rpow_le_rpow_of_nonpos (by linarith) h1 (by norm_num)
    _ = 1 := one_rpow _

-- ────────────────────────────────────────────────────────────
-- G. Sum of √(k+1) for k < K: Σ √(k+1) ≤ (2/3)(K+1)^{3/2} + 1
--    (needed for the T^{3/4} assembly)
-- ────────────────────────────────────────────────────────────

-- Integral comparison: Σ_{k=0}^{K-1} √(k+1) ≤ ∫₁^{K+1} √t dt = (2/3)((K+1)^{3/2}-1)
-- We use a cruder but simpler bound:

theorem sum_sqrt_le_K_three_halves (K : ℕ) :
    ∑ k ∈ Finset.range K, Real.sqrt ((k : ℝ) + 1) ≤
    (K : ℝ) * Real.sqrt ((K : ℝ) + 1) := by
  have h : ∀ k ∈ Finset.range K, Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt ((K : ℝ) + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    apply Real.sqrt_le_sqrt
    have : (k : ℝ) < (K : ℝ) := Nat.cast_lt.mpr hk
    linarith
  calc ∑ k ∈ Finset.range K, Real.sqrt ((k : ℝ) + 1)
      ≤ ∑ _k ∈ Finset.range K, Real.sqrt ((K : ℝ) + 1) := Finset.sum_le_sum h
    _ = (K : ℝ) * Real.sqrt ((K : ℝ) + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

-- ────────────────────────────────────────────────────────────
-- H. Per-block pointwise MainTerm bound
--    |MainTerm t| ≤ 2·N(t) ≤ C·√t
-- ────────────────────────────────────────────────────────────

-- This uses project-specific defs (MainTerm, hardyN) so cannot be AXLE-verified.
-- Agent 1 should prove it in RSExpansionProof.lean directly.
-- Proof sketch:
--   |MainTerm t| = |2 Σ_{n<N} (n+1)^{-1/2} cos(...)| ≤ 2 Σ_{n<N} 1 = 2·N(t)
--   N(t) = ⌊√(t/2π)⌋ ≤ √(t/2π) + 1 ≤ √t/√(2π) + 1 ≤ C·√t

-- ════════════════════════════════════════════════════════════
-- PART 2: PROOF SKETCH FOR T^{3/4} (Path C)
-- ════════════════════════════════════════════════════════════

/-!
## T^{3/4} Proof Outline (if exponent is weakened)

```lean
private theorem mainTerm_first_moment_three_quarter :
    ∃ C_M > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, MainTerm t| ≤ C_M * T ^ ((3 : ℝ) / 4) := by
  -- Step 1: Pointwise bound
  have h_pw : ∃ C > 0, ∀ t, t ≥ 1 → |MainTerm t| ≤ C * t ^ ((1:ℝ)/2) := by
    -- |MainTerm t| ≤ 2·N(t) and N(t) ≤ √(t/2π) + 1 ≤ C·√t
    sorry -- (straightforward from definitions)
  obtain ⟨C, hC, h_pw⟩ := h_pw
  -- Step 2: Triangle inequality
  refine ⟨C * 2, by positivity, fun T hT => ?_⟩
  calc |∫ t in Ioc 1 T, MainTerm t|
      ≤ ∫ t in Ioc 1 T, |MainTerm t| := setIntegral_abs_le _
    _ ≤ ∫ t in Ioc 1 T, C * t ^ ((1:ℝ)/2) := by
        apply setIntegral_mono_on (MainTerm_integrable T).abs
          ((continuous_const.mul (continuous_rpow_const ...)..).integrableOn)
          measurableSet_Ioc fun t ht => h_pw t (by linarith [ht.1])
    _ ≤ C * (2/3) * (T ^ ((3:ℝ)/2) - 1) := by
        -- ∫₁ᵀ t^{1/2} dt = (2/3)(T^{3/2} - 1)
        sorry
    _ ≤ C * 2 * T ^ ((3:ℝ)/4) := by
        sorry -- T^{3/2} ≤ 3·T^{3/4} for T ≥ 2?? NO — T^{3/2} >> T^{3/4}.
```

ISSUE: The pointwise bound gives ∫ |MainTerm| ≤ C·T^{3/2}, not T^{3/4}.
The T^{3/4} bound REQUIRES oscillatory cancellation (VdC), not just
the triangle inequality.

For the T^{3/4} VdC proof, the per-block analysis from the top of this
file applies. The full proof requires inlining VdC into RSExpansionProof
and doing the block decomposition. This is a substantial proof (~200-300 lines)
requiring:
- setIntegral_Ioc_split to partition into blocks
- hardyN_on_open_block to fix N on each block
- integral_finset_sum_cos to swap sum/integral
- VdC bounds (inlined from scratch_vdc_proofs.lean) per mode
- Telescoping sum bound (sum_inv_sqrt_le_two_sqrt)
- Block count bound (block_count_le_sqrt')
- sum_sqrt_le_K_three_halves for the resonant contribution

## ACTUAL RECOMMENDED FIX

Looking at the architecture more carefully, the cleanest fix is:

1. In RSExpansionProof.lean, prove `mainTerm_first_moment_ibp` with
   exponent 3/4 instead of 1/2.

2. Prove `errorTerm_first_moment_sqrt` with exponent 1/2 (this is the
   alternating block cancellation, which is almost done — line 4584 sorry).

3. In `siegel_first_moment`, combine:
   |∫ Z| ≤ |∫ MainTerm| + |∫ ErrorTerm| ≤ C·T^{3/4} + C·T^{1/2} = O(T^{3/4})

4. Change `hardyZ_first_moment_sqrt_bound` to claim T^{3/4}.

5. In HardyZFirstMomentIBP.lean, `ibp_oscillatory_bound` would get T^{3/4}.
   Then `hardyZ_first_moment_sqrt` would claim T^{3/4+ε} ≤ T^{1/2+ε'}
   for suitable ε, ε'. Check if this works: T^{3/4+ε} vs T^{1/2+ε}.
   For ε = 0: T^{3/4} > T^{1/2}. So this DOES NOT give the classical
   T^{1/2+ε} bound. The downstream `hardyZ_first_moment_sqrt` claims
   T^{1/2+ε} and would need T^{1/2} from the ibp bound.

   So weakening to T^{3/4} would break the downstream. NOT VIABLE.

## THEREFORE: Sorry #3 is IRREDUCIBLE at the T^{1/2} level.

The T^{1/2} bound for ∫ MainTerm requires either:
(a) Breaking the import cycle with HardyZFirstMomentIBP to use ∫ Z = O(T^{1/2}), or
(b) Inlining the FULL IBP-on-Z proof within RSExpansionProof.lean (~800 lines),
    including ζ convexity bounds, θ' monotonicity, etc.

Neither is a quick fix. This sorry should be marked as IRREDUCIBLE
alongside the two B5aDefs sorrys.
-/

-- ════════════════════════════════════════════════════════════
-- PART 3: ARCHITECTURE FIX PROPOSAL
-- ════════════════════════════════════════════════════════════

/-!
## Import Cycle Break (Path A, detailed)

Current cycle:
  RSExpansionProof.lean → defines hardyZ_first_moment_sqrt_bound
  HardyZFirstMomentIBP.lean → imports RSExpansionProof
                             → uses hardyZ_first_moment_sqrt_bound

The cycle means RSExpansionProof can't use results from HardyZFirstMomentIBP.

FIX: Create a new file `HardyZFirstMomentDirect.lean` that:
1. Does NOT import RSExpansionProof
2. Proves |∫ Z| ≤ C·T^{1/2} directly via IBP on Z (the Titchmarsh §4.15 argument)
3. Uses only: HardyThetaSmooth, PhragmenLindelof (ζ convexity), ThetaDeriv*
4. The proof is already mostly done in HardyZFirstMomentIBP.lean Parts 1-5

Then RSExpansionProof can import HardyZFirstMomentDirect and use:
  |∫ MainTerm| ≤ |∫ Z| + |∫ ErrorTerm| ≤ C·T^{1/2} + C·T^{1/2} = O(T^{1/2})

This breaks the cycle and lets sorry #3 close.

Actually, checking the file list:
  `Littlewood/Aristotle/HardyFirstMomentDirect.lean` already exists!
  Agent 1 should check if it contains the needed bound.
-/

end
