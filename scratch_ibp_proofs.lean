/-
  scratch_ibp_proofs.lean
  =======================
  AXLE-verified Mathlib-only sub-lemmas for closing sorry #3
  (mainTerm_first_moment_ibp) in RSExpansionProof.lean.

  Agent 2 (iteration 2), 2026-03-15.

  These proofs are AXLE-verified: they compile against Mathlib alone
  with no Littlewood imports. Agent 1 can inline them into the sorry
  proof after adapting to the local definitions.

  CONTEXT: The sorry is
    ∃ C_M > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, MainTerm t| ≤ C_M * T ^ (1/2)

  where MainTerm t = 2 * Σ_{n<N(t)} (n+1)^{-1/2} * cos(θ(t) - t*log(n+1))
  and N(t) = ⌊√(t/2π)⌋.

  PROOF STRATEGY (Titchmarsh §4.15):
  1. Split [1,T] = [1,T₀] ∪ [T₀,T]
  2. [1,T₀]: bounded integral (continuity on compact interval)
  3. [T₀,T]: split into Hardy blocks [hs(k), hs(k+1)]
     - On each block, N(t) = k+1 is constant → swap sum/integral
     - Per-mode VdC: mode n has phase φ_n(t) = θ(t) - t·log(n+1)
       with φ'_n(t) = θ'(t) - log(n+1)
     - Off-resonant modes (n ≠ k): |φ'_n| ≥ δ_n, VdC gives O(1/δ_n)
     - Sum over modes: Σ 1/(√n·δ_n) per block ≤ C/log(k)
     - Sum over blocks: Σ_{k≤K} C/log(k) ≤ C·K/log(K) ≤ C·√T/log(T)

  The VdC infrastructure exists in the project (VanDerCorputGeneric.lean:
  vdc_first_deriv_cos, vdc_first_deriv_sin — both sorry-free).
  These cannot be imported into RSExpansionProof due to circular deps.

  The sub-lemmas below handle the MATHLIB-ONLY arithmetic/analysis steps.
-/

import Mathlib

set_option linter.unusedVariables false

open Real MeasureTheory Set Filter Topology Finset

noncomputable section

/-! ## Part A: Sum of 1/√(n+1) ≤ 2√N (telescoping) -/

/-- 1/√(n+1) ≤ 2(√(n+1) - √n) for all n : ℕ.
    Proof: conjugate multiplication gives √(n+1) - √n = 1/(√(n+1) + √n),
    and √(n+1) + √n ≤ 2√(n+1), so 1/√(n+1) ≤ 2(√(n+1) - √n). -/
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

/-- Sum of 1/√(n+1) for n in range N telescopes to ≤ 2√N.
    This is the key harmonic sum bound for per-mode VdC aggregation:
    Σ_{n<N} (n+1)^{-1/2} ≤ 2√N. -/
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

/-! ## Part B: rpow comparison lemmas -/

/-- T^{1/4} ≤ T^{1/2} for T ≥ 1. -/
theorem rpow_quarter_le_half {T : ℝ} (hT : 1 ≤ T) :
    T ^ ((1 : ℝ)/4) ≤ T ^ ((1 : ℝ)/2) :=
  rpow_le_rpow_of_exponent_le hT (by norm_num : (1:ℝ)/4 ≤ 1/2)

/-- T^{1/4}/log(T) ≤ T^{1/2} for T ≥ e (since log T ≥ 1). -/
theorem rpow_quarter_div_log_le_half {T : ℝ} (hT : Real.exp 1 ≤ T) :
    T ^ ((1 : ℝ)/4) / Real.log T ≤ T ^ ((1 : ℝ)/2) := by
  have hT_pos : 0 < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  have hexp_gt_1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hT_ge_1 : 1 ≤ T := le_trans (le_of_lt hexp_gt_1) hT
  have hlog_ge_one : 1 ≤ Real.log T := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos 1) hT
  calc T ^ ((1 : ℝ)/4) / Real.log T
      ≤ T ^ ((1 : ℝ)/4) :=
        div_le_self (rpow_nonneg (le_of_lt hT_pos) _) hlog_ge_one
    _ ≤ T ^ ((1 : ℝ)/2) :=
        rpow_le_rpow_of_exponent_le hT_ge_1 (by norm_num)

/-! ## Part C: √N ≤ C·T^{1/4} when N ≈ √(T/2π) -/

/-- If N ≤ √(T/(2π)) + 1 (the hardyN bound), then √N ≤ (T/(2π))^{1/4} + 1.
    Used to convert the mode count into an rpow bound on T. -/
theorem sqrt_hardyN_le_rpow_quarter {N : ℕ} {T : ℝ} (hT : 0 < T)
    (hN : (N : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) + 1) :
    Real.sqrt N ≤ (T / (2 * Real.pi)) ^ ((1:ℝ)/4) + 1 := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have h1 : Real.sqrt N ≤ Real.sqrt (Real.sqrt (T / (2 * Real.pi)) + 1) := by
    apply Real.sqrt_le_sqrt; exact_mod_cast hN
  have h_sqrt_T2pi_nn : 0 ≤ Real.sqrt (T / (2 * Real.pi)) := Real.sqrt_nonneg _
  -- √(a+1) ≤ √a + 1 for a ≥ 0
  have h2 : Real.sqrt (Real.sqrt (T / (2 * Real.pi)) + 1) ≤
      Real.sqrt (Real.sqrt (T / (2 * Real.pi))) + 1 := by
    rw [← Real.sqrt_sq
      (show 0 ≤ Real.sqrt (Real.sqrt (T / (2 * Real.pi))) + 1 by positivity)]
    apply Real.sqrt_le_sqrt
    nlinarith [Real.sq_sqrt h_sqrt_T2pi_nn,
               Real.sqrt_nonneg (Real.sqrt (T / (2 * Real.pi)))]
  -- √(√x) = x^{1/4}
  have h3 : Real.sqrt (Real.sqrt (T / (2 * Real.pi))) =
      (T / (2 * Real.pi)) ^ ((1:ℝ)/4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    rw [← rpow_mul (div_nonneg (le_of_lt hT) (le_of_lt hpi))]
    norm_num
  linarith

/-! ## Part D: Interval integral norm bound -/

/-- Interval integral norm bound: ‖∫_a^b f‖ ≤ M·(b-a) when ‖f(t)‖ ≤ M on [a,b].
    Used for bounding the compact piece [1,T₀]. -/
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

/-! ## Part E: Integral interchange for finite sums -/

/-- Swap sum and integral for finite weighted cosine sums.
    Used to decompose ∫ MainTerm into per-mode integrals on each block
    (where N(t) is constant). -/
theorem integral_finset_sum_cos {a b : ℝ} (N : ℕ)
    (w : ℕ → ℝ) (φ : ℕ → ℝ → ℝ)
    (hint : ∀ n ∈ Finset.range N,
      IntervalIntegrable (fun t => w n * Real.cos (φ n t)) volume a b) :
    ∫ t in a..b, ∑ n ∈ Finset.range N, w n * Real.cos (φ n t) =
    ∑ n ∈ Finset.range N, ∫ t in a..b, w n * Real.cos (φ n t) :=
  intervalIntegral.integral_finset_sum (s := Finset.range N)
    (f := fun n t => w n * Real.cos (φ n t)) hint

/-! ## Part F: Set integral splitting -/

/-- |∫ f over Ioc a b| = |∫_a^b f| when a ≤ b.
    Converts between the set integral notation and interval integral. -/
theorem abs_setIntegral_Ioc_eq_abs_intervalIntegral
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (_hf : IntervalIntegrable f volume a b) :
    |∫ t in Ioc a b, f t| = |∫ t in a..b, f t| := by
  rw [intervalIntegral.integral_of_le hab]

/-- Splitting an Ioc integral: ∫_{(a,b]} = ∫_{(a,c]} + ∫_{(c,b]}.
    Used to decompose ∫₁ᵀ MainTerm into [1,T₀] + [T₀,T]. -/
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

/-! ## Part G: Triangle inequality for integral sums -/

/-- |Σᵢ ∫_a^b fᵢ| ≤ Σᵢ |∫_a^b fᵢ|. Trivial but useful for assembly. -/
theorem abs_sum_integrals_le (N : ℕ) (a : ℕ → ℝ) :
    |∑ n ∈ Finset.range N, a n| ≤ ∑ n ∈ Finset.range N, |a n| :=
  Finset.abs_sum_le_sum_abs _ _

/-! ## Usage Guide for Agent 1

The proof of `mainTerm_first_moment_ibp` should follow this outline:

1. Fix T₀ large enough (from thetaDeriv_lower_bound, which exists in the project)
2. Split: |∫₁ᵀ MainTerm| ≤ |∫₁^{T₀} MainTerm| + |∫_{T₀}^T MainTerm|
   - Use `setIntegral_Ioc_split` + triangle inequality
3. Compact piece: |∫₁^{T₀} MainTerm| ≤ C₀ (constant, absorbed into C_M)
   - MainTerm is continuous → integrable on compact [1,T₀]
   - Use `interval_integral_norm_le` or just ⟨|∫| + 1, by positivity, by linarith⟩
4. Tail piece: Split [T₀,T] into Hardy blocks [hs(k), hs(k+1)]
   - On each block, N(t) = k+1 is constant
   - Use `integral_finset_sum_cos` to swap sum/integral
   - Each mode n: ∫ (n+1)^{-1/2} cos(θ(t) - t·log(n+1)) dt
     = (n+1)^{-1/2} · ∫ cos(φ_n(t)) dt
   - Per-mode VdC: ‖∫ cos(φ_n(t))‖ ≤ 2/|φ'_n(a)| where
     φ'_n(t) = θ'(t) - log(n+1)
   - Use existing `vdc_first_deriv_cos` from VanDerCorputGeneric
     (must be inlined since circular import blocks it)
   - Sum over modes: Σ_n (n+1)^{-1/2} · 2/|φ'_n| ≤ C/log(k) per block
   - Use `sum_inv_sqrt_le_two_sqrt` for the 1/√n sum
5. Sum over K ≤ √T blocks → total ≤ C·√T/log(T₀) ≤ C·√T
   - Use `rpow_quarter_div_log_le_half`
   - Use `sqrt_hardyN_le_rpow_quarter` to control mode count

CRITICAL NOTE: The VdC first derivative test (vdc_first_deriv_cos) is ~90 lines
and requires IBP + monotone derivative assumptions. It IS proved in the project
at VanDerCorputGeneric.lean:196 but cannot be imported into RSExpansionProof.
Agent 1 has two options:
  (a) Inline the ~90-line proof of vdc_first_deriv_cos
  (b) Use the weaker approach: on each block of length L ~ √k,
      |∫ cos(φ_n)| ≤ L (trivial bound for resonant mode n=k),
      and sum of non-resonant VdC bounds is O(1/log k).
      Both approaches give O(√T) total.
-/

end
