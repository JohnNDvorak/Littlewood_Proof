/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Dirichlet series infrastructure from Aristotle.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib

set_option maxHeartbeats 400000

open Complex Topology Filter

noncomputable section

/-- For any positive epsilon, the sequence (log n)^k * n^(-epsilon) is bounded.
    This is the key lemma for bounding growth of Dirichlet series derivatives. -/
lemma log_pow_mul_neg_power_bounded (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (Real.log n)^k * (n : ℝ)^(-ε) ≤ C := by
  -- Use the fact that y^k * exp(-y) → 0 as y → ∞
  -- For x = ε * log n, we get (log n)^k * n^(-ε) = (x/ε)^k * exp(-x) / ε^(-k)
  -- This is bounded since x^k * exp(-x) → 0
  have h_tendsto := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
  -- Get bound from eventual behavior
  obtain ⟨M, hM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 0 ≤ x → x^k * Real.exp (-x) ≤ M := by
    -- The function is continuous on [0, ∞) and tends to 0
    have h_cont : Continuous (fun x : ℝ => x^k * Real.exp (-x)) := by continuity
    -- On [0, K] for large K, bounded by compactness
    -- Eventually bounded by 1
    obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ x : ℝ, K ≤ x → x^k * Real.exp (-x) ≤ 1 := by
      have h_ev := h_tendsto.eventually (ge_mem_nhds zero_lt_one)
      exact eventually_atTop.mp h_ev
    -- On [0, max K 1], bounded by compactness
    have h_nonempty : Set.Nonempty (Set.Icc 0 (max K 1)) := ⟨0, ⟨le_refl 0, le_max_of_le_right (by linarith : (0 : ℝ) ≤ 1)⟩⟩
    obtain ⟨x₀, hx₀_mem, hx₀_max⟩ := isCompact_Icc.exists_isMaxOn h_nonempty h_cont.continuousOn
    use max 1 (x₀^k * Real.exp (-x₀))
    constructor
    · exact lt_max_of_lt_left zero_lt_one
    · intro x hx
      by_cases hx_small : x ≤ max K 1
      · calc x^k * Real.exp (-x) ≤ x₀^k * Real.exp (-x₀) := hx₀_max ⟨hx, hx_small⟩
          _ ≤ max 1 (x₀^k * Real.exp (-x₀)) := le_max_right _ _
      · push_neg at hx_small
        have hK_le : K ≤ x := le_trans (le_max_left K 1) (le_of_lt hx_small)
        calc x^k * Real.exp (-x) ≤ 1 := hK x hK_le
          _ ≤ max 1 (x₀^k * Real.exp (-x₀)) := le_max_left _ _
  use M / ε^k + 1
  constructor
  · have hε_pow_pos : 0 < ε^k := pow_pos hε k
    linarith [div_pos hM.1 hε_pow_pos]
  intro n hn
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
  have h_log_nonneg : 0 ≤ Real.log n := Real.log_nonneg (Nat.one_le_cast.mpr hn)
  -- n^(-ε) = exp(-ε * log n)
  have h_rpow : (n : ℝ)^(-ε) = Real.exp (-ε * Real.log n) := by
    rw [Real.rpow_def_of_pos hn_pos]
    ring_nf
  -- Set x = ε * log n ≥ 0
  set x := ε * Real.log n with hx_def
  have hx_nonneg : 0 ≤ x := mul_nonneg (le_of_lt hε) h_log_nonneg
  -- Rewrite goal using x
  have h_exp_eq : Real.exp (-ε * Real.log n) = Real.exp (-x) := by rw [hx_def]; ring_nf
  rw [h_rpow, h_exp_eq]
  -- (log n)^k = (x/ε)^k = x^k / ε^k
  have h_log_eq : (Real.log n)^k = x^k / ε^k := by
    rw [hx_def]
    have hε_ne : ε ≠ 0 := ne_of_gt hε
    field_simp
    ring
  rw [h_log_eq]
  -- Goal: x^k / ε^k * exp(-x) ≤ M / ε^k + 1
  have h_bound := hM.2 x hx_nonneg
  have hε_pow_pos : 0 < ε^k := pow_pos hε k
  calc x^k / ε^k * Real.exp (-x) = (x^k * Real.exp (-x)) / ε^k := by ring
    _ ≤ M / ε^k := div_le_div_of_nonneg_right h_bound (le_of_lt hε_pow_pos)
    _ ≤ M / ε^k + 1 := by linarith

end
