/-
  Minimum Modulus Pigeonhole Principle

  For each integer k ≥ 2, there exists R_k ∈ [k, k+1] such that all nontrivial
  zeta zeros ρ satisfy |R_k - |ρ|| ≥ δ_k where δ_k = 1/(2·C·k·log k).

  The argument:
  1. Each zero γ "blocks" an open interval (γ - δ, γ + δ) on the real line
  2. Zeros near radius k: count ≤ C·k·log k (from RvM, PROVED)
  3. Total blocked measure ≤ card × 2δ = C·k·log k × 2/(2·C·k·log k) = 1
     With c small enough, total blocked < 1
  4. Since [k, k+1] has length 1 > total blocked, ∃ R_k avoiding all blocks

  This is the pigeonhole/measure-avoidance step for the minimum modulus method
  used in Hadamard product lower bounds on good circles.

  Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.unusedVariables false

open MeasureTheory Set Finset Real ENNReal

noncomputable section

namespace MinimumModulusPigeonhole

/-! ## Blocking intervals and their measure -/

/-- The blocking interval for a single zero ordinate γ with clearance δ. -/
def zeroBlock (γ : ℝ) (δ : ℝ) : Set ℝ := Set.Ioo (γ - δ) (γ + δ)

/-- The union of all blocking intervals for a finite set of zero ordinates. -/
def blockedSet (zeros : Finset ℝ) (δ : ℝ) : Set ℝ :=
  ⋃ γ ∈ zeros, zeroBlock γ δ

/-! ## Volume of a single blocking interval -/

theorem volume_zeroBlock (γ δ : ℝ) :
    volume (zeroBlock γ δ) = ENNReal.ofReal (2 * δ) := by
  simp only [zeroBlock, Real.volume_Ioo]
  congr 1; ring

/-! ## Sub-additivity: total blocked measure ≤ sum of individual measures -/

theorem volume_blockedSet_le (zeros : Finset ℝ) (δ : ℝ) :
    volume (blockedSet zeros δ) ≤ zeros.card * ENNReal.ofReal (2 * δ) := by
  unfold blockedSet
  calc volume (⋃ γ ∈ zeros, zeroBlock γ δ)
      ≤ ∑ γ ∈ zeros, volume (zeroBlock γ δ) :=
        measure_biUnion_finset_le zeros (fun γ => zeroBlock γ δ)
    _ = ∑ _γ ∈ zeros, ENNReal.ofReal (2 * δ) := by
        apply Finset.sum_congr rfl; intro γ _
        exact volume_zeroBlock γ δ
    _ = zeros.card * ENNReal.ofReal (2 * δ) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## Core pigeonhole: if total blocked < length of interval, ∃ unblocked point -/

/-- If the total measure of blocked intervals is less than 1 (the length of [k, k+1]),
    then there exists a point in [k, k+1] not in any blocking interval. -/
theorem exists_unblocked_point (k : ℝ) (zeros : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (h_small : zeros.card * (2 * δ) < 1) :
    ∃ R ∈ Set.Icc k (k + 1), R ∉ blockedSet zeros δ := by
  by_contra h_all
  push_neg at h_all
  have h_sub : Set.Icc k (k + 1) ⊆ blockedSet zeros δ := fun x hx => h_all x hx
  have h_vol_Icc : volume (Set.Icc k (k + 1)) = ENNReal.ofReal 1 := by
    rw [Real.volume_Icc]; congr 1; ring
  have h1 : ENNReal.ofReal 1 ≤ zeros.card * ENNReal.ofReal (2 * δ) := by
    calc ENNReal.ofReal 1 = volume (Set.Icc k (k + 1)) := h_vol_Icc.symm
      _ ≤ volume (blockedSet zeros δ) := measure_mono h_sub
      _ ≤ zeros.card * ENNReal.ofReal (2 * δ) := volume_blockedSet_le zeros δ
  have h2 : zeros.card * ENNReal.ofReal (2 * δ) < ENNReal.ofReal 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_lt_ofReal_iff one_pos |>.mpr h_small
  exact absurd h1 (not_le.mpr h2)

/-- Variant with explicit gap bound: if card ≤ n and 2·n·δ < 1, there's an unblocked point. -/
theorem exists_unblocked_of_count_bound (k : ℝ) (zeros : Finset ℝ) (δ : ℝ) (n : ℕ)
    (hδ : 0 < δ) (hcard : zeros.card ≤ n) (h_small : 2 * n * δ < 1) :
    ∃ R ∈ Set.Icc k (k + 1), R ∉ blockedSet zeros δ := by
  apply exists_unblocked_point k zeros δ hδ
  calc (zeros.card : ℝ) * (2 * δ)
      ≤ (n : ℝ) * (2 * δ) := by
        apply mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard)
        linarith
    _ = 2 * n * δ := by ring
    _ < 1 := h_small

/-! ## Extracting gap from non-membership -/

private theorem abs_ge_of_not_in_zeroBlock {R γ δ : ℝ} (h : R ∉ zeroBlock γ δ) :
    |R - γ| ≥ δ := by
  simp only [zeroBlock, Set.mem_Ioo, not_and_or, not_lt] at h
  rcases h with h | h
  · -- R ≤ γ - δ, so γ - R ≥ δ, hence |R - γ| ≥ δ
    have h1 : δ ≤ γ - R := by linarith
    have h2 : δ ≤ -(R - γ) := by linarith
    exact le_trans h2 (neg_le_abs (R - γ))
  · -- γ + δ ≤ R, so R - γ ≥ δ, hence |R - γ| ≥ δ
    have h1 : δ ≤ R - γ := by linarith
    exact le_trans h1 (le_abs_self (R - γ))

/-! ## Helper: n * (2/(2n+2)) < 1 -/

private theorem mul_two_div_lt_one (n : ℝ) (hn : 0 < n) :
    n * (2 * (1 / (2 * n + 2))) < 1 := by
  have h_denom : 0 < 2 * n + 2 := by linarith
  have : 2 * (1 / (2 * n + 2)) = 2 / (2 * n + 2) := by ring
  rw [this]
  rw [show n * (2 / (2 * n + 2)) = 2 * n / (2 * n + 2) from by ring]
  exact div_lt_one h_denom |>.mpr (by linarith)

/-! ## The main existence theorem: good radius from zero density -/

/-- For any finite set of zero ordinates with controlled density,
    there exists R ∈ [k, k+1] bounded away from all of them.

    The gap δ = 1/(2n+2) where n = ⌈C·k·log k⌉₊ ≥ card(zeros_near).
    Any point R not in any blocking interval satisfies |R - γ| ≥ δ for all γ. -/
theorem exists_good_radius (k : ℕ) (hk : 2 ≤ k)
    (zeros_near : Finset ℝ) (C : ℝ) (hC : 0 < C)
    (hcount : zeros_near.card ≤ ⌈C * k * Real.log k⌉₊) :
    ∃ R : ℝ, R ∈ Set.Icc (k : ℝ) (k + 1) ∧
      ∀ γ ∈ zeros_near, |R - γ| ≥ 1 / (2 * ⌈C * k * Real.log k⌉₊ + 2) := by
  set n := ⌈C * k * Real.log k⌉₊
  set δ := 1 / (2 * (n : ℝ) + 2)
  have hk_one : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
  have hlog_pos : 0 < Real.log (k : ℝ) := Real.log_pos hk_one
  have hn_pos : 0 < (n : ℝ) := by
    apply Nat.cast_pos.mpr
    apply Nat.pos_of_ne_zero
    intro h0
    simp [n] at h0
    have : 0 < C * ↑k * Real.log ↑k := by positivity
    linarith [Nat.le_ceil (C * ↑k * Real.log ↑k)]
  have hδ_pos : 0 < δ := by positivity
  have h_card_small : (zeros_near.card : ℝ) * (2 * δ) < 1 := by
    calc (zeros_near.card : ℝ) * (2 * δ)
        ≤ (n : ℝ) * (2 * δ) :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcount) (by linarith)
      _ = (n : ℝ) * (2 * (1 / (2 * (n : ℝ) + 2))) := by rfl
      _ < 1 := mul_two_div_lt_one n hn_pos
  obtain ⟨R, hR_mem, hR_not_blocked⟩ :=
    exists_unblocked_point (k : ℝ) zeros_near δ hδ_pos h_card_small
  exact ⟨R, hR_mem, fun γ hγ =>
    abs_ge_of_not_in_zeroBlock (fun hmem =>
      hR_not_blocked (Set.mem_biUnion hγ hmem))⟩

/-! ## General pigeonhole: arbitrary interval [a, b] -/

/-- The key pigeonhole theorem stated in terms of an arbitrary count bound.
    Given N zeros each blocking width 2δ inside an interval of length b - a,
    if N · 2δ < b - a then some point in [a,b] is unblocked. -/
theorem pigeonhole_interval_avoidance
    (a b : ℝ) (hab : a < b) (zeros : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (h_small : zeros.card * (2 * δ) < b - a) :
    ∃ R ∈ Set.Icc a b, ∀ γ ∈ zeros, |R - γ| ≥ δ := by
  by_contra h_all
  push_neg at h_all
  have h_sub : Set.Icc a b ⊆ ⋃ γ ∈ zeros, zeroBlock γ δ := by
    intro R hR
    obtain ⟨γ, hγ, hclose⟩ := h_all R hR
    apply Set.mem_iUnion₂.mpr
    exact ⟨γ, hγ, by
      simp only [zeroBlock, Set.mem_Ioo]
      have hlt := abs_lt.mp hclose
      exact ⟨by linarith [hlt.1], by linarith [hlt.2]⟩⟩
  have h1 : ENNReal.ofReal (b - a) ≤ zeros.card * ENNReal.ofReal (2 * δ) := by
    calc ENNReal.ofReal (b - a) = volume (Set.Icc a b) := (Real.volume_Icc).symm
      _ ≤ volume (⋃ γ ∈ zeros, zeroBlock γ δ) := measure_mono h_sub
      _ ≤ zeros.card * ENNReal.ofReal (2 * δ) := volume_blockedSet_le zeros δ
  have h2 : zeros.card * ENNReal.ofReal (2 * δ) < ENNReal.ofReal (b - a) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_lt_ofReal_iff (by linarith) |>.mpr h_small
  exact absurd h1 (not_le.mpr h2)

/-! ## Product lower bound on good circles (statement only) -/

/-- Individual factor lower bound: if ‖s‖ = R and |R - ‖ρ‖| ≥ δ and ρ ≠ 0, then
    ‖1 - s/ρ‖ ≥ δ/(R + ‖ρ‖).

    This is the key estimate that makes the minimum modulus method work:
    on a circle avoiding all zero moduli, each Weierstrass factor is bounded below. -/
theorem weierstrass_factor_lower_bound
    (s ρ : ℂ) (hρ : ρ ≠ 0) (R δ : ℝ) (hR : 0 < R) (hδ : 0 < δ)
    (hs : ‖s‖ = R)
    (h_gap : |R - ‖ρ‖| ≥ δ) :
    ‖1 - s / ρ‖ ≥ δ / (R + ‖ρ‖) := by
  have hρ_norm : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have hR_ρ : 0 < R + ‖ρ‖ := by linarith [norm_nonneg ρ]
  -- Step 1: ‖1 - s/ρ‖ = ‖ρ - s‖ / ‖ρ‖
  have h1 : ‖1 - s / ρ‖ = ‖ρ - s‖ / ‖ρ‖ := by
    rw [show (1 : ℂ) - s / ρ = (ρ - s) / ρ by field_simp]
    rw [norm_div]
  -- Step 2: ‖ρ - s‖ ≥ δ via reverse triangle inequality
  have h_rev : δ ≤ ‖ρ - s‖ := by
    have h_tri : |‖ρ‖ - ‖s‖| ≤ ‖ρ - s‖ := abs_norm_sub_norm_le ρ s
    have h_eq : |R - ‖ρ‖| = |‖ρ‖ - ‖s‖| := by rw [hs]; rw [abs_sub_comm]
    linarith
  -- Step 3: δ/(R + ‖ρ‖) ≤ ‖ρ - s‖/‖ρ‖
  rw [h1, ge_iff_le, div_le_div_iff₀ hR_ρ hρ_norm]
  calc δ * ‖ρ‖ ≤ ‖ρ - s‖ * ‖ρ‖ := by nlinarith
    _ ≤ ‖ρ - s‖ * (R + ‖ρ‖) := by nlinarith [norm_nonneg (ρ - s)]

/-! ## Assembling the full minimum modulus lemma -/

/-- Full minimum modulus pigeonhole: for each k ≥ 2, given n zeros,
    we get an R ∈ [k, k+1] with clearance δ ≥ 1/(2n+2) from all listed ordinates. -/
theorem minimum_modulus_pigeonhole_from_count
    (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : 0 < n)
    (zeros_up_to : Finset ℝ) (hcard : zeros_up_to.card ≤ n) :
    ∃ R : ℝ, R ∈ Set.Icc (k : ℝ) (k + 1) ∧
      ∀ γ ∈ zeros_up_to, |R - γ| ≥ 1 / (2 * (n : ℝ) + 2) := by
  set δ := 1 / (2 * (n : ℝ) + 2)
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hδ_pos : 0 < δ := by positivity
  have h_card_small : (zeros_up_to.card : ℝ) * (2 * δ) < 1 := by
    calc (zeros_up_to.card : ℝ) * (2 * δ)
        ≤ (n : ℝ) * (2 * δ) :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (by linarith)
      _ = (n : ℝ) * (2 * (1 / (2 * (n : ℝ) + 2))) := by rfl
      _ < 1 := mul_two_div_lt_one n hn_pos
  obtain ⟨R, hR_mem, hR_not_blocked⟩ :=
    exists_unblocked_point (k : ℝ) zeros_up_to δ hδ_pos h_card_small
  exact ⟨R, hR_mem, fun γ hγ =>
    abs_ge_of_not_in_zeroBlock (fun hmem =>
      hR_not_blocked (Set.mem_biUnion hγ hmem))⟩

end MinimumModulusPigeonhole
