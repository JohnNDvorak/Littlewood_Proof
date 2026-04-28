/-
# Pigeonhole-on-T height selection

Given a finite set `S : Finset ℝ` with `|S| ≤ N`, we can select a point
`T ∈ [T₀, T₀+1]` whose distance to every element of `S` is bounded below by
`1 / (4 * N + 2)`.

This is the key combinatorial input for the min-distance refactor of the
Hadamard zero sum: downstream consumers apply this to `S = finset of zero
ordinates near height T₀` (of cardinality `O(log T₀)` by Riemann-von
Mangoldt), yielding `|T - Im(ρ)| ≥ c / Real.log T` for every non-trivial
zeta zero.

## Proof

Partition `[T₀, T₀+1]` into `2N+1` equal subintervals of length
`1/(2N+1) = 2ε` where `ε = 1/(4N+2)`. Let `mₖ = T₀ + (2k+1)·ε` for
`k : Fin (2N+1)` be the midpoints.

For each `x ∈ S`, at most one midpoint `mₖ` satisfies `|mₖ - x| < ε`: if two
midpoints `mⱼ`, `mₖ` both satisfied this, then
`|mⱼ - mₖ| ≤ |mⱼ - x| + |x - mₖ| < 2ε`; but distinct midpoints are at
distance `≥ 2ε` apart. Choosing a witness `x ∈ S` for each "bad" midpoint
thus gives an injection from the bad set into `S`, so at most `|S| ≤ N`
midpoints are bad. Since there are `2N+1` midpoints total, at least
`N+1 ≥ 1` are "good" — at distance `≥ ε` from every `x ∈ S`. Any good
midpoint witnesses the theorem.

Co-authored-by: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
-/

import Mathlib

set_option maxHeartbeats 1600000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Littlewood.ZetaZeros.ZeroAvoidingHeight

open Finset

/-- **Pigeonhole on T.**

Given a finite set `S ⊆ ℝ` with `|S| ≤ N`, there exists a height
`T ∈ [T₀, T₀ + 1]` such that `|T - x| ≥ 1 / (4N + 2)` for every `x ∈ S`. -/
theorem exists_height_far_from_finset
    (S : Finset ℝ) (T₀ : ℝ) (N : ℕ) (hS : S.card ≤ N) :
    ∃ T ∈ Set.Icc T₀ (T₀ + 1),
      ∀ x ∈ S, (1 : ℝ) / (4 * (N : ℝ) + 2) ≤ |T - x| := by
  classical
  set ε : ℝ := 1 / (4 * (N : ℝ) + 2) with hε_def
  have h4N2_pos : (0 : ℝ) < 4 * (N : ℝ) + 2 := by positivity
  have hε_pos : 0 < ε := by positivity
  -- Midpoints m k = T₀ + (2k+1)·ε for k : Fin (2N+1)
  set midpt : Fin (2 * N + 1) → ℝ :=
    fun k => T₀ + (2 * ((k : ℕ) : ℝ) + 1) * ε with midpt_def
  -- Each midpoint lies in [T₀, T₀+1]
  have midpt_mem : ∀ k, midpt k ∈ Set.Icc T₀ (T₀ + 1) := by
    intro k
    refine ⟨?_, ?_⟩
    · have h1 : (0 : ℝ) ≤ 2 * ((k : ℕ) : ℝ) + 1 := by positivity
      have h2 : 0 ≤ (2 * ((k : ℕ) : ℝ) + 1) * ε := mul_nonneg h1 hε_pos.le
      show T₀ ≤ midpt k
      simp only [midpt_def]; linarith
    · have hk_lt : (k : ℕ) < 2 * N + 1 := k.isLt
      have hk_le : ((k : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
        have : (k : ℕ) ≤ 2 * N := Nat.le_of_lt_succ hk_lt
        exact_mod_cast this
      have hk_le_r : (2 * ((k : ℕ) : ℝ) + 1) ≤ 4 * (N : ℝ) + 1 := by linarith
      have step1 : (2 * ((k : ℕ) : ℝ) + 1) * ε ≤ (4 * (N : ℝ) + 1) * ε :=
        mul_le_mul_of_nonneg_right hk_le_r hε_pos.le
      have step2 : (4 * (N : ℝ) + 1) * ε ≤ 1 := by
        have : (4 * (N : ℝ) + 1) * ε = (4 * N + 1) / (4 * N + 2) := by
          simp [hε_def]; ring
        rw [this, div_le_one h4N2_pos]
        linarith
      show midpt k ≤ T₀ + 1
      simp only [midpt_def]; linarith
  -- Distinct midpoints are at distance ≥ 2ε
  have midpt_dist : ∀ {j k : Fin (2 * N + 1)}, j ≠ k →
      2 * ε ≤ |midpt j - midpt k| := by
    intro j k hjk
    have hval_ne : ((j : ℕ) : ℝ) ≠ ((k : ℕ) : ℝ) := by
      intro h
      apply hjk
      apply Fin.ext
      exact_mod_cast h
    have expand :
        midpt j - midpt k = 2 * ε * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) := by
      simp only [midpt_def]; ring
    rw [expand, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * ε)]
    have h_int_one_le : (1 : ℝ) ≤ |((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)| := by
      rcases lt_or_gt_of_ne hval_ne with hlt | hgt
      · rw [abs_of_neg (sub_neg.mpr hlt)]
        have hlt_nat : (j : ℕ) < (k : ℕ) := by exact_mod_cast hlt
        have h_one_le_sub : (1 : ℕ) ≤ (k : ℕ) - (j : ℕ) :=
          Nat.one_le_iff_ne_zero.mpr (fun h =>
            absurd (Nat.sub_eq_zero_iff_le.mp h) (not_le.mpr hlt_nat))
        have : ((1 : ℕ) : ℝ) ≤ (((k : ℕ) - (j : ℕ) : ℕ) : ℝ) :=
          by exact_mod_cast h_one_le_sub
        push_cast [Nat.cast_sub hlt_nat.le] at this
        linarith
      · rw [abs_of_pos (sub_pos.mpr hgt)]
        have hgt_nat : (k : ℕ) < (j : ℕ) := by exact_mod_cast hgt
        have h_one_le_sub : (1 : ℕ) ≤ (j : ℕ) - (k : ℕ) :=
          Nat.one_le_iff_ne_zero.mpr (fun h =>
            absurd (Nat.sub_eq_zero_iff_le.mp h) (not_le.mpr hgt_nat))
        have : ((1 : ℕ) : ℝ) ≤ (((j : ℕ) - (k : ℕ) : ℕ) : ℝ) :=
          by exact_mod_cast h_one_le_sub
        push_cast [Nat.cast_sub hgt_nat.le] at this
        linarith
    have := mul_le_mul_of_nonneg_left h_int_one_le (by linarith : (0 : ℝ) ≤ 2 * ε)
    linarith
  -- "Bad" midpoints: those within ε of some x ∈ S
  set bad : Finset (Fin (2 * N + 1)) :=
    (Finset.univ).filter (fun k => ∃ x ∈ S, |midpt k - x| < ε) with bad_def
  -- Witness function (total, returns 0 outside bad)
  set witness : Fin (2 * N + 1) → ℝ := fun k =>
    if hk : k ∈ bad then
      Classical.choose (Finset.mem_filter.mp hk).2
    else 0
    with witness_def
  have w_mem : ∀ k ∈ bad, witness k ∈ S := by
    intro k hk
    simp only [witness_def, dif_pos hk]
    exact (Classical.choose_spec (Finset.mem_filter.mp hk).2).1
  have w_lt : ∀ k ∈ bad, |midpt k - witness k| < ε := by
    intro k hk
    simp only [witness_def, dif_pos hk]
    exact (Classical.choose_spec (Finset.mem_filter.mp hk).2).2
  -- witness is injective on bad
  have w_inj : Set.InjOn witness (bad : Set (Fin (2 * N + 1))) := by
    intro j hj k hk heq
    by_contra hjk
    have hjk' : j ≠ k := hjk
    have hdist := midpt_dist hjk'
    have hj_lt := w_lt j hj
    have hk_lt := w_lt k hk
    have triangle :
        midpt j - midpt k = (midpt j - witness j) + (witness k - midpt k) := by
      rw [heq]; ring
    have habs : |midpt j - midpt k| < 2 * ε := by
      calc |midpt j - midpt k|
          = |(midpt j - witness j) + (witness k - midpt k)| := by rw [triangle]
        _ ≤ |midpt j - witness j| + |witness k - midpt k| := abs_add_le _ _
        _ = |midpt j - witness j| + |midpt k - witness k| := by
              rw [abs_sub_comm (witness k)]
        _ < ε + ε := by linarith
        _ = 2 * ε := by ring
    linarith
  -- bad.card ≤ S.card
  have bad_card_le : bad.card ≤ S.card := by
    calc bad.card
        = (bad.image witness).card := by
            rw [Finset.card_image_of_injOn w_inj]
      _ ≤ S.card := by
            apply Finset.card_le_card
            intro x hx
            obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
            exact w_mem k hk
  -- bad.card < 2N+1
  have bad_card_lt : bad.card < 2 * N + 1 := by
    calc bad.card ≤ S.card := bad_card_le
      _ ≤ N := hS
      _ < 2 * N + 1 := by omega
  -- Some midpoint is not bad
  have exists_good : ∃ k : Fin (2 * N + 1), k ∉ bad := by
    by_contra h
    push_neg at h
    have heq : bad = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    have : bad.card = 2 * N + 1 := by
      rw [heq, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k₀, hk₀⟩ := exists_good
  refine ⟨midpt k₀, midpt_mem k₀, ?_⟩
  intro x hx
  by_contra hlt
  push_neg at hlt
  apply hk₀
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ k₀, x, hx, ?_⟩
  show |midpt k₀ - x| < ε
  exact hlt

/-- **Pigeonhole on T, packaged for log-scaled distances.**

If `S.card ≤ a * Real.log T₀` with `a > 0` and `T₀ ≥ Real.exp 1 > 1`, the
height bound reduces to `|T - x| ≥ 1 / (4 * a * Real.log T₀ + 2)` for every
`x ∈ S`. This is the packaging the thin-strip integral wants. -/
theorem exists_height_far_from_finset_log
    (S : Finset ℝ) (T₀ : ℝ) (a : ℝ) (ha : 0 < a)
    (hT₀ : Real.exp 1 ≤ T₀)
    (hS : (S.card : ℝ) ≤ a * Real.log T₀) :
    ∃ T ∈ Set.Icc T₀ (T₀ + 1),
      ∀ x ∈ S, (1 : ℝ) / (4 * a * Real.log T₀ + 2) ≤ |T - x| := by
  set N : ℕ := ⌊a * Real.log T₀⌋₊ with hN_def
  have hlogT₀_ge_one : (1 : ℝ) ≤ Real.log T₀ := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    exact Real.log_le_log (Real.exp_pos _) hT₀
  have halogT₀_pos : 0 < a * Real.log T₀ :=
    mul_pos ha (by linarith : (0 : ℝ) < Real.log T₀)
  have halogT₀_nn : (0 : ℝ) ≤ a * Real.log T₀ := halogT₀_pos.le
  have hS_le_N : S.card ≤ N := Nat.le_floor hS
  obtain ⟨T, hT_mem, hT_bd⟩ := exists_height_far_from_finset S T₀ N hS_le_N
  refine ⟨T, hT_mem, fun x hx => ?_⟩
  have hN_le : ((N : ℕ) : ℝ) ≤ a * Real.log T₀ := Nat.floor_le halogT₀_nn
  have h4N2_pos : (0 : ℝ) < 4 * (N : ℝ) + 2 := by positivity
  have h4alog2_pos : (0 : ℝ) < 4 * a * Real.log T₀ + 2 := by linarith
  have h_denom : 4 * (N : ℝ) + 2 ≤ 4 * a * Real.log T₀ + 2 := by linarith
  have h_inv : (1 : ℝ) / (4 * a * Real.log T₀ + 2) ≤ 1 / (4 * (N : ℝ) + 2) :=
    one_div_le_one_div_of_le h4N2_pos h_denom
  linarith [hT_bd x hx]

end Littlewood.ZetaZeros.ZeroAvoidingHeight
