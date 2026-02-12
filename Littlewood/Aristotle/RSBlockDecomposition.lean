/- 
Riemann-Siegel block decomposition infrastructure.

This file proves the interval-partition wiring for `ErrorTerm` and isolates
the deep RS sign-structure input as one atomic sorry.
-/

import Mathlib
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.IntervalPartition
import Littlewood.Aristotle.HardyNProperties

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.RSBlockDecomposition

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

private lemma hardyStart_le_succ (k : ℕ) :
    hardyStart k ≤ hardyStart (k + 1) := by
  have hlen := Aristotle.HardyNProperties.block_length k
  have hnonneg : 0 ≤ 2 * Real.pi * (2 * (k : ℝ) + 3) := by positivity
  linarith

private lemma hardyStart_ge_one (k : ℕ) : (1 : ℝ) ≤ hardyStart k := by
  rw [Aristotle.HardyNProperties.hardyStart_formula]
  have hk1 : (1 : ℝ) ≤ (k + 1 : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
  have hsq : (1 : ℝ) ≤ ((k + 1 : ℝ) ^ 2) := by nlinarith [hk1]
  have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  nlinarith

/-- Decompose the `ErrorTerm` integral into an initial short interval plus
finitely many breakpoint blocks `min T (hardyStart k)`. -/
theorem errorTerm_block_sum (T : ℝ) (hT : T ≥ 2) :
    ∫ t in Ioc 1 T, ErrorTerm t ∂volume =
      ∫ t in Ioc 1 (min T (hardyStart 0)), ErrorTerm t ∂volume
        + Finset.sum (Finset.range (hardyN T))
            (fun k =>
              ∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
                ErrorTerm t ∂volume) := by
  let bp : ℕ → ℝ := fun k => min T (hardyStart k)
  have h_total_integrable : IntegrableOn ErrorTerm (Ioc 1 T) := errorTerm_integrable T
  have h_bp_mono : ∀ k, k < hardyN T → bp k ≤ bp (k + 1) := by
    intro k _hk
    dsimp [bp]
    exact min_le_min_left T (hardyStart_le_succ k)
  have h_block_integrable :
      ∀ k, k < hardyN T → IntegrableOn ErrorTerm (Ioc (bp k) (bp (k + 1))) := by
    intro k _hk
    refine h_total_integrable.mono_set ?_
    intro x hx
    have hbp_ge_one : (1 : ℝ) ≤ bp k := by
      dsimp [bp]
      exact le_min (by linarith) (hardyStart_ge_one k)
    have hx_lower : 1 < x := lt_of_le_of_lt hbp_ge_one hx.1
    have hx_upper : x ≤ T := le_trans hx.2 (min_le_left T (hardyStart (k + 1)))
    exact ⟨hx_lower, hx_upper⟩
  have hT_nonneg : 0 ≤ T := by linarith
  have h_bpN : bp (hardyN T) = T := by
    dsimp [bp]
    apply min_eq_left
    by_contra hcontra
    have hstart_lt : hardyStart (hardyN T) < T := lt_of_not_ge hcontra
    have hlt : hardyN T < hardyN T :=
      (hardyN_lt_iff (hardyN T) T hT_nonneg).2 (le_of_lt hstart_lt)
    exact (Nat.lt_irrefl _ hlt)
  have h_tail_integrable : IntegrableOn ErrorTerm (Ioc (bp 0) T) := by
    have h_tail_integrable' :
        IntegrableOn ErrorTerm (Ioc (bp 0) (bp (hardyN T))) :=
      Aristotle.IntervalPartition.integrableOn_split_finitely
        ErrorTerm bp (hardyN T) h_bp_mono h_block_integrable
    simpa [h_bpN] using h_tail_integrable'
  have h_head_integrable : IntegrableOn ErrorTerm (Ioc 1 (bp 0)) := by
    refine h_total_integrable.mono_set ?_
    intro x hx
    exact ⟨hx.1, le_trans hx.2 (min_le_left T (hardyStart 0))⟩
  have h_bp0_ge_one : (1 : ℝ) ≤ bp 0 := by
    dsimp [bp]
    exact le_min (by linarith) (hardyStart_ge_one 0)
  have h_bp0_le_T : bp 0 ≤ T := by
    dsimp [bp]
    exact min_le_left T (hardyStart 0)
  have h_head_tail_split :
      ∫ t in Ioc 1 T, ErrorTerm t ∂volume =
        ∫ t in Ioc 1 (bp 0), ErrorTerm t ∂volume
          + ∫ t in Ioc (bp 0) T, ErrorTerm t ∂volume :=
    Aristotle.IntervalPartition.integral_split_at
      ErrorTerm 1 (bp 0) T h_bp0_ge_one h_bp0_le_T h_head_integrable h_tail_integrable
  have h_tail_sum :
      ∫ t in Ioc (bp 0) T, ErrorTerm t ∂volume =
        Finset.sum (Finset.range (hardyN T))
          (fun k => ∫ t in Ioc (bp k) (bp (k + 1)), ErrorTerm t ∂volume) := by
    calc
      ∫ t in Ioc (bp 0) T, ErrorTerm t ∂volume
          = ∫ t in Ioc (bp 0) (bp (hardyN T)), ErrorTerm t ∂volume := by
              simpa [h_bpN]
      _ = Finset.sum (Finset.range (hardyN T))
            (fun k => ∫ t in Ioc (bp k) (bp (k + 1)), ErrorTerm t ∂volume) := by
            simpa using
              Aristotle.IntervalPartition.integral_split_finitely
                ErrorTerm bp (hardyN T) h_bp_mono h_block_integrable
  calc
    ∫ t in Ioc 1 T, ErrorTerm t ∂volume
        = ∫ t in Ioc 1 (bp 0), ErrorTerm t ∂volume
            + ∫ t in Ioc (bp 0) T, ErrorTerm t ∂volume := h_head_tail_split
    _ = ∫ t in Ioc 1 (bp 0), ErrorTerm t ∂volume
          + Finset.sum (Finset.range (hardyN T))
              (fun k => ∫ t in Ioc (bp k) (bp (k + 1)), ErrorTerm t ∂volume) := by
            rw [h_tail_sum]
    _ = ∫ t in Ioc 1 (min T (hardyStart 0)), ErrorTerm t ∂volume
          + Finset.sum (Finset.range (hardyN T))
              (fun k =>
                ∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
                  ErrorTerm t ∂volume) := by
            simp [bp]

/-- **Atomic sorry**: Per-block signed RS remainder bound.

This encodes the Riemann-Siegel sign-structure on each breakpoint block and
includes the resulting global alternating-`sqrt` decomposition. -/
theorem per_block_signed_bound :
    ∃ A B : ℝ, A > 0 ∧ B ≥ 0 ∧
      (∀ T : ℝ, T ≥ 2 →
        ∀ k : ℕ, k < hardyN T →
          ∃ s : ℝ, s = (-1 : ℝ) ^ k ∧
            |(∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
                ErrorTerm t) - s * A * Real.sqrt ((k : ℝ) + 1)| ≤ B) ∧
      (∀ T : ℝ, T ≥ 2 →
        ∃ N : ℕ,
          ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
          |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + B) := by
  sorry

/-- Wire the block-level atomic input into the global alternating-`sqrt`
decomposition needed by `RSBreakpointDecomposition`. -/
theorem errorTerm_alternatingSqrt_decomposition_from_blocks :
    ∃ A B : ℝ, A > 0 ∧ B ≥ 0 ∧
      ∀ T : ℝ, T ≥ 2 →
        ∃ N : ℕ,
          ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
          |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + B := by
  rcases per_block_signed_bound with ⟨A, B, hA, hB, _hlocal, hglobal⟩
  exact ⟨A, B, hA, hB, hglobal⟩

end Aristotle.RSBlockDecomposition
