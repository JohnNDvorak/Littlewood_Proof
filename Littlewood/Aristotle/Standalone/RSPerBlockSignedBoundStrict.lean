/-
Standalone strict decomposition around the RS per-block signed bound.

Goal:
- avoid `sorry`/axioms,
- reprove the non-sorry block decomposition infrastructure,
- derive maximal nontrivial consequences,
- isolate the minimal remaining analytic input needed to recover the
  full `RSBlockDecomposition.per_block_signed_bound` shape.
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

namespace Aristotle.Standalone.RSPerBlockSignedBoundStrict

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

private def blockIntegral (T : ℝ) (k : ℕ) : ℝ :=
  ∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t

private def headIntegral (T : ℝ) : ℝ :=
  ∫ t in Ioc 1 (min T (hardyStart 0)), ErrorTerm t

private def altCenter (A : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)

/-- Local per-block signed approximation clause (first conjunct shape). -/
def LocalPerBlockSigned (A B : ℝ) : Prop :=
  ∀ T : ℝ, T ≥ 2 →
    ∀ k : ℕ, k < hardyN T →
      ∃ s : ℝ, s = (-1 : ℝ) ^ k ∧
        |(∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
            ErrorTerm t) - s * A * Real.sqrt ((k : ℝ) + 1)| ≤ B

/-- Global alternating-sqrt decomposition clause (second conjunct shape). -/
def GlobalAlternatingBound (A B : ℝ) : Prop :=
  ∀ T : ℝ, T ≥ 2 →
    ∃ N : ℕ,
      ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
      |∫ t in Ioc 1 T, ErrorTerm t|
        ≤ A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + B

/-- Minimal missing analytic input for the global clause:
uniform control of the affine residual after choosing `N(T)`. -/
def GlobalResidualControl (A B : ℝ) : Prop :=
  ∀ T : ℝ, T ≥ 2 →
    ∃ N : ℕ,
      ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
      |(∫ t in Ioc 1 T, ErrorTerm t)
          - A * (∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1))| ≤ B

/-- Standalone reproof of the finite breakpoint decomposition
for `∫_1^T ErrorTerm`. -/
theorem errorTerm_block_sum_strict (T : ℝ) (hT : T ≥ 2) :
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
    exact Nat.lt_irrefl _ hlt
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
              simp [h_bpN]
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

private lemma local_signed_centered
    {A B : ℝ} {T : ℝ} {k : ℕ}
    (hlocal : LocalPerBlockSigned A B)
    (hT : T ≥ 2) (hk : k < hardyN T) :
    |blockIntegral T k - altCenter A k| ≤ B := by
  rcases hlocal T hT k hk with ⟨s, hs, hbound⟩
  calc
    |blockIntegral T k - altCenter A k|
        = |blockIntegral T k - s * A * Real.sqrt ((k : ℝ) + 1)| := by
            simp [blockIntegral, altCenter, hs, mul_assoc, mul_comm]
    _ ≤ B := hbound

private lemma residual_sum_abs_le
    {A B T : ℝ}
    (hlocal : LocalPerBlockSigned A B)
    (hT : T ≥ 2) :
    |∑ k ∈ Finset.range (hardyN T), (blockIntegral T k - altCenter A k)|
      ≤ (hardyN T : ℝ) * B := by
  have hterm :
      ∀ k ∈ Finset.range (hardyN T), |blockIntegral T k - altCenter A k| ≤ B := by
    intro k hk
    exact local_signed_centered hlocal hT (Finset.mem_range.mp hk)
  have hsumabs :
      |∑ k ∈ Finset.range (hardyN T), (blockIntegral T k - altCenter A k)|
        ≤ ∑ k ∈ Finset.range (hardyN T), |blockIntegral T k - altCenter A k| := by
    simpa using
      (Finset.abs_sum_le_sum_abs
        (fun k => blockIntegral T k - altCenter A k)
        (Finset.range (hardyN T)))
  have hsumle :
      (∑ k ∈ Finset.range (hardyN T), |blockIntegral T k - altCenter A k|)
        ≤ ∑ _k ∈ Finset.range (hardyN T), B := by
    exact Finset.sum_le_sum hterm
  calc
    |∑ k ∈ Finset.range (hardyN T), (blockIntegral T k - altCenter A k)|
        ≤ ∑ k ∈ Finset.range (hardyN T), |blockIntegral T k - altCenter A k| := hsumabs
    _ ≤ ∑ _k ∈ Finset.range (hardyN T), B := hsumle
    _ = (hardyN T : ℝ) * B := by simp [mul_comm]

private lemma sum_altCenter_eq (A : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, altCenter A k
      = A * ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1) := by
  calc
    ∑ k ∈ Finset.range N, altCenter A k
        = ∑ k ∈ Finset.range N, A * ((-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp [altCenter, mul_assoc, mul_comm]
    _ = A * ∑ k ∈ Finset.range N, ((-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)) := by
            rw [Finset.mul_sum]

private lemma abs_sum_altCenter_eq (A : ℝ) (hA : 0 ≤ A) (N : ℕ) :
    |∑ k ∈ Finset.range N, altCenter A k|
      = A * |∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| := by
  rw [sum_altCenter_eq A N, abs_mul, abs_of_nonneg hA]

/-- Maximal nontrivial consequence of local signed block control alone:
a global alternating-sqrt bound with explicit linear residual term `(N : ℝ) * B`.
-/
theorem global_alternating_with_linear_residual
    {A B : ℝ} (hA : A > 0)
    (hlocal : LocalPerBlockSigned A B) :
    ∀ T : ℝ, T ≥ 2 →
      ∃ N : ℕ,
        (N : ℝ) ≤ T ^ (1 / 2 : ℝ) ∧
        |∫ t in Ioc 1 T, ErrorTerm t|
          ≤ |headIntegral T|
              + A * |∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)|
              + (N : ℝ) * B := by
  intro T hT
  let N : ℕ := hardyN T
  have hN_plus : ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) := by
    simpa [N] using Aristotle.HardyNProperties.hardyN_le_sqrt T hT
  have hN : (N : ℝ) ≤ T ^ (1 / 2 : ℝ) := by linarith
  refine ⟨N, hN, ?_⟩

  let C : ℝ := ∑ k ∈ Finset.range N, altCenter A k
  let R : ℝ := ∑ k ∈ Finset.range N, (blockIntegral T k - altCenter A k)

  have hsum :
      (∑ k ∈ Finset.range N, blockIntegral T k) = C + R := by
    calc
      (∑ k ∈ Finset.range N, blockIntegral T k)
          = ∑ k ∈ Finset.range N, (altCenter A k + (blockIntegral T k - altCenter A k)) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              ring
      _ = (∑ k ∈ Finset.range N, altCenter A k)
            + (∑ k ∈ Finset.range N, (blockIntegral T k - altCenter A k)) := by
              simp
      _ = C + R := by simp [C, R]

  have hdecomp :
      ∫ t in Ioc 1 T, ErrorTerm t = headIntegral T + C + R := by
    calc
      ∫ t in Ioc 1 T, ErrorTerm t
          = headIntegral T + ∑ k ∈ Finset.range N, blockIntegral T k := by
              simpa [headIntegral, blockIntegral, N] using errorTerm_block_sum_strict T hT
      _ = headIntegral T + (C + R) := by rw [hsum]
      _ = headIntegral T + C + R := by ring

  have hR : |R| ≤ (N : ℝ) * B := by
    simpa [R, N] using residual_sum_abs_le (A := A) (B := B) (T := T) hlocal hT

  let S : ℝ := ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)
  have hC : |C| = A * |S| := by
    simpa [C, S] using abs_sum_altCenter_eq A (le_of_lt hA) N

  have htri : |headIntegral T + C + R| ≤ |headIntegral T| + |C| + |R| := by
    simpa [add_assoc] using abs_add_three (headIntegral T) C R

  calc
    |∫ t in Ioc 1 T, ErrorTerm t| = |headIntegral T + C + R| := by rw [hdecomp]
    _ ≤ |headIntegral T| + |C| + |R| := htri
    _ = |headIntegral T| + A * |S| + |R| := by rw [hC]
    _ ≤ |headIntegral T| + A * |S| + (N : ℝ) * B := by
          linarith [hR]
    _ = |headIntegral T|
          + A * |∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)|
          + (N : ℝ) * B := by simp [S]

/-- Residual control implies the exact global alternating bound clause. -/
theorem globalAlternating_of_globalResidual
    {A B : ℝ} (hA : 0 ≤ A)
    (hres : GlobalResidualControl A B) :
    GlobalAlternatingBound A B := by
  intro T hT
  rcases hres T hT with ⟨N, hN, hresN⟩
  refine ⟨N, hN, ?_⟩
  let I : ℝ := ∫ t in Ioc 1 T, ErrorTerm t
  let S : ℝ := ∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)
  have htri : |I| ≤ |I - A * S| + |A * S| := by
    simpa [I, S, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (abs_sub (a := I - A * S) (b := -A * S))
  have hmul : |A * S| = A * |S| := by
    rw [abs_mul, abs_of_nonneg hA]
  have hmain : |I| ≤ B + A * |S| := by
    linarith [htri, hresN, hmul]
  simpa [I, S, add_comm, add_left_comm, add_assoc] using hmain

/-- Isolated minimal missing theorem statement for recovering
`RSBlockDecomposition.per_block_signed_bound` in strict standalone form. -/
def MinimalMissingPerBlockInput : Prop :=
  ∃ A B : ℝ, A > 0 ∧ B ≥ 0 ∧
    LocalPerBlockSigned A B ∧
    GlobalResidualControl A B

/-- Strict reduction theorem: the isolated minimal missing input implies
a full theorem matching the shape of `RSBlockDecomposition.per_block_signed_bound`. -/
theorem per_block_signed_bound_strict_from_minimal_input
    (hmin : MinimalMissingPerBlockInput) :
    ∃ A B : ℝ, A > 0 ∧ B ≥ 0 ∧
      LocalPerBlockSigned A B ∧
      GlobalAlternatingBound A B := by
  rcases hmin with ⟨A, B, hA, hB, hlocal, hres⟩
  refine ⟨A, B, hA, hB, hlocal, ?_⟩
  exact globalAlternating_of_globalResidual (A := A) (B := B) (le_of_lt hA) hres

/-- Same reduction theorem with the global/local clauses expanded exactly
in the original `per_block_signed_bound` syntax. -/
theorem per_block_signed_bound_strict_expanded
    (hmin : MinimalMissingPerBlockInput) :
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
  rcases per_block_signed_bound_strict_from_minimal_input hmin with
    ⟨A, B, hA, hB, hlocal, hglobal⟩
  exact ⟨A, B, hA, hB, hlocal, hglobal⟩

end Aristotle.Standalone.RSPerBlockSignedBoundStrict
