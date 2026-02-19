import Mathlib
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.RSBlockDecomposition

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RSPerBlockSignedBoundConstructive

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

private lemma hardyStart_zero_eq_two_pi :
    hardyStart 0 = 2 * Real.pi := by
  rw [Aristotle.HardyNProperties.hardyStart_formula]
  norm_num

private lemma hardyN_pos_of_ge_two_pi {T : ℝ} (hT : T ≥ 2 * Real.pi) :
    0 < hardyN T := by
  have hT_nonneg : 0 ≤ T := by
    exact le_trans (by positivity : (0 : ℝ) ≤ 2 * Real.pi) hT
  have hstart0 : hardyStart 0 ≤ T := by
    rw [Aristotle.HardyNProperties.hardyStart_formula]
    simpa using hT
  exact (hardyN_lt_iff 0 T hT_nonneg).2 hstart0

private lemma sum_alt_center (A : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))
      = A * (∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)) := by
  calc
    (∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))
        = ∑ k ∈ Finset.range N, A * (((-1 : ℝ) ^ k) * Real.sqrt ((k : ℝ) + 1)) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            ring
    _ = A * (∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)) := by
          rw [Finset.mul_sum]

/-- Constructive residual-to-global reduction on the long range `T ≥ 2π`.

Assumptions:
1. the initial head interval contribution is uniformly bounded by `H`;
2. the centered block residual sum is uniformly bounded by `R`.

Conclusion:
`∫_1^T ErrorTerm` is approximated by an alternating `sqrt` sum with a uniform
residual `H + R`, in the same finite-sum shape used by
`RSBlockDecomposition.per_block_signed_bound` (up to the threshold `2π`). -/
theorem centered_blocks_to_global_residual
    {A H R : ℝ}
    (hhead :
      ∀ T : ℝ, T ≥ 2 * Real.pi →
        |∫ t in Ioc 1 (min T (hardyStart 0)), ErrorTerm t| ≤ H)
    (hcenter :
      ∀ T : ℝ, T ≥ 2 * Real.pi →
        |∑ k ∈ Finset.range (hardyN T),
          ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
              ErrorTerm t)
            - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))| ≤ R) :
    ∀ T : ℝ, T ≥ 2 * Real.pi →
      ∃ N : ℕ,
        ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
        |(∫ t in Ioc 1 T, ErrorTerm t)
            - A * (∑ k ∈ Finset.range (N + 1),
                (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1))| ≤ H + R := by
  intro T hT
  have hT_two : T ≥ 2 := by
    have htwo_pi : (2 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    exact le_trans htwo_pi hT
  have hN_pos : 0 < hardyN T := hardyN_pos_of_ge_two_pi hT
  let N : ℕ := Nat.pred (hardyN T)
  have hN_succ : N + 1 = hardyN T := by
    dsimp [N]
    simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hN_pos
  have hN_le_sqrt_plus :
      ((hardyN T : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) :=
    Aristotle.HardyNProperties.hardyN_le_sqrt T hT_two
  have hN_le_sqrt : (hardyN T : ℝ) ≤ T ^ (1 / 2 : ℝ) := by
    linarith
  have hN_bound : ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) := by
    have hcast : ((N : ℝ) + 1) = (hardyN T : ℝ) := by
      exact_mod_cast hN_succ
    linarith

  let I : ℝ := ∫ t in Ioc 1 T, ErrorTerm t
  let H0 : ℝ := ∫ t in Ioc 1 (min T (hardyStart 0)), ErrorTerm t
  let C : ℝ :=
    ∑ k ∈ Finset.range (hardyN T),
      ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
          ErrorTerm t)
        - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))
  let S : ℝ :=
    ∑ k ∈ Finset.range (hardyN T), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)

  have hdecomp :
      I = H0
          + ∑ k ∈ Finset.range (hardyN T),
              (∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
                ErrorTerm t) := by
    simpa [I, H0] using
      Aristotle.RSBlockDecomposition.errorTerm_block_sum T hT_two

  have hsum_blocks :
      (∑ k ∈ Finset.range (hardyN T),
          (∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
            ErrorTerm t))
        = C + A * S := by
    calc
      (∑ k ∈ Finset.range (hardyN T),
          (∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
            ErrorTerm t))
          =
          ∑ k ∈ Finset.range (hardyN T),
            (((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
                ErrorTerm t)
              - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))
              + ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            ring
      _ =
          (∑ k ∈ Finset.range (hardyN T),
            ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
                ErrorTerm t)
              - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))))
            +
          (∑ k ∈ Finset.range (hardyN T),
            ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))) := by
            simp
      _ = C + (∑ k ∈ Finset.range (hardyN T),
          ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))) := by
            simp [C]
      _ = C + A * S := by
            simpa [S] using congrArg (fun x : ℝ => C + x) (sum_alt_center A (hardyN T))

  have hresid_eq : I - A * S = H0 + C := by
    calc
      I - A * S
          = (H0
              + ∑ k ∈ Finset.range (hardyN T),
                  (∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
                    ErrorTerm t))
              - A * S := by rw [hdecomp]
      _ = H0
            + ((∑ k ∈ Finset.range (hardyN T),
                  (∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
                    ErrorTerm t))
                - A * S) := by ring
      _ = H0 + ((C + A * S) - A * S) := by rw [hsum_blocks]
      _ = H0 + C := by ring

  have hhead_T : |H0| ≤ H := by
    simpa [H0] using hhead T hT
  have hcenter_T : |C| ≤ R := by
    simpa [C] using hcenter T hT
  have hresid_abs : |I - A * S| ≤ H + R := by
    calc
      |I - A * S| = |H0 + C| := by rw [hresid_eq]
      _ ≤ |H0| + |C| := by
            simpa [sub_eq_add_neg] using (abs_sub H0 (-C))
      _ ≤ H + R := by linarith

  refine ⟨N, hN_bound, ?_⟩
  simpa [I, S, hN_succ] using hresid_abs

/-- Long-range global alternating bound (`T ≥ 2π`) derived from the residual form. -/
theorem centered_blocks_to_global_alternating
    {A H R : ℝ} (hA : 0 ≤ A)
    (hhead :
      ∀ T : ℝ, T ≥ 2 * Real.pi →
        |∫ t in Ioc 1 (min T (hardyStart 0)), ErrorTerm t| ≤ H)
    (hcenter :
      ∀ T : ℝ, T ≥ 2 * Real.pi →
        |∑ k ∈ Finset.range (hardyN T),
          ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
              ErrorTerm t)
            - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))| ≤ R) :
    ∀ T : ℝ, T ≥ 2 * Real.pi →
      ∃ N : ℕ,
        ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
        |∫ t in Ioc 1 T, ErrorTerm t|
          ≤ A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)|
              + (H + R) := by
  intro T hT
  rcases centered_blocks_to_global_residual (A := A) (H := H) (R := R) hhead hcenter T hT with
    ⟨N, hN, hres⟩
  refine ⟨N, hN, ?_⟩
  let I : ℝ := ∫ t in Ioc 1 T, ErrorTerm t
  let S : ℝ := ∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)
  have htri : |I| ≤ |I - A * S| + |A * S| := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (abs_sub (I - A * S) (-A * S))
  have hmul : |A * S| = A * |S| := by
    rw [abs_mul, abs_of_nonneg hA]
  have hres' : |I - A * S| ≤ H + R := by
    simpa [I, S] using hres
  have hmain : |I| ≤ A * |S| + (H + R) := by
    linarith [htri, hres', hmul]
  simpa [I, S, add_assoc, add_left_comm, add_comm] using hmain

/-- Head-free residual form on the long range `T ≥ 2π`.

This removes the separate `hhead` input from `centered_blocks_to_global_residual`:
for `T ≥ 2π`, `min T (hardyStart 0) = hardyStart 0 = 2π`, so the head contribution
is a fixed constant. -/
theorem centered_blocks_to_global_residual_of_centered_blocks
    {A R : ℝ}
    (hcenter :
      ∀ T : ℝ, T ≥ 2 * Real.pi →
        |∑ k ∈ Finset.range (hardyN T),
          ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
              ErrorTerm t)
            - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))| ≤ R) :
    ∀ T : ℝ, T ≥ 2 * Real.pi →
      ∃ N : ℕ,
        ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
        |(∫ t in Ioc 1 T, ErrorTerm t)
            - A * (∑ k ∈ Finset.range (N + 1),
                (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1))|
          ≤ |∫ t in Ioc 1 (hardyStart 0), ErrorTerm t| + R := by
  intro T hT
  have hhead :
      |∫ t in Ioc 1 (min T (hardyStart 0)), ErrorTerm t|
        ≤ |∫ t in Ioc 1 (hardyStart 0), ErrorTerm t| := by
    have hmin : min T (hardyStart 0) = hardyStart 0 := by
      apply min_eq_right
      rw [hardyStart_zero_eq_two_pi]
      exact hT
    simpa [hmin]
  rcases centered_blocks_to_global_residual
      (A := A)
      (H := |∫ t in Ioc 1 (hardyStart 0), ErrorTerm t|)
      (R := R)
      (hhead := fun _T hT' => by
        have hmin' : min _T (hardyStart 0) = hardyStart 0 := by
          apply min_eq_right
          rw [hardyStart_zero_eq_two_pi]
          exact hT'
        simpa [hmin'] using
          (le_rfl :
            |∫ t in Ioc 1 (hardyStart 0), ErrorTerm t|
              ≤ |∫ t in Ioc 1 (hardyStart 0), ErrorTerm t|))
      (hcenter := hcenter)
      T hT with ⟨N, hN, hres⟩
  refine ⟨N, hN, ?_⟩
  simpa [add_comm, add_left_comm, add_assoc] using hres

/-- Head-free alternating form on the long range `T ≥ 2π`.

This is the `A*|sum| + B` shape with
`B = |∫_{1}^{hardyStart 0} ErrorTerm| + R`, assuming only centered block
control. -/
theorem centered_blocks_to_global_alternating_of_centered_blocks
    {A R : ℝ} (hA : 0 ≤ A)
    (hcenter :
      ∀ T : ℝ, T ≥ 2 * Real.pi →
        |∑ k ∈ Finset.range (hardyN T),
          ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))),
              ErrorTerm t)
            - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))| ≤ R) :
    ∀ T : ℝ, T ≥ 2 * Real.pi →
      ∃ N : ℕ,
        ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
        |∫ t in Ioc 1 T, ErrorTerm t|
          ≤ A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)|
              + (|∫ t in Ioc 1 (hardyStart 0), ErrorTerm t| + R) := by
  intro T hT
  rcases centered_blocks_to_global_residual_of_centered_blocks
      (A := A) (R := R) hcenter T hT with ⟨N, hN, hres⟩
  refine ⟨N, hN, ?_⟩
  let I : ℝ := ∫ t in Ioc 1 T, ErrorTerm t
  let S : ℝ := ∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)
  have htri : |I| ≤ |I - A * S| + |A * S| := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (abs_sub (I - A * S) (-A * S))
  have hmul : |A * S| = A * |S| := by
    rw [abs_mul, abs_of_nonneg hA]
  have hres' :
      |I - A * S| ≤ |∫ t in Ioc 1 (hardyStart 0), ErrorTerm t| + R := by
    simpa [I, S] using hres
  have hmain :
      |I| ≤ A * |S| + (|∫ t in Ioc 1 (hardyStart 0), ErrorTerm t| + R) := by
    linarith [htri, hres', hmul]
  simpa [I, S, add_assoc, add_left_comm, add_comm] using hmain

end Aristotle.Standalone.RSPerBlockSignedBoundConstructive
