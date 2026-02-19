import Mathlib
import Littlewood.Aristotle.RSBlockDecomposition
import Littlewood.Aristotle.CosPiSqSign
import Littlewood.Aristotle.Standalone.RSPerBlockSignedBoundChain
import Littlewood.Bridge.HardyFirstMomentWiring

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RSFirstMomentHalfFromLocalBlocks

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.Standalone.RSPerBlockSignedBoundChain

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

private lemma alternating_sqrt_sum_range_bound (N : ℕ) :
    |∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| ≤ Real.sqrt (N : ℝ) := by
  cases' N with n
  · simp
  · simpa [Nat.cast_add, Nat.cast_one] using CosPiSqSign.alternating_sqrt_sum_bound n

private lemma head_integral_abs_le_fixed (T : ℝ) :
    |∫ t in Ioc 1 (min T (hardyStart 0)), ErrorTerm t|
      ≤ ∫ t in Ioc 1 (hardyStart 0), ‖ErrorTerm t‖ := by
  have hsubset : Ioc (1 : ℝ) (min T (hardyStart 0)) ⊆ Ioc (1 : ℝ) (hardyStart 0) := by
    intro t ht
    exact ⟨ht.1, le_trans ht.2 (min_le_right T (hardyStart 0))⟩
  have h_int_full : IntegrableOn (fun t : ℝ => ‖ErrorTerm t‖) (Ioc (1 : ℝ) (hardyStart 0)) := by
    exact (errorTerm_integrable (hardyStart 0)).norm
  have h_abs_le_norm :
      |∫ t in Ioc (1 : ℝ) (min T (hardyStart 0)), ErrorTerm t|
        ≤ ∫ t in Ioc (1 : ℝ) (min T (hardyStart 0)), ‖ErrorTerm t‖ := by
    simpa [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm
        (f := fun t : ℝ => ErrorTerm t)
        (μ := volume.restrict (Ioc (1 : ℝ) (min T (hardyStart 0)))))
  have h_norm_le_fixed :
      ∫ t in Ioc (1 : ℝ) (min T (hardyStart 0)), ‖ErrorTerm t‖
        ≤ ∫ t in Ioc (1 : ℝ) (hardyStart 0), ‖ErrorTerm t‖ :=
    setIntegral_mono_set h_int_full
      (ae_of_all _ (fun _ => norm_nonneg _))
      (Eventually.of_forall (fun t ht => hsubset ht))
  exact le_trans h_abs_le_norm h_norm_le_fixed

private lemma local_residual_sum_abs_le
    {A B T : ℝ} (hlocal : LocalPerBlockSignedInput A B)
    (hT : T ≥ 2) :
    |∑ k ∈ Finset.range (hardyN T),
      ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t)
        - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))|
      ≤ (hardyN T : ℝ) * B := by
  have hterm :
      ∀ k ∈ Finset.range (hardyN T),
        |(∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t)
          - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))| ≤ B := by
    intro k hk
    rcases hlocal T hT k (Finset.mem_range.mp hk) with ⟨s, hs, hbound⟩
    simpa [hs, mul_assoc, mul_comm, mul_left_comm] using hbound
  have hsumabs :
      |∑ k ∈ Finset.range (hardyN T),
          ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t)
            - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))|
        ≤
      ∑ k ∈ Finset.range (hardyN T),
        |(∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t)
          - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))| := by
    simpa using
      (Finset.abs_sum_le_sum_abs
        (fun k : ℕ =>
          (∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t)
            - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))
        (Finset.range (hardyN T)))
  have hsumle :
      (∑ k ∈ Finset.range (hardyN T),
        |(∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t)
          - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))|)
        ≤ ∑ _k ∈ Finset.range (hardyN T), B := by
    exact Finset.sum_le_sum hterm
  calc
    |∑ k ∈ Finset.range (hardyN T),
        ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t)
          - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))|
      ≤
    ∑ k ∈ Finset.range (hardyN T),
      |(∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t)
        - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))| := hsumabs
    _ ≤ ∑ _k ∈ Finset.range (hardyN T), B := hsumle
    _ = (hardyN T : ℝ) * B := by simp [mul_comm]

/-- First-moment upper-bound wiring from local signed block control alone.

This avoids a global constant residual hypothesis by keeping the natural linear
`N * B` residual from blockwise summation; since `N ≤ T^(1/2)`, this still yields
`O(T^(1/2 + ε))` for every `ε > 0`. -/
theorem errorTermFirstMomentBoundHyp_of_local_blocks
    {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hlocal : LocalPerBlockSignedInput A B) :
    HardyFirstMomentWiring.ErrorTermFirstMomentBoundHyp := by
  refine ⟨?_⟩
  intro ε hε
  let H : ℝ := ∫ t in Ioc (1 : ℝ) (hardyStart 0), ‖ErrorTerm t‖
  let C : ℝ := H + A + B
  have hH_nonneg : 0 ≤ H := by
    exact integral_nonneg (fun _ => norm_nonneg _)
  have hC_pos : 0 < C := by
    dsimp [C]
    linarith
  refine ⟨C, hC_pos, ?_⟩
  intro T hT
  let N : ℕ := hardyN T
  let I : ℝ := ∫ t in Ioc 1 T, ErrorTerm t
  let Head : ℝ := ∫ t in Ioc 1 (min T (hardyStart 0)), ErrorTerm t
  let S : ℝ := ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)
  let Rsum : ℝ :=
    ∑ k ∈ Finset.range N,
      ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t)
        - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))

  have hdecomp :
      I = Head + (∑ k ∈ Finset.range N,
        ∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t) := by
    simpa [I, Head, N] using Aristotle.RSBlockDecomposition.errorTerm_block_sum T hT

  have hsum_blocks :
      (∑ k ∈ Finset.range N,
        ∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t)
        = Rsum + A * S := by
    calc
      (∑ k ∈ Finset.range N,
          ∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t)
          = ∑ k ∈ Finset.range N,
              (((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t)
                - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))
                + ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            ring
      _ = (∑ k ∈ Finset.range N,
            ((∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t)
              - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))))
          + (∑ k ∈ Finset.range N,
              ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)) ) := by
            simp
      _ = Rsum + (∑ k ∈ Finset.range N,
            ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1))) := by
            simp [Rsum]
      _ = Rsum + A * S := by
            simpa [S] using congrArg (fun x : ℝ => Rsum + x) (sum_alt_center A N)

  have hI_eq : I = Head + Rsum + A * S := by
    calc
      I = Head + (∑ k ∈ Finset.range N,
          ∫ t in Ioc (min T (hardyStart k)) (min T (hardyStart (k + 1))), ErrorTerm t) := hdecomp
      _ = Head + (Rsum + A * S) := by rw [hsum_blocks]
      _ = Head + Rsum + A * S := by ring

  have hRsum : |Rsum| ≤ (N : ℝ) * B := by
    simpa [Rsum, N] using local_residual_sum_abs_le (A := A) (B := B) (T := T) hlocal hT

  have hHead : |Head| ≤ H := by
    simpa [Head, H] using head_integral_abs_le_fixed T

  have hS : |S| ≤ Real.sqrt (N : ℝ) := by
    simpa [S] using alternating_sqrt_sum_range_bound N

  have hN_plus : ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) := by
    simpa [N] using Aristotle.HardyNProperties.hardyN_le_sqrt T hT

  have hN_nonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hsqrtN_le_Nplus : Real.sqrt (N : ℝ) ≤ (N : ℝ) + 1 := by
    nlinarith [Real.sq_sqrt hN_nonneg]
  have hsqrtN_le_Thalf : Real.sqrt (N : ℝ) ≤ T ^ (1 / 2 : ℝ) := by
    exact le_trans hsqrtN_le_Nplus hN_plus
  have hN_le_Thalf : (N : ℝ) ≤ T ^ (1 / 2 : ℝ) := by linarith

  have htri : |I| ≤ |Head| + |Rsum| + A * |S| := by
    calc
      |I| = |Head + Rsum + A * S| := by rw [hI_eq]
      _ ≤ |Head| + |Rsum| + |A * S| := by
            simpa [add_assoc] using abs_add_three Head Rsum (A * S)
      _ = |Head| + |Rsum| + A * |S| := by
            rw [abs_mul, abs_of_nonneg (le_of_lt hA)]

  have hpow_mono : T ^ (1 / 2 : ℝ) ≤ T ^ (1 / 2 + ε) := by
    have hT1 : (1 : ℝ) ≤ T := by linarith
    exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)

  have hpow_ge_one : (1 : ℝ) ≤ T ^ (1 / 2 + ε) := by
    have hT1 : (1 : ℝ) ≤ T := by linarith
    exact Real.one_le_rpow hT1 (by linarith)

  calc
    |∫ t in Ioc 1 T, ErrorTerm t| = |I| := by simp [I]
    _ ≤ |Head| + |Rsum| + A * |S| := htri
    _ ≤ H + (N : ℝ) * B + A * Real.sqrt (N : ℝ) := by
          gcongr
    _ ≤ H + (T ^ (1 / 2 : ℝ)) * B + A * (T ^ (1 / 2 : ℝ)) := by
          gcongr
    _ ≤ H + (T ^ (1 / 2 + ε)) * B + A * (T ^ (1 / 2 + ε)) := by
          gcongr
    _ = H + (A + B) * T ^ (1 / 2 + ε) := by ring
    _ ≤ H * T ^ (1 / 2 + ε) + (A + B) * T ^ (1 / 2 + ε) := by
          have hH_mul : H ≤ H * T ^ (1 / 2 + ε) := by
            nlinarith [hH_nonneg, hpow_ge_one]
          linarith
    _ = T ^ (1 / 2 + ε) * (H + A + B) := by ring
    _ = (H + A + B) * T ^ (1 / 2 + ε) := by ring
    _ = C * T ^ (1 / 2 + ε) := by simp [C]

/-- Combined Hardy first-moment wiring from:
1) any main-term first-moment bound hypothesis, and
2) local per-block signed RS control. -/
theorem hardyFirstMomentUpperHyp_of_mainTerm_and_local_blocks
    [HardyFirstMomentWiring.MainTermFirstMomentBoundHyp]
    {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hlocal : LocalPerBlockSignedInput A B) :
    HardyFirstMomentUpperHyp := by
  letI : HardyFirstMomentWiring.ErrorTermFirstMomentBoundHyp :=
    errorTermFirstMomentBoundHyp_of_local_blocks (A := A) (B := B) hA hB hlocal
  exact HardyFirstMomentWiring.hardyFirstMomentUpper_from_two_bounds

end Aristotle.Standalone.RSFirstMomentHalfFromLocalBlocks
