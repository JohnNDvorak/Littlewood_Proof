/-
MainTermFirstMomentBoundHyp from stationary phase decomposition.

This file proves MainTermFirstMomentBoundHyp (Deep Blocker B2) from a single
atomic sorry: the per-mode stationary phase evaluation.

## Mathematical content

Each Hardy cosine integral has a stationary point at t₀ = 2π(n+1)²:
  ∫_{t₀}^T cos(θ(t) - t·log(n+1)) dt = (-1)^n · A · (n+1) + O(1)

where A is the Fresnel constant and the O(1) error is UNIFORM in n and T.

The weighted sum decomposes as:
  Σ_n (n+1)^{-1/2} [(-1)^n · A · (n+1) + r(n,T)]
  = A · Σ (-1)^n √(n+1)  +  Σ (n+1)^{-1/2} · r(n,T)

By alternating_sqrt_sum_bound: |Σ (-1)^n √(n+1)| ≤ √N.
By triangle inequality: |Σ (n+1)^{-1/2} · r| ≤ B · N.
Total: A√N + BN ≤ (A+B)(N+1).

SORRY COUNT: 1 (stationary_phase_per_mode)

Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.HardyZMeasurability
import Littlewood.Aristotle.CosPiSqSign
import Littlewood.Bridge.HardyFirstMomentWiring

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.MainTermFirstMomentFromStationaryPhase

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

/-! ## Atomic sorry: per-mode stationary phase evaluation -/

/-- **Atomic sorry**: Per-mode stationary phase evaluation for Hardy cosine integrals.

Near the stationary point t₀ = 2π(n+1)², the phase φ(t) = θ(t) - t·log(n+1) has
φ'(t₀) ≈ 0 and φ''(t₀) ≈ 1/(4π(n+1)²). The Fresnel integral evaluation gives:

  ∫_{t₀}^T cos(φ(t)) dt = (-1)^n · A · (n+1) + r(n,T)

with |r(n,T)| ≤ B uniformly. The leading sign (-1)^n comes from
cos(πn²) = (-1)^n (CosPiSqSign.lean).

The remainder r(n,T) absorbs:
- The Fresnel integral tail (bounded by Fresnel convergence, FresnelBound.lean)
- The VdC first-derivative tail on [t₀ + c(n+1), T] (O(1), VdcFirstDerivTest.lean)
- The cubic phase correction in the Fresnel zone (O(1))
- The error in θ'(t₀) ≈ log(n+1) (O(1/(n+1)²), ThetaDerivAsymptotic.lean)

REFERENCES: Titchmarsh §7.6, Hardy-Littlewood 1918. -/
theorem stationary_phase_per_mode :
    ∃ (A : ℝ) (B : ℝ), A > 0 ∧ B ≥ 0 ∧
    ∀ (n : ℕ) (T : ℝ), T ≥ 2 → n < hardyN T →
      |(∫ t in Ioc (hardyStart n) T, hardyCos n t)
        - (-1 : ℝ) ^ n * A * ((n : ℝ) + 1)| ≤ B := by
  sorry

/-! ## Wiring: from per-mode decomposition to MainTermFirstMomentBoundHyp -/

/-- Key algebraic identity: (n+1)^{-1/2} · (n+1) = √(n+1). -/
private lemma rpow_neg_half_mul (n : ℕ) :
    ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) * ((n : ℝ) + 1) = Real.sqrt ((n : ℝ) + 1) := by
  have hn1_nn : (0 : ℝ) ≤ (↑n + 1) := by positivity
  have hsqrt_ne : Real.sqrt (↑n + 1) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have h_rpow : ((↑n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) = (Real.sqrt (↑n + 1))⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hn1_nn]
  rw [h_rpow]
  field_simp
  exact (Real.sq_sqrt hn1_nn).symm

/-- (n+1)^{-1/2} ≤ 1 for all n : ℕ. -/
private lemma rpow_neg_half_le_one (n : ℕ) :
    ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by norm_cast; omega) (by norm_num)

/-- Main wiring: the per-mode decomposition implies MainTermFirstMomentBoundHyp.

    Each mode integral: I_n = (-1)^n · A · (n+1) + r_n with |r_n| ≤ B.
    Weighted: w_n · I_n = A · (-1)^n · √(n+1) + w_n · r_n
    Sum: A · Σ(-1)^n√(n+1) + Σ w_n·r_n
    |first| ≤ A·√N  [alternating_sqrt_sum_bound]
    |second| ≤ B·N   [triangle, w_n ≤ 1]
    Total ≤ (A+B)·(N+1). -/
theorem mainTermFirstMomentBound_proved :
    HardyFirstMomentWiring.MainTermFirstMomentBoundHyp := by
  obtain ⟨A, B, hA, hB, hmode⟩ := stationary_phase_per_mode
  apply HardyFirstMomentWiring.mainTermFirstMomentBound_of_alternatingSqrtDecomposition
  refine ⟨A + B + 1, by positivity, ?_⟩
  intro T hT
  set N := hardyN T
  -- Abbreviations for the proof
  set w : ℕ → ℝ := fun n => ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)))
  set I : ℕ → ℝ := fun n => ∫ t in Ioc (hardyStart n) T, hardyCos n t
  set lead : ℕ → ℝ := fun n => (-1 : ℝ) ^ n * A * ((n : ℝ) + 1)
  set r : ℕ → ℝ := fun n => I n - lead n
  -- Step 1: Each w_n * lead_n = A * ((-1)^n * √(n+1))
  have hw_lead : ∀ n, w n * lead n =
      A * ((-1 : ℝ) ^ n * Real.sqrt ((n : ℝ) + 1)) := by
    intro n
    show ((↑n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) * ((-1 : ℝ) ^ n * A * (↑n + 1))
        = A * ((-1 : ℝ) ^ n * Real.sqrt (↑n + 1))
    calc ((↑n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) * ((-1 : ℝ) ^ n * A * (↑n + 1))
        = (-1 : ℝ) ^ n * A * (((↑n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) * (↑n + 1)) := by ring
      _ = (-1 : ℝ) ^ n * A * Real.sqrt (↑n + 1) := by rw [rpow_neg_half_mul]
      _ = A * ((-1 : ℝ) ^ n * Real.sqrt (↑n + 1)) := by ring
  -- Step 2: Sum decomposition
  have hsum_eq :
      ∑ n ∈ Finset.range N, w n * I n
      = A * ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * Real.sqrt ((n : ℝ) + 1)
        + ∑ n ∈ Finset.range N, w n * r n := by
    show ∑ n ∈ Finset.range N, w n * I n
      = A * ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * Real.sqrt ((n : ℝ) + 1)
        + ∑ n ∈ Finset.range N, w n * (I n - lead n)
    simp_rw [show ∀ n, w n * I n = w n * lead n + w n * (I n - lead n) from
      fun n => by ring, Finset.sum_add_distrib]
    congr 1
    simp_rw [hw_lead, Finset.mul_sum]
  -- Step 3: Bound part 1 via alternating_sqrt_sum_bound
  have hpart1 : |A * ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * Real.sqrt ((n : ℝ) + 1)|
      ≤ A * Real.sqrt N := by
    rw [abs_mul, abs_of_pos hA]
    exact mul_le_mul_of_nonneg_left
      (HardyFirstMomentWiring.alternating_sqrt_sum_bound_range N) (le_of_lt hA)
  -- Step 4: Bound part 2 using |r_n| ≤ B and w_n ≤ 1
  have hr_bound : ∀ n, n < N → |r n| ≤ B := fun n hn => hmode n T hT hn
  have hpart2 : |∑ n ∈ Finset.range N, w n * r n| ≤ B * (N : ℝ) := by
    calc |∑ n ∈ Finset.range N, w n * r n|
        ≤ ∑ n ∈ Finset.range N, |w n * r n| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ n ∈ Finset.range N, w n * |r n| := by
          apply Finset.sum_congr rfl; intro n _
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ w n)]
      _ ≤ ∑ n ∈ Finset.range N, 1 * B := by
          apply Finset.sum_le_sum; intro n hn
          exact mul_le_mul (rpow_neg_half_le_one n) (hr_bound n (Finset.mem_range.mp hn))
            (abs_nonneg _) (by linarith [show 0 ≤ w n from by positivity])
      _ = B * N := by simp [mul_comm]
  -- Step 5: √N ≤ N+1
  have hsqrt_le : Real.sqrt (N : ℝ) ≤ (N : ℝ) + 1 := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N), Real.sqrt_nonneg (N : ℝ)]
  -- Step 6: Combine
  calc |∑ n ∈ Finset.range N, w n * I n|
      = |A * ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * Real.sqrt ((n : ℝ) + 1)
          + ∑ n ∈ Finset.range N, w n * r n| := by rw [hsum_eq]
    _ ≤ |A * ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * Real.sqrt ((n : ℝ) + 1)|
        + |∑ n ∈ Finset.range N, w n * r n| := abs_add_le _ _
    _ ≤ A * Real.sqrt N + B * N := add_le_add hpart1 hpart2
    _ ≤ A * ((N : ℝ) + 1) + B * ((N : ℝ) + 1) := by
        nlinarith [le_of_lt hA, hsqrt_le]
    _ = (A + B) * ((N : ℝ) + 1) := by ring
    _ ≤ (A + B + 1) * ((N : ℝ) + 1) := by
        have : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
        nlinarith

end Aristotle.Standalone.MainTermFirstMomentFromStationaryPhase
