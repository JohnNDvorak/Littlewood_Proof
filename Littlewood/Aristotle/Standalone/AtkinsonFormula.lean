/-
Atkinson formula infrastructure for the MainTerm first moment bound.

Provides `mainTerm_first_moment_sqrt`:
  ∃ C_M > 0, ∀ T ≥ 2, |∫₁ᵀ MainTerm(t) dt| ≤ C_M · T^{1/2}

The proof reduces to `atkinson_integral_le_N`: the Atkinson per-mode
IBP + signed Fresnel sum analysis shows |∫ MainTerm| ≤ C · (N+1),
where N = hardyN(T) ≤ √T.

CURRENT EXPLICIT HYPOTHESIS SURFACES:
  `AtkinsonShiftedInversePhaseCorePrefixBoundHyp`
  `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`

  The weighted cosine integral sum bound:
  |Σ_{n<N} (n+1)^{-1/2} · ∫ cos(θ(t) - t·log(n+1))| ≤ C · (N+1)

  PROOF STATUS (Agent analysis 2026-03-17):
  Constructive helpers now isolate the diagonal algebra/cancellation surface:
  - `atkinson_alternating_shifted_sqrt_sum_bound_range`
  - `atkinsonCompleteModeTarget_sum_bound_range`
  - `hardyCos_integral_abs_le_length`
  The remaining unresolved pieces are the fixed-shift resonant row endpoint
  sums, the corresponding correction sum, and the genuine post-first-block
  prefix-tail estimate.

  The proof splits into DIAGONAL (resonant block) + OFF-DIAGONAL (tail).

  DIAGONAL — INFRASTRUCTURE COMPLETE:
  - `hardyCos_firstBlock_anchor_main_term_eventually` (StationaryPhaseMainMode):
    w_n · J_n = completeModeTarget(n) + O(1) for the complete first block.
  - `completeModeTarget_sum_bound_range` (StationaryPhaseDecomposition):
    |Σ completeModeTarget| = O(√N) via Abel alternating cancellation.
  - Total diagonal: O(N).

  OFF-DIAGONAL TAILS — GAP:
  - VdC first derivative gives |tail of mode n| = O(n+1), so weighted
    tail is O(√(n+1)), summing to O(N^{3/2}). This is INSUFFICIENT.
  - The TRUE per-mode tail is O(√(n+1)) (not O(n+1)), giving O(1)
    after weighting and O(N) sum. This requires Fresnel evaluation
    precision (stationary phase remainder estimate R_n = O(√(n+1))).
  - NEEDED: Quantitative θ(t) expansion to cubic order near the
    stationary point t₀ = 2π(n+1)², showing the Fresnel tail
    contribution is bounded uniformly after weighting.

  NOTE: `HardyCosIntegralSqrtModeBoundHyp` (|I_n| ≤ B·√(n+1))
  is FALSE — the Fresnel main term gives I_n = Θ(n+1). The O(N) result
  requires signed cancellation on the main terms, NOT absolute bounding.

Reference: Atkinson 1949, Acta Math. 81; Titchmarsh 1951 §4.15.
-/

import Mathlib
import Littlewood.Aristotle.ComplexVdC
import Littlewood.Aristotle.AbelSummation
import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.HardyCosExpOmega
import Littlewood.Aristotle.HardyCosSmooth
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyZMeasurability
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.IntervalPartition
import Littlewood.Aristotle.OffResonanceSmoothVdC
import Littlewood.Aristotle.RSBlockParam
import Littlewood.Aristotle.StationaryPhaseMainMode
import Littlewood.Aristotle.ThetaDerivAsymptotic
import Littlewood.Aristotle.ThetaDerivMonotone
import Littlewood.Aristotle.CosPiSqSign
import Littlewood.Bridge.HardyFirstMomentWiring

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real Filter Topology
open HardyEstimatesPartial
open Aristotle.HardyNProperties
open Aristotle.HardyCosExpOmega
open Aristotle.OffResonanceSmoothVdC
open Aristotle.RSBlockParam

namespace Aristotle.Standalone.AtkinsonFormula

/-! ## Section 1: hardyN bound -/

/-- hardyN(T) + 1 ≤ 2√T for T ≥ 1. -/
private theorem hardyN_add_one_le (T : ℝ) (hT : T ≥ 1) :
    (↑(hardyN T) : ℝ) + 1 ≤ 2 * Real.sqrt T := by
  have hN : (↑(hardyN T) : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) :=
    Nat.floor_le (Real.sqrt_nonneg _)
  have h1 : Real.sqrt (T / (2 * Real.pi)) ≤ Real.sqrt T :=
    Real.sqrt_le_sqrt (div_le_self (by linarith) (by linarith [Real.pi_gt_three]))
  have h2 : (1 : ℝ) ≤ Real.sqrt T := by
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt T := Real.sqrt_le_sqrt (by linarith)
  linarith

/-! ## Section 2: Abel bound for alternating series with increasing terms -/

/-- For an increasing nonneg sequence, |Σ_{n<N} (-1)^n a_n| ≤ a_{N-1}. -/
theorem abel_alternating_bound (a : ℕ → ℝ) (ha_nn : ∀ n, 0 ≤ a n)
    (ha_mono : Monotone a) (N : ℕ) (hN : 0 < N) :
    |∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * a n| ≤ a (N - 1) := by
  set S := fun N => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * a n with hS_def
  suffices h_refined : ∀ N : ℕ, 0 < N →
    (Even N → S N ≤ 0 ∧ -(a (N - 1)) ≤ S N) ∧
    (Odd N → 0 ≤ S N ∧ S N ≤ a (N - 1)) by
    obtain ⟨h_even, h_odd⟩ := h_refined N hN
    rcases Nat.even_or_odd N with hpar | hpar
    · obtain ⟨h1, h2⟩ := h_even hpar
      rw [abs_le]; exact ⟨h2, le_trans h1 (ha_nn _)⟩
    · obtain ⟨h1, h2⟩ := h_odd hpar
      rw [abs_le]; exact ⟨le_trans (neg_nonpos_of_nonneg (ha_nn _)) h1, h2⟩
  intro M hM
  induction M with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk; constructor
      · intro h; exact absurd h (by decide)
      · intro _; simp [hS_def, ha_nn 0]
    · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
      obtain ⟨ih_even, ih_odd⟩ := ih hk_pos
      simp only [hS_def] at ih_even ih_odd ⊢
      rw [Finset.sum_range_succ]
      constructor
      · intro hpar
        have hk_odd : Odd k := by rw [Nat.odd_iff]; rw [Nat.even_iff] at hpar; omega
        obtain ⟨hSk_nn, hSk_upper⟩ := ih_odd hk_odd
        have hpow : (-1 : ℝ) ^ k * a k = -(a k) := by rw [Odd.neg_one_pow hk_odd]; ring
        rw [hpow]
        show S k + -(a k) ≤ 0 ∧ -(a ((k + 1) - 1)) ≤ S k + -(a k)
        simp only [Nat.add_sub_cancel]
        have hmk : a (k - 1) ≤ a k := ha_mono (Nat.sub_le k 1)
        constructor <;> linarith
      · intro hpar
        have hk_even : Even k := by rw [Nat.even_iff]; rw [Nat.odd_iff] at hpar; omega
        obtain ⟨hSk_upper, hSk_lower⟩ := ih_even hk_even
        have hpow : (-1 : ℝ) ^ k * a k = a k := by rw [Even.neg_one_pow hk_even]; ring
        rw [hpow]
        show 0 ≤ S k + a k ∧ S k + a k ≤ a ((k + 1) - 1)
        simp only [Nat.add_sub_cancel]
        have hmk : a (k - 1) ≤ a k := ha_mono (Nat.sub_le k 1)
        constructor <;> linarith

private noncomputable def atkinsonModeWeight (n : ℕ) : ℝ :=
  (n + 1 : ℝ) ^ (-(1 / 2 : ℝ))

private noncomputable def atkinsonCompleteModeSlope : ℝ :=
  (Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor *
      Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope).re

private noncomputable def atkinsonCompleteModeOffset : ℝ :=
  (Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor *
      Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset).re

private noncomputable def atkinsonCompleteModeTarget (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) *
    (atkinsonCompleteModeSlope * Real.sqrt (n + 1)
      + atkinsonCompleteModeOffset * atkinsonModeWeight n)

private lemma atkinsonModeWeight_nonneg (n : ℕ) :
    0 ≤ atkinsonModeWeight n := by
  simpa [atkinsonModeWeight] using
    (show 0 ≤ (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) by positivity)

private lemma atkinsonModeWeight_le_one (n : ℕ) :
    atkinsonModeWeight n ≤ 1 := by
  simpa [atkinsonModeWeight] using
    (Real.rpow_le_one_of_one_le_of_nonpos
      (show (1 : ℝ) ≤ (n + 1 : ℝ) by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      (by norm_num : (-(1 / 2 : ℝ)) ≤ 0))

private lemma atkinsonModeWeight_mul_succ_eq_sqrt (n : ℕ) :
    atkinsonModeWeight n * ((n + 1 : ℝ)) = Real.sqrt (n + 1) := by
  have hpos : 0 < (n + 1 : ℝ) := by positivity
  calc
    atkinsonModeWeight n * ((n + 1 : ℝ))
        = (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * (n + 1 : ℝ) ^ (1 : ℝ) := by
            rw [atkinsonModeWeight, Real.rpow_one]
    _ = (n + 1 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hpos]
          norm_num
    _ = Real.sqrt (n + 1) := by rw [Real.sqrt_eq_rpow]

private lemma atkinsonModeWeight_pos (n : ℕ) : 0 < atkinsonModeWeight n := by
  unfold atkinsonModeWeight
  positivity

private lemma atkinsonModeWeight_ne_zero (n : ℕ) : atkinsonModeWeight n ≠ 0 :=
  ne_of_gt (atkinsonModeWeight_pos n)

private lemma atkinsonCompleteModeUnweighted_eq (n : ℕ) :
    ((((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
        Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
      (((((n : ℝ) + 1 : ℝ) : ℂ) *
          Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope) +
        Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset)).re)
      =
    (-1 : ℝ) ^ (n + 1) *
      (atkinsonCompleteModeSlope * ((n : ℝ) + 1) + atkinsonCompleteModeOffset) := by
  set s : ℝ := (-1 : ℝ) ^ (n + 1)
  let A : ℂ :=
    Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor *
      (((((n : ℝ) + 1 : ℝ) : ℂ) *
            Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope) +
        Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset)
  have hsign :
      (((s : ℂ) * A).re) = s * A.re := by
    change ((s : ℂ).re * A.re - (s : ℂ).im * A.im = s * A.re)
    simp
  have hlin :
      A.re
        =
      atkinsonCompleteModeSlope * ((n : ℝ) + 1) + atkinsonCompleteModeOffset := by
    unfold A atkinsonCompleteModeSlope atkinsonCompleteModeOffset
    simp [Complex.mul_re, Complex.add_re, mul_add, mul_comm, mul_left_comm]
    ring
  calc
    ((((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
        Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
      (((((n : ℝ) + 1 : ℝ) : ℂ) *
          Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope) +
        Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset)).re)
        =
      (((s : ℂ) * A).re) := by
        simp [A, s, mul_assoc]
    _ = s * A.re := hsign
    _ = s * (atkinsonCompleteModeSlope * ((n : ℝ) + 1) + atkinsonCompleteModeOffset) := by
          rw [hlin]
    _ = (-1 : ℝ) ^ (n + 1) *
        (atkinsonCompleteModeSlope * ((n : ℝ) + 1) + atkinsonCompleteModeOffset) := by
          simp [s]

private lemma atkinsonCompleteModeTarget_eq (n : ℕ) :
    atkinsonModeWeight n *
        ((((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
            Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
          (((((n : ℝ) + 1 : ℝ) : ℂ) *
              Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope) +
            Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset)).re)
      = atkinsonCompleteModeTarget n := by
  rw [atkinsonCompleteModeUnweighted_eq]
  unfold atkinsonCompleteModeTarget
  rw [show atkinsonModeWeight n *
      ((-1 : ℝ) ^ (n + 1) *
        (atkinsonCompleteModeSlope * ((n : ℝ) + 1) + atkinsonCompleteModeOffset))
      =
    (-1 : ℝ) ^ (n + 1) *
      (atkinsonModeWeight n *
        (atkinsonCompleteModeSlope * ((n : ℝ) + 1) + atkinsonCompleteModeOffset)) by
      ring]
  rw [show atkinsonModeWeight n *
      (atkinsonCompleteModeSlope * ((n : ℝ) + 1) + atkinsonCompleteModeOffset)
      =
    atkinsonCompleteModeSlope * (atkinsonModeWeight n * ((n : ℝ) + 1))
      + atkinsonCompleteModeOffset * atkinsonModeWeight n by
      ring]
  rw [atkinsonModeWeight_mul_succ_eq_sqrt]

private theorem atkinson_weighted_complete_block_resonant_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      |atkinsonModeWeight n *
          (∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t)
          - atkinsonCompleteModeTarget n| ≤ C := by
  obtain ⟨C, hC, N0, hmain⟩ :=
    Aristotle.StationaryPhaseMainMode.hardyCos_firstBlock_anchor_main_term_eventually
  refine ⟨C, hC, N0, ?_⟩
  intro n hn
  have hmain' :
      |(∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t)
          - ((((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
                Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
              (((((n : ℝ) + 1 : ℝ) : ℂ) *
                    Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope) +
                Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset)).re)| ≤ C := by
    simpa using hmain n hn
  have hw_nonneg : 0 ≤ atkinsonModeWeight n := atkinsonModeWeight_nonneg n
  have hfactor :
      atkinsonModeWeight n *
          (∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t)
        - atkinsonCompleteModeTarget n
        =
      atkinsonModeWeight n *
        ((∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t)
          - ((((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
                Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
              (((((n : ℝ) + 1 : ℝ) : ℂ) *
                    Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope) +
                Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset)).re)) := by
    rw [← atkinsonCompleteModeTarget_eq n]
    ring
  calc
    |atkinsonModeWeight n *
        (∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t)
        - atkinsonCompleteModeTarget n|
        =
      |atkinsonModeWeight n *
          ((∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t)
            - ((((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
                  Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
                (((((n : ℝ) + 1 : ℝ) : ℂ) *
                      Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope) +
                  Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset)).re))| := by
            rw [hfactor]
    _ = atkinsonModeWeight n *
          |(∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t)
            - ((((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
                  Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
                (((((n : ℝ) + 1 : ℝ) : ℂ) *
                      Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope) +
                  Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset)).re)| := by
          rw [abs_mul, abs_of_nonneg hw_nonneg]
    _ ≤ atkinsonModeWeight n * C := by
          gcongr
    _ ≤ 1 * C := by
          gcongr
          exact atkinsonModeWeight_le_one n
    _ = C := by ring

private lemma atkinson_alternating_shifted_sqrt_sum_bound_range (N : ℕ) :
    |∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1)|
      ≤ Real.sqrt N := by
  have hsign :
      (∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1))
        = -(∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * Real.sqrt ((n : ℝ) + 1)) := by
          calc
            (∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1))
                = ∑ n ∈ Finset.range N,
                    -(((-1 : ℝ) ^ n) * Real.sqrt ((n : ℝ) + 1)) := by
                      refine Finset.sum_congr rfl ?_
                      intro n hn
                      rw [pow_succ]
                      ring
            _ = -(∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * Real.sqrt ((n : ℝ) + 1)) := by
                  rw [Finset.sum_neg_distrib]
  rw [hsign, abs_neg]
  exact HardyFirstMomentWiring.alternating_sqrt_sum_bound_range N

private lemma atkinsonCompleteModeTarget_sum_bound_range (N : ℕ) :
    |∑ n ∈ Finset.range N, atkinsonCompleteModeTarget n|
      ≤ (|atkinsonCompleteModeSlope| + 2 * |atkinsonCompleteModeOffset|) * Real.sqrt N := by
  have hsplit :
      ∑ n ∈ Finset.range N, atkinsonCompleteModeTarget n
        =
      atkinsonCompleteModeSlope *
          ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1)
        + atkinsonCompleteModeOffset *
          ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * atkinsonModeWeight n := by
    calc
      ∑ n ∈ Finset.range N, atkinsonCompleteModeTarget n
          =
          ∑ n ∈ Finset.range N,
            (atkinsonCompleteModeSlope * ((-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1))
              + atkinsonCompleteModeOffset * ((-1 : ℝ) ^ (n + 1) * atkinsonModeWeight n)) := by
                refine Finset.sum_congr rfl ?_
                intro n hn
                unfold atkinsonCompleteModeTarget
                ring
      _ =
          atkinsonCompleteModeSlope *
              ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1)
            + atkinsonCompleteModeOffset *
              ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * atkinsonModeWeight n := by
                rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hweight_sum :
      |∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * atkinsonModeWeight n|
        ≤ 2 * Real.sqrt N := by
    have habs_term (n : ℕ) :
        |(-1 : ℝ) ^ (n + 1) * atkinsonModeWeight n| = atkinsonModeWeight n := by
      rw [abs_mul, abs_of_nonneg (atkinsonModeWeight_nonneg n)]
      simp
    calc
      |∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * atkinsonModeWeight n|
          ≤ ∑ n ∈ Finset.range N, |(-1 : ℝ) ^ (n + 1) * atkinsonModeWeight n| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ n ∈ Finset.range N, atkinsonModeWeight n := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [habs_term n]
      _ = ∑ n ∈ Finset.range N, ((n + 1 : ℝ) ^ (-(1 : ℝ) / 2)) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [atkinsonModeWeight]
            congr 1
            ring
      _ ≤ 2 * Real.sqrt N := Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le N
  calc
    |∑ n ∈ Finset.range N, atkinsonCompleteModeTarget n|
        =
        |atkinsonCompleteModeSlope *
            ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1)
          + atkinsonCompleteModeOffset *
            ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * atkinsonModeWeight n| := by
            rw [hsplit]
    _ ≤
        |atkinsonCompleteModeSlope *
            ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1)|
          + |atkinsonCompleteModeOffset *
              ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * atkinsonModeWeight n| := by
            exact abs_add_le _ _
    _ =
        |atkinsonCompleteModeSlope| *
            |∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1)|
          + |atkinsonCompleteModeOffset| *
              |∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * atkinsonModeWeight n| := by
            rw [abs_mul, abs_mul]
    _ ≤ |atkinsonCompleteModeSlope| * Real.sqrt N
          + |atkinsonCompleteModeOffset| * (2 * Real.sqrt N) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left
              (atkinson_alternating_shifted_sqrt_sum_bound_range N) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hweight_sum (abs_nonneg _))
    _ = (|atkinsonCompleteModeSlope| + 2 * |atkinsonCompleteModeOffset|) * Real.sqrt N := by
          ring

private lemma hardyCos_integral_abs_le_length (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    |∫ t in Ioc a b, hardyCos n t| ≤ b - a := by
  have hInt : IntervalIntegrable (hardyCos n) volume a b :=
    HardyCosSmooth.intervalIntegrable_hardyCos n a b
  calc
    |∫ t in Ioc a b, hardyCos n t|
        = |∫ t in a..b, hardyCos n t| := by
            rw [← intervalIntegral.integral_of_le hab]
    _ ≤ ∫ t in a..b, |hardyCos n t| := by
          simpa [Real.norm_eq_abs] using
            (intervalIntegral.norm_integral_le_integral_norm (f := hardyCos n) hab)
    _ ≤ ∫ t in a..b, (1 : ℝ) := by
          refine intervalIntegral.integral_mono_on hab hInt.norm intervalIntegrable_const ?_
          intro t ht
          simpa [HardyEstimatesPartial.hardyCos] using
            (Real.abs_cos_le_one (hardyTheta t - t * Real.log (n + 1)))
    _ = b - a := by simp [intervalIntegral.integral_const]

private lemma hardyStart_mono {m n : ℕ} (hmn : m ≤ n) :
    hardyStart m ≤ hardyStart n := by
  rw [hardyStart_formula, hardyStart_formula]
  have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ hmn
  have hsq : ((m : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
    nlinarith
  exact mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * Real.pi)

private lemma modeOmega_le_of_le (n : ℕ) (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    modeOmega n s ≤ modeOmega n t := by
  simp only [modeOmega]
  have hmono : MonotoneOn ThetaDerivAsymptotic.thetaDeriv (Set.Ioi 0) :=
    ThetaDerivMonotone.thetaDeriv_strictMonoOn.monotoneOn
  have htd :
      ThetaDerivAsymptotic.thetaDeriv s ≤ ThetaDerivAsymptotic.thetaDeriv t := by
    exact hmono (Set.mem_Ioi.mpr hs) (Set.mem_Ioi.mpr (lt_of_lt_of_le hs hst)) hst
  linarith [htd]

private theorem atkinson_global_mode_tail_vdc_bound :
    ∃ K₁ : ℕ, ∀ k n : ℕ, n < k → K₁ ≤ k →
      ∀ T : ℝ, hardyStart k ≤ T →
        |∫ t in Ioc (hardyStart k) T, hardyCos n t|
          ≤ 6 / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
  obtain ⟨K₀, hK₀⟩ := modeOmega_lower_bound_eventually
  refine ⟨K₀, ?_⟩
  intro k n hnk hk T hT
  have hm_pos :
      0 < Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) / 2 := by
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hratio_gt : 1 < ((k : ℝ) + 1) / ((n : ℝ) + 1) := by
      rw [one_lt_div hn1_pos]
      exact_mod_cast Nat.succ_lt_succ hnk
    have hlog_pos : 0 < Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := Real.log_pos hratio_gt
    positivity
  have ha_pos : 0 < hardyStart k := by
    rw [hardyStart_formula]
    positivity
  have hω_lower :
      ∀ t ∈ Set.Icc (hardyStart k) T,
        Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) / 2 ≤ modeOmega n t := by
    intro t ht
    have hbase := hK₀ k hk n hnk (hardyStart k) le_rfl (hardyStart_mono (Nat.le_succ k))
    exact le_trans hbase (modeOmega_le_of_le n _ t ha_pos ht.1)
  have hBound :=
    Aristotle.ComplexVdC.complex_vdc_angular_re
      (HardyCosSmooth.hardyCosExp n) (modeOmega n)
      (hardyStart k) T (Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) / 2)
      hT hm_pos
      (fun t _ht => by
        simpa [modeOmega, Nat.cast_succ] using
          (Aristotle.HardyCosExpOmega.hardyCosExp_angular_velocity n t))
      (fun t _ht => le_of_eq (norm_hardyCosExp n t))
      (differentiable_modeOmega n)
      (continuous_deriv_modeOmega n)
      hω_lower
      (fun t ht => deriv_modeOmega_nonneg n t (lt_of_lt_of_le ha_pos ht.1))
  have h_cos_eq :
      (fun t => hardyCos n t) = (fun t => (HardyCosSmooth.hardyCosExp n t).re) := by
    funext t
    exact HardyCosSmooth.hardyCos_eq_re_hardyCosExp n t
  calc
    |∫ t in Ioc (hardyStart k) T, hardyCos n t|
        = |∫ t in hardyStart k..T, hardyCos n t| := by
            rw [← intervalIntegral.integral_of_le hT]
    _ = |∫ t in hardyStart k..T, (HardyCosSmooth.hardyCosExp n t).re| := by
          rw [h_cos_eq]
    _ ≤ 3 / (Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) / 2) := hBound
    _ = 6 / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
          ring

private lemma hardyCos_ioc_integral_split (n : ℕ) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    ∫ t in Ioc a c, hardyCos n t
      =
    (∫ t in Ioc a b, hardyCos n t)
      +
    ∫ t in Ioc b c, hardyCos n t := by
  have hIntAB : IntegrableOn (hardyCos n) (Ioc a b) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact HardyCosSmooth.intervalIntegrable_hardyCos n a b
  have hIntBC : IntegrableOn (hardyCos n) (Ioc b c) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hbc]
    exact HardyCosSmooth.intervalIntegrable_hardyCos n b c
  convert
    (Aristotle.IntervalPartition.integral_split_at
      (hardyCos n) a b c hab hbc hIntAB hIntBC) using 1 <;> simp

private lemma atkinson_weighted_ioc_integral_split (n : ℕ) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    atkinsonModeWeight n * ∫ t in Ioc a c, hardyCos n t
      =
    (atkinsonModeWeight n * ∫ t in Ioc a b, hardyCos n t)
      +
    (atkinsonModeWeight n * ∫ t in Ioc b c, hardyCos n t) := by
  have hsplit := congrArg (fun x : ℝ => atkinsonModeWeight n * x)
    (hardyCos_ioc_integral_split n hab hbc)
  convert hsplit using 1 <;> ring

private lemma atkinson_tail_integral_split (n : ℕ) {T : ℝ}
    (hstart : hardyStart (n + 1) ≤ T) :
    ∫ t in Ioc (hardyStart (n + 1)) T, hardyCos n t
      =
    (∫ t in Ioc (hardyStart (n + 1)) (min T (hardyStart (2 * n + 1))), hardyCos n t)
      +
    ∫ t in Ioc (min T (hardyStart (2 * n + 1))) T, hardyCos n t := by
  have hab : hardyStart (n + 1) ≤ min T (hardyStart (2 * n + 1)) := by
    refine le_min hstart ?_
    exact hardyStart_mono (by omega)
  have hbc : min T (hardyStart (2 * n + 1)) ≤ T := min_le_left _ _
  exact hardyCos_ioc_integral_split n hab hbc

private theorem atkinson_small_modes_tail_bound (M : ℕ) :
    ∃ C_small > 0, ∀ T : ℝ, T ≥ 2 →
      |∑ n ∈ Finset.range (min M (hardyN T - 1)),
          atkinsonModeWeight n *
            ∫ t in Ioc (hardyStart (n + 1)) T, hardyCos n t|
        ≤ C_small * ((↑(hardyN T) : ℝ) + 1) := by
  by_cases hM0 : M = 0
  · refine ⟨1, by positivity, ?_⟩
    intro T hT
    have hnonneg : 0 ≤ ((↑(hardyN T) : ℝ) + 1) := by positivity
    simpa [hM0] using hnonneg
  obtain ⟨K₁, hTail⟩ := atkinson_global_mode_tail_vdc_bound
  let K : ℕ := max K₁ M
  have hM_pos : 0 < M := Nat.pos_of_ne_zero hM0
  have hK_ge_M : M ≤ K := le_max_right _ _
  have hK_ge_K₁ : K₁ ≤ K := le_max_left _ _
  have hratio_gt : 1 < ((K : ℝ) + 1) / (M : ℝ) := by
    have hM_real_pos : (0 : ℝ) < M := by exact_mod_cast hM_pos
    rw [one_lt_div hM_real_pos]
    have hMK : (M : ℝ) ≤ K := by exact_mod_cast hK_ge_M
    linarith
  let D : ℝ := hardyStart K + 6 / Real.log (((K : ℝ) + 1) / (M : ℝ))
  have hD_pos : 0 < D := by
    have hlog_pos : 0 < Real.log (((K : ℝ) + 1) / (M : ℝ)) := Real.log_pos hratio_gt
    have hstart_nonneg : 0 ≤ hardyStart K := by
      rw [hardyStart_formula]
      positivity
    dsimp [D]
    positivity
  refine ⟨M * D, by
    have hM_nonneg : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    positivity, ?_⟩
  intro T hT
  have hT_nonneg : 0 ≤ T := by linarith
  calc
    |∑ n ∈ Finset.range (min M (hardyN T - 1)),
        atkinsonModeWeight n *
          ∫ t in Ioc (hardyStart (n + 1)) T, hardyCos n t|
      ≤ ∑ n ∈ Finset.range (min M (hardyN T - 1)),
          |atkinsonModeWeight n *
            ∫ t in Ioc (hardyStart (n + 1)) T, hardyCos n t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range (min M (hardyN T - 1)), D := by
        refine Finset.sum_le_sum ?_
        intro n hn
        have hnM : n < M := lt_of_lt_of_le (Finset.mem_range.mp hn) (Nat.min_le_left _ _)
        have hstartn : hardyStart (n + 1) ≤ T := by
          have hnN : n + 1 < hardyN T := by
            have hmin : n < min M (hardyN T - 1) := Finset.mem_range.mp hn
            omega
          exact (hardyN_lt_iff (n + 1) T hT_nonneg).1 hnN
        have hweight_nonneg : 0 ≤ atkinsonModeWeight n := atkinsonModeWeight_nonneg n
        rw [abs_mul, abs_of_nonneg hweight_nonneg]
        have hweight_le : atkinsonModeWeight n ≤ 1 := atkinsonModeWeight_le_one n
        have hterm :
            |∫ t in Ioc (hardyStart (n + 1)) T, hardyCos n t| ≤ D := by
          by_cases hTK : T ≤ hardyStart K
          · calc
              |∫ t in Ioc (hardyStart (n + 1)) T, hardyCos n t|
                  ≤ T - hardyStart (n + 1) :=
                    hardyCos_integral_abs_le_length n hstartn
              _ ≤ hardyStart K - hardyStart (n + 1) := by linarith
              _ ≤ hardyStart K := by
                    have hstart_nonneg : 0 ≤ hardyStart (n + 1) := by
                      rw [hardyStart_formula]
                      positivity
                    linarith
              _ ≤ D := by
                    dsimp [D]
                    have htail_nonneg : 0 ≤ 6 / Real.log (((K : ℝ) + 1) / (M : ℝ)) := by
                      have hlog_pos : 0 < Real.log (((K : ℝ) + 1) / (M : ℝ)) :=
                        Real.log_pos hratio_gt
                      positivity
                    linarith
          · have hKT : hardyStart K ≤ T := le_of_not_ge hTK
            have hsplit :
                (∫ t in Ioc (hardyStart (n + 1)) T, hardyCos n t)
                  =
                (∫ t in Ioc (hardyStart (n + 1)) (hardyStart K), hardyCos n t)
                  + (∫ t in Ioc (hardyStart K) T, hardyCos n t) := by
                    have hIntA :
                        IntervalIntegrable (hardyCos n) volume
                          (hardyStart (n + 1)) (hardyStart K) :=
                      HardyCosSmooth.intervalIntegrable_hardyCos n _ _
                    have hIntB :
                        IntervalIntegrable (hardyCos n) volume (hardyStart K) T :=
                      HardyCosSmooth.intervalIntegrable_hardyCos n _ _
                    have hsplit_int :
                        (∫ x in (hardyStart (n + 1))..T, hardyCos n x)
                          =
                        (∫ x in (hardyStart (n + 1))..(hardyStart K), hardyCos n x)
                          + (∫ x in (hardyStart K)..T, hardyCos n x) := by
                        simpa [add_comm, add_left_comm, add_assoc] using
                          (intervalIntegral.integral_add_adjacent_intervals hIntA hIntB).symm
                    rw [← intervalIntegral.integral_of_le hstartn,
                      ← intervalIntegral.integral_of_le
                        (hardyStart_mono (by
                          have : n + 1 ≤ M := Nat.succ_le_of_lt hnM
                          exact le_trans this hK_ge_M)),
                      ← intervalIntegral.integral_of_le hKT]
                    exact hsplit_int
            have hratio_ge :
                ((K : ℝ) + 1) / (M : ℝ)
                  ≤ ((K : ℝ) + 1) / ((n : ℝ) + 1) := by
              have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
              have hn1_le : (n : ℝ) + 1 ≤ (M : ℝ) := by
                exact_mod_cast Nat.succ_le_of_lt hnM
              rw [div_le_div_iff₀ (show (0 : ℝ) < M by exact_mod_cast hM_pos) hn1_pos]
              nlinarith
            have hlog_ge :
                Real.log (((K : ℝ) + 1) / (M : ℝ))
                  ≤ Real.log (((K : ℝ) + 1) / ((n : ℝ) + 1)) := by
              exact Real.log_le_log (lt_trans zero_lt_one hratio_gt) hratio_ge
            have htail_bound :
                |∫ t in Ioc (hardyStart K) T, hardyCos n t|
                  ≤ 6 / Real.log (((K : ℝ) + 1) / ((n : ℝ) + 1)) := by
              exact hTail K n
                (lt_of_lt_of_le hnM hK_ge_M)
                hK_ge_K₁ T hKT
            have htail_bound' :
                |∫ t in Ioc (hardyStart K) T, hardyCos n t|
                  ≤ 6 / Real.log (((K : ℝ) + 1) / (M : ℝ)) := by
              have hden_pos : 0 < Real.log (((K : ℝ) + 1) / (M : ℝ)) := Real.log_pos hratio_gt
              have hscalar :
                  6 / Real.log (((K : ℝ) + 1) / ((n : ℝ) + 1))
                    ≤ 6 / Real.log (((K : ℝ) + 1) / (M : ℝ)) := by
                exact div_le_div_of_nonneg_left (by positivity) hden_pos hlog_ge
              exact le_trans htail_bound hscalar
            calc
              |∫ t in Ioc (hardyStart (n + 1)) T, hardyCos n t|
                  ≤ |∫ t in Ioc (hardyStart (n + 1)) (hardyStart K), hardyCos n t|
                    + |∫ t in Ioc (hardyStart K) T, hardyCos n t| := by
                      rw [hsplit]
                      exact abs_add_le _ _
              _ ≤ (hardyStart K - hardyStart (n + 1))
                    + |∫ t in Ioc (hardyStart K) T, hardyCos n t| := by
                      gcongr
                      exact hardyCos_integral_abs_le_length n
                        (hardyStart_mono (by
                          have : n + 1 ≤ M := Nat.succ_le_of_lt hnM
                          exact le_trans this hK_ge_M))
              _ ≤ (hardyStart K - hardyStart (n + 1))
                    + 6 / Real.log (((K : ℝ) + 1) / (M : ℝ)) := by
                      gcongr
              _ ≤ D := by
                    dsimp [D]
                    have hstart_nonneg : 0 ≤ hardyStart (n + 1) := by
                      rw [hardyStart_formula]
                      positivity
                    linarith
        calc
          atkinsonModeWeight n *
              |∫ t in Ioc (hardyStart (n + 1)) T, hardyCos n t|
            ≤ 1 * D := by
                have hweight_le : atkinsonModeWeight n ≤ 1 := atkinsonModeWeight_le_one n
                nlinarith [hterm, atkinsonModeWeight_nonneg n]
          _ = D := by ring
    _ = ((min M (hardyN T - 1) : ℕ) : ℝ) * D := by simp
    _ ≤ (M : ℝ) * D := by
        gcongr
        exact_mod_cast Nat.min_le_left M (hardyN T - 1)
    _ ≤ (M : ℝ) * D * ((↑(hardyN T) : ℝ) + 1) := by
        have hone : 1 ≤ ((↑(hardyN T) : ℝ) + 1) := by
          have hN_nonneg : 0 ≤ (↑(hardyN T) : ℝ) := Nat.cast_nonneg (hardyN T)
          linarith
        nlinarith [show 0 ≤ (M : ℝ) * D from mul_nonneg (Nat.cast_nonneg M) (le_of_lt hD_pos)]
    _ = ((M : ℝ) * D) * ((↑(hardyN T) : ℝ) + 1) := by ring

private theorem atkinson_large_modes_far_tail_bound :
    ∃ K₁ : ℕ, ∃ C_far > 0, ∀ M : ℕ, K₁ ≤ M →
      ∀ T : ℝ, T ≥ 2 →
        |∑ n ∈ Finset.Ico M (hardyN T - 1),
            atkinsonModeWeight n *
              ∫ t in Ioc (min T (hardyStart (2 * n + 1))) T, hardyCos n t|
          ≤ C_far * ((↑(hardyN T) : ℝ) + 1) := by
  obtain ⟨K₁, hTail⟩ := atkinson_global_mode_tail_vdc_bound
  refine ⟨K₁, 6 / Real.log 2, ?_, ?_⟩
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  intro M hM T hT
  calc
    |∑ n ∈ Finset.Ico M (hardyN T - 1),
        atkinsonModeWeight n *
          ∫ t in Ioc (min T (hardyStart (2 * n + 1))) T, hardyCos n t|
      ≤ ∑ n ∈ Finset.Ico M (hardyN T - 1),
          |atkinsonModeWeight n *
            ∫ t in Ioc (min T (hardyStart (2 * n + 1))) T, hardyCos n t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Ico M (hardyN T - 1), 6 / Real.log 2 := by
        refine Finset.sum_le_sum ?_
        intro n hn
        have hnM : M ≤ n := (Finset.mem_Ico.mp hn).1
        have hweight_nonneg : 0 ≤ atkinsonModeWeight n := atkinsonModeWeight_nonneg n
        rw [abs_mul, abs_of_nonneg hweight_nonneg]
        by_cases hstart : hardyStart (2 * n + 1) ≤ T
        · have hratio_two :
              (((2 * n + 1 : ℕ) : ℝ) + 1) / ((n : ℝ) + 1) = 2 := by
            norm_num [Nat.cast_add, Nat.cast_mul]
            field_simp
            ring
          have htail_two :
              |∫ t in Ioc (hardyStart (2 * n + 1)) T, hardyCos n t| ≤ 6 / Real.log 2 := by
            have htail_raw :=
              hTail (2 * n + 1) n (by omega)
                (by
                  calc
                    K₁ ≤ M := hM
                    _ ≤ n := hnM
                    _ ≤ 2 * n + 1 := by omega) T hstart
            have hratio_two' : (2 * (n : ℝ) + 1 + 1) / ((n : ℝ) + 1) = 2 := by
              field_simp
              ring
            simpa [Nat.cast_add, Nat.cast_mul, hratio_two'] using htail_raw
          calc
            atkinsonModeWeight n *
                |∫ t in Ioc (min T (hardyStart (2 * n + 1))) T, hardyCos n t|
              = atkinsonModeWeight n *
                  |∫ t in Ioc (hardyStart (2 * n + 1)) T, hardyCos n t| := by
                    rw [min_eq_right hstart]
            _ ≤ atkinsonModeWeight n * (6 / Real.log 2) := by
                  exact mul_le_mul_of_nonneg_left htail_two hweight_nonneg
            _ ≤ 1 * (6 / Real.log 2) := by
                  gcongr
                  exact atkinsonModeWeight_le_one n
            _ = 6 / Real.log 2 := by ring
        · have hzero :
              ∫ t in Ioc (min T (hardyStart (2 * n + 1))) T, hardyCos n t = 0 := by
                have hmin : min T (hardyStart (2 * n + 1)) = T := min_eq_left (le_of_not_ge hstart)
                simp [hmin]
          have hnonneg : 0 ≤ 6 / Real.log 2 := by
            have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
            positivity
          simpa [hzero] using hnonneg
    _ = (Finset.Ico M (hardyN T - 1)).card * (6 / Real.log 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((↑(hardyN T) : ℝ) + 1) * (6 / Real.log 2) := by
        have hcard_le : (Finset.Ico M (hardyN T - 1)).card ≤ hardyN T := by
          rw [Nat.card_Ico]
          omega
        have hcast_le : ((Finset.Ico M (hardyN T - 1)).card : ℝ) ≤ (↑(hardyN T) : ℝ) + 1 := by
          exact_mod_cast Nat.le_succ_of_le hcard_le
        gcongr
    _ = (6 / Real.log 2) * ((↑(hardyN T) : ℝ) + 1) := by ring

private lemma atkinson_log_le_sqrt_of_ge_two {x : ℝ} (hx : 2 ≤ x) :
    Real.log x ≤ Real.sqrt x := by
  have haux := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt x / 2 by positivity)
  rw [Real.log_div (by positivity) (by positivity), Real.log_sqrt (by positivity)] at haux
  have htwo := Real.log_two_lt_d9
  nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith)]

private lemma atkinson_log_le_sqrt_of_ge_one {y : ℝ} (hy : 1 ≤ y) :
    Real.log y ≤ Real.sqrt y := by
  by_cases h2 : 2 ≤ y
  · exact atkinson_log_le_sqrt_of_ge_two h2
  · have hlog_le : Real.log y ≤ Real.log 2 := Real.log_le_log (by linarith) (le_of_not_ge h2)
    linarith [Real.log_two_lt_d9, Real.one_le_sqrt.mpr hy]

/-- `log(x)·(1+log(x)) ≤ 6·√x` for `x ≥ 2`. Uses `log(x) = 2·log(√x)` and
    `log(y) ≤ √y` to get `log²(y) ≤ y` and `√y ≤ y`. -/
private lemma atkinson_log_mul_succ_le_sqrt {x : ℝ} (hx : 2 ≤ x) :
    Real.log x * (1 + Real.log x) ≤ 6 * Real.sqrt x := by
  set y := Real.sqrt x with hy_def
  have hy_ge : 1 ≤ y := Real.one_le_sqrt.mpr (by linarith)
  have hsq : y ^ 2 = x := Real.sq_sqrt (by linarith)
  have hlog_eq : Real.log x = 2 * Real.log y := by
    rw [← hsq, Real.log_pow]; simp
  have hlog_y_nonneg : 0 ≤ Real.log y := Real.log_nonneg hy_ge
  have hlog_y_le_sqrt_y : Real.log y ≤ Real.sqrt y := atkinson_log_le_sqrt_of_ge_one hy_ge
  have hlog_y_sq_le_y : Real.log y ^ 2 ≤ y := by
    calc Real.log y ^ 2 ≤ (Real.sqrt y) ^ 2 :=
          sq_le_sq' (by linarith) hlog_y_le_sqrt_y
        _ = y := Real.sq_sqrt (by linarith)
  have hsqrt_y_le_y : Real.sqrt y ≤ y := by
    nlinarith [sq_nonneg (Real.sqrt y - 1), Real.sq_sqrt (show 0 ≤ y by linarith)]
  rw [hlog_eq]
  nlinarith

private noncomputable def atkinsonShiftedCompleteCell (n j : ℕ) : ℝ :=
  atkinsonModeWeight n *
    ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)), hardyCos n t

private noncomputable def atkinsonShiftedCompleteRow (M j : ℕ) : ℝ :=
  ∑ n ∈ Finset.range M, (if j ≤ n then atkinsonShiftedCompleteCell n j else 0)

private noncomputable def atkinsonShiftedCompleteRowIntegrand (n j : ℕ) (u : ℝ) : ℝ :=
  atkinsonModeWeight n * hardyCos n (blockCoord (n + j) u) * blockJacobian (n + j) u

private lemma atkinsonShiftedCompleteRowIntegrand_continuous (n j : ℕ) :
    Continuous (atkinsonShiftedCompleteRowIntegrand n j) := by
  unfold atkinsonShiftedCompleteRowIntegrand
  exact (continuous_const.mul
    ((HardyCosSmooth.continuous_hardyCos n).comp (blockCoord_continuous (n + j)))).mul
    (blockJacobian_continuous (n + j))

private lemma atkinsonHalfLogPiMulSqLocal (n : ℕ) :
    (1 / 2 : ℝ) * Real.log (Real.pi * ((n : ℝ) + 1) ^ 2)
      = (1 / 2 : ℝ) * Real.log Real.pi + Real.log ((n : ℝ) + 1) := by
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn_ne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hn_pos
  calc
    (1 / 2 : ℝ) * Real.log (Real.pi * ((n : ℝ) + 1) ^ 2)
        = (1 / 2 : ℝ) * (Real.log Real.pi + Real.log (((n : ℝ) + 1) ^ 2)) := by
            rw [Real.log_mul hpi_ne (pow_ne_zero 2 hn_ne)]
    _ = (1 / 2 : ℝ) * Real.log Real.pi
          + (1 / 2 : ℝ) * Real.log (((n : ℝ) + 1) ^ 2) := by
            ring
    _ = (1 / 2 : ℝ) * Real.log Real.pi
          + (1 / 2 : ℝ) * (Real.log ((n : ℝ) + 1) + Real.log ((n : ℝ) + 1)) := by
            rw [show (((n : ℝ) + 1) ^ 2) = ((n : ℝ) + 1) * ((n : ℝ) + 1) by ring,
              Real.log_mul hn_ne hn_ne]
    _ = (1 / 2 : ℝ) * Real.log Real.pi + Real.log ((n : ℝ) + 1) := by
            ring

private noncomputable def atkinsonCommonBlockCarrier (k : ℕ) (u : ℝ) : ℂ :=
  let t := blockCoord k u
  Complex.Gamma (1 / 4 + Complex.I * (↑t / 2)) /
      ↑‖Complex.Gamma (1 / 4 + Complex.I * (↑t / 2))‖ *
    Complex.exp (-Complex.I * ↑((t / 2) * Real.log Real.pi))

private noncomputable def atkinsonShiftedRelativeWeight (k j : ℕ) : ℝ :=
  atkinsonModeWeight (k - j) / atkinsonModeWeight k

private noncomputable def atkinsonShiftedRelativePhase (k j : ℕ) : ℝ :=
  Real.log (((k : ℝ) + 1) / (((k - j : ℕ) : ℝ) + 1))

private noncomputable def atkinsonResonantBlockCarrier (k : ℕ) (u : ℝ) : ℂ :=
  ((((atkinsonModeWeight k : ℝ) : ℂ) *
      HardyCosSmooth.hardyCosExp k (blockCoord k u))) *
    (blockJacobian k u : ℂ)

private noncomputable def atkinsonShiftedSinglePacket (k j : ℕ) (u : ℝ) : ℂ :=
  ((((atkinsonShiftedRelativeWeight k j : ℝ) : ℂ)) *
    Complex.exp (Complex.I * ↑(blockCoord k u * atkinsonShiftedRelativePhase k j)))

private noncomputable def atkinsonComplexShiftedCompleteRowIntegrand (n j : ℕ) (u : ℝ) : ℂ :=
  (((atkinsonModeWeight n : ℝ) : ℂ) *
    (HardyCosSmooth.hardyCosExp n (blockCoord (n + j) u) *
      ((blockJacobian (n + j) u : ℝ) : ℂ)))

private noncomputable def atkinsonResonantShiftedRowSummand (n j : ℕ) (u : ℝ) : ℂ :=
  atkinsonResonantBlockCarrier (n + j) u * atkinsonShiftedSinglePacket (n + j) j u

private lemma atkinsonModeWeight_mul_shiftedRelativeWeight (k j : ℕ) :
    atkinsonModeWeight k * atkinsonShiftedRelativeWeight k j = atkinsonModeWeight (k - j) := by
  unfold atkinsonShiftedRelativeWeight
  field_simp [atkinsonModeWeight_ne_zero k]

private lemma atkinsonShiftedRelativePhase_eq_sub_logs (k j : ℕ) :
    atkinsonShiftedRelativePhase k j
      = Real.log ((k : ℝ) + 1) - Real.log ((((k - j : ℕ) : ℝ) + 1)) := by
  unfold atkinsonShiftedRelativePhase
  have hk_pos : 0 < (k : ℝ) + 1 := by positivity
  have hkj_pos : 0 < (((k - j : ℕ) : ℝ) + 1) := by positivity
  rw [Real.log_div hk_pos.ne' hkj_pos.ne']

private lemma atkinsonWeighted_hardyCosExp_eq_commonBlockCarrier (k n : ℕ) (u : ℝ) :
    (((atkinsonModeWeight n : ℝ) : ℂ) * HardyCosSmooth.hardyCosExp n (blockCoord k u))
      =
      atkinsonCommonBlockCarrier k u *
        ((((atkinsonModeWeight n : ℝ) : ℂ) *
          Complex.exp (-Complex.I *
            ↑(blockCoord k u * Real.log ((n : ℝ) + 1))))) := by
  let t : ℝ := blockCoord k u
  have hsplit :
      (t / 2) * Real.log (Real.pi * ((n : ℝ) + 1) ^ 2)
        = (t / 2) * Real.log Real.pi + t * Real.log ((n : ℝ) + 1) := by
    calc
      (t / 2) * Real.log (Real.pi * ((n : ℝ) + 1) ^ 2)
          = t * ((1 / 2 : ℝ) * Real.log (Real.pi * ((n : ℝ) + 1) ^ 2)) := by
              ring
      _ = t * ((1 / 2 : ℝ) * Real.log Real.pi + Real.log ((n : ℝ) + 1)) := by
            rw [atkinsonHalfLogPiMulSqLocal]
      _ = (t / 2) * Real.log Real.pi + t * Real.log ((n : ℝ) + 1) := by
            ring
  have hexp_split :
      Complex.exp (-Complex.I * ↑((t / 2) * Real.log (Real.pi * ((n : ℝ) + 1) ^ 2)))
        =
      Complex.exp (-Complex.I * ↑((t / 2) * Real.log Real.pi)) *
        Complex.exp (-Complex.I * ↑(t * Real.log ((n : ℝ) + 1))) := by
    have harg :
        (-Complex.I * ↑((t / 2) * Real.log (Real.pi * ((n : ℝ) + 1) ^ 2)))
          =
        (-Complex.I * ↑((t / 2) * Real.log Real.pi))
          + (-Complex.I * ↑(t * Real.log ((n : ℝ) + 1))) := by
      rw [hsplit]
      simp [mul_add, add_mul]
    rw [harg, Complex.exp_add]
  calc
    (((atkinsonModeWeight n : ℝ) : ℂ) * HardyCosSmooth.hardyCosExp n (blockCoord k u))
        =
        (((atkinsonModeWeight n : ℝ) : ℂ) *
          (Complex.Gamma (1 / 4 + Complex.I * (↑t / 2)) /
              ↑‖Complex.Gamma (1 / 4 + Complex.I * (↑t / 2))‖ *
            Complex.exp (-Complex.I *
              ↑((t / 2) * Real.log (Real.pi * ((n : ℝ) + 1) ^ 2))))) := by
              simp [HardyCosSmooth.hardyCosExp, t]
    _ =
        (Complex.Gamma (1 / 4 + Complex.I * (↑t / 2)) /
            ↑‖Complex.Gamma (1 / 4 + Complex.I * (↑t / 2))‖ *
          Complex.exp (-Complex.I * ↑((t / 2) * Real.log Real.pi))) *
          ((((atkinsonModeWeight n : ℝ) : ℂ) *
            Complex.exp (-Complex.I * ↑(t * Real.log ((n : ℝ) + 1))))) := by
              rw [hexp_split]
              ring
    _ = atkinsonCommonBlockCarrier k u *
          ((((atkinsonModeWeight n : ℝ) : ℂ) *
            Complex.exp (-Complex.I *
              ↑(blockCoord k u * Real.log ((n : ℝ) + 1))))) := by
              simp [atkinsonCommonBlockCarrier, t]

private lemma atkinsonWeighted_hardyCosExp_eq_resonant_times_shiftedPacket (k j : ℕ) (u : ℝ) :
    (((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
        HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u))
      =
      ((((atkinsonModeWeight k : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp k (blockCoord k u))) *
        atkinsonShiftedSinglePacket k j u := by
  let t : ℝ := blockCoord k u
  have hleft :=
    atkinsonWeighted_hardyCosExp_eq_commonBlockCarrier k (k - j) u
  have hres :=
    atkinsonWeighted_hardyCosExp_eq_commonBlockCarrier k k u
  have hlog :
      Real.log ((((k - j : ℕ) : ℝ) + 1))
        = Real.log ((k : ℝ) + 1) - atkinsonShiftedRelativePhase k j := by
    rw [atkinsonShiftedRelativePhase_eq_sub_logs]
    ring
  have hexp :
      Complex.exp (-Complex.I * ↑(t * Real.log ((((k - j : ℕ) : ℝ) + 1))))
        =
      Complex.exp (-Complex.I * ↑(t * Real.log ((k : ℝ) + 1))) *
        Complex.exp (Complex.I * ↑(t * atkinsonShiftedRelativePhase k j)) := by
    have harg :
        -Complex.I * ↑(t * Real.log ((((k - j : ℕ) : ℝ) + 1)))
          =
        (-Complex.I * ↑(t * Real.log ((k : ℝ) + 1)))
          + (Complex.I * ↑(t * atkinsonShiftedRelativePhase k j)) := by
      rw [hlog]
      simp [sub_eq_add_neg, mul_add, add_mul, mul_assoc]
    rw [harg, Complex.exp_add]
  calc
    (((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
        HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u))
      =
      atkinsonCommonBlockCarrier k u *
        ((((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
          Complex.exp (-Complex.I * ↑(t * Real.log ((((k - j : ℕ) : ℝ) + 1)))))) := by
            simpa [t] using hleft
    _ =
      atkinsonCommonBlockCarrier k u *
        (((((atkinsonModeWeight k : ℝ) : ℂ) *
            Complex.exp (-Complex.I * ↑(t * Real.log ((k : ℝ) + 1)))) *
          atkinsonShiftedSinglePacket k j u)) := by
            rw [hexp]
            have hw :
                (((atkinsonModeWeight (k - j) : ℝ) : ℂ))
                  = (((atkinsonModeWeight k : ℝ) : ℂ) *
                      (((atkinsonShiftedRelativeWeight k j : ℝ) : ℂ))) := by
                  rw [← Complex.ofReal_mul]
                  congr 1
                  exact (atkinsonModeWeight_mul_shiftedRelativeWeight k j).symm
            rw [hw]
            unfold atkinsonShiftedSinglePacket
            ac_rfl
    _ =
      ((((atkinsonModeWeight k : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp k (blockCoord k u))) *
        atkinsonShiftedSinglePacket k j u := by
            rw [show atkinsonCommonBlockCarrier k u *
                  (((((atkinsonModeWeight k : ℝ) : ℂ) *
                      Complex.exp (-Complex.I * ↑(t * Real.log ((k : ℝ) + 1)))) *
                    atkinsonShiftedSinglePacket k j u))
                  =
                (atkinsonCommonBlockCarrier k u *
                  (((atkinsonModeWeight k : ℝ) : ℂ) *
                    Complex.exp (-Complex.I * ↑(t * Real.log ((k : ℝ) + 1))))) *
                  atkinsonShiftedSinglePacket k j u by
                      ac_rfl]
            rw [← hres]
    _ =
      ((((atkinsonModeWeight k : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp k (blockCoord k u))) *
        atkinsonShiftedSinglePacket k j u := by
            simp [t]

private lemma atkinsonComplexShiftedCompleteRowIntegrand_re (n j : ℕ) (u : ℝ) :
    (atkinsonComplexShiftedCompleteRowIntegrand n j u).re = atkinsonShiftedCompleteRowIntegrand n j u := by
  unfold atkinsonComplexShiftedCompleteRowIntegrand atkinsonShiftedCompleteRowIntegrand
  simpa [HardyCosSmooth.hardyCos_eq_re_hardyCosExp, mul_assoc, mul_left_comm, mul_comm]

private lemma atkinsonComplexShiftedCompleteRowIntegrand_eq_resonantCarrier_singlePacket
    (n j : ℕ) (u : ℝ) :
    atkinsonComplexShiftedCompleteRowIntegrand n j u
      = atkinsonResonantShiftedRowSummand n j u := by
  have hpacket :
      (((atkinsonModeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (blockCoord (n + j) u))
        =
        ((((atkinsonModeWeight (n + j) : ℝ) : ℂ) *
            HardyCosSmooth.hardyCosExp (n + j) (blockCoord (n + j) u))) *
          atkinsonShiftedSinglePacket (n + j) j u := by
            simpa [show n + j - j = n by omega] using
              atkinsonWeighted_hardyCosExp_eq_resonant_times_shiftedPacket (n + j) j u
  calc
    atkinsonComplexShiftedCompleteRowIntegrand n j u
        =
      ((((atkinsonModeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (blockCoord (n + j) u)) *
        ((blockJacobian (n + j) u : ℝ) : ℂ)) := by
          unfold atkinsonComplexShiftedCompleteRowIntegrand
          ring
    _ =
      ((((atkinsonModeWeight (n + j) : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp (n + j) (blockCoord (n + j) u)) *
        atkinsonShiftedSinglePacket (n + j) j u) *
        ((blockJacobian (n + j) u : ℝ) : ℂ) := by
          rw [hpacket]
    _ = atkinsonResonantShiftedRowSummand n j u := by
          unfold atkinsonResonantShiftedRowSummand atkinsonResonantBlockCarrier
          ring

private lemma atkinsonWeightedShiftedCompleteBlockComplex_eq_rowIntegral
    (n j : ℕ) (hj : 1 ≤ j) :
    (((atkinsonModeWeight n : ℝ) : ℂ) *
        ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
          HardyCosSmooth.hardyCosExp n t)
      =
    ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u := by
  have hblock :=
    Aristotle.StationaryPhaseMainMode.hardyCosExp_completeBlock_eq_common_blockParamIntegral
      (n + j) j hj (by omega)
  calc
    (((atkinsonModeWeight n : ℝ) : ℂ) *
        ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
          HardyCosSmooth.hardyCosExp n t)
        =
      (((atkinsonModeWeight n : ℝ) : ℂ) *
        ∫ u in Ioc (0 : ℝ) 1,
          HardyCosSmooth.hardyCosExp n (blockCoord (n + j) u) *
            blockJacobian (n + j) u) := by
            simpa [Nat.add_assoc, add_left_comm, add_comm] using
              congrArg (fun x => (((atkinsonModeWeight n : ℝ) : ℂ) * x)) hblock
    _ =
      ∫ u in Ioc (0 : ℝ) 1,
        atkinsonComplexShiftedCompleteRowIntegrand n j u := by
          rw [← MeasureTheory.integral_const_mul]
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
          unfold atkinsonComplexShiftedCompleteRowIntegrand
          simp [Nat.add_assoc, add_left_comm, add_comm]
    _ =
      ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
        exact atkinsonComplexShiftedCompleteRowIntegrand_eq_resonantCarrier_singlePacket n j u

private lemma atkinsonShiftedCompleteCell_eq_rowIntegral (n j : ℕ) (hj : 1 ≤ j) :
    atkinsonShiftedCompleteCell n j
      = ∫ u in Ioc (0 : ℝ) 1, atkinsonShiftedCompleteRowIntegrand n j u := by
  have hblock :=
    Aristotle.StationaryPhaseMainMode.hardyCos_completeBlock_eq_common_blockParamIntegral
      (n + j) j hj (by omega)
  unfold atkinsonShiftedCompleteCell
  calc
    atkinsonModeWeight n *
        ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)), hardyCos n t
      =
    atkinsonModeWeight n *
        ∫ u in Ioc (0 : ℝ) 1,
          hardyCos n (blockCoord (n + j) u) * blockJacobian (n + j) u := by
            simpa [Nat.add_assoc, add_left_comm, add_comm] using congrArg (fun x => atkinsonModeWeight n * x) hblock
    _ =
      ∫ u in Ioc (0 : ℝ) 1,
        atkinsonModeWeight n *
          (hardyCos n (blockCoord (n + j) u) * blockJacobian (n + j) u) := by
            rw [MeasureTheory.integral_const_mul]
    _ = ∫ u in Ioc (0 : ℝ) 1, atkinsonShiftedCompleteRowIntegrand n j u := by
            simp [atkinsonShiftedCompleteRowIntegrand, mul_assoc]

private lemma atkinsonShiftedCompleteRow_eq_rowIntegral (M j : ℕ) (hj : 1 ≤ j) :
    atkinsonShiftedCompleteRow M j
      =
    ∫ u in Ioc (0 : ℝ) 1,
      ∑ n ∈ Finset.range M,
        if j ≤ n then atkinsonShiftedCompleteRowIntegrand n j u else 0 := by
  calc
    atkinsonShiftedCompleteRow M j
      =
    ∑ n ∈ Finset.range M,
      ∫ u in Ioc (0 : ℝ) 1,
        if j ≤ n then atkinsonShiftedCompleteRowIntegrand n j u else 0 := by
          unfold atkinsonShiftedCompleteRow
          refine Finset.sum_congr rfl ?_
          intro n hn
          by_cases hjn : j ≤ n
          · simpa [hjn] using atkinsonShiftedCompleteCell_eq_rowIntegral n j hj
          · simp [hjn]
    _ =
      ∫ u in Ioc (0 : ℝ) 1,
        ∑ n ∈ Finset.range M,
          if j ≤ n then atkinsonShiftedCompleteRowIntegrand n j u else 0 := by
            rw [MeasureTheory.integral_finset_sum]
            intro n hn
            by_cases hjn : j ≤ n
            · simpa [hjn] using
                (atkinsonShiftedCompleteRowIntegrand_continuous n j).integrableOn_Ioc
            · simp [hjn]

private noncomputable def atkinsonWeightedResonantBlockMode (k : ℕ) (u : ℝ) : ℂ :=
  (((atkinsonModeWeight k : ℝ) : ℂ)) * Aristotle.StationaryPhaseMainMode.blockMode k u

private lemma atkinsonWeightedResonantBlockMode_hasDerivAt (k : ℕ) (u : ℝ) :
    HasDerivAt (atkinsonWeightedResonantBlockMode k)
      (Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega k u : ℝ) : ℂ) *
        atkinsonWeightedResonantBlockMode k u) u := by
  have h :=
    (Aristotle.StationaryPhaseMainMode.blockMode_hasDerivAt k u).const_mul
      (((atkinsonModeWeight k : ℝ) : ℂ))
  unfold atkinsonWeightedResonantBlockMode
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

private lemma atkinsonWeightedResonantBlockMode_continuous (k : ℕ) :
    Continuous (atkinsonWeightedResonantBlockMode k) := by
  unfold atkinsonWeightedResonantBlockMode Aristotle.StationaryPhaseMainMode.blockMode
  exact continuous_const.mul
    ((HardyCosSmooth.continuous_hardyCosExp_complex k).comp (blockCoord_continuous k))

private noncomputable def atkinsonShiftedPacketPhase (k j : ℕ) (u : ℝ) : ℂ :=
  Complex.exp (Complex.I * ↑(blockCoord k u * atkinsonShiftedRelativePhase k j))

private noncomputable def atkinsonShiftedPacketOmega (k j : ℕ) (u : ℝ) : ℝ :=
  blockJacobian k u * atkinsonShiftedRelativePhase k j

private lemma atkinsonShiftedPacketPhase_hasDerivAt (k j : ℕ) (u : ℝ) :
    HasDerivAt (atkinsonShiftedPacketPhase k j)
      (Complex.I * ↑(atkinsonShiftedPacketOmega k j u) * atkinsonShiftedPacketPhase k j u) u := by
  have hinner :
      HasDerivAt (fun u => blockCoord k u * atkinsonShiftedRelativePhase k j)
        (blockJacobian k u * atkinsonShiftedRelativePhase k j) u := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (blockCoord_hasDerivAt k u).mul_const (atkinsonShiftedRelativePhase k j)
  have hcomplex :
      HasDerivAt (fun u => ((blockCoord k u * atkinsonShiftedRelativePhase k j : ℝ) : ℂ))
        (↑(blockJacobian k u * atkinsonShiftedRelativePhase k j)) u := hinner.ofReal_comp
  have hi :
      HasDerivAt
        (fun u => Complex.I * ((blockCoord k u * atkinsonShiftedRelativePhase k j : ℝ) : ℂ))
        (Complex.I * ↑(atkinsonShiftedPacketOmega k j u)) u := hcomplex.const_mul Complex.I
  unfold atkinsonShiftedPacketPhase
  simpa [atkinsonShiftedPacketOmega, mul_assoc, mul_left_comm, mul_comm] using
    (Complex.hasDerivAt_exp _).comp u hi

private lemma atkinsonShiftedPacketPhase_continuous (k j : ℕ) :
    Continuous (atkinsonShiftedPacketPhase k j) := by
  exact continuous_iff_continuousAt.2 fun u =>
    (atkinsonShiftedPacketPhase_hasDerivAt k j u).continuousAt

private lemma atkinsonShiftedPacketOmega_hasDerivAt (k j : ℕ) (u : ℝ) :
    HasDerivAt (atkinsonShiftedPacketOmega k j)
      (4 * Real.pi * atkinsonShiftedRelativePhase k j) u := by
  unfold atkinsonShiftedPacketOmega blockJacobian
  convert (((hasDerivAt_id u).const_add ((k : ℝ) + 1)).const_mul (4 * Real.pi)).mul_const
      (atkinsonShiftedRelativePhase k j) using 1 <;> ring

private lemma atkinson_deriv_shiftedPacketOmega (k j : ℕ) (u : ℝ) :
    deriv (atkinsonShiftedPacketOmega k j) u = 4 * Real.pi * atkinsonShiftedRelativePhase k j := by
  rw [(atkinsonShiftedPacketOmega_hasDerivAt k j u).deriv]

private lemma atkinson_differentiable_shiftedPacketOmega (k j : ℕ) :
    Differentiable ℝ (atkinsonShiftedPacketOmega k j) := by
  intro u
  exact (atkinsonShiftedPacketOmega_hasDerivAt k j u).differentiableAt

private lemma atkinson_continuous_deriv_shiftedPacketOmega (k j : ℕ) :
    Continuous (deriv (atkinsonShiftedPacketOmega k j)) := by
  have hderiv :
      deriv (atkinsonShiftedPacketOmega k j)
        = fun _ : ℝ => 4 * Real.pi * atkinsonShiftedRelativePhase k j := by
    funext u
    rw [atkinson_deriv_shiftedPacketOmega]
  rw [hderiv]
  exact continuous_const

private lemma atkinson_norm_shiftedPacketPhase (k j : ℕ) (u : ℝ) :
    ‖atkinsonShiftedPacketPhase k j u‖ = 1 := by
  unfold atkinsonShiftedPacketPhase
  simpa using Complex.norm_exp_I_mul_ofReal (blockCoord k u * atkinsonShiftedRelativePhase k j)

private lemma atkinsonShiftedRelativePhase_pos (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    0 < atkinsonShiftedRelativePhase k j := by
  rw [atkinsonShiftedRelativePhase_eq_sub_logs]
  have hsmall_pos : 0 < (((k - j : ℕ) : ℝ) + 1) := by positivity
  have hlt : (((k - j : ℕ) : ℝ) + 1) < (k : ℝ) + 1 := by
    exact_mod_cast (show k - j + 1 < k + 1 by omega)
  exact sub_pos.mpr (Real.log_lt_log hsmall_pos hlt)

private noncomputable def atkinsonShiftedSinglePrimitive (k j : ℕ) (u : ℝ) : ℂ :=
  (-Complex.I) *
    (((atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j : ℝ) : ℂ)) *
      atkinsonShiftedPacketPhase k j u

private lemma atkinsonShiftedSinglePrimitive_hasDerivAt (k j : ℕ) (hj : 1 ≤ j)
    (hjk : j ≤ k) (u : ℝ) :
    HasDerivAt (atkinsonShiftedSinglePrimitive k j)
      (((blockJacobian k u : ℂ)) * atkinsonShiftedSinglePacket k j u) u := by
  unfold atkinsonShiftedSinglePrimitive atkinsonShiftedSinglePacket
  have hphase_ne : atkinsonShiftedRelativePhase k j ≠ 0 := by
    exact ne_of_gt (atkinsonShiftedRelativePhase_pos k j hj hjk)
  have hterm :=
    (atkinsonShiftedPacketPhase_hasDerivAt k j u).const_mul
      (((-Complex.I) *
        (((atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j : ℝ) : ℂ))))
  have hquot :
      (atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j) *
          atkinsonShiftedPacketOmega k j u
        =
      atkinsonShiftedRelativeWeight k j * blockJacobian k u := by
    unfold atkinsonShiftedPacketOmega
    field_simp [hphase_ne]
  have hquotC :
      ((((atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j) *
            atkinsonShiftedPacketOmega k j u : ℝ)) : ℂ)
        =
      ((((atkinsonShiftedRelativeWeight k j * blockJacobian k u : ℝ)) : ℂ)) := by
    exact congrArg (fun x : ℝ => (x : ℂ)) hquot
  have hderiv :
      (-Complex.I * (((atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j : ℝ) : ℂ))) *
          (Complex.I * ↑(atkinsonShiftedPacketOmega k j u) * atkinsonShiftedPacketPhase k j u)
        =
      (((blockJacobian k u : ℂ)) * atkinsonShiftedSinglePacket k j u) := by
    have hI : (-Complex.I) * Complex.I = 1 := by norm_num
    calc
      (-Complex.I * (((atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j : ℝ) : ℂ))) *
          (Complex.I * ↑(atkinsonShiftedPacketOmega k j u) * atkinsonShiftedPacketPhase k j u)
          =
        ((-Complex.I * Complex.I) *
          ((((atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j : ℝ) : ℂ)) *
            (((atkinsonShiftedPacketOmega k j u : ℝ) : ℂ)) * atkinsonShiftedPacketPhase k j u)) := by
            ring
      _ =
        ((((atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j) *
            atkinsonShiftedPacketOmega k j u : ℝ) : ℂ) *
          atkinsonShiftedPacketPhase k j u) := by
            rw [hI]
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ =
        ((((atkinsonShiftedRelativeWeight k j * blockJacobian k u : ℝ)) : ℂ) *
          atkinsonShiftedPacketPhase k j u) := by
            rw [hquotC]
      _ = (((blockJacobian k u : ℂ)) * atkinsonShiftedSinglePacket k j u) := by
            unfold atkinsonShiftedSinglePacket atkinsonShiftedPacketPhase
            simp [mul_assoc, mul_left_comm, mul_comm]
  exact hterm.congr_deriv hderiv

private lemma atkinsonShiftedSinglePrimitive_continuous (k j : ℕ) :
    Continuous (atkinsonShiftedSinglePrimitive k j) := by
  unfold atkinsonShiftedSinglePrimitive
  simpa [mul_assoc] using
    ((continuous_const : Continuous fun _ : ℝ =>
      (-Complex.I) * (((atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j : ℝ) : ℂ))).mul
        (atkinsonShiftedPacketPhase_continuous k j))

private lemma atkinsonResonantShiftedRowSummand_continuous (n j : ℕ) :
    Continuous (atkinsonResonantShiftedRowSummand n j) := by
  unfold atkinsonResonantShiftedRowSummand atkinsonResonantBlockCarrier
    atkinsonShiftedSinglePacket
  exact ((continuous_const.mul
      ((HardyCosSmooth.continuous_hardyCosExp_complex (n + j)).comp
        (blockCoord_continuous (n + j)))).mul
      (Complex.continuous_ofReal.comp (blockJacobian_continuous (n + j)))).mul
      (continuous_const.mul (atkinsonShiftedPacketPhase_continuous (n + j) j))

private lemma atkinsonBlockOmega_continuous (k : ℕ) :
    Continuous (Aristotle.StationaryPhaseMainMode.blockOmega k) := by
  unfold Aristotle.StationaryPhaseMainMode.blockOmega
  exact (((continuous_iff_continuousAt.mpr
    (fun t => (ThetaDerivMonotone.thetaDeriv_hasDerivAt t).continuousAt)).comp
      (blockCoord_continuous k)).sub continuous_const).mul
    (blockJacobian_continuous k)

private noncomputable def atkinsonResonantShiftedBoundaryTerm (n j : ℕ) : ℂ :=
  atkinsonWeightedResonantBlockMode (n + j) 1 * atkinsonShiftedSinglePrimitive (n + j) j 1
    - atkinsonWeightedResonantBlockMode (n + j) 0 * atkinsonShiftedSinglePrimitive (n + j) j 0

private noncomputable def atkinsonResonantShiftedCorrectionTerm (n j : ℕ) : ℂ :=
  ∫ u in (0 : ℝ)..1,
    (Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega (n + j) u : ℝ) : ℂ) *
      atkinsonWeightedResonantBlockMode (n + j) u) *
        atkinsonShiftedSinglePrimitive (n + j) j u

private theorem atkinsonResonantShiftedCell_eq_boundary_minus_correction (n j : ℕ) (hj : 1 ≤ j) :
    ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u
      =
    atkinsonResonantShiftedBoundaryTerm n j - atkinsonResonantShiftedCorrectionTerm n j := by
  have hjk : j ≤ n + j := by omega
  let k : ℕ := n + j
  let f : ℝ → ℂ := atkinsonWeightedResonantBlockMode k
  let G : ℝ → ℂ := atkinsonShiftedSinglePrimitive k j
  have hG_deriv :
      ∀ u ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt G (((blockJacobian k u : ℂ)) * atkinsonShiftedSinglePacket k j u) u := by
    intro u hu
    exact atkinsonShiftedSinglePrimitive_hasDerivAt k j hj hjk u
  have hf_deriv :
      ∀ u ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt f
          (Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega k u : ℝ) : ℂ) * f u) u := by
    intro u hu
    exact atkinsonWeightedResonantBlockMode_hasDerivAt k u
  have hf'_int :
      IntervalIntegrable
        (fun u =>
          Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega k u : ℝ) : ℂ) * f u)
        volume (0 : ℝ) 1 := by
    have hcont : Continuous fun u : ℝ =>
        Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega k u : ℝ) : ℂ) * f u := by
      exact (continuous_const.mul
        (Complex.continuous_ofReal.comp (atkinsonBlockOmega_continuous k))).mul
        (atkinsonWeightedResonantBlockMode_continuous k)
    simpa [f] using hcont.intervalIntegrable (0 : ℝ) 1
  have hG'_int :
      IntervalIntegrable
        (fun u => (((blockJacobian k u : ℂ)) * atkinsonShiftedSinglePacket k j u))
        volume (0 : ℝ) 1 := by
    have hcont : Continuous fun u : ℝ =>
        (((blockJacobian k u : ℂ)) * atkinsonShiftedSinglePacket k j u) := by
      exact (Complex.continuous_ofReal.comp (blockJacobian_continuous k)).mul
        (continuous_const.mul (atkinsonShiftedPacketPhase_continuous k j))
    simpa [atkinsonShiftedSinglePacket] using hcont.intervalIntegrable (0 : ℝ) 1
  have hibp :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hf_deriv hG_deriv hf'_int hG'_int
  have hrewrite :
      (fun u => f u * (((blockJacobian k u : ℂ)) * atkinsonShiftedSinglePacket k j u))
        =
      fun u => atkinsonResonantShiftedRowSummand n j u := by
        funext u
        dsimp [f, G, k]
        unfold atkinsonWeightedResonantBlockMode
          atkinsonResonantShiftedRowSummand atkinsonResonantBlockCarrier
          Aristotle.StationaryPhaseMainMode.blockMode
        simp [mul_assoc, mul_left_comm, mul_comm]
  rw [hrewrite] at hibp
  calc
    ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u
        = ∫ u in (0 : ℝ)..1, atkinsonResonantShiftedRowSummand n j u := by
            rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    _ =
      f 1 * G 1 - f 0 * G 0
        - ∫ u in (0 : ℝ)..1,
            (Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega k u : ℝ) : ℂ) * f u) *
              G u := by
                simpa [f, G] using hibp
    _ =
      atkinsonResonantShiftedBoundaryTerm n j - atkinsonResonantShiftedCorrectionTerm n j := by
        unfold atkinsonResonantShiftedBoundaryTerm atkinsonResonantShiftedCorrectionTerm
        simp [f, G, k]

private theorem atkinsonResonantShiftedRowIntegral_eq_boundary_correction_sum
    (j M : ℕ) (hj : 1 ≤ j) :
    ∫ u in Ioc (0 : ℝ) 1,
      ∑ n ∈ Finset.range M,
        (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0)
      =
    ∑ n ∈ Finset.range M,
      (if j ≤ n then
        atkinsonResonantShiftedBoundaryTerm n j - atkinsonResonantShiftedCorrectionTerm n j
      else 0) := by
  calc
    ∫ u in Ioc (0 : ℝ) 1,
        ∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0)
        =
      ∑ n ∈ Finset.range M,
        ∫ u in Ioc (0 : ℝ) 1,
          (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0) := by
            rw [MeasureTheory.integral_finset_sum]
            intro n hn
            by_cases hjn : j ≤ n
            · simpa [hjn] using (atkinsonResonantShiftedRowSummand_continuous n j).integrableOn_Ioc
            · simp [hjn]
    _ =
      ∑ n ∈ Finset.range M,
        (if j ≤ n then
          atkinsonResonantShiftedBoundaryTerm n j - atkinsonResonantShiftedCorrectionTerm n j
        else 0) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            by_cases hjn : j ≤ n
            · simpa [hjn] using atkinsonResonantShiftedCell_eq_boundary_minus_correction n j hj
            · simp [hjn]

private lemma atkinsonWeightedResonantBlockMode_norm (k : ℕ) (u : ℝ) :
    ‖atkinsonWeightedResonantBlockMode k u‖ = atkinsonModeWeight k := by
  unfold atkinsonWeightedResonantBlockMode Aristotle.StationaryPhaseMainMode.blockMode
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_hardyCosExp]
  simp [abs_of_nonneg (atkinsonModeWeight_nonneg k)]

private lemma atkinsonWeightedResonantBlockMode_deriv_norm (k : ℕ) (u : ℝ) :
    ‖Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega k u : ℝ) : ℂ) *
        atkinsonWeightedResonantBlockMode k u‖
      = |Aristotle.StationaryPhaseMainMode.blockOmega k u| * atkinsonModeWeight k := by
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    atkinsonWeightedResonantBlockMode_norm]

private lemma atkinsonWeightedResonantBlockMode_one_eq_next_zero_shift (k : ℕ) :
    atkinsonWeightedResonantBlockMode k 1
      =
      atkinsonWeightedResonantBlockMode (k + 1) 0 *
        ((((atkinsonShiftedRelativeWeight (k + 1) 1 : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ↑(hardyStart (k + 1) * atkinsonShiftedRelativePhase (k + 1) 1))) := by
  simpa [atkinsonWeightedResonantBlockMode, Aristotle.StationaryPhaseMainMode.blockMode,
    atkinsonShiftedSinglePacket, blockCoord_zero, blockCoord_one] using
    (atkinsonWeighted_hardyCosExp_eq_resonant_times_shiftedPacket (k + 1) 1 0)

private lemma atkinsonShiftedRelativeWeight_step (k j : ℕ) (hjk : j ≤ k) :
    atkinsonShiftedRelativeWeight (k + 1) 1 * atkinsonShiftedRelativeWeight k j
      = atkinsonShiftedRelativeWeight (k + 1) (j + 1) := by
  unfold atkinsonShiftedRelativeWeight
  have hk : k + 1 - 1 = k := by omega
  have hkj : k + 1 - (j + 1) = k - j := by omega
  rw [show atkinsonModeWeight (k + 1 - 1) = atkinsonModeWeight k by simpa [hk]]
  rw [show atkinsonModeWeight (k + 1 - (j + 1)) = atkinsonModeWeight (k - j) by simpa [hkj]]
  field_simp [atkinsonModeWeight_ne_zero k, atkinsonModeWeight_ne_zero (k + 1)]

private lemma atkinsonShiftedRelativePhase_step (k j : ℕ) (hjk : j ≤ k) :
    atkinsonShiftedRelativePhase (k + 1) 1 + atkinsonShiftedRelativePhase k j
      = atkinsonShiftedRelativePhase (k + 1) (j + 1) := by
  have hA_ne : (((k : ℝ) + 2) / ((k : ℝ) + 1)) ≠ 0 := by positivity
  have hB_ne : (((k : ℝ) + 1) / (((k - j : ℕ) : ℝ) + 1)) ≠ 0 := by positivity
  have hphi1 :
      atkinsonShiftedRelativePhase (k + 1) 1 = Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1)) := by
    unfold atkinsonShiftedRelativePhase
    norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
  have hmul :
      (((k : ℝ) + 2) / ((k : ℝ) + 1)) * (((k : ℝ) + 1) / (((k - j : ℕ) : ℝ) + 1))
        = (((k : ℝ) + 2) / (((k - j : ℕ) : ℝ) + 1)) := by
    field_simp [show ((k : ℝ) + 1) ≠ 0 by positivity]
  calc
    atkinsonShiftedRelativePhase (k + 1) 1 + atkinsonShiftedRelativePhase k j
        = Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1))
            + Real.log (((k : ℝ) + 1) / (((k - j : ℕ) : ℝ) + 1)) := by
            rw [hphi1]
            simp [atkinsonShiftedRelativePhase]
    _ = Real.log ((((k : ℝ) + 2) / ((k : ℝ) + 1)) *
          (((k : ℝ) + 1) / (((k - j : ℕ) : ℝ) + 1))) := by
            rw [Real.log_mul hA_ne hB_ne]
    _ = Real.log (((k : ℝ) + 2) / (((k - j : ℕ) : ℝ) + 1)) := by rw [hmul]
    _ = atkinsonShiftedRelativePhase (k + 1) (j + 1) := by
          have hkj : k + 1 - (j + 1) = k - j := by omega
          have hk2 : ((k : ℝ) + 2) = ((k : ℝ) + (1 + 1 : ℝ)) := by ring
          unfold atkinsonShiftedRelativePhase
          simp [hkj, Nat.cast_add, add_assoc, add_comm, add_left_comm, hk2]

private lemma atkinsonWeightedResonantBlockMode_one_mul_shiftedSinglePrimitive_step
    (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    atkinsonWeightedResonantBlockMode k 1 * atkinsonShiftedSinglePrimitive k j 1
      =
      (((atkinsonShiftedRelativePhase (k + 1) (j + 1) / atkinsonShiftedRelativePhase k j : ℝ) : ℂ)) *
        (atkinsonWeightedResonantBlockMode (k + 1) 0 *
          atkinsonShiftedSinglePrimitive (k + 1) (j + 1) 0) := by
  have hphase_pos : 0 < atkinsonShiftedRelativePhase k j := atkinsonShiftedRelativePhase_pos k j hj hjk
  have hphase_next_pos : 0 < atkinsonShiftedRelativePhase (k + 1) (j + 1) := by
    exact atkinsonShiftedRelativePhase_pos (k + 1) (j + 1)
      (Nat.succ_le_succ (Nat.zero_le j)) (Nat.succ_le_succ hjk)
  have hweight :
      atkinsonShiftedRelativeWeight (k + 1) 1 * atkinsonShiftedRelativeWeight k j
        = atkinsonShiftedRelativeWeight (k + 1) (j + 1) :=
    atkinsonShiftedRelativeWeight_step k j hjk
  have hphase :
      atkinsonShiftedRelativePhase (k + 1) 1 + atkinsonShiftedRelativePhase k j
        = atkinsonShiftedRelativePhase (k + 1) (j + 1) :=
    atkinsonShiftedRelativePhase_step k j hjk
  have hcoeff :
      (((atkinsonShiftedRelativeWeight (k + 1) 1 * atkinsonShiftedRelativeWeight k j
          / atkinsonShiftedRelativePhase k j : ℝ) : ℂ))
        =
      (((atkinsonShiftedRelativePhase (k + 1) (j + 1) / atkinsonShiftedRelativePhase k j : ℝ) : ℂ)) *
        (((atkinsonShiftedRelativeWeight (k + 1) (j + 1)
            / atkinsonShiftedRelativePhase (k + 1) (j + 1) : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [hweight]
    field_simp [ne_of_gt hphase_pos, ne_of_gt hphase_next_pos]
  have harg :
      hardyStart (k + 1) * atkinsonShiftedRelativePhase (k + 1) 1
        + hardyStart (k + 1) * atkinsonShiftedRelativePhase k j
        = hardyStart (k + 1) * atkinsonShiftedRelativePhase (k + 1) (j + 1) := by
    rw [← mul_add, hphase]
  have hargC :
      Complex.I * ↑(hardyStart (k + 1) * atkinsonShiftedRelativePhase (k + 1) 1)
        + Complex.I * ↑(hardyStart (k + 1) * atkinsonShiftedRelativePhase k j)
        =
      Complex.I * ↑(hardyStart (k + 1) * atkinsonShiftedRelativePhase (k + 1) (j + 1)) := by
    calc
      Complex.I * ↑(hardyStart (k + 1) * atkinsonShiftedRelativePhase (k + 1) 1)
          + Complex.I * ↑(hardyStart (k + 1) * atkinsonShiftedRelativePhase k j)
          =
        Complex.I * ↑(hardyStart (k + 1) * atkinsonShiftedRelativePhase (k + 1) 1
          + hardyStart (k + 1) * atkinsonShiftedRelativePhase k j) := by
            simp [mul_add, add_mul]
      _ = Complex.I * ↑(hardyStart (k + 1) * atkinsonShiftedRelativePhase (k + 1) (j + 1)) := by
            rw [harg]
  have hexp :
      Complex.exp (Complex.I * ↑(hardyStart (k + 1) * atkinsonShiftedRelativePhase (k + 1) 1)) *
          Complex.exp (Complex.I * ↑(hardyStart (k + 1) * atkinsonShiftedRelativePhase k j))
        =
      Complex.exp (Complex.I * ↑(hardyStart (k + 1) * atkinsonShiftedRelativePhase (k + 1) (j + 1))) := by
    rw [← Complex.exp_add, hargC]
  have hpacket1 :
      Complex.exp (Complex.I * ↑(hardyStart (k + 1) * atkinsonShiftedRelativePhase (k + 1) 1)) *
          atkinsonShiftedPacketPhase k j 1
        =
      Complex.exp (Complex.I * ↑(hardyStart (k + 1) * atkinsonShiftedRelativePhase (k + 1) (j + 1))) := by
    unfold atkinsonShiftedPacketPhase
    simpa [blockCoord_one] using hexp
  rw [atkinsonWeightedResonantBlockMode_one_eq_next_zero_shift]
  unfold atkinsonShiftedSinglePrimitive
  calc
    (atkinsonWeightedResonantBlockMode (k + 1) 0 *
          ((((atkinsonShiftedRelativeWeight (k + 1) 1 : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ↑(hardyStart (k + 1) * atkinsonShiftedRelativePhase (k + 1) 1)))) *
        ((-Complex.I) * (((atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j : ℝ) : ℂ)) *
          atkinsonShiftedPacketPhase k j 1)
        =
      atkinsonWeightedResonantBlockMode (k + 1) 0 *
        (((-Complex.I) * (((atkinsonShiftedRelativeWeight (k + 1) 1 * atkinsonShiftedRelativeWeight k j
              / atkinsonShiftedRelativePhase k j : ℝ) : ℂ))) *
          (Complex.exp (Complex.I * ↑(hardyStart (k + 1) * atkinsonShiftedRelativePhase (k + 1) 1)) *
            atkinsonShiftedPacketPhase k j 1)) := by
            unfold atkinsonShiftedPacketPhase
            simp [blockCoord_one]
            ring
    _ =
      atkinsonWeightedResonantBlockMode (k + 1) 0 *
        (((-Complex.I) * (((atkinsonShiftedRelativeWeight (k + 1) 1 * atkinsonShiftedRelativeWeight k j
              / atkinsonShiftedRelativePhase k j : ℝ) : ℂ))) *
          Complex.exp (Complex.I * ↑(hardyStart (k + 1) * atkinsonShiftedRelativePhase (k + 1) (j + 1)))) := by
            rw [hpacket1]
    _ =
      atkinsonWeightedResonantBlockMode (k + 1) 0 *
        ((((atkinsonShiftedRelativePhase (k + 1) (j + 1) / atkinsonShiftedRelativePhase k j : ℝ) : ℂ)) *
          (((-Complex.I) * (((atkinsonShiftedRelativeWeight (k + 1) (j + 1)
                / atkinsonShiftedRelativePhase (k + 1) (j + 1) : ℝ) : ℂ))) *
            Complex.exp (Complex.I * ↑(hardyStart (k + 1) * atkinsonShiftedRelativePhase (k + 1) (j + 1))))) := by
            rw [hcoeff]
            ring
    _ =
      (((atkinsonShiftedRelativePhase (k + 1) (j + 1) / atkinsonShiftedRelativePhase k j : ℝ) : ℂ)) *
        (atkinsonWeightedResonantBlockMode (k + 1) 0 *
          ((-Complex.I) *
              (((atkinsonShiftedRelativeWeight (k + 1) (j + 1)
                  / atkinsonShiftedRelativePhase (k + 1) (j + 1) : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ↑(hardyStart (k + 1) * atkinsonShiftedRelativePhase (k + 1) (j + 1))))) := by
            ring
    _ =
      (((atkinsonShiftedRelativePhase (k + 1) (j + 1) / atkinsonShiftedRelativePhase k j : ℝ) : ℂ)) *
        (atkinsonWeightedResonantBlockMode (k + 1) 0 *
          atkinsonShiftedSinglePrimitive (k + 1) (j + 1) 0) := by
            unfold atkinsonShiftedSinglePrimitive atkinsonShiftedPacketPhase
            simp [blockCoord_zero]

private noncomputable def atkinsonUpperBoundaryStepCoeff (n j : ℕ) : ℝ :=
  atkinsonShiftedRelativePhase (n + j + 1) (j + 1) / atkinsonShiftedRelativePhase (n + j) j

private lemma atkinsonUpperBoundaryStepCoeff_pos (n j : ℕ) (hj : 1 ≤ j) :
    0 < atkinsonUpperBoundaryStepCoeff n j := by
  unfold atkinsonUpperBoundaryStepCoeff
  have hden :
      0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j hj (by omega)
  have hnum :
      0 < atkinsonShiftedRelativePhase (n + j + 1) (j + 1) := by
    exact atkinsonShiftedRelativePhase_pos (n + j + 1) (j + 1)
      (Nat.succ_le_succ (Nat.zero_le j)) (by omega)
  exact div_pos hnum hden

private lemma atkinsonUpperBoundaryStepCoeff_nonneg (n j : ℕ) (hj : 1 ≤ j) :
    0 ≤ atkinsonUpperBoundaryStepCoeff n j :=
  (atkinsonUpperBoundaryStepCoeff_pos n j hj).le

private lemma atkinsonShiftedRelativePhase_lower (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    (j : ℝ) / ((k : ℝ) + 1) ≤ atkinsonShiftedRelativePhase k j := by
  let x : ℝ := ((k : ℝ) + 1) / ((((k - j : ℕ) : ℝ) + 1))
  have hx_pos : 0 < x := by
    dsimp [x]
    positivity
  have hbase : 1 - x⁻¹ ≤ Real.log x := Real.one_sub_inv_le_log_of_pos hx_pos
  have hk1_ne : (k : ℝ) + 1 ≠ 0 := by positivity
  have hlog : Real.log x = atkinsonShiftedRelativePhase k j := by
    simp [x, atkinsonShiftedRelativePhase]
  have hleft : 1 - x⁻¹ = (j : ℝ) / ((k : ℝ) + 1) := by
    have hsub : ((((k - j : ℕ) : ℝ) + 1)) = (k : ℝ) + 1 - j := by
      rw [Nat.cast_sub hjk]
      ring
    dsimp [x]
    rw [inv_div, hsub]
    field_simp [hk1_ne]
    ring
  simpa [hleft, hlog] using hbase

private lemma atkinsonShiftedRelativePhase_upper (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    atkinsonShiftedRelativePhase k j ≤ (j : ℝ) / ((((k - j : ℕ) : ℝ) + 1)) := by
  let x : ℝ := ((k : ℝ) + 1) / ((((k - j : ℕ) : ℝ) + 1))
  have hx_pos : 0 < x := by
    dsimp [x]
    positivity
  have hlog : Real.log x = atkinsonShiftedRelativePhase k j := by
    simp [x, atkinsonShiftedRelativePhase]
  have hright : x - 1 = (j : ℝ) / ((((k - j : ℕ) : ℝ) + 1)) := by
    have hden_ne : ((((k - j : ℕ) : ℝ) + 1) : ℝ) ≠ 0 := by positivity
    dsimp [x]
    field_simp [hden_ne]
    have hcast :
        (((k : ℕ) : ℝ) + 1) - ((((k - j : ℕ) : ℝ) + 1)) = (j : ℝ) := by
      rw [Nat.cast_sub hjk]
      ring
    linarith
  calc
    atkinsonShiftedRelativePhase k j = Real.log x := by rw [hlog]
    _ ≤ x - 1 := by exact Real.log_le_sub_one_of_pos hx_pos
    _ = (j : ℝ) / ((((k - j : ℕ) : ℝ) + 1)) := hright

private lemma atkinsonShiftedRelativePhase_inv_upper
    (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    1 / atkinsonShiftedRelativePhase k j ≤ ((k : ℝ) + 1) / j := by
  have hphase_pos : 0 < atkinsonShiftedRelativePhase k j :=
    atkinsonShiftedRelativePhase_pos k j hj hjk
  have hden_pos : 0 < (j : ℝ) / ((k : ℝ) + 1) := by positivity
  calc
    1 / atkinsonShiftedRelativePhase k j ≤ 1 / ((j : ℝ) / ((k : ℝ) + 1)) := by
      exact one_div_le_one_div_of_le hden_pos (atkinsonShiftedRelativePhase_lower k j hj hjk)
    _ = ((k : ℝ) + 1) / j := by
      field_simp [show (j : ℝ) ≠ 0 by positivity, show ((k : ℝ) + 1) ≠ 0 by positivity]

private lemma atkinsonShiftedPacketOmega_lower (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1,
      4 * Real.pi * j ≤ atkinsonShiftedPacketOmega k j u := by
  intro u hu
  have hphase_lower := atkinsonShiftedRelativePhase_lower k j hj hjk
  have hphase_nonneg : 0 ≤ atkinsonShiftedRelativePhase k j := by
    exact le_of_lt (atkinsonShiftedRelativePhase_pos k j hj hjk)
  have hk1_ne : (k : ℝ) + 1 ≠ 0 := by positivity
  have hbase :
      4 * Real.pi * j
        ≤ (4 * Real.pi * ((k : ℝ) + 1)) * atkinsonShiftedRelativePhase k j := by
    have hmul :=
      mul_le_mul_of_nonneg_left hphase_lower
        (by positivity : 0 ≤ 4 * Real.pi * ((k : ℝ) + 1))
    have hrewrite :
        (4 * Real.pi * ((k : ℝ) + 1)) * ((j : ℝ) / ((k : ℝ) + 1))
          = 4 * Real.pi * j := by
      field_simp [hk1_ne]
    simpa [hrewrite] using hmul
  have hjac :
      (4 * Real.pi * ((k : ℝ) + 1)) * atkinsonShiftedRelativePhase k j
        ≤ atkinsonShiftedPacketOmega k j u := by
    unfold atkinsonShiftedPacketOmega
    have hbj :
        4 * Real.pi * ((k : ℝ) + 1) ≤ blockJacobian k u := by
      unfold blockJacobian
      nlinarith [hu.1, Real.pi_pos]
    exact mul_le_mul_of_nonneg_right hbj hphase_nonneg
  exact le_trans hbase hjac

private lemma atkinsonShiftedRelativeWeight_le_sqrt_two (k j : ℕ)
    (hj_half : j ≤ (k + 1) / 2) :
    atkinsonShiftedRelativeWeight k j ≤ Real.sqrt 2 := by
  have hjk : j ≤ k := by omega
  have hk1_pos : 0 < (k : ℝ) + 1 := by positivity
  have hden_pos : 0 < ((((k - j : ℕ) : ℝ) + 1)) := by positivity
  have hrepr :
      atkinsonShiftedRelativeWeight k j
        = Real.sqrt ((k : ℝ) + 1) / Real.sqrt ((((k - j : ℕ) : ℝ) + 1)) := by
    unfold atkinsonShiftedRelativeWeight atkinsonModeWeight
    rw [Real.rpow_neg hk1_pos.le, Real.rpow_neg hden_pos.le, div_eq_mul_inv, inv_inv,
      mul_comm, ← div_eq_mul_inv]
    rw [show ((k : ℝ) + 1) ^ (1 / 2 : ℝ) = Real.sqrt ((k : ℝ) + 1) by
          rw [Real.sqrt_eq_rpow]]
    rw [show ((((k - j : ℕ) : ℝ) + 1)) ^ (1 / 2 : ℝ)
          = Real.sqrt ((((k - j : ℕ) : ℝ) + 1)) by
          rw [Real.sqrt_eq_rpow]]
  have hmain :
      (k : ℝ) + 1 ≤ 2 * ((((k - j : ℕ) : ℝ) + 1)) := by
    have hsub : ((((k - j : ℕ) : ℝ) + 1)) = (k : ℝ) + 1 - j := by
      rw [Nat.cast_sub hjk]
      ring
    have htwo : 2 * j ≤ k + 1 := by omega
    have htwo' : (2 : ℝ) * j ≤ (k : ℝ) + 1 := by
      exact_mod_cast htwo
    have hj_half'' : (j : ℝ) ≤ ((k : ℝ) + 1) / 2 := by
      nlinarith
    linarith
  have hsqrt :
      Real.sqrt ((k : ℝ) + 1)
        ≤ Real.sqrt 2 * Real.sqrt ((((k - j : ℕ) : ℝ) + 1)) := by
    have h1 :
        Real.sqrt ((k : ℝ) + 1)
          ≤ Real.sqrt (2 * ((((k - j : ℕ) : ℝ) + 1))) := by
      exact Real.sqrt_le_sqrt hmain
    have h2 :
        Real.sqrt (2 * ((((k - j : ℕ) : ℝ) + 1)))
          = Real.sqrt 2 * Real.sqrt ((((k - j : ℕ) : ℝ) + 1)) := by
      rw [Real.sqrt_mul (by positivity)]
    exact h1.trans_eq h2
  have hden_sqrt_pos : 0 < Real.sqrt ((((k - j : ℕ) : ℝ) + 1)) := by positivity
  rw [hrepr]
  exact (div_le_iff₀ hden_sqrt_pos).2 hsqrt

private lemma atkinsonShiftedRelativeWeight_nonneg (k j : ℕ) :
    0 ≤ atkinsonShiftedRelativeWeight k j := by
  unfold atkinsonShiftedRelativeWeight
  exact div_nonneg (atkinsonModeWeight_nonneg (k - j)) (atkinsonModeWeight_nonneg k)

private lemma atkinsonShiftedSinglePrimitive_norm
    (k j : ℕ) (u : ℝ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    ‖atkinsonShiftedSinglePrimitive k j u‖ =
      atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j := by
  have hphase_pos : 0 < atkinsonShiftedRelativePhase k j :=
    atkinsonShiftedRelativePhase_pos k j hj hjk
  have hphase_nonneg : 0 ≤ atkinsonShiftedRelativePhase k j := le_of_lt hphase_pos
  have hweight_nonneg : 0 ≤ atkinsonShiftedRelativeWeight k j :=
    atkinsonShiftedRelativeWeight_nonneg k j
  unfold atkinsonShiftedSinglePrimitive
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  have habs :
      |atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j| =
        atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j := by
    exact abs_of_nonneg (div_nonneg hweight_nonneg hphase_nonneg)
  rw [habs]
  unfold atkinsonShiftedPacketPhase
  rw [Complex.norm_exp]
  simp

private lemma atkinsonShiftedSinglePrimitive_norm_bound (k j : ℕ)
    (hj : 1 ≤ j) (hj_half : j ≤ (k + 1) / 2) (u : ℝ) :
    ‖atkinsonShiftedSinglePrimitive k j u‖ ≤ Real.sqrt 2 * (((k : ℝ) + 1) / j) := by
  have hjk : j ≤ k := by omega
  have hphase_pos : 0 < atkinsonShiftedRelativePhase k j :=
    atkinsonShiftedRelativePhase_pos k j hj hjk
  have hweight :
      atkinsonShiftedRelativeWeight k j ≤ Real.sqrt 2 := by
    exact atkinsonShiftedRelativeWeight_le_sqrt_two k j hj_half
  have hphase_lower :
      (j : ℝ) / ((k : ℝ) + 1) ≤ atkinsonShiftedRelativePhase k j :=
    atkinsonShiftedRelativePhase_lower k j hj hjk
  have hcoeff :
      atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j
        ≤ Real.sqrt 2 * (((k : ℝ) + 1) / j) := by
    refine (div_le_iff₀ hphase_pos).2 ?_
    have htmp :
        Real.sqrt 2
          ≤ Real.sqrt 2 * ((((k : ℝ) + 1) / j) * atkinsonShiftedRelativePhase k j) := by
      have hmul :=
        mul_le_mul_of_nonneg_left hphase_lower
          (by positivity : 0 ≤ Real.sqrt 2 * (((k : ℝ) + 1) / j))
      have hrewrite :
          (Real.sqrt 2 * (((k : ℝ) + 1) / j)) * ((j : ℝ) / ((k : ℝ) + 1))
            = Real.sqrt 2 := by
        field_simp [show (j : ℝ) ≠ 0 by positivity,
          show ((k : ℝ) + 1) ≠ 0 by positivity]
      simpa [mul_assoc, hrewrite] using hmul
    exact le_trans hweight <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using htmp
  calc
    ‖(-Complex.I) * (((atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j : ℝ) : ℂ)) *
        atkinsonShiftedPacketPhase k j u‖
        = atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, atkinson_norm_shiftedPacketPhase]
            simp [div_nonneg, atkinsonShiftedRelativeWeight_nonneg k j, le_of_lt hphase_pos]
    _ ≤ Real.sqrt 2 * (((k : ℝ) + 1) / j) := hcoeff

private lemma atkinsonLowerBoundaryTerm_norm
    (n j : ℕ) (hj : 1 ≤ j) :
    ‖atkinsonWeightedResonantBlockMode (n + j) 0 * atkinsonShiftedSinglePrimitive (n + j) j 0‖
      =
    atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + j) j := by
  have hjk : j ≤ n + j := by omega
  have hphase_pos :
      0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j hj hjk
  have hphase_nonneg :
      0 ≤ atkinsonShiftedRelativePhase (n + j) j := le_of_lt hphase_pos
  have hweight_nonneg :
      0 ≤ atkinsonShiftedRelativeWeight (n + j) j :=
    atkinsonShiftedRelativeWeight_nonneg (n + j) j
  have hmul :
      atkinsonModeWeight (n + j) * atkinsonShiftedRelativeWeight (n + j) j
        = atkinsonModeWeight n := by
    simpa using atkinsonModeWeight_mul_shiftedRelativeWeight (n + j) j
  unfold atkinsonShiftedSinglePrimitive
  rw [norm_mul, atkinsonWeightedResonantBlockMode_norm]
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  have habs :
      |atkinsonShiftedRelativeWeight (n + j) j / atkinsonShiftedRelativePhase (n + j) j|
        =
      atkinsonShiftedRelativeWeight (n + j) j / atkinsonShiftedRelativePhase (n + j) j := by
    exact abs_of_nonneg (div_nonneg hweight_nonneg hphase_nonneg)
  rw [habs]
  unfold atkinsonShiftedPacketPhase
  rw [Complex.norm_exp]
  simp
  calc
    atkinsonModeWeight (n + j) *
        (atkinsonShiftedRelativeWeight (n + j) j /
          atkinsonShiftedRelativePhase (n + j) j)
      =
    (atkinsonModeWeight (n + j) * atkinsonShiftedRelativeWeight (n + j) j) /
        atkinsonShiftedRelativePhase (n + j) j := by
          field_simp [ne_of_gt hphase_pos]
    _ = atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + j) j := by rw [hmul]

private lemma atkinsonCorrectionIntegrand_norm
    (n j : ℕ) (u : ℝ) (hj : 1 ≤ j) :
    ‖((Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega (n + j) u : ℝ) : ℂ) *
          atkinsonWeightedResonantBlockMode (n + j) u) *
        atkinsonShiftedSinglePrimitive (n + j) j u)‖
      =
    |Aristotle.StationaryPhaseMainMode.blockOmega (n + j) u| *
      (atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + j) j) := by
  have hjk : j ≤ n + j := by omega
  have hphase_pos :
      0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j hj hjk
  have hmul :
      atkinsonModeWeight (n + j) * atkinsonShiftedRelativeWeight (n + j) j
        = atkinsonModeWeight n := by
    simpa using atkinsonModeWeight_mul_shiftedRelativeWeight (n + j) j
  rw [norm_mul, atkinsonShiftedSinglePrimitive_norm (n + j) j u hj hjk]
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, atkinsonWeightedResonantBlockMode_norm]
  simp
  calc
    |Aristotle.StationaryPhaseMainMode.blockOmega (n + j) u| *
        atkinsonModeWeight (n + j) *
          (atkinsonShiftedRelativeWeight (n + j) j /
            atkinsonShiftedRelativePhase (n + j) j)
        =
      |Aristotle.StationaryPhaseMainMode.blockOmega (n + j) u| *
        ((atkinsonModeWeight (n + j) * atkinsonShiftedRelativeWeight (n + j) j) /
          atkinsonShiftedRelativePhase (n + j) j) := by
            field_simp [ne_of_gt hphase_pos]
    _ = |Aristotle.StationaryPhaseMainMode.blockOmega (n + j) u| *
        (atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + j) j) := by
          rw [hmul]

private lemma atkinsonShiftedRelativePhase_mul_shiftedSinglePrimitive
    (k j : ℕ) (u : ℝ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    (((atkinsonShiftedRelativePhase k j : ℝ) : ℂ)) * atkinsonShiftedSinglePrimitive k j u
      = (-Complex.I) * atkinsonShiftedSinglePacket k j u := by
  unfold atkinsonShiftedSinglePrimitive atkinsonShiftedSinglePacket
  have hphase_pos : 0 < atkinsonShiftedRelativePhase k j :=
    atkinsonShiftedRelativePhase_pos k j hj hjk
  have hreal :
      atkinsonShiftedRelativePhase k j *
          (atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j)
        = atkinsonShiftedRelativeWeight k j := by
    field_simp [ne_of_gt hphase_pos]
  have hrealC :
      ((((atkinsonShiftedRelativePhase k j) *
          (atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j) : ℝ) : ℂ))
        =
      (((atkinsonShiftedRelativeWeight k j : ℝ) : ℂ)) := by
    exact congrArg (fun x : ℝ => (x : ℂ)) hreal
  calc
    (((atkinsonShiftedRelativePhase k j : ℝ) : ℂ)) *
        ((-Complex.I) *
          (((atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j : ℝ) : ℂ)) *
            atkinsonShiftedPacketPhase k j u)
        =
      (-Complex.I) *
        ((((atkinsonShiftedRelativePhase k j) *
            (atkinsonShiftedRelativeWeight k j / atkinsonShiftedRelativePhase k j) : ℝ) : ℂ)) *
          atkinsonShiftedPacketPhase k j u := by
            calc
              (((atkinsonShiftedRelativePhase k j : ℝ) : ℂ)) *
                  ((-Complex.I) *
                    (((atkinsonShiftedRelativeWeight k j /
                        atkinsonShiftedRelativePhase k j : ℝ) : ℂ)) *
                      atkinsonShiftedPacketPhase k j u)
                  =
                ((((atkinsonShiftedRelativePhase k j : ℝ) : ℂ)) * (-Complex.I) *
                    (((atkinsonShiftedRelativeWeight k j /
                        atkinsonShiftedRelativePhase k j : ℝ) : ℂ))) *
                  atkinsonShiftedPacketPhase k j u := by
                    simp [mul_assoc]
              _ =
                (((-Complex.I) * (((atkinsonShiftedRelativePhase k j : ℝ) : ℂ))) *
                    (((atkinsonShiftedRelativeWeight k j /
                        atkinsonShiftedRelativePhase k j : ℝ) : ℂ))) *
                  atkinsonShiftedPacketPhase k j u := by
                    rw [mul_comm (((atkinsonShiftedRelativePhase k j : ℝ) : ℂ)) (-Complex.I)]
              _ =
                (-Complex.I) *
                  ((((atkinsonShiftedRelativePhase k j : ℝ) : ℂ)) *
                    (((atkinsonShiftedRelativeWeight k j /
                        atkinsonShiftedRelativePhase k j : ℝ) : ℂ))) *
                  atkinsonShiftedPacketPhase k j u := by
                    simp [mul_assoc]
              _ =
                (-Complex.I) *
                  ((((atkinsonShiftedRelativePhase k j) *
                      (atkinsonShiftedRelativeWeight k j /
                        atkinsonShiftedRelativePhase k j) : ℝ) : ℂ)) *
                    atkinsonShiftedPacketPhase k j u := by
                      rw [← Complex.ofReal_mul]
    _ =
      (-Complex.I) *
        (((atkinsonShiftedRelativeWeight k j : ℝ) : ℂ)) *
          atkinsonShiftedPacketPhase k j u := by
            rw [hrealC]
    _ = (-Complex.I) * atkinsonShiftedSinglePacket k j u := by
          unfold atkinsonShiftedSinglePacket atkinsonShiftedPacketPhase
          ring

private noncomputable def atkinsonShiftedSingleBoundaryCore (n j : ℕ) : ℂ :=
  (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
    (atkinsonWeightedResonantBlockMode (n + j) 0 *
      atkinsonShiftedSinglePrimitive (n + j) j 0)

private lemma atkinsonShiftedSingleBoundaryCore_step
    (n j : ℕ) (hj : 1 ≤ j) :
    (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        (atkinsonWeightedResonantBlockMode (n + j) 1 *
          atkinsonShiftedSinglePrimitive (n + j) j 1)
      =
    atkinsonShiftedSingleBoundaryCore n (j + 1) := by
  have hjk : j ≤ n + j := by omega
  have hstep :=
    atkinsonWeightedResonantBlockMode_one_mul_shiftedSinglePrimitive_step (n + j) j hj hjk
  unfold atkinsonShiftedSingleBoundaryCore
  have hphase_pos : 0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j hj hjk
  calc
    (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          (atkinsonWeightedResonantBlockMode (n + j) 1 *
            atkinsonShiftedSinglePrimitive (n + j) j 1)
        =
      (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        ((((atkinsonShiftedRelativePhase (n + j + 1) (j + 1) /
            atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          (atkinsonWeightedResonantBlockMode (n + j + 1) 0 *
            atkinsonShiftedSinglePrimitive (n + j + 1) (j + 1) 0)) := by
            rw [hstep]
    _ =
      (((atkinsonShiftedRelativePhase (n + j + 1) (j + 1) : ℝ) : ℂ)) *
        (atkinsonWeightedResonantBlockMode (n + j + 1) 0 *
          atkinsonShiftedSinglePrimitive (n + j + 1) (j + 1) 0) := by
            calc
              (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                    ((((atkinsonShiftedRelativePhase (n + j + 1) (j + 1) /
                        atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                      (atkinsonWeightedResonantBlockMode (n + j + 1) 0 *
                        atkinsonShiftedSinglePrimitive (n + j + 1) (j + 1) 0))
                  =
                ((((atkinsonShiftedRelativePhase (n + j) j) *
                    (atkinsonShiftedRelativePhase (n + j + 1) (j + 1) /
                      atkinsonShiftedRelativePhase (n + j) j) : ℝ) : ℂ)) *
                  (atkinsonWeightedResonantBlockMode (n + j + 1) 0 *
                    atkinsonShiftedSinglePrimitive (n + j + 1) (j + 1) 0) := by
                      rw [← mul_assoc, ← Complex.ofReal_mul]
              _ =
                (((atkinsonShiftedRelativePhase (n + j + 1) (j + 1) : ℝ) : ℂ)) *
                  (atkinsonWeightedResonantBlockMode (n + j + 1) 0 *
                    atkinsonShiftedSinglePrimitive (n + j + 1) (j + 1) 0) := by
                      congr 1
                      field_simp [ne_of_gt hphase_pos]

private lemma atkinsonShiftedSingleBoundaryCore_norm
    (n j : ℕ) (hj : 1 ≤ j) :
    ‖atkinsonShiftedSingleBoundaryCore n j‖ = atkinsonModeWeight n := by
  have hjk : j ≤ n + j := by omega
  have hphase_pos : 0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j hj hjk
  have hphase_nonneg : 0 ≤ atkinsonShiftedRelativePhase (n + j) j := le_of_lt hphase_pos
  have hweight_nonneg : 0 ≤ atkinsonShiftedRelativeWeight (n + j) j :=
    atkinsonShiftedRelativeWeight_nonneg (n + j) j
  have hmul :
      atkinsonModeWeight (n + j) * atkinsonShiftedRelativeWeight (n + j) j
        = atkinsonModeWeight n := by
    simpa using atkinsonModeWeight_mul_shiftedRelativeWeight (n + j) j
  have habs :
      |atkinsonShiftedRelativeWeight (n + j) j / atkinsonShiftedRelativePhase (n + j) j|
        =
      atkinsonShiftedRelativeWeight (n + j) j / atkinsonShiftedRelativePhase (n + j) j := by
    exact abs_of_nonneg (div_nonneg hweight_nonneg hphase_nonneg)
  unfold atkinsonShiftedSingleBoundaryCore atkinsonShiftedSinglePrimitive
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hphase_nonneg]
  rw [norm_mul, atkinsonWeightedResonantBlockMode_norm]
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  rw [habs]
  unfold atkinsonShiftedPacketPhase
  rw [Complex.norm_exp]
  simp
  calc
    atkinsonShiftedRelativePhase (n + j) j *
        (atkinsonModeWeight (n + j) *
          (atkinsonShiftedRelativeWeight (n + j) j /
            atkinsonShiftedRelativePhase (n + j) j))
      =
    atkinsonShiftedRelativePhase (n + j) j *
        ((atkinsonModeWeight (n + j) * atkinsonShiftedRelativeWeight (n + j) j) /
          atkinsonShiftedRelativePhase (n + j) j) := by
            ring
    _ = atkinsonShiftedRelativePhase (n + j) j *
        (atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + j) j) := by
          rw [hmul]
    _ = atkinsonModeWeight n := by
          field_simp [ne_of_gt hphase_pos]

private lemma atkinsonShiftedSingleBoundaryCore_eq_weightedModeStart
    (n j : ℕ) (hj : 1 ≤ j) :
    atkinsonShiftedSingleBoundaryCore n j
      =
      (-Complex.I) *
        ((((atkinsonModeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (hardyStart (n + j)))) := by
  have hjk : j ≤ n + j := by omega
  calc
    atkinsonShiftedSingleBoundaryCore n j
        =
      (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        (atkinsonWeightedResonantBlockMode (n + j) 0 *
          atkinsonShiftedSinglePrimitive (n + j) j 0) := by
            rfl
    _ =
      atkinsonWeightedResonantBlockMode (n + j) 0 *
        ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonShiftedSinglePrimitive (n + j) j 0) := by
            ring
    _ =
      atkinsonWeightedResonantBlockMode (n + j) 0 *
        ((-Complex.I) * atkinsonShiftedSinglePacket (n + j) j 0) := by
            rw [atkinsonShiftedRelativePhase_mul_shiftedSinglePrimitive (n + j) j 0 hj hjk]
    _ =
      (-Complex.I) *
        (atkinsonWeightedResonantBlockMode (n + j) 0 *
          atkinsonShiftedSinglePacket (n + j) j 0) := by
            ring
    _ =
      (-Complex.I) *
        ((((atkinsonModeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (blockCoord (n + j) 0))) := by
            simpa [show n + j - j = n by omega, atkinsonShiftedSinglePacket,
              atkinsonShiftedPacketPhase] using
              congrArg (fun z : ℂ => (-Complex.I) * z)
                (atkinsonWeighted_hardyCosExp_eq_resonant_times_shiftedPacket (n + j) j 0).symm
    _ =
      (-Complex.I) *
        ((((atkinsonModeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (hardyStart (n + j)))) := by
            simp [blockCoord_zero]

private lemma atkinsonShiftedRelativeWeight_antidiagonal_ratio
    (n j : ℕ) :
    atkinsonShiftedRelativeWeight (n + j + 1) (j + 1) /
        atkinsonShiftedRelativeWeight (n + j + 1) j
      =
    atkinsonModeWeight n / atkinsonModeWeight (n + 1) := by
  unfold atkinsonShiftedRelativeWeight
  have hk_ne :
      atkinsonModeWeight (n + j + 1) ≠ 0 := atkinsonModeWeight_ne_zero (n + j + 1)
  have hn1_ne :
      atkinsonModeWeight (n + 1) ≠ 0 := atkinsonModeWeight_ne_zero (n + 1)
  have hsub1 : n + j + 1 - (j + 1) = n := by omega
  have hsub2 : n + j + 1 - j = n + 1 := by omega
  rw [show atkinsonModeWeight (n + j + 1 - (j + 1)) = atkinsonModeWeight n by
    simpa [hsub1]]
  rw [show atkinsonModeWeight (n + j + 1 - j) = atkinsonModeWeight (n + 1) by
    simpa [hsub2]]
  field_simp [hk_ne, hn1_ne]

private lemma atkinsonShiftedRelativePhase_antidiagonal_step
    (n j : ℕ) (hj : 1 ≤ j) :
    atkinsonShiftedRelativePhase (n + j + 1) (j + 1)
      - atkinsonShiftedRelativePhase (n + j + 1) j
        = atkinsonShiftedRelativePhase (n + 1) 1 := by
  have hsub1 : n + j + 1 - (j + 1) = n := by omega
  have hsub2 : n + j + 1 - j = n + 1 := by omega
  rw [atkinsonShiftedRelativePhase_eq_sub_logs, atkinsonShiftedRelativePhase_eq_sub_logs]
  have h1 : (((n + j + 1 - (j + 1) : ℕ) : ℝ) + 1) = (n : ℝ) + 1 := by
    norm_num [hsub1]
  have h2 : (((n + j + 1 - j : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by
    rw [hsub2]
    norm_num [Nat.cast_add]
    ring
  rw [h1, h2]
  have h3 :
      atkinsonShiftedRelativePhase (n + 1) 1
        =
      Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) := by
    rw [atkinsonShiftedRelativePhase_eq_sub_logs]
    norm_num
    ring
  rw [h3]
  ring

/-- Exact anti-diagonal transport for the Atkinson weighted Hardy mode at block starts. -/
private lemma atkinsonWeightedModeStart_antidiagonal_transport
    (n j : ℕ) (hj : 1 ≤ j) :
    (((atkinsonModeWeight n : ℝ) : ℂ) *
        HardyCosSmooth.hardyCosExp n (hardyStart (n + j + 1)))
      =
      ((((atkinsonModeWeight (n + 1) : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp (n + 1) (hardyStart (n + j + 1))) *
        ((((atkinsonModeWeight n / atkinsonModeWeight (n + 1) : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ↑(hardyStart (n + j + 1) * atkinsonShiftedRelativePhase (n + 1) 1)))) := by
  let k : ℕ := n + j + 1
  have hkj : j ≤ k := by
    dsimp [k]
    omega
  have hkj1 : j + 1 ≤ k := by
    dsimp [k]
    omega
  have hA :=
    atkinsonWeighted_hardyCosExp_eq_resonant_times_shiftedPacket k (j + 1) 0
  have hB :=
    atkinsonWeighted_hardyCosExp_eq_resonant_times_shiftedPacket k j 0
  have hratio :
      atkinsonShiftedRelativeWeight k (j + 1) / atkinsonShiftedRelativeWeight k j
        = atkinsonModeWeight n / atkinsonModeWeight (n + 1) := by
    dsimp [k]
    exact atkinsonShiftedRelativeWeight_antidiagonal_ratio n j
  have hphase_step :
      atkinsonShiftedRelativePhase k (j + 1) - atkinsonShiftedRelativePhase k j
        = atkinsonShiftedRelativePhase (n + 1) 1 := by
    dsimp [k]
    exact atkinsonShiftedRelativePhase_antidiagonal_step n j hj
  have hweight_ne : atkinsonShiftedRelativeWeight k j ≠ 0 := by
    exact ne_of_gt <| by
      unfold atkinsonShiftedRelativeWeight
      exact div_pos
        (atkinsonModeWeight_pos (k - j))
        (atkinsonModeWeight_pos k)
  have hexp :
      Complex.exp (Complex.I * ↑(hardyStart k * atkinsonShiftedRelativePhase k (j + 1)))
        =
      Complex.exp (Complex.I * ↑(hardyStart k * atkinsonShiftedRelativePhase k j)) *
        Complex.exp (Complex.I * ↑(hardyStart k * atkinsonShiftedRelativePhase (n + 1) 1)) := by
    rw [← hphase_step]
    have hsplit :
        hardyStart k * atkinsonShiftedRelativePhase k (j + 1)
          =
        hardyStart k * atkinsonShiftedRelativePhase k j
          + hardyStart k *
              (atkinsonShiftedRelativePhase k (j + 1) - atkinsonShiftedRelativePhase k j) := by
      ring
    have harg :
        Complex.I *
            ↑(hardyStart k * atkinsonShiftedRelativePhase k j +
                hardyStart k *
                  (atkinsonShiftedRelativePhase k (j + 1) - atkinsonShiftedRelativePhase k j))
          =
        Complex.I * ↑(hardyStart k * atkinsonShiftedRelativePhase k j)
          + Complex.I *
              ↑(hardyStart k *
                (atkinsonShiftedRelativePhase k (j + 1) - atkinsonShiftedRelativePhase k j)) := by
      simp [mul_add, add_mul]
    rw [hsplit, harg, Complex.exp_add]
  let R : ℂ :=
    (((atkinsonModeWeight k : ℝ) : ℂ) * HardyCosSmooth.hardyCosExp k (hardyStart k))
  let Pj : ℂ :=
    ((((atkinsonShiftedRelativeWeight k j : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ↑(hardyStart k * atkinsonShiftedRelativePhase k j)))
  let Pj1 : ℂ :=
    ((((atkinsonShiftedRelativeWeight k (j + 1) : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ↑(hardyStart k * atkinsonShiftedRelativePhase k (j + 1))))
  let F : ℂ :=
    ((((atkinsonModeWeight n / atkinsonModeWeight (n + 1) : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ↑(hardyStart k * atkinsonShiftedRelativePhase (n + 1) 1)))
  have hk_sub_j1 : k - (j + 1) = n := by
    dsimp [k]
    omega
  have hk_sub_j : k - j = n + 1 := by
    dsimp [k]
    omega
  have hA' :
      (((atkinsonModeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (hardyStart (n + j + 1)))
        = R * Pj1 := by
    simpa [R, Pj1, k, blockCoord_zero, hk_sub_j1,
      atkinsonShiftedSinglePacket, atkinsonShiftedPacketPhase] using hA
  have hB' :
      (((atkinsonModeWeight (n + 1) : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp (n + 1) (hardyStart (n + j + 1)))
        = R * Pj := by
    simpa [R, Pj, k, blockCoord_zero, hk_sub_j,
      atkinsonShiftedSinglePacket, atkinsonShiftedPacketPhase] using hB
  have hratio' :
      atkinsonShiftedRelativeWeight k (j + 1)
        = (atkinsonModeWeight n / atkinsonModeWeight (n + 1)) *
            atkinsonShiftedRelativeWeight k j := by
    exact (div_eq_iff hweight_ne).mp hratio
  have hpacket : Pj1 = Pj * F := by
    unfold Pj1 Pj F
    rw [hexp, hratio']
    simp [mul_assoc, mul_left_comm, mul_comm]
  calc
    (((atkinsonModeWeight n : ℝ) : ℂ) *
        HardyCosSmooth.hardyCosExp n (hardyStart (n + j + 1)))
        = R * Pj1 := hA'
    _ = R * (Pj * F) := by rw [hpacket]
    _ = (R * Pj) * F := by ring
    _ =
      ((((atkinsonModeWeight (n + 1) : ℝ) : ℂ) *
            HardyCosSmooth.hardyCosExp (n + 1) (hardyStart (n + j + 1))) * F) := by
              rw [hB']
    _ =
      ((((atkinsonModeWeight (n + 1) : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp (n + 1) (hardyStart (n + j + 1))) *
        ((((atkinsonModeWeight n / atkinsonModeWeight (n + 1) : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ↑(hardyStart (n + j + 1) * atkinsonShiftedRelativePhase (n + 1) 1)))) := by
          rfl

/-- Exact anti-diagonal transport for the Atkinson normalized boundary core. -/
private theorem atkinsonShiftedSingleBoundaryCore_antidiagonal_transport
    (n j : ℕ) (hj : 1 ≤ j) :
    atkinsonShiftedSingleBoundaryCore n (j + 1)
      =
      atkinsonShiftedSingleBoundaryCore (n + 1) j *
        ((((atkinsonModeWeight n / atkinsonModeWeight (n + 1) : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ↑(hardyStart (n + j + 1) * atkinsonShiftedRelativePhase (n + 1) 1))) := by
  have htransport := atkinsonWeightedModeStart_antidiagonal_transport n j hj
  calc
    atkinsonShiftedSingleBoundaryCore n (j + 1)
      =
      (-Complex.I) *
        ((((atkinsonModeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (hardyStart (n + j + 1)))) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          atkinsonShiftedSingleBoundaryCore_eq_weightedModeStart n (j + 1) (by omega)
    _ =
      (-Complex.I) *
        (((((atkinsonModeWeight (n + 1) : ℝ) : ℂ) *
            HardyCosSmooth.hardyCosExp (n + 1) (hardyStart (n + j + 1))) *
          ((((atkinsonModeWeight n / atkinsonModeWeight (n + 1) : ℝ) : ℂ)) *
            Complex.exp (Complex.I *
              ↑(hardyStart (n + j + 1) * atkinsonShiftedRelativePhase (n + 1) 1))))) := by
        rw [htransport]
    _ =
      ((-Complex.I) *
          ((((atkinsonModeWeight (n + 1) : ℝ) : ℂ) *
            HardyCosSmooth.hardyCosExp (n + 1) (hardyStart (n + j + 1))))) *
        ((((atkinsonModeWeight n / atkinsonModeWeight (n + 1) : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ↑(hardyStart (n + j + 1) * atkinsonShiftedRelativePhase (n + 1) 1))) := by
        ring
    _ =
      atkinsonShiftedSingleBoundaryCore (n + 1) j *
        ((((atkinsonModeWeight n / atkinsonModeWeight (n + 1) : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ↑(hardyStart (n + j + 1) * atkinsonShiftedRelativePhase (n + 1) 1))) := by
        rw [atkinsonShiftedSingleBoundaryCore_eq_weightedModeStart (n + 1) j hj]
        simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private lemma atkinsonShiftedSingleBoundaryCore_antidiagonal_transport_factor_norm
    (n j : ℕ) :
    ‖((((atkinsonModeWeight n / atkinsonModeWeight (n + 1) : ℝ) : ℂ)) *
        Complex.exp (Complex.I *
          ↑(hardyStart (n + j + 1) * atkinsonShiftedRelativePhase (n + 1) 1)))‖
      = atkinsonModeWeight n / atkinsonModeWeight (n + 1) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have hnonneg : 0 ≤ atkinsonModeWeight n / atkinsonModeWeight (n + 1) := by
    exact div_nonneg
      (le_of_lt (atkinsonModeWeight_pos n))
      (le_of_lt (atkinsonModeWeight_pos (n + 1)))
  simp [abs_of_nonneg hnonneg]

private noncomputable def atkinsonAntiDiagonalStepPhase (n j : ℕ) : ℝ :=
  hardyStart (n + j + 1) * atkinsonShiftedRelativePhase (n + 1) 1

private noncomputable def atkinsonNormalizedShiftedSingleBoundaryCore (n j : ℕ) : ℂ :=
  atkinsonShiftedSingleBoundaryCore n j / (((atkinsonModeWeight n : ℝ) : ℂ))

private theorem atkinsonNormalizedShiftedSingleBoundaryCore_antidiagonal_transport
    (n j : ℕ) (hj : 1 ≤ j) :
    atkinsonNormalizedShiftedSingleBoundaryCore n (j + 1)
      =
      atkinsonNormalizedShiftedSingleBoundaryCore (n + 1) j *
        Complex.exp (Complex.I * ↑(atkinsonAntiDiagonalStepPhase n j)) := by
  have hn_ne : (((atkinsonModeWeight n : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast atkinsonModeWeight_ne_zero n
  have hn1_ne : (((atkinsonModeWeight (n + 1) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast atkinsonModeWeight_ne_zero (n + 1)
  have hratio_div :
      ((((atkinsonModeWeight n / atkinsonModeWeight (n + 1) : ℝ) : ℂ)) /
          (((atkinsonModeWeight n : ℝ) : ℂ)))
        =
      1 / (((atkinsonModeWeight (n + 1) : ℝ) : ℂ)) := by
    field_simp [hn_ne, hn1_ne]
    have hratio_mul :
        (atkinsonModeWeight n / atkinsonModeWeight (n + 1)) * atkinsonModeWeight (n + 1)
          = atkinsonModeWeight n := by
      field_simp [atkinsonModeWeight_ne_zero (n + 1)]
    exact_mod_cast hratio_mul
  unfold atkinsonNormalizedShiftedSingleBoundaryCore atkinsonAntiDiagonalStepPhase
  rw [atkinsonShiftedSingleBoundaryCore_antidiagonal_transport n j hj]
  calc
    (atkinsonShiftedSingleBoundaryCore (n + 1) j *
        ((((atkinsonModeWeight n / atkinsonModeWeight (n + 1) : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ↑(hardyStart (n + j + 1) * atkinsonShiftedRelativePhase (n + 1) 1)))) /
        (((atkinsonModeWeight n : ℝ) : ℂ))
      =
    atkinsonShiftedSingleBoundaryCore (n + 1) j *
      (((((atkinsonModeWeight n / atkinsonModeWeight (n + 1) : ℝ) : ℂ)) /
          (((atkinsonModeWeight n : ℝ) : ℂ))) *
        Complex.exp (Complex.I *
          ↑(hardyStart (n + j + 1) * atkinsonShiftedRelativePhase (n + 1) 1))) := by
            rw [div_eq_mul_inv]
            ring
    _ =
      atkinsonShiftedSingleBoundaryCore (n + 1) j *
        ((1 / (((atkinsonModeWeight (n + 1) : ℝ) : ℂ))) *
          Complex.exp (Complex.I *
            ↑(hardyStart (n + j + 1) * atkinsonShiftedRelativePhase (n + 1) 1))) := by
              rw [hratio_div]
    _ =
      (atkinsonShiftedSingleBoundaryCore (n + 1) j /
          (((atkinsonModeWeight (n + 1) : ℝ) : ℂ))) *
        Complex.exp (Complex.I *
          ↑(hardyStart (n + j + 1) * atkinsonShiftedRelativePhase (n + 1) 1)) := by
            rw [div_eq_mul_inv]
            ring

private theorem atkinsonNormalizedShiftedSingleBoundaryCore_norm
    (n j : ℕ) (hj : 1 ≤ j) :
    ‖atkinsonNormalizedShiftedSingleBoundaryCore n j‖ = 1 := by
  unfold atkinsonNormalizedShiftedSingleBoundaryCore
  rw [norm_div, atkinsonShiftedSingleBoundaryCore_norm n j hj, Complex.norm_real, Real.norm_eq_abs]
  simp [abs_of_pos (atkinsonModeWeight_pos n), atkinsonModeWeight_ne_zero n]

private lemma atkinsonMulExpIOfRealAdd (z : ℂ) (a b : ℝ) :
    z * Complex.exp (Complex.I * ((a : ℝ) : ℂ)) * Complex.exp (Complex.I * ((b : ℝ) : ℂ))
      =
    z * Complex.exp (Complex.I * (((a + b : ℝ) : ℝ) : ℂ)) := by
  calc
    z * Complex.exp (Complex.I * ((a : ℝ) : ℂ)) * Complex.exp (Complex.I * ((b : ℝ) : ℂ))
        = z * (Complex.exp (Complex.I * ((a : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ((b : ℝ) : ℂ))) := by ring
    _ = z * Complex.exp
          (Complex.I * ((a : ℝ) : ℂ) + Complex.I * ((b : ℝ) : ℂ)) := by
            rw [← Complex.exp_add]
    _ = z * Complex.exp (Complex.I * (((a + b : ℝ) : ℝ) : ℂ)) := by
          congr 1
          rw [← mul_add, ← Complex.ofReal_add]

private lemma atkinsonExpIOfRealSubSplit (a b : ℝ) :
    Complex.exp (Complex.I * (((a - b : ℝ) : ℝ) : ℂ))
      =
    Complex.exp (Complex.I * ((a : ℝ) : ℂ)) *
      Complex.exp (-Complex.I * ((b : ℝ) : ℂ)) := by
  have harg :
      Complex.I * (((a - b : ℝ) : ℝ) : ℂ)
        =
      Complex.I * ((a : ℝ) : ℂ) + (-Complex.I * ((b : ℝ) : ℂ)) := by
    rw [sub_eq_add_neg, Complex.ofReal_add, Complex.ofReal_neg, mul_add]
    ring
  rw [harg, Complex.exp_add]

private theorem atkinsonAntiDiagonalStepPhase_antidiagonal
    (K j : ℕ) (hj1 : 1 ≤ j) (hjK : j ≤ K) :
    atkinsonAntiDiagonalStepPhase (K - j) j
      =
      hardyStart (K + 1) *
        (Real.log ((((K - j : ℕ) : ℝ) + 2)) - Real.log ((((K - j : ℕ) : ℝ) + 1))) := by
  have hsum : K - j + j + 1 = K + 1 := by omega
  unfold atkinsonAntiDiagonalStepPhase
  rw [atkinsonShiftedRelativePhase_eq_sub_logs]
  rw [show hardyStart (K - j + j + 1) = hardyStart (K + 1) by simpa [hsum]]
  have hfirst : (((K - j + 1 : ℕ) : ℝ) + 1) = (((K - j : ℕ) : ℝ) + 2) := by
    calc
      (((K - j + 1 : ℕ) : ℝ) + 1)
          = (((K - j : ℕ) : ℝ) + (1 : ℝ)) + 1 := by
              simp [Nat.cast_add, add_assoc, add_left_comm, add_comm]
      _ = (((K - j : ℕ) : ℝ) + 2) := by ring
  have hpred : K - j + 1 - 1 = K - j := by omega
  have hsecond : (((K - j + 1 - 1 : ℕ) : ℝ) + 1) = (((K - j : ℕ) : ℝ) + 1) := by
    simp [hpred]
  rw [hfirst, hsecond]

private theorem atkinsonAntiDiagonalStepPhase_antidiagonal_sum
    (K m : ℕ) (hm : m ≤ K) :
    Finset.sum (Finset.range m)
        (fun r => atkinsonAntiDiagonalStepPhase (K - (r + 1)) (r + 1))
      =
      hardyStart (K + 1) *
        (Real.log ((K : ℝ) + 1) - Real.log ((((K - m : ℕ) : ℝ) + 1))) := by
  induction' m with m ih
  · simp
  · have hmK : m ≤ K := by omega
    have hm1K : m + 1 ≤ K := by omega
    have hstep := atkinsonAntiDiagonalStepPhase_antidiagonal K (m + 1) (by omega) hm1K
    have hmid :
        Real.log ((((K - (m + 1) : ℕ) : ℝ) + 2))
          = Real.log ((((K - m : ℕ) : ℝ) + 1)) := by
      congr 1
      calc
        (((K - (m + 1) : ℕ) : ℝ) + 2)
            = (((K - (m + 1) + 2 : ℕ) : ℝ)) := by
                simp [Nat.cast_add, add_assoc]
        _ = (((K - m + 1 : ℕ) : ℝ)) := by
              have hsub : K - (m + 1) + 2 = K - m + 1 := by omega
              exact_mod_cast hsub
        _ = (((K - m : ℕ) : ℝ) + 1) := by
              simp [Nat.cast_add, add_assoc]
    calc
      Finset.sum (Finset.range (m + 1))
          (fun r => atkinsonAntiDiagonalStepPhase (K - (r + 1)) (r + 1))
          =
        Finset.sum (Finset.range m)
            (fun r => atkinsonAntiDiagonalStepPhase (K - (r + 1)) (r + 1))
          + atkinsonAntiDiagonalStepPhase (K - (m + 1)) (m + 1) := by
              rw [Finset.sum_range_succ]
      _ =
        hardyStart (K + 1) *
          (Real.log ((K : ℝ) + 1) - Real.log ((((K - m : ℕ) : ℝ) + 1)))
          + atkinsonAntiDiagonalStepPhase (K - (m + 1)) (m + 1) := by
              rw [ih hmK]
      _ =
        hardyStart (K + 1) *
          (Real.log ((K : ℝ) + 1) - Real.log ((((K - m : ℕ) : ℝ) + 1)))
          +
        hardyStart (K + 1) *
          (Real.log ((((K - (m + 1) : ℕ) : ℝ) + 2)) -
            Real.log ((((K - (m + 1) : ℕ) : ℝ) + 1))) := by
              rw [hstep]
      _ =
        hardyStart (K + 1) *
          (Real.log ((K : ℝ) + 1) - Real.log ((((K - (m + 1) : ℕ) : ℝ) + 1))) := by
              rw [hmid]
              ring

private theorem atkinsonNormalizedShiftedSingleBoundaryCore_antidiagonal_expSum
    (K m : ℕ) (hm : m ≤ K) :
    atkinsonNormalizedShiftedSingleBoundaryCore (K - m) (m + 1)
      =
      atkinsonNormalizedShiftedSingleBoundaryCore K 1 *
        Complex.exp
          (Complex.I *
            ↑((Finset.sum (Finset.range m)
              (fun r => atkinsonAntiDiagonalStepPhase (K - (r + 1)) (r + 1))) : ℝ)) := by
  induction' m with m ih
  · simp
  · have hmK : m ≤ K := by omega
    have hsub : K - m = K - (m + 1) + 1 := by omega
    have htransport :
        atkinsonNormalizedShiftedSingleBoundaryCore (K - (m + 1)) ((m + 1) + 1)
          =
        atkinsonNormalizedShiftedSingleBoundaryCore (K - m) (m + 1) *
          Complex.exp
            (Complex.I * ↑(atkinsonAntiDiagonalStepPhase (K - (m + 1)) (m + 1))) := by
      simpa [hsub, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        atkinsonNormalizedShiftedSingleBoundaryCore_antidiagonal_transport
          (K - (m + 1)) (m + 1) (by omega)
    calc
      atkinsonNormalizedShiftedSingleBoundaryCore (K - (m + 1)) ((m + 1) + 1)
          =
        atkinsonNormalizedShiftedSingleBoundaryCore (K - m) (m + 1) *
          Complex.exp
            (Complex.I * ↑(atkinsonAntiDiagonalStepPhase (K - (m + 1)) (m + 1))) := htransport
      _ =
        (atkinsonNormalizedShiftedSingleBoundaryCore K 1 *
          Complex.exp
            (Complex.I *
              ↑((Finset.sum (Finset.range m)
                (fun r => atkinsonAntiDiagonalStepPhase (K - (r + 1)) (r + 1))) : ℝ)) *
          Complex.exp
            (Complex.I * ↑(atkinsonAntiDiagonalStepPhase (K - (m + 1)) (m + 1)))) := by
              rw [ih hmK]
      _ =
        atkinsonNormalizedShiftedSingleBoundaryCore K 1 *
          Complex.exp
            (Complex.I *
              ↑((Finset.sum (Finset.range m)
                  (fun r => atkinsonAntiDiagonalStepPhase (K - (r + 1)) (r + 1)))
                + atkinsonAntiDiagonalStepPhase (K - (m + 1)) (m + 1))) := by
              simpa using atkinsonMulExpIOfRealAdd
                (atkinsonNormalizedShiftedSingleBoundaryCore K 1)
                (Finset.sum (Finset.range m)
                  (fun r => atkinsonAntiDiagonalStepPhase (K - (r + 1)) (r + 1)))
                (atkinsonAntiDiagonalStepPhase (K - (m + 1)) (m + 1))
      _ =
        atkinsonNormalizedShiftedSingleBoundaryCore K 1 *
          Complex.exp
            (Complex.I *
              ↑((Finset.sum (Finset.range (m + 1))
                (fun r => atkinsonAntiDiagonalStepPhase (K - (r + 1)) (r + 1))) : ℝ)) := by
              rw [Finset.sum_range_succ]

private theorem atkinsonNormalizedShiftedSingleBoundaryCore_antidiagonal_closed_form
    (K m : ℕ) (hm : m ≤ K) :
    atkinsonNormalizedShiftedSingleBoundaryCore (K - m) (m + 1)
      =
      atkinsonNormalizedShiftedSingleBoundaryCore K 1 *
        Complex.exp
          (Complex.I *
            ↑(hardyStart (K + 1) *
              (Real.log ((K : ℝ) + 1) - Real.log ((((K - m : ℕ) : ℝ) + 1))))) := by
  rw [atkinsonNormalizedShiftedSingleBoundaryCore_antidiagonal_expSum K m hm]
  rw [atkinsonAntiDiagonalStepPhase_antidiagonal_sum K m hm]

private theorem atkinsonNormalizedShiftedSingleBoundaryCore_antidiagonal_closed_form'
    (J n : ℕ) (hn : n ≤ J) :
    atkinsonNormalizedShiftedSingleBoundaryCore n (J + 1 - n)
      =
      atkinsonNormalizedShiftedSingleBoundaryCore J 1 *
        Complex.exp
          (Complex.I *
            ↑(hardyStart (J + 1) *
              (Real.log ((J : ℝ) + 1) - Real.log ((n : ℝ) + 1)))) := by
  have h :=
    atkinsonNormalizedShiftedSingleBoundaryCore_antidiagonal_closed_form
      J (J - n) (by omega)
  have hsub : J - (J - n) = n := by omega
  have hj : J - n + 1 = J + 1 - n := by omega
  simpa [hsub, hj, Nat.cast_add, add_assoc, add_left_comm, add_comm] using h

private lemma atkinsonShiftedSingleBoundaryCore_eq_modeWeight_mul_normalized
    (n j : ℕ) :
    atkinsonShiftedSingleBoundaryCore n j
      = (((atkinsonModeWeight n : ℝ) : ℂ)) * atkinsonNormalizedShiftedSingleBoundaryCore n j := by
  have hne : (((atkinsonModeWeight n : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast atkinsonModeWeight_ne_zero n
  unfold atkinsonNormalizedShiftedSingleBoundaryCore
  field_simp [hne]

private theorem atkinsonShiftedSingleBoundaryCore_antidiagonal_sum_eq_weightedDirichletSlice
    (J : ℕ) :
    Finset.sum (Finset.range (J + 1))
        (fun n => atkinsonShiftedSingleBoundaryCore n (J + 1 - n))
      =
      atkinsonNormalizedShiftedSingleBoundaryCore J 1 *
        Complex.exp (Complex.I * ↑(hardyStart (J + 1) * Real.log ((J : ℝ) + 1))) *
        Finset.sum (Finset.range (J + 1))
          (fun n =>
            (((atkinsonModeWeight n : ℝ) : ℂ)) *
              Complex.exp (-Complex.I * ↑(hardyStart (J + 1) * Real.log ((n : ℝ) + 1)))) := by
  calc
    Finset.sum (Finset.range (J + 1))
        (fun n => atkinsonShiftedSingleBoundaryCore n (J + 1 - n))
        =
      Finset.sum (Finset.range (J + 1))
        (fun n => (((atkinsonModeWeight n : ℝ) : ℂ)) *
          atkinsonNormalizedShiftedSingleBoundaryCore n (J + 1 - n)) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [atkinsonShiftedSingleBoundaryCore_eq_modeWeight_mul_normalized]
    _ =
      Finset.sum (Finset.range (J + 1))
        (fun n =>
          atkinsonNormalizedShiftedSingleBoundaryCore J 1 *
            Complex.exp (Complex.I * ↑(hardyStart (J + 1) * Real.log ((J : ℝ) + 1))) *
            ((((atkinsonModeWeight n : ℝ) : ℂ)) *
              Complex.exp (-Complex.I * ↑(hardyStart (J + 1) * Real.log ((n : ℝ) + 1))))) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [atkinsonNormalizedShiftedSingleBoundaryCore_antidiagonal_closed_form' J n
              (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]
            have hexp :
                Complex.exp
                    (Complex.I *
                      ↑(hardyStart (J + 1) *
                        (Real.log ((J : ℝ) + 1) - Real.log ((n : ℝ) + 1))))
                  =
                Complex.exp (Complex.I * ↑(hardyStart (J + 1) * Real.log ((J : ℝ) + 1))) *
                  Complex.exp (-Complex.I * ↑(hardyStart (J + 1) * Real.log ((n : ℝ) + 1))) := by
                    rw [show hardyStart (J + 1) *
                        (Real.log ((J : ℝ) + 1) - Real.log ((n : ℝ) + 1))
                          =
                        hardyStart (J + 1) * Real.log ((J : ℝ) + 1)
                          - hardyStart (J + 1) * Real.log ((n : ℝ) + 1) by ring]
                    exact atkinsonExpIOfRealSubSplit
                      (hardyStart (J + 1) * Real.log ((J : ℝ) + 1))
                      (hardyStart (J + 1) * Real.log ((n : ℝ) + 1))
            rw [hexp]
            ring
    _ =
      atkinsonNormalizedShiftedSingleBoundaryCore J 1 *
        Complex.exp (Complex.I * ↑(hardyStart (J + 1) * Real.log ((J : ℝ) + 1))) *
        Finset.sum (Finset.range (J + 1))
          (fun n =>
            (((atkinsonModeWeight n : ℝ) : ℂ)) *
              Complex.exp (-Complex.I * ↑(hardyStart (J + 1) * Real.log ((n : ℝ) + 1)))) := by
            rw [Finset.mul_sum]

private theorem atkinsonShiftedSingleBoundaryCore_antidiagonal_sum_bound
    (J : ℕ) :
    ‖Finset.sum (Finset.range (J + 1))
        (fun n => atkinsonShiftedSingleBoundaryCore n (J + 1 - n))‖
      ≤ 2 * Real.sqrt (J + 1) := by
  rw [atkinsonShiftedSingleBoundaryCore_antidiagonal_sum_eq_weightedDirichletSlice]
  rw [norm_mul, norm_mul]
  have hnorm_anchor :
      ‖atkinsonNormalizedShiftedSingleBoundaryCore J 1‖ = 1 :=
    atkinsonNormalizedShiftedSingleBoundaryCore_norm J 1 (by norm_num)
  have hnorm_phase :
      ‖Complex.exp (Complex.I * ↑(hardyStart (J + 1) * Real.log ((J : ℝ) + 1)))‖ = 1 := by
        rw [Complex.norm_exp]
        simp
  rw [hnorm_anchor, hnorm_phase, one_mul, one_mul]
  calc
    ‖Finset.sum (Finset.range (J + 1))
        (fun n =>
          (((atkinsonModeWeight n : ℝ) : ℂ)) *
            Complex.exp (-Complex.I * ↑(hardyStart (J + 1) * Real.log ((n : ℝ) + 1))))‖
        ≤ Finset.sum (Finset.range (J + 1))
            (fun n =>
              ‖(((atkinsonModeWeight n : ℝ) : ℂ)) *
                Complex.exp (-Complex.I * ↑(hardyStart (J + 1) * Real.log ((n : ℝ) + 1)))‖) := by
          exact norm_sum_le _ _
    _ = Finset.sum (Finset.range (J + 1)) (fun n => atkinsonModeWeight n) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have hnonneg : 0 ≤ atkinsonModeWeight n := by
            exact atkinsonModeWeight_nonneg n
          have hexp :
              ‖Complex.exp (-Complex.I * ↑(hardyStart (J + 1) * Real.log ((n : ℝ) + 1)))‖ = 1 := by
                rw [Complex.norm_exp]
                simp
          rw [hexp]
          simp [abs_of_nonneg hnonneg]
    _ ≤ 2 * Real.sqrt (J + 1) := by
          calc
            Finset.sum (Finset.range (J + 1)) (fun n => atkinsonModeWeight n)
                = Finset.sum (Finset.range (J + 1))
                    (fun n => ((n + 1 : ℝ) ^ (-1 / 2 : ℝ))) := by
                        refine Finset.sum_congr rfl ?_
                        intro n hn
                        rw [atkinsonModeWeight]
                        congr
                        norm_num
            _ ≤ 2 * Real.sqrt (J + 1) := by
                simpa [div_eq_mul_inv, show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by ring_nf] using
                  Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le (J + 1)

private lemma atkinsonShiftedRelativePhase_mul_correctionTerm_eq_packetIntegral
    (n j : ℕ) (hj : 1 ≤ j) :
    (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        atkinsonResonantShiftedCorrectionTerm n j
      =
    ∫ u in (0 : ℝ)..1,
      ((((Aristotle.StationaryPhaseMainMode.blockOmega (n + j) u : ℝ) : ℂ)) *
          atkinsonWeightedResonantBlockMode (n + j) u) *
        atkinsonShiftedSinglePacket (n + j) j u := by
  have hjk : j ≤ n + j := by omega
  unfold atkinsonResonantShiftedCorrectionTerm
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr ?_
  intro u hu
  calc
    (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        ((Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega (n + j) u : ℝ) : ℂ) *
            atkinsonWeightedResonantBlockMode (n + j) u) *
          atkinsonShiftedSinglePrimitive (n + j) j u)
        =
      (Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega (n + j) u : ℝ) : ℂ) *
          atkinsonWeightedResonantBlockMode (n + j) u) *
        ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonShiftedSinglePrimitive (n + j) j u) := by
            ring
    _ =
      (Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega (n + j) u : ℝ) : ℂ) *
          atkinsonWeightedResonantBlockMode (n + j) u) *
        ((-Complex.I) * atkinsonShiftedSinglePacket (n + j) j u) := by
            rw [atkinsonShiftedRelativePhase_mul_shiftedSinglePrimitive (n + j) j u hj hjk]
    _ =
      ((((Aristotle.StationaryPhaseMainMode.blockOmega (n + j) u : ℝ) : ℂ)) *
          atkinsonWeightedResonantBlockMode (n + j) u) *
        atkinsonShiftedSinglePacket (n + j) j u := by
            have hI2 : -(Complex.I ^ 2) = (1 : ℂ) := by norm_num
            calc
              (Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega (n + j) u : ℝ) : ℂ) *
                    atkinsonWeightedResonantBlockMode (n + j) u) *
                  (-Complex.I * atkinsonShiftedSinglePacket (n + j) j u)
                  =
                (-(Complex.I ^ 2)) *
                    ((((Aristotle.StationaryPhaseMainMode.blockOmega (n + j) u : ℝ) : ℂ)) *
                      atkinsonWeightedResonantBlockMode (n + j) u *
                      atkinsonShiftedSinglePacket (n + j) j u) := by
                        ring
              _ =
                ((((Aristotle.StationaryPhaseMainMode.blockOmega (n + j) u : ℝ) : ℂ)) *
                    atkinsonWeightedResonantBlockMode (n + j) u) *
                  atkinsonShiftedSinglePacket (n + j) j u := by
                    rw [hI2, one_mul]

private theorem atkinsonShiftedSingleBoundaryCore_truncated_upper_bound
    (K J : ℕ) :
    ‖∑ n ∈ Finset.range (K + 1),
        atkinsonShiftedSingleBoundaryCore n (min J (K - n) + 1)‖
      ≤ 2 * Real.sqrt (K + 1) := by
  calc
    ‖∑ n ∈ Finset.range (K + 1),
        atkinsonShiftedSingleBoundaryCore n (min J (K - n) + 1)‖
      ≤ ∑ n ∈ Finset.range (K + 1),
          ‖atkinsonShiftedSingleBoundaryCore n (min J (K - n) + 1)‖ := by
            exact norm_sum_le _ _
    _ = ∑ n ∈ Finset.range (K + 1), atkinsonModeWeight n := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [atkinsonShiftedSingleBoundaryCore_norm n (min J (K - n) + 1)]
          omega
    _ = ∑ n ∈ Finset.range (K + 1), ((n + 1 : ℝ) ^ (-1 / 2 : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [atkinsonModeWeight]
          congr
          norm_num
    _ ≤ 2 * Real.sqrt (K + 1) := by
          simpa [div_eq_mul_inv, show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by ring_nf] using
            Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le (K + 1)

private theorem atkinsonShiftedSingleBoundaryCore_vertical_sum_bound
    (K : ℕ) :
    ‖∑ n ∈ Finset.range (K + 1), atkinsonShiftedSingleBoundaryCore n 1‖
      ≤ 2 * Real.sqrt (K + 1) := by
  calc
    ‖∑ n ∈ Finset.range (K + 1), atkinsonShiftedSingleBoundaryCore n 1‖
      ≤ ∑ n ∈ Finset.range (K + 1), ‖atkinsonShiftedSingleBoundaryCore n 1‖ := by
            exact norm_sum_le _ _
    _ = ∑ n ∈ Finset.range (K + 1), atkinsonModeWeight n := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [atkinsonShiftedSingleBoundaryCore_norm n 1 (by norm_num)]
    _ = ∑ n ∈ Finset.range (K + 1), ((n + 1 : ℝ) ^ (-1 / 2 : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [atkinsonModeWeight]
          congr
          norm_num
    _ ≤ 2 * Real.sqrt (K + 1) := by
          simpa [div_eq_mul_inv, show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by ring_nf] using
            Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le (K + 1)

private noncomputable def atkinsonShiftedSingleBoundaryTruncated
    (K J : ℕ) : ℂ :=
  (∑ n ∈ Finset.range (K + 1),
      atkinsonShiftedSingleBoundaryCore n (min J (K - n) + 1))
    - ∑ n ∈ Finset.range (K + 1), atkinsonShiftedSingleBoundaryCore n 1

private theorem atkinsonShiftedSingleBoundaryTruncated_bound
    (K J : ℕ) :
    ‖atkinsonShiftedSingleBoundaryTruncated K J‖
      ≤ 4 * Real.sqrt (K + 1) := by
  unfold atkinsonShiftedSingleBoundaryTruncated
  calc
    ‖∑ n ∈ Finset.range (K + 1),
          atkinsonShiftedSingleBoundaryCore n (min J (K - n) + 1)
        - ∑ n ∈ Finset.range (K + 1), atkinsonShiftedSingleBoundaryCore n 1‖
      ≤ ‖∑ n ∈ Finset.range (K + 1),
            atkinsonShiftedSingleBoundaryCore n (min J (K - n) + 1)‖
          + ‖∑ n ∈ Finset.range (K + 1), atkinsonShiftedSingleBoundaryCore n 1‖ := by
            exact norm_sub_le _ _
    _ ≤ 2 * Real.sqrt (K + 1) + 2 * Real.sqrt (K + 1) := by
          exact add_le_add
            (atkinsonShiftedSingleBoundaryCore_truncated_upper_bound K J)
            (atkinsonShiftedSingleBoundaryCore_vertical_sum_bound K)
    _ = 4 * Real.sqrt (K + 1) := by ring

private lemma atkinsonShiftedSingleBoundaryTruncated_diff_bound
    (K j : ℕ) :
    ‖atkinsonShiftedSingleBoundaryTruncated K j
        - atkinsonShiftedSingleBoundaryTruncated K (j - 1)‖
      ≤ 8 * Real.sqrt (K + 1) := by
  calc
    ‖atkinsonShiftedSingleBoundaryTruncated K j
        - atkinsonShiftedSingleBoundaryTruncated K (j - 1)‖
        ≤ ‖atkinsonShiftedSingleBoundaryTruncated K j‖
            + ‖atkinsonShiftedSingleBoundaryTruncated K (j - 1)‖ := by
              exact norm_sub_le _ _
    _ ≤ 4 * Real.sqrt (K + 1) + 4 * Real.sqrt (K + 1) := by
          exact add_le_add
            (atkinsonShiftedSingleBoundaryTruncated_bound K j)
            (atkinsonShiftedSingleBoundaryTruncated_bound K (j - 1))
    _ = 8 * Real.sqrt (K + 1) := by ring

private theorem atkinsonShiftedSingleBoundaryCore_prefix_bound
    (M j : ℕ) (hj : 1 ≤ j) :
    ‖∑ n ∈ Finset.range (M + 1), atkinsonShiftedSingleBoundaryCore n j‖
      ≤ 8 * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
  let J : ℕ := j - 1
  let K : ℕ := M + J
  have hKJ : K + 1 = M + j := by
    dsimp [K, J]
    omega
  have hmain_split :
      ∑ n ∈ Finset.range (K + 1),
          atkinsonShiftedSingleBoundaryCore n (min J (K - n) + 1)
        =
      (∑ n ∈ Finset.range (M + 1), atkinsonShiftedSingleBoundaryCore n j)
        + ∑ n ∈ Finset.Ico (M + 1) (K + 1),
            atkinsonShiftedSingleBoundaryCore n (K + 1 - n) := by
    calc
      ∑ n ∈ Finset.range (K + 1),
          atkinsonShiftedSingleBoundaryCore n (min J (K - n) + 1)
        =
      (∑ n ∈ Finset.range (M + 1),
          atkinsonShiftedSingleBoundaryCore n (min J (K - n) + 1))
        + ∑ n ∈ Finset.Ico (M + 1) (K + 1),
            atkinsonShiftedSingleBoundaryCore n (min J (K - n) + 1) := by
              simpa using
                (Finset.sum_range_add_sum_Ico
                  (fun n => atkinsonShiftedSingleBoundaryCore n (min J (K - n) + 1))
                  (by
                    dsimp [K, J]
                    omega : M + 1 ≤ K + 1)).symm
      _ =
        (∑ n ∈ Finset.range (M + 1), atkinsonShiftedSingleBoundaryCore n j)
          + ∑ n ∈ Finset.Ico (M + 1) (K + 1),
              atkinsonShiftedSingleBoundaryCore n (min J (K - n) + 1) := by
                congr 1
                refine Finset.sum_congr rfl ?_
                intro n hn
                have hn_le : n ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
                have hmin : min J (K - n) = J := by
                  apply Nat.min_eq_left
                  dsimp [K, J]
                  omega
                have hJ : J + 1 = j := by
                  dsimp [J]
                  omega
                simpa [hmin, hJ]
      _ =
        (∑ n ∈ Finset.range (M + 1), atkinsonShiftedSingleBoundaryCore n j)
          + ∑ n ∈ Finset.Ico (M + 1) (K + 1),
              atkinsonShiftedSingleBoundaryCore n (K + 1 - n) := by
                congr 1
                refine Finset.sum_congr rfl ?_
                intro n hn
                have hn_lo : M + 1 ≤ n := (Finset.mem_Ico.mp hn).1
                have hn_hi : n < K + 1 := (Finset.mem_Ico.mp hn).2
                have hkn : K - n ≤ J := by
                  have hn_le : n ≤ K := Nat.lt_succ_iff.mp hn_hi
                  dsimp [K, J] at hn_lo hn_le ⊢
                  omega
                have hmin : min J (K - n) = K - n := by
                  exact Nat.min_eq_right hkn
                have hsub : K - n + 1 = K + 1 - n := by
                  have hn_le : n ≤ K := Nat.lt_succ_iff.mp hn_hi
                  omega
                simpa [hmin, hsub]
  have hrewrite :
      ∑ n ∈ Finset.range (M + 1), atkinsonShiftedSingleBoundaryCore n j
        =
      atkinsonShiftedSingleBoundaryTruncated K J
        + ∑ n ∈ Finset.range (K + 1), atkinsonShiftedSingleBoundaryCore n 1
        - ∑ n ∈ Finset.Ico (M + 1) (K + 1),
            atkinsonShiftedSingleBoundaryCore n (K + 1 - n) := by
    unfold atkinsonShiftedSingleBoundaryTruncated
    rw [hmain_split]
    ring
  have htail :
      ‖∑ n ∈ Finset.Ico (M + 1) (K + 1),
          atkinsonShiftedSingleBoundaryCore n (K + 1 - n)‖
        ≤ 2 * Real.sqrt (K + 1) := by
    calc
      ‖∑ n ∈ Finset.Ico (M + 1) (K + 1),
          atkinsonShiftedSingleBoundaryCore n (K + 1 - n)‖
        ≤ ∑ n ∈ Finset.Ico (M + 1) (K + 1),
            ‖atkinsonShiftedSingleBoundaryCore n (K + 1 - n)‖ := by
              exact norm_sum_le _ _
      _ = ∑ n ∈ Finset.Ico (M + 1) (K + 1), atkinsonModeWeight n := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [atkinsonShiftedSingleBoundaryCore_norm n (K + 1 - n)]
            have hhn := Finset.mem_Ico.mp hn
            omega
      _ ≤ ∑ n ∈ Finset.range (K + 1), atkinsonModeWeight n := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by
                intro n hn
                exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2)
              (by
                intro n hn hnot
                exact atkinsonModeWeight_nonneg n)
      _ = ∑ n ∈ Finset.range (K + 1), ((n + 1 : ℝ) ^ (-1 / 2 : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [atkinsonModeWeight]
            congr
            norm_num
      _ ≤ 2 * Real.sqrt (K + 1) := by
            simpa [div_eq_mul_inv, show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by ring_nf] using
              Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le (K + 1)
  calc
    ‖∑ n ∈ Finset.range (M + 1), atkinsonShiftedSingleBoundaryCore n j‖
      =
    ‖atkinsonShiftedSingleBoundaryTruncated K J
        + ∑ n ∈ Finset.range (K + 1), atkinsonShiftedSingleBoundaryCore n 1
        - ∑ n ∈ Finset.Ico (M + 1) (K + 1),
            atkinsonShiftedSingleBoundaryCore n (K + 1 - n)‖ := by
            rw [hrewrite]
    _ ≤ ‖atkinsonShiftedSingleBoundaryTruncated K J
            + ∑ n ∈ Finset.range (K + 1), atkinsonShiftedSingleBoundaryCore n 1‖
          + ‖∑ n ∈ Finset.Ico (M + 1) (K + 1),
              atkinsonShiftedSingleBoundaryCore n (K + 1 - n)‖ := by
                exact norm_sub_le _ _
    _ ≤ ‖atkinsonShiftedSingleBoundaryTruncated K J‖
          + ‖∑ n ∈ Finset.range (K + 1), atkinsonShiftedSingleBoundaryCore n 1‖
          + ‖∑ n ∈ Finset.Ico (M + 1) (K + 1),
              atkinsonShiftedSingleBoundaryCore n (K + 1 - n)‖ := by
                gcongr
                exact norm_add_le _ _
    _ ≤ 4 * Real.sqrt (K + 1)
          + 2 * Real.sqrt (K + 1)
          + 2 * Real.sqrt (K + 1) := by
                exact add_le_add
                  (add_le_add
                    (atkinsonShiftedSingleBoundaryTruncated_bound K J)
                    (atkinsonShiftedSingleBoundaryCore_vertical_sum_bound K))
                  htail
    _ = 8 * Real.sqrt (K + 1) := by ring
    _ = 8 * Real.sqrt ((M + j : ℕ) : ℝ) := by
          have hKJ' : ((K : ℝ) + 1) = ((M + j : ℕ) : ℝ) := by
            exact_mod_cast hKJ
          rw [hKJ']
    _ ≤ 8 * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
          have hsqrt :
              Real.sqrt (((M + j : ℕ) : ℝ))
                ≤ Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
            apply Real.sqrt_le_sqrt
            linarith
          exact mul_le_mul_of_nonneg_left hsqrt (by positivity)

private theorem
    atkinson_large_modes_complete_resonant_packet_row_lower_boundary_sum_bound_atomic_phase_weighted :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then
            (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              (atkinsonWeightedResonantBlockMode (n + j) 0 *
                atkinsonShiftedSinglePrimitive (n + j) j 0)
          else 0)‖
        ≤ C_complete * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
  refine ⟨16, by positivity, ?_⟩
  intro j hj M
  by_cases hMj : M ≤ j
  · have hzero :
        ∑ n ∈ Finset.range M,
            (if j ≤ n then
              (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                (atkinsonWeightedResonantBlockMode (n + j) 0 *
                  atkinsonShiftedSinglePrimitive (n + j) j 0)
            else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnlt : n < j := lt_of_lt_of_le (Finset.mem_range.mp hn) hMj
      simp [hnlt.not_ge]
    have hnonneg : 0 ≤ (16 : ℝ) * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by positivity
    simpa [hzero] using hnonneg
  · have hJM : j ≤ M := le_of_lt (lt_of_not_ge hMj)
    let base : ℕ → ℂ := fun n => atkinsonShiftedSingleBoundaryCore n j
    have hsum :
        ∑ n ∈ Finset.range M,
            (if j ≤ n then
              (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                (atkinsonWeightedResonantBlockMode (n + j) 0 *
                  atkinsonShiftedSinglePrimitive (n + j) j 0)
            else 0)
          =
        ∑ n ∈ Finset.Ico j M, base n := by
      calc
        ∑ n ∈ Finset.range M,
            (if j ≤ n then
              (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                (atkinsonWeightedResonantBlockMode (n + j) 0 *
                  atkinsonShiftedSinglePrimitive (n + j) j 0)
            else 0)
            =
        ∑ n ∈ Finset.range M, (if j ≤ n then base n else 0) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              by_cases hjn : j ≤ n
              · simp [base, hjn, atkinsonShiftedSingleBoundaryCore]
              · simp [base, hjn]
        _ =
        (∑ n ∈ Finset.range j, (if j ≤ n then base n else 0))
          + ∑ n ∈ Finset.Ico j M, (if j ≤ n then base n else 0) := by
            simpa using
              (Finset.sum_range_add_sum_Ico (fun n => if j ≤ n then base n else 0) hJM).symm
        _ = ∑ n ∈ Finset.Ico j M, (if j ≤ n then base n else 0) := by
              have hprefix_zero :
                  ∑ n ∈ Finset.range j, (if j ≤ n then base n else 0) = 0 := by
                    apply Finset.sum_eq_zero
                    intro n hn
                    simp [(Finset.mem_range.mp hn).not_ge]
              rw [hprefix_zero, zero_add]
        _ = ∑ n ∈ Finset.Ico j M, base n := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              simp [base, (Finset.mem_Ico.mp hn).1]
    have hsplit :
        ∑ n ∈ Finset.Ico j M, base n
          =
        (∑ n ∈ Finset.range M, base n) - ∑ n ∈ Finset.range j, base n := by
      rw [Finset.sum_Ico_eq_sub _ hJM]
    have hprefix_M :
        ‖∑ n ∈ Finset.range M, base n‖
          ≤ 8 * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
      have hraw := atkinsonShiftedSingleBoundaryCore_prefix_bound (M - 1) j hj
      calc
        ‖∑ n ∈ Finset.range M, base n‖
            ≤ 8 * Real.sqrt (((M - 1 + j : ℕ) : ℝ) + 1) := by
              simpa [base, show M - 1 + 1 = M by omega, Nat.add_assoc, add_left_comm, add_comm]
                using hraw
        _ = 8 * Real.sqrt ((M + j : ℕ) : ℝ) := by
              have hM : (M - 1 + j : ℕ) + 1 = M + j := by
                omega
              have hM' : (((M - 1 + j : ℕ) : ℝ) + 1) = ((M + j : ℕ) : ℝ) := by
                exact_mod_cast hM
              rw [hM']
        _ ≤ 8 * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
              exact mul_le_mul_of_nonneg_left
                (Real.sqrt_le_sqrt (by linarith))
                (by positivity)
    have hprefix_j :
        ‖∑ n ∈ Finset.range j, base n‖
          ≤ 8 * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
      have hraw := atkinsonShiftedSingleBoundaryCore_prefix_bound (j - 1) j hj
      have hj_le : ((j - 1 + j : ℕ) : ℝ) + 1 ≤ (((M + j : ℕ) : ℝ) + 1) := by
        exact_mod_cast (by
          omega : (j - 1 + j) + 1 ≤ M + j + 1)
      calc
        ‖∑ n ∈ Finset.range j, base n‖
            ≤ 8 * Real.sqrt (((j - 1 + j : ℕ) : ℝ) + 1) := by
              simpa [base, show j - 1 + 1 = j by omega, Nat.add_assoc, add_left_comm, add_comm] using hraw
        _ ≤ 8 * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
              exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hj_le) (by positivity)
    calc
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then
            (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              (atkinsonWeightedResonantBlockMode (n + j) 0 *
                atkinsonShiftedSinglePrimitive (n + j) j 0)
          else 0)‖
        = ‖∑ n ∈ Finset.Ico j M, base n‖ := by
            rw [hsum]
      _ = ‖(∑ n ∈ Finset.range M, base n) - ∑ n ∈ Finset.range j, base n‖ := by
            rw [hsplit]
      _ ≤ ‖∑ n ∈ Finset.range M, base n‖ + ‖∑ n ∈ Finset.range j, base n‖ := by
            exact norm_sub_le _ _
      _ ≤ 8 * Real.sqrt (((M + j : ℕ) : ℝ) + 1)
            + 8 * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
              exact add_le_add hprefix_M hprefix_j
      _ = (16 : ℝ) * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by ring

private lemma atkinson_complex_mul_phase_eq_boundaryCore_diff
    (n j : ℕ) (hj : 1 ≤ j) :
    (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        atkinsonResonantShiftedBoundaryTerm n j
      =
    atkinsonShiftedSingleBoundaryCore n (j + 1)
      - atkinsonShiftedSingleBoundaryCore n j := by
  unfold atkinsonResonantShiftedBoundaryTerm
  rw [mul_sub]
  rw [atkinsonShiftedSingleBoundaryCore_step n j hj]
  rfl

private theorem atkinsonShiftedSingleBoundaryTruncated_diff_eq_fixedShiftPrefix
    (m j : ℕ) (hj : 1 ≤ j) :
    atkinsonShiftedSingleBoundaryTruncated (m + j) j
      - atkinsonShiftedSingleBoundaryTruncated (m + j) (j - 1)
      =
      ∑ n ∈ Finset.range (m + 1),
        (atkinsonShiftedSingleBoundaryCore n (j + 1) -
          atkinsonShiftedSingleBoundaryCore n j) := by
  unfold atkinsonShiftedSingleBoundaryTruncated
  calc
    ((∑ n ∈ Finset.range (m + j + 1),
          atkinsonShiftedSingleBoundaryCore n (min j (m + j - n) + 1))
        - ∑ n ∈ Finset.range (m + j + 1), atkinsonShiftedSingleBoundaryCore n 1)
      -
      ((∑ n ∈ Finset.range (m + j + 1),
          atkinsonShiftedSingleBoundaryCore n (min (j - 1) (m + j - n) + 1))
        - ∑ n ∈ Finset.range (m + j + 1), atkinsonShiftedSingleBoundaryCore n 1)
        =
      (∑ n ∈ Finset.range (m + j + 1),
          atkinsonShiftedSingleBoundaryCore n (min j (m + j - n) + 1))
        -
      (∑ n ∈ Finset.range (m + j + 1),
          atkinsonShiftedSingleBoundaryCore n (min (j - 1) (m + j - n) + 1)) := by
            ring
    _ =
      ∑ n ∈ Finset.range (m + j + 1),
        (atkinsonShiftedSingleBoundaryCore n (min j (m + j - n) + 1)
          - atkinsonShiftedSingleBoundaryCore n (min (j - 1) (m + j - n) + 1)) := by
            rw [Finset.sum_sub_distrib]
    _ =
      ∑ n ∈ Finset.range (m + 1),
        (atkinsonShiftedSingleBoundaryCore n (j + 1)
          - atkinsonShiftedSingleBoundaryCore n j) := by
            let F : ℕ → ℂ := fun n =>
              atkinsonShiftedSingleBoundaryCore n (min j (m + j - n) + 1)
                - atkinsonShiftedSingleBoundaryCore n (min (j - 1) (m + j - n) + 1)
            have hsplit :
                ∑ n ∈ Finset.range (m + j + 1), F n
                  =
                ∑ n ∈ Finset.range (m + 1), F n
                  + ∑ n ∈ Finset.Ico (m + 1) (m + j + 1), F n := by
                    rw [← Finset.sum_range_add_sum_Ico F (by omega : m + 1 ≤ m + j + 1)]
            have hprefix :
                ∑ n ∈ Finset.range (m + 1), F n
                  =
                ∑ n ∈ Finset.range (m + 1),
                  (atkinsonShiftedSingleBoundaryCore n (j + 1) -
                    atkinsonShiftedSingleBoundaryCore n j) := by
                      refine Finset.sum_congr rfl ?_
                      intro n hn
                      have hn_le : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
                      have hupper : j ≤ m + j - n := by omega
                      have hupper' : j - 1 ≤ m + j - n := by omega
                      rw [show F n =
                          atkinsonShiftedSingleBoundaryCore n (min j (m + j - n) + 1)
                            - atkinsonShiftedSingleBoundaryCore n
                                (min (j - 1) (m + j - n) + 1) by rfl]
                      rw [Nat.min_eq_left hupper, Nat.min_eq_left hupper']
                      have hjs : j - 1 + 1 = j := by omega
                      simpa [hjs]
            have hIco :
                ∑ n ∈ Finset.Ico (m + 1) (m + j + 1), F n = 0 := by
                  refine Finset.sum_eq_zero ?_
                  intro n hn
                  have hn_gt : m + 1 ≤ n := (Finset.mem_Ico.mp hn).1
                  have hn_lt : n < m + j + 1 := (Finset.mem_Ico.mp hn).2
                  have hsmall : m + j - n ≤ j - 1 := by
                    omega
                  have hsmall' : m + j - n ≤ j := le_trans hsmall (by omega)
                  rw [show F n =
                      atkinsonShiftedSingleBoundaryCore n (min j (m + j - n) + 1)
                        - atkinsonShiftedSingleBoundaryCore n
                            (min (j - 1) (m + j - n) + 1) by rfl]
                  rw [Nat.min_eq_right hsmall', Nat.min_eq_right hsmall]
                  simp
            rw [hsplit, hprefix, hIco, add_zero]

private theorem atkinsonShiftedSingleBoundaryCoreFixedShiftPrefix_eq_boundaryDiff
    (m j : ℕ) (hj : 2 ≤ j) (hnonempty : j - 1 ≤ m) :
    (atkinsonShiftedSingleBoundaryTruncated (m + j) j
        - atkinsonShiftedSingleBoundaryTruncated (m + j) (j - 1))
      -
      (atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) j
        - atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) (j - 1))
      =
    ∑ n ∈ Finset.Ico (j - 1) (m + 1),
      (atkinsonShiftedSingleBoundaryCore n (j + 1) -
        atkinsonShiftedSingleBoundaryCore n j) := by
  have hj_one : 1 ≤ j := le_trans (by norm_num) hj
  have hmain :=
    atkinsonShiftedSingleBoundaryTruncated_diff_eq_fixedShiftPrefix m j hj_one
  have hinit :
      atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) j
        - atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) (j - 1)
      =
      ∑ n ∈ Finset.range (j - 1),
        (atkinsonShiftedSingleBoundaryCore n (j + 1) -
          atkinsonShiftedSingleBoundaryCore n j) := by
            simpa [show j - 2 + 1 = j - 1 by omega] using
              atkinsonShiftedSingleBoundaryTruncated_diff_eq_fixedShiftPrefix (j - 2) j hj_one
  calc
    (atkinsonShiftedSingleBoundaryTruncated (m + j) j
        - atkinsonShiftedSingleBoundaryTruncated (m + j) (j - 1))
      -
      (atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) j
        - atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) (j - 1))
        =
      (∑ n ∈ Finset.range (m + 1),
          (atkinsonShiftedSingleBoundaryCore n (j + 1) -
            atkinsonShiftedSingleBoundaryCore n j))
        -
      ∑ n ∈ Finset.range (j - 1),
        (atkinsonShiftedSingleBoundaryCore n (j + 1) -
          atkinsonShiftedSingleBoundaryCore n j) := by
            rw [hmain, hinit]
    _ =
      ∑ n ∈ Finset.Ico (j - 1) (m + 1),
        (atkinsonShiftedSingleBoundaryCore n (j + 1) -
          atkinsonShiftedSingleBoundaryCore n j) := by
            rw [Finset.sum_Ico_eq_sub _ (by omega : j - 1 ≤ m + 1)]

private theorem atkinsonShiftedSingleBoundaryCoreFixedShiftPrefix_bound
    (m j : ℕ) (hj : 1 ≤ j) :
    ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
        (atkinsonShiftedSingleBoundaryCore n (j + 1) -
          atkinsonShiftedSingleBoundaryCore n j)‖
      ≤ 16 * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
  by_cases hnonempty : j - 1 ≤ m
  · by_cases hj_two : 2 ≤ j
    · have hEq :=
        atkinsonShiftedSingleBoundaryCoreFixedShiftPrefix_eq_boundaryDiff m j hj_two hnonempty
      have hroot_ge :
          Real.sqrt ((((j - 2) + j : ℕ) : ℝ) + 1)
            ≤ Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
        refine Real.sqrt_le_sqrt ?_
        exact_mod_cast (by omega : (j - 2) + j + 1 ≤ m + j + 1)
      calc
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            (atkinsonShiftedSingleBoundaryCore n (j + 1) -
              atkinsonShiftedSingleBoundaryCore n j)‖
            =
          ‖(atkinsonShiftedSingleBoundaryTruncated (m + j) j
                - atkinsonShiftedSingleBoundaryTruncated (m + j) (j - 1))
              -
              (atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) j
                - atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) (j - 1))‖ := by
                rw [← hEq]
        _ ≤ ‖atkinsonShiftedSingleBoundaryTruncated (m + j) j
                - atkinsonShiftedSingleBoundaryTruncated (m + j) (j - 1)‖
              + ‖atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) j
                  - atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) (j - 1)‖ := by
                exact norm_sub_le _ _
        _ ≤ 8 * Real.sqrt (((m + j : ℕ) : ℝ) + 1)
              + 8 * Real.sqrt ((((j - 2) + j : ℕ) : ℝ) + 1) := by
                exact add_le_add
                  (atkinsonShiftedSingleBoundaryTruncated_diff_bound (m + j) j)
                  (atkinsonShiftedSingleBoundaryTruncated_diff_bound ((j - 2) + j) j)
        _ ≤ 16 * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
                nlinarith
    · have hj_one : j = 1 := by omega
      subst j
      have hIco : Finset.Ico (0 : ℕ) (m + 1) = Finset.range (m + 1) := by
        simp
      calc
        ‖∑ n ∈ Finset.Ico (0 : ℕ) (m + 1),
            (atkinsonShiftedSingleBoundaryCore n (1 + 1) -
              atkinsonShiftedSingleBoundaryCore n 1)‖
            ≤ ∑ n ∈ Finset.Ico (0 : ℕ) (m + 1),
                ‖atkinsonShiftedSingleBoundaryCore n (1 + 1) -
                  atkinsonShiftedSingleBoundaryCore n 1‖ := by
                    exact norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.Ico (0 : ℕ) (m + 1),
              (‖atkinsonShiftedSingleBoundaryCore n (1 + 1)‖
                + ‖atkinsonShiftedSingleBoundaryCore n 1‖) := by
                  refine Finset.sum_le_sum ?_
                  intro n hn
                  exact norm_sub_le _ _
        _ = ∑ n ∈ Finset.range (m + 1), (atkinsonModeWeight n + atkinsonModeWeight n) := by
              rw [hIco]
              refine Finset.sum_congr rfl ?_
              intro n hn
              rw [atkinsonShiftedSingleBoundaryCore_norm n 2 (by norm_num),
                atkinsonShiftedSingleBoundaryCore_norm n 1 (by norm_num)]
        _ = 2 * ∑ n ∈ Finset.range (m + 1), atkinsonModeWeight n := by
              rw [two_mul]
              simp [two_mul, Finset.sum_add_distrib, add_comm, add_left_comm, add_assoc]
        _ ≤ 2 * (2 * Real.sqrt (((m + 1 : ℕ) : ℝ))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              calc
                ∑ n ∈ Finset.range (m + 1), atkinsonModeWeight n
                    = ∑ n ∈ Finset.range (m + 1), ((n + 1 : ℝ) ^ (-1 / 2 : ℝ)) := by
                        refine Finset.sum_congr rfl ?_
                        intro n hn
                        rw [atkinsonModeWeight]
                        congr
                        norm_num
                _ ≤ 2 * Real.sqrt (((m + 1 : ℕ) : ℝ)) := by
                      simpa [div_eq_mul_inv, show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by ring_nf] using
                        Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le (m + 1)
        _ = 4 * Real.sqrt (((m + 1 : ℕ) : ℝ)) := by ring
        _ ≤ 4 * Real.sqrt (((m + 1 : ℕ) : ℝ) + 1) := by
              have hsqrt :
                  Real.sqrt ((m + 1 : ℕ) : ℝ) ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) + 1) := by
                    exact Real.sqrt_le_sqrt (by linarith)
              gcongr
        _ ≤ 16 * Real.sqrt (((m + 1 : ℕ) : ℝ) + 1) := by
              nlinarith [Real.sqrt_nonneg ((((m + 1 : ℕ) : ℝ) + 1))]
  · have hEmpty : Finset.Ico (j - 1) (m + 1) = ∅ := by
      apply Finset.Ico_eq_empty_of_le
      omega
    rw [hEmpty, Finset.sum_empty]
    have hnonneg : 0 ≤ 16 * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
      positivity
    simpa using hnonneg

private noncomputable def atkinsonResonantShiftedPhaseWeightedCell (n j : ℕ) : ℂ :=
  (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
    ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u

private noncomputable def atkinsonResonantShiftedPhaseWeightedTruncatedTriangle
    (K J : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (K + 1),
    ∑ x ∈ Finset.Icc 1 (min J (K - n)),
      atkinsonResonantShiftedPhaseWeightedCell n x

private noncomputable def atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle
    (K J : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (K + 1),
    ∑ x ∈ Finset.Icc 1 (min J (K - n)),
      ((((atkinsonShiftedRelativePhase (n + x) x : ℝ) : ℂ)) *
        atkinsonResonantShiftedCorrectionTerm n x)

private theorem atkinsonResonantShiftedPhaseWeightedCell_eq_boundaryCore_diff_minus_correction
    (n j : ℕ) (hj : 1 ≤ j) :
    atkinsonResonantShiftedPhaseWeightedCell n j
      =
    (atkinsonShiftedSingleBoundaryCore n (j + 1) -
        atkinsonShiftedSingleBoundaryCore n j)
      -
    ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
      atkinsonResonantShiftedCorrectionTerm n j) := by
  unfold atkinsonResonantShiftedPhaseWeightedCell
  rw [atkinsonResonantShiftedCell_eq_boundary_minus_correction n j hj]
  rw [mul_sub, atkinson_complex_mul_phase_eq_boundaryCore_diff n j hj]

private theorem atkinsonResonantShiftedPhaseWeightedCell_sum_eq_boundaryCore_diff_minus_correction
    (n J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, atkinsonResonantShiftedPhaseWeightedCell n j
      =
    atkinsonShiftedSingleBoundaryCore n (J + 1) - atkinsonShiftedSingleBoundaryCore n 1
      -
    ∑ j ∈ Finset.Icc 1 J,
      ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        atkinsonResonantShiftedCorrectionTerm n j) := by
  induction J with
  | zero =>
      simp [atkinsonResonantShiftedPhaseWeightedCell]
  | succ J ih =>
      rw [Finset.sum_Icc_succ_top (a := 1) (b := J)
            (f := fun j => atkinsonResonantShiftedPhaseWeightedCell n j) (by omega)]
      rw [Finset.sum_Icc_succ_top (a := 1) (b := J)
            (f := fun j =>
              ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                atkinsonResonantShiftedCorrectionTerm n j)) (by omega)]
      rw [ih]
      have hcell :
          atkinsonResonantShiftedPhaseWeightedCell n (J + 1)
            =
          (atkinsonShiftedSingleBoundaryCore n (J + 1 + 1) -
              atkinsonShiftedSingleBoundaryCore n (J + 1))
            -
          ((((atkinsonShiftedRelativePhase (n + (J + 1)) (J + 1) : ℝ) : ℂ)) *
            atkinsonResonantShiftedCorrectionTerm n (J + 1)) := by
              simpa using
                atkinsonResonantShiftedPhaseWeightedCell_eq_boundaryCore_diff_minus_correction
                  n (J + 1) (by omega)
      rw [hcell]
      ring

private theorem atkinsonResonantShiftedPhaseWeightedTruncatedTriangle_eq_boundary_diff_minus_correction
    (K J : ℕ) :
    atkinsonResonantShiftedPhaseWeightedTruncatedTriangle K J
      =
    atkinsonShiftedSingleBoundaryTruncated K J
      - atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle K J := by
  unfold atkinsonResonantShiftedPhaseWeightedTruncatedTriangle
    atkinsonShiftedSingleBoundaryTruncated
    atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle
  calc
    ∑ n ∈ Finset.range (K + 1),
        ∑ x ∈ Finset.Icc 1 (min J (K - n)),
          atkinsonResonantShiftedPhaseWeightedCell n x
      =
    ∑ n ∈ Finset.range (K + 1),
      (atkinsonShiftedSingleBoundaryCore n (min J (K - n) + 1)
          - atkinsonShiftedSingleBoundaryCore n 1
          - ∑ x ∈ Finset.Icc 1 (min J (K - n)),
              ((((atkinsonShiftedRelativePhase (n + x) x : ℝ) : ℂ)) *
                atkinsonResonantShiftedCorrectionTerm n x)) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simpa using
              atkinsonResonantShiftedPhaseWeightedCell_sum_eq_boundaryCore_diff_minus_correction
                n (min J (K - n))
    _ =
      (∑ n ∈ Finset.range (K + 1),
          atkinsonShiftedSingleBoundaryCore n (min J (K - n) + 1))
        -
      ∑ n ∈ Finset.range (K + 1), atkinsonShiftedSingleBoundaryCore n 1
        -
      ∑ n ∈ Finset.range (K + 1),
          ∑ x ∈ Finset.Icc 1 (min J (K - n)),
            ((((atkinsonShiftedRelativePhase (n + x) x : ℝ) : ℂ)) *
              atkinsonResonantShiftedCorrectionTerm n x) := by
              rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ =
      atkinsonShiftedSingleBoundaryTruncated K J
        - atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle K J := by
            simp [atkinsonShiftedSingleBoundaryTruncated,
              atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle]

private theorem atkinsonTruncatedTriangle_diff_eq_fixedShiftPrefix
    (F : ℕ → ℕ → ℂ) (K J : ℕ) (hJ : 1 ≤ J) :
    (∑ n ∈ Finset.range (K + 1),
        ∑ x ∈ Finset.Icc 1 (min J (K - n)), F n x)
      -
    (∑ n ∈ Finset.range (K + 1),
        ∑ x ∈ Finset.Icc 1 (min (J - 1) (K - n)), F n x)
      =
    ∑ n ∈ Finset.range (K + 1 - J), F n J := by
  let G : ℕ → ℂ := fun n =>
    (∑ x ∈ Finset.Icc 1 (min J (K - n)), F n x)
      -
    (∑ x ∈ Finset.Icc 1 (min (J - 1) (K - n)), F n x)
  calc
    (∑ n ∈ Finset.range (K + 1),
        ∑ x ∈ Finset.Icc 1 (min J (K - n)), F n x)
      -
    (∑ n ∈ Finset.range (K + 1),
        ∑ x ∈ Finset.Icc 1 (min (J - 1) (K - n)), F n x)
        =
    ∑ n ∈ Finset.range (K + 1), G n := by
          simp [G, Finset.sum_sub_distrib]
    _ =
      ∑ n ∈ Finset.range (K + 1 - J), G n
        +
      ∑ n ∈ Finset.Ico (K + 1 - J) (K + 1), G n := by
            rw [← Finset.sum_range_add_sum_Ico G (by omega : K + 1 - J ≤ K + 1)]
    _ =
      ∑ n ∈ Finset.range (K + 1 - J), F n J
        +
      ∑ n ∈ Finset.Ico (K + 1 - J) (K + 1), G n := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro n hn
            have hn_lt : n < K + 1 - J := Finset.mem_range.mp hn
            have hKJ : J ≤ K + 1 := by
              omega
            have hsub : K + 1 - J = K - J + 1 := by
              omega
            have hn_le : n ≤ K - J := by
              rw [hsub] at hn_lt
              exact Nat.lt_succ_iff.mp hn_lt
            have hupper : J ≤ K - n := by
              omega
            have hupper' : J - 1 ≤ K - n := by
              omega
            have hjs : J = (J - 1) + 1 := by
              omega
            rw [show G n =
                (∑ x ∈ Finset.Icc 1 (min J (K - n)), F n x)
                  -
                (∑ x ∈ Finset.Icc 1 (min (J - 1) (K - n)), F n x) by rfl]
            rw [Nat.min_eq_left hupper, Nat.min_eq_left hupper', hjs]
            rw [Finset.sum_Icc_succ_top (a := 1) (b := J - 1)
                  (f := fun x => F n x) (by omega)]
            simp [G, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = ∑ n ∈ Finset.range (K + 1 - J), F n J := by
            have htail :
                ∑ n ∈ Finset.Ico (K + 1 - J) (K + 1), G n = 0 := by
                  refine Finset.sum_eq_zero ?_
                  intro n hn
                  have hn_ge : K + 1 - J ≤ n := (Finset.mem_Ico.mp hn).1
                  have hn_lt : n < K + 1 := (Finset.mem_Ico.mp hn).2
                  have hn_leK : n ≤ K := Nat.lt_succ_iff.mp hn_lt
                  have hsmall : K - n ≤ J - 1 := by
                    omega
                  have hsmall' : K - n ≤ J := le_trans hsmall (by omega)
                  rw [show G n =
                      (∑ x ∈ Finset.Icc 1 (min J (K - n)), F n x)
                        -
                      (∑ x ∈ Finset.Icc 1 (min (J - 1) (K - n)), F n x) by rfl]
                  rw [Nat.min_eq_right hsmall', Nat.min_eq_right hsmall]
                  simp [G]
            rw [htail, add_zero]

private theorem atkinsonResonantShiftedPhaseWeightedTruncatedTriangle_diff_eq_fixedShiftPrefix
    (K J : ℕ) (hJ : 1 ≤ J) :
    atkinsonResonantShiftedPhaseWeightedTruncatedTriangle K J
      - atkinsonResonantShiftedPhaseWeightedTruncatedTriangle K (J - 1)
      =
    ∑ n ∈ Finset.range (K + 1 - J), atkinsonResonantShiftedPhaseWeightedCell n J := by
  simpa [atkinsonResonantShiftedPhaseWeightedTruncatedTriangle] using
    atkinsonTruncatedTriangle_diff_eq_fixedShiftPrefix
      (F := atkinsonResonantShiftedPhaseWeightedCell) K J hJ

private theorem atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle_diff_eq_fixedShiftPrefix
    (K J : ℕ) (hJ : 1 ≤ J) :
    atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle K J
      - atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle K (J - 1)
      =
    ∑ n ∈ Finset.range (K + 1 - J),
      ((((atkinsonShiftedRelativePhase (n + J) J : ℝ) : ℂ)) *
        atkinsonResonantShiftedCorrectionTerm n J) := by
  simpa [atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle] using
    atkinsonTruncatedTriangle_diff_eq_fixedShiftPrefix
      (F := fun n j =>
        ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonResonantShiftedCorrectionTerm n j)) K J hJ

private theorem
    atkinsonShiftedSingleBoundaryTruncated_diff_eq_phaseWeightedCellPrefix_add_correctionTriangleDiff
    (K J : ℕ) (hJ : 1 ≤ J) :
    atkinsonShiftedSingleBoundaryTruncated K J
      - atkinsonShiftedSingleBoundaryTruncated K (J - 1)
      =
    ∑ n ∈ Finset.range (K + 1 - J), atkinsonResonantShiftedPhaseWeightedCell n J
      +
    (atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle K J
        - atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle K (J - 1)) := by
  have htriJ :=
    atkinsonResonantShiftedPhaseWeightedTruncatedTriangle_eq_boundary_diff_minus_correction K J
  have htriPrev :=
    atkinsonResonantShiftedPhaseWeightedTruncatedTriangle_eq_boundary_diff_minus_correction K (J - 1)
  have hcell :=
    atkinsonResonantShiftedPhaseWeightedTruncatedTriangle_diff_eq_fixedShiftPrefix K J hJ
  have hcorr :=
    atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle_diff_eq_fixedShiftPrefix K J hJ
  calc
    atkinsonShiftedSingleBoundaryTruncated K J
        - atkinsonShiftedSingleBoundaryTruncated K (J - 1)
        =
      (atkinsonResonantShiftedPhaseWeightedTruncatedTriangle K J
          + atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle K J)
        -
      (atkinsonResonantShiftedPhaseWeightedTruncatedTriangle K (J - 1)
          + atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle K (J - 1)) := by
            rw [htriJ, htriPrev]
            ring
    _ =
      (atkinsonResonantShiftedPhaseWeightedTruncatedTriangle K J
          - atkinsonResonantShiftedPhaseWeightedTruncatedTriangle K (J - 1))
        +
      (atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle K J
          - atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle K (J - 1)) := by
            ring
    _ =
      ∑ n ∈ Finset.range (K + 1 - J), atkinsonResonantShiftedPhaseWeightedCell n J
        +
      (atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle K J
          - atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle K (J - 1)) := by
            rw [hcell, hcorr]

private theorem atkinsonResonantShiftedPhaseWeightedCorrectionFixedShiftPrefix_eq_anchoredDifference
    (m j : ℕ) (hj : 2 ≤ j) (hnonempty : j - 1 ≤ m) :
    ∑ n ∈ Finset.Ico (j - 1) (m + 1),
      ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        atkinsonResonantShiftedCorrectionTerm n j)
      =
    (atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle (m + j) j
        - atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle (m + j) (j - 1))
      -
    (atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle ((j - 2) + j) j
        - atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle ((j - 2) + j) (j - 1)) := by
  have hj_one : 1 ≤ j := by
    omega
  have hmainRaw :=
    atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle_diff_eq_fixedShiftPrefix
      (m + j) j hj_one
  have hmain :
      atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle (m + j) j
        - atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle (m + j) (j - 1)
      =
      ∑ n ∈ Finset.range (m + 1),
        ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonResonantShiftedCorrectionTerm n j) := by
            simpa [show m + j + 1 - j = m + 1 by omega] using hmainRaw
  have hinitRaw :=
    atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle_diff_eq_fixedShiftPrefix
      ((j - 2) + j) j hj_one
  have hinit :
      atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle ((j - 2) + j) j
        - atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle ((j - 2) + j) (j - 1)
      =
      ∑ n ∈ Finset.range (j - 1),
        ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonResonantShiftedCorrectionTerm n j) := by
            simpa [show (j - 2) + j + 1 - j = j - 1 by omega] using hinitRaw
  calc
    ∑ n ∈ Finset.Ico (j - 1) (m + 1),
        ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonResonantShiftedCorrectionTerm n j)
      =
    (∑ n ∈ Finset.range (m + 1),
        ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonResonantShiftedCorrectionTerm n j))
      -
    ∑ n ∈ Finset.range (j - 1),
        ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonResonantShiftedCorrectionTerm n j) := by
            rw [Finset.sum_Ico_eq_sub _ (by omega : j - 1 ≤ m + 1)]
    _ =
      (atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle (m + j) j
          - atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle (m + j) (j - 1))
        -
      (atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle ((j - 2) + j) j
          - atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle ((j - 2) + j) (j - 1)) := by
            rw [← hmain, ← hinit]

private theorem atkinsonResonantShiftedPhaseWeightedCorrectionFixedShiftPrefix_eq_boundaryDiff_minus_cellPrefix
    (m j : ℕ) (hj : 2 ≤ j) (hnonempty : j - 1 ≤ m) :
    ∑ n ∈ Finset.Ico (j - 1) (m + 1),
      ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        atkinsonResonantShiftedCorrectionTerm n j)
      =
    ((atkinsonShiftedSingleBoundaryTruncated (m + j) j
          - atkinsonShiftedSingleBoundaryTruncated (m + j) (j - 1))
        -
      (atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) j
          - atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) (j - 1)))
      -
    ∑ n ∈ Finset.Ico (j - 1) (m + 1),
      atkinsonResonantShiftedPhaseWeightedCell n j := by
  have hj_one : 1 ≤ j := by
    omega
  have hcorr :=
    atkinsonResonantShiftedPhaseWeightedCorrectionFixedShiftPrefix_eq_anchoredDifference
      m j hj hnonempty
  have hmainRaw :=
    atkinsonShiftedSingleBoundaryTruncated_diff_eq_phaseWeightedCellPrefix_add_correctionTriangleDiff
      (m + j) j hj_one
  have hmain :
      atkinsonShiftedSingleBoundaryTruncated (m + j) j
        - atkinsonShiftedSingleBoundaryTruncated (m + j) (j - 1)
      =
      ∑ n ∈ Finset.range (m + 1), atkinsonResonantShiftedPhaseWeightedCell n j
        +
      (atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle (m + j) j
          - atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle (m + j) (j - 1)) := by
            simpa [show m + j + 1 - j = m + 1 by omega] using hmainRaw
  have hinitRaw :=
    atkinsonShiftedSingleBoundaryTruncated_diff_eq_phaseWeightedCellPrefix_add_correctionTriangleDiff
      ((j - 2) + j) j hj_one
  have hinit :
      atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) j
        - atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) (j - 1)
      =
      ∑ n ∈ Finset.range (j - 1), atkinsonResonantShiftedPhaseWeightedCell n j
        +
      (atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle ((j - 2) + j) j
          - atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle ((j - 2) + j) (j - 1)) := by
            simpa [show ((j - 2) + j + 1 - j) = j - 1 by omega] using hinitRaw
  have hcorrMain :
      atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle (m + j) j
        - atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle (m + j) (j - 1)
      =
      (atkinsonShiftedSingleBoundaryTruncated (m + j) j
          - atkinsonShiftedSingleBoundaryTruncated (m + j) (j - 1))
        -
      ∑ n ∈ Finset.range (m + 1), atkinsonResonantShiftedPhaseWeightedCell n j := by
            rw [hmain]
            ring
  have hcorrInit :
      atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle ((j - 2) + j) j
        - atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle ((j - 2) + j) (j - 1)
      =
      (atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) j
          - atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) (j - 1))
        -
      ∑ n ∈ Finset.range (j - 1), atkinsonResonantShiftedPhaseWeightedCell n j := by
            rw [hinit]
            ring
  have hcell_sub :
      ∑ n ∈ Finset.range (m + 1), atkinsonResonantShiftedPhaseWeightedCell n j
        - ∑ n ∈ Finset.range (j - 1), atkinsonResonantShiftedPhaseWeightedCell n j
      =
      ∑ n ∈ Finset.Ico (j - 1) (m + 1), atkinsonResonantShiftedPhaseWeightedCell n j := by
        rw [Finset.sum_Ico_eq_sub _ (by omega : j - 1 ≤ m + 1)]
  calc
    ∑ n ∈ Finset.Ico (j - 1) (m + 1),
        ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonResonantShiftedCorrectionTerm n j)
      =
    (atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle (m + j) j
        - atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle (m + j) (j - 1))
      -
    (atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle ((j - 2) + j) j
        - atkinsonResonantShiftedPhaseWeightedCorrectionTruncatedTriangle ((j - 2) + j) (j - 1)) := by
            exact hcorr
    _ =
      ((atkinsonShiftedSingleBoundaryTruncated (m + j) j
            - atkinsonShiftedSingleBoundaryTruncated (m + j) (j - 1))
          -
        ∑ n ∈ Finset.range (m + 1), atkinsonResonantShiftedPhaseWeightedCell n j)
        -
      ((atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) j
            - atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) (j - 1))
          -
        ∑ n ∈ Finset.range (j - 1), atkinsonResonantShiftedPhaseWeightedCell n j) := by
            rw [hcorrMain, hcorrInit]
    _ =
      ((atkinsonShiftedSingleBoundaryTruncated (m + j) j
            - atkinsonShiftedSingleBoundaryTruncated (m + j) (j - 1))
          -
        (atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) j
            - atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) (j - 1)))
        -
      (∑ n ∈ Finset.range (m + 1), atkinsonResonantShiftedPhaseWeightedCell n j
          - ∑ n ∈ Finset.range (j - 1), atkinsonResonantShiftedPhaseWeightedCell n j) := by
            ring
    _ =
      ((atkinsonShiftedSingleBoundaryTruncated (m + j) j
            - atkinsonShiftedSingleBoundaryTruncated (m + j) (j - 1))
          -
        (atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) j
            - atkinsonShiftedSingleBoundaryTruncated ((j - 2) + j) (j - 1)))
        -
      ∑ n ∈ Finset.Ico (j - 1) (m + 1), atkinsonResonantShiftedPhaseWeightedCell n j := by
            rw [hcell_sub]

private theorem
    atkinson_large_modes_complete_resonant_packet_row_boundary_sum_bound_atomic_phase_weighted :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then
            (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonResonantShiftedBoundaryTerm n j
          else 0)‖
        ≤ C_complete * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
  refine ⟨18, by positivity, ?_⟩
  intro j hj M
  by_cases hMj : M ≤ j
  · have hzero :
        ∑ n ∈ Finset.range M,
            (if j ≤ n then
              (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                atkinsonResonantShiftedBoundaryTerm n j
            else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnlt : n < j := lt_of_lt_of_le (Finset.mem_range.mp hn) hMj
      simp [hnlt.not_ge]
    have hnonneg : 0 ≤ (18 : ℝ) * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
      positivity
    simpa [hzero] using hnonneg
  · have hJM : j ≤ M := le_of_lt (lt_of_not_ge hMj)
    let diff : ℕ → ℂ := fun n =>
      atkinsonShiftedSingleBoundaryCore n (j + 1) - atkinsonShiftedSingleBoundaryCore n j
    have hsum :
        ∑ n ∈ Finset.range M,
            (if j ≤ n then
              (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                atkinsonResonantShiftedBoundaryTerm n j
            else 0)
          =
        ∑ n ∈ Finset.Ico j M, diff n := by
      calc
        ∑ n ∈ Finset.range M,
            (if j ≤ n then
              (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                atkinsonResonantShiftedBoundaryTerm n j
            else 0)
            =
        ∑ n ∈ Finset.range M, (if j ≤ n then diff n else 0) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              by_cases hjn : j ≤ n
              · simp [diff, hjn, atkinson_complex_mul_phase_eq_boundaryCore_diff n j hj]
              · simp [diff, hjn]
        _ =
        (∑ n ∈ Finset.range j, (if j ≤ n then diff n else 0))
          + ∑ n ∈ Finset.Ico j M, (if j ≤ n then diff n else 0) := by
            simpa using
              (Finset.sum_range_add_sum_Ico (fun n => if j ≤ n then diff n else 0) hJM).symm
        _ = ∑ n ∈ Finset.Ico j M, (if j ≤ n then diff n else 0) := by
              have hprefix_zero :
                  ∑ n ∈ Finset.range j, (if j ≤ n then diff n else 0) = 0 := by
                    apply Finset.sum_eq_zero
                    intro n hn
                    simp [(Finset.mem_range.mp hn).not_ge]
              rw [hprefix_zero, zero_add]
        _ = ∑ n ∈ Finset.Ico j M, diff n := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              simp [diff, (Finset.mem_Ico.mp hn).1]
    have hsplit :
        ∑ n ∈ Finset.Ico j M, diff n
          =
        (∑ n ∈ Finset.Ico (j - 1) M, diff n) - diff (j - 1) := by
      have hsub1 :
          ∑ n ∈ Finset.Ico (j - 1) M, diff n
            =
          (∑ n ∈ Finset.range M, diff n) - ∑ n ∈ Finset.range (j - 1), diff n := by
              rw [Finset.sum_Ico_eq_sub _ (by omega : j - 1 ≤ M)]
      have hsub2 :
          ∑ n ∈ Finset.Ico j M, diff n
            =
          (∑ n ∈ Finset.range M, diff n) - ∑ n ∈ Finset.range j, diff n := by
              rw [Finset.sum_Ico_eq_sub _ hJM]
      have hsum_range :
          ∑ n ∈ Finset.range j, diff n
            = ∑ n ∈ Finset.range (j - 1), diff n + diff (j - 1) := by
              calc
                ∑ n ∈ Finset.range j, diff n
                    = ∑ n ∈ Finset.range ((j - 1) + 1), diff n := by
                        congr
                        omega
                _ = ∑ n ∈ Finset.range (j - 1), diff n + diff (j - 1) := by
                      rw [Finset.sum_range_succ]
      rw [hsub1, hsub2]
      rw [hsum_range]
      ring
    have hprefix_bound :
        ‖∑ n ∈ Finset.Ico (j - 1) M, diff n‖
          ≤ 16 * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
      have hraw := atkinsonShiftedSingleBoundaryCoreFixedShiftPrefix_bound (M - 1) j hj
      calc
        ‖∑ n ∈ Finset.Ico (j - 1) M, diff n‖
            ≤ 16 * Real.sqrt (((M - 1 + j : ℕ) : ℝ) + 1) := by
              simpa [diff, show M - 1 + 1 = M by omega,
                Nat.add_assoc, add_left_comm, add_comm] using hraw
        _ = 16 * Real.sqrt ((M + j : ℕ) : ℝ) := by
              have hM : (M - 1 + j : ℕ) + 1 = M + j := by omega
              have hM' : (((M - 1 + j : ℕ) : ℝ) + 1) = ((M + j : ℕ) : ℝ) := by
                exact_mod_cast hM
              rw [hM']
        _ ≤ 16 * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
              exact mul_le_mul_of_nonneg_left
                (Real.sqrt_le_sqrt (by linarith))
                (by positivity)
    have hdiff_bound :
        ‖diff (j - 1)‖ ≤ 2 * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
      calc
        ‖diff (j - 1)‖
            ≤ ‖atkinsonShiftedSingleBoundaryCore (j - 1) (j + 1)‖
              + ‖atkinsonShiftedSingleBoundaryCore (j - 1) j‖ := by
                exact norm_sub_le _ _
        _ = atkinsonModeWeight (j - 1) + atkinsonModeWeight (j - 1) := by
              rw [atkinsonShiftedSingleBoundaryCore_norm (j - 1) (j + 1) (by omega),
                atkinsonShiftedSingleBoundaryCore_norm (j - 1) j hj]
        _ ≤ 1 + 1 := by
              exact add_le_add
                (atkinsonModeWeight_le_one (j - 1))
                (atkinsonModeWeight_le_one (j - 1))
        _ ≤ 2 * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
              have hone : (1 : ℝ) ≤ Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
                have hsq : (1 : ℝ) ≤ (((M + j : ℕ) : ℝ) + 1) := by
                  linarith
                exact (Real.one_le_sqrt).2 hsq
              nlinarith
    calc
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then
            (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonResonantShiftedBoundaryTerm n j
          else 0)‖
        = ‖∑ n ∈ Finset.Ico j M, diff n‖ := by
            rw [hsum]
      _ = ‖(∑ n ∈ Finset.Ico (j - 1) M, diff n) - diff (j - 1)‖ := by
            rw [hsplit]
      _ ≤ ‖∑ n ∈ Finset.Ico (j - 1) M, diff n‖ + ‖diff (j - 1)‖ := by
            exact norm_sub_le _ _
      _ ≤ 16 * Real.sqrt (((M + j : ℕ) : ℝ) + 1)
            + 2 * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
              exact add_le_add hprefix_bound hdiff_bound
      _ = (18 : ℝ) * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by ring

private lemma atkinson_upper_boundary_step
    (n j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
    atkinsonWeightedResonantBlockMode (n + j) 1 * atkinsonShiftedSinglePrimitive (n + j) j 1
      =
    (((atkinsonUpperBoundaryStepCoeff n j : ℝ) : ℂ)) *
        (atkinsonWeightedResonantBlockMode (n + j + 1) 0 *
          atkinsonShiftedSinglePrimitive (n + j + 1) (j + 1) 0) := by
  simpa [atkinsonUpperBoundaryStepCoeff] using
    atkinsonWeightedResonantBlockMode_one_mul_shiftedSinglePrimitive_step
      (n + j) j hj (by omega)

private lemma atkinsonUpperBoundaryStepCoeff_sub_one_eq
    (n j : ℕ) (hj : 1 ≤ j) :
    atkinsonUpperBoundaryStepCoeff n j - 1
      = atkinsonShiftedRelativePhase (n + j + 1) 1 /
          atkinsonShiftedRelativePhase (n + j) j := by
  have hphase_pos :
      0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j hj (by omega)
  unfold atkinsonUpperBoundaryStepCoeff
  have hneq : atkinsonShiftedRelativePhase (n + j) j ≠ 0 := ne_of_gt hphase_pos
  have hstep := atkinsonShiftedRelativePhase_step (n + j) j (by omega)
  field_simp [hneq]
  linarith

private lemma atkinsonUpperBoundaryStepCoeff_sub_one_le
    (n j : ℕ) (hj : 1 ≤ j) :
    atkinsonUpperBoundaryStepCoeff n j - 1 ≤ 1 / j := by
  have hphase_pos :
      0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j hj (by omega)
  have hnum :
      atkinsonShiftedRelativePhase (n + j + 1) 1 ≤ 1 / (((n + j : ℕ) : ℝ) + 1) := by
    have hphi1 :
        atkinsonShiftedRelativePhase (n + j + 1) 1
          = Real.log ((((n + j : ℕ) : ℝ) + 2) / (((n + j : ℕ) : ℝ) + 1)) := by
      unfold atkinsonShiftedRelativePhase
      norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
    calc
      atkinsonShiftedRelativePhase (n + j + 1) 1
          = Real.log ((((n + j : ℕ) : ℝ) + 2) / (((n + j : ℕ) : ℝ) + 1)) := hphi1
      _ ≤ ((((n + j : ℕ) : ℝ) + 2) / (((n + j : ℕ) : ℝ) + 1)) - 1 := by
            exact Real.log_le_sub_one_of_pos (by positivity)
      _ = 1 / (((n + j : ℕ) : ℝ) + 1) := by
            field_simp [show (((n + j : ℕ) : ℝ) + 1) ≠ 0 by positivity]
            ring
  have hden :
      (j : ℝ) / ((((n + j : ℕ) : ℝ) + 1)) ≤ atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_lower (n + j) j hj (by omega)
  have hphi1_nonneg : 0 ≤ atkinsonShiftedRelativePhase (n + j + 1) 1 := by
    exact le_of_lt <|
      atkinsonShiftedRelativePhase_pos (n + j + 1) 1 (by norm_num) (by omega)
  have hj_div_pos : 0 < (j : ℝ) / ((((n + j : ℕ) : ℝ) + 1)) := by positivity
  calc
    atkinsonUpperBoundaryStepCoeff n j - 1
        = atkinsonShiftedRelativePhase (n + j + 1) 1 /
            atkinsonShiftedRelativePhase (n + j) j :=
          atkinsonUpperBoundaryStepCoeff_sub_one_eq n j hj
    _ ≤ atkinsonShiftedRelativePhase (n + j + 1) 1 /
          ((j : ℝ) / ((((n + j : ℕ) : ℝ) + 1))) := by
            exact div_le_div_of_nonneg_left hphi1_nonneg hj_div_pos hden
    _ ≤ (1 / (((n + j : ℕ) : ℝ) + 1) : ℝ) /
          ((j : ℝ) / ((((n + j : ℕ) : ℝ) + 1))) := by
            exact div_le_div_of_nonneg_right hnum hj_div_pos.le
    _ = (1 : ℝ) / j := by
          field_simp [show (j : ℝ) ≠ 0 by positivity,
            show ((((n + j : ℕ) : ℝ) + 1) : ℝ) ≠ 0 by positivity]

private lemma atkinsonUpperBoundaryStepCoeff_one_le
    (n j : ℕ) (hj : 1 ≤ j) :
    1 ≤ atkinsonUpperBoundaryStepCoeff n j := by
  have hphase_pos :
      0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j hj (by omega)
  have hratio :
      atkinsonUpperBoundaryStepCoeff n j - 1
        = atkinsonShiftedRelativePhase (n + j + 1) 1 /
            atkinsonShiftedRelativePhase (n + j) j := by
    unfold atkinsonUpperBoundaryStepCoeff
    have hneq : atkinsonShiftedRelativePhase (n + j) j ≠ 0 := ne_of_gt hphase_pos
    have hstep := atkinsonShiftedRelativePhase_step (n + j) j (by omega)
    field_simp [hneq]
    linarith
  have hsub_nonneg :
      0 ≤ atkinsonUpperBoundaryStepCoeff n j - 1 := by
    rw [hratio]
    exact div_nonneg
      (le_of_lt <| atkinsonShiftedRelativePhase_pos (n + j + 1) 1 (by norm_num) (by omega))
      hphase_pos.le
  linarith

private lemma atkinsonUpperBoundaryStepCoeff_le_two
    (n j : ℕ) (hj : 1 ≤ j) :
    atkinsonUpperBoundaryStepCoeff n j ≤ 2 := by
  have hsub := atkinsonUpperBoundaryStepCoeff_sub_one_le n j hj
  have hfrac : (1 : ℝ) / j ≤ 1 := by
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    simpa using one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1) hj'
  linarith

private noncomputable def atkinsonUpperBoundaryWeightedCoeff (n j : ℕ) : ℝ :=
  2 - atkinsonUpperBoundaryStepCoeff n j

private lemma atkinsonUpperBoundaryWeightedCoeff_nonneg
    (n j : ℕ) (hj : 1 ≤ j) :
    0 ≤ atkinsonUpperBoundaryWeightedCoeff n j := by
  unfold atkinsonUpperBoundaryWeightedCoeff
  linarith [atkinsonUpperBoundaryStepCoeff_le_two n j hj]

private lemma atkinsonUpperBoundaryWeightedCoeff_le_one
    (n j : ℕ) (hj : 1 ≤ j) :
    atkinsonUpperBoundaryWeightedCoeff n j ≤ 1 := by
  unfold atkinsonUpperBoundaryWeightedCoeff
  linarith [atkinsonUpperBoundaryStepCoeff_one_le n j hj]

private noncomputable def atkinsonLogSecantAux (x : ℝ) : ℝ :=
  ((1 + x) * Real.log (1 + x)) / x

private lemma atkinsonLogSecantAux_eq_slope {x : ℝ} (hx : 0 < x) :
    atkinsonLogSecantAux x = slope (fun u : ℝ => u * Real.log u) 1 (1 + x) := by
  rw [slope_def_field]
  unfold atkinsonLogSecantAux
  field_simp [ne_of_gt hx]
  ring_nf
  simp

private lemma atkinsonLogSecantAux_monotoneOn :
    MonotoneOn atkinsonLogSecantAux (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by simpa using hx
  have hy0 : 0 < y := by simpa using hy
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun u : ℝ => u * Real.log u) :=
    convexOn_mul_log
  have hslope := hconv.slope_mono (by simp : (1 : ℝ) ∈ Set.Ici (0 : ℝ))
  have hx' : 1 + x ∈ Set.Ici (0 : ℝ) \ ({1} : Set ℝ) := by
    constructor
    · have h1x : 0 ≤ 1 + x := by linarith
      simpa using h1x
    · simp [hx0.ne']
  have hy' : 1 + y ∈ Set.Ici (0 : ℝ) \ ({1} : Set ℝ) := by
    constructor
    · have h1y : 0 ≤ 1 + y := by linarith
      simpa using h1y
    · simp [hy0.ne']
  have hxy' : 1 + x ≤ 1 + y := by linarith
  have hmono := hslope hx' hy' hxy'
  simpa [atkinsonLogSecantAux_eq_slope hx0, atkinsonLogSecantAux_eq_slope hy0] using hmono

private noncomputable def atkinsonLogSlopeAux (x : ℝ) : ℝ :=
  Real.log (1 + x) / x

private lemma atkinsonLogSlopeAux_eq_slope {x : ℝ} (hx : 0 < x) :
    atkinsonLogSlopeAux x = slope Real.log 1 (1 + x) := by
  rw [slope_def_field]
  unfold atkinsonLogSlopeAux
  field_simp [ne_of_gt hx]
  ring_nf
  simp

private lemma atkinsonLogSlopeAux_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ atkinsonLogSlopeAux x := by
  unfold atkinsonLogSlopeAux
  exact div_nonneg (Real.log_nonneg (by linarith : 1 ≤ 1 + x)) hx.le

private lemma atkinsonLogSlopeAux_antitoneOn :
    AntitoneOn atkinsonLogSlopeAux (Set.Ioi 0) := by
  intro x hx y hy hxy
  rcases lt_or_eq_of_le hxy with hlt | rfl
  · have hx0 : 0 < x := by simpa using hx
    have hy0 : 0 < y := by simpa using hy
    have h1 : (1 : ℝ) ∈ Set.Ioi 0 := by
      simpa using (zero_lt_one : (0 : ℝ) < 1)
    have hx1 : 1 + x ∈ Set.Ioi 0 := by
      show 0 < 1 + x
      linarith
    have hy1 : 1 + y ∈ Set.Ioi 0 := by
      show 0 < 1 + y
      linarith
    have hx_ne : (1 + x : ℝ) ≠ 1 := by linarith
    have hy_ne : (1 + y : ℝ) ≠ 1 := by linarith
    have hsec :=
      strictConcaveOn_log_Ioi.secant_strict_mono
        h1 hx1 hy1 hx_ne hy_ne
        (by linarith : 1 + x < 1 + y)
    exact le_of_lt <| by
      simpa [atkinsonLogSlopeAux, log_one] using hsec
  · simp

private lemma atkinsonLogIncrement_sum
    (j : ℕ) {t : ℝ} (ht : 0 < t) :
    Finset.sum (Finset.range j) (fun r => Real.log (1 + (1 : ℝ) / (t + r)))
      = Real.log (1 + (j : ℝ) / t) := by
  induction j with
  | zero =>
      simp
  | succ j ih =>
      have htj : 0 < t + j := by positivity
      have hA : 0 < 1 + (j : ℝ) / t := by positivity
      have hB : 0 < 1 + (1 : ℝ) / (t + j) := by positivity
      calc
        Finset.sum (Finset.range (j + 1)) (fun r => Real.log (1 + (1 : ℝ) / (t + r)))
            = Finset.sum (Finset.range j) (fun r => Real.log (1 + (1 : ℝ) / (t + r)))
                + Real.log (1 + (1 : ℝ) / (t + j)) := by
                  rw [Finset.sum_range_succ]
        _ = Real.log (1 + (j : ℝ) / t) + Real.log (1 + (1 : ℝ) / (t + j)) := by
              rw [ih]
        _ = Real.log ((1 + (j : ℝ) / t) * (1 + (1 : ℝ) / (t + j))) := by
              rw [← Real.log_mul hA.ne' hB.ne']
        _ = Real.log (1 + ((j + 1 : ℕ) : ℝ) / t) := by
              congr 1
              have ht_ne : t ≠ 0 := ne_of_gt ht
              have htj_ne : t + j ≠ 0 := ne_of_gt htj
              field_simp [ht_ne, htj_ne]
              norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]

private noncomputable def atkinsonUpperBoundaryWeightedCoeffProfile (j : ℕ) (t : ℝ) : ℝ :=
  1 - Real.log (1 + (1 : ℝ) / (t + j)) / Real.log (1 + (j : ℝ) / t)

private lemma atkinsonLogSlopeAux_pos {x : ℝ} (hx : 0 < x) :
    0 < atkinsonLogSlopeAux x := by
  unfold atkinsonLogSlopeAux
  apply div_pos
  · apply Real.log_pos
    have : (1 : ℝ) < 1 + x := by linarith
    simpa using this
  · exact hx

private noncomputable def atkinsonLogIncrementDerivDenom (u : ℝ) : ℝ :=
  (u + 1) * atkinsonLogSlopeAux (1 / u)

private lemma atkinsonLogIncrementDerivDenom_pos {u : ℝ} (hu : 0 < u) :
    0 < atkinsonLogIncrementDerivDenom u := by
  unfold atkinsonLogIncrementDerivDenom
  apply mul_pos
  · linarith
  · exact atkinsonLogSlopeAux_pos (by positivity : 0 < (1 : ℝ) / u)

private lemma atkinsonLogIncrementDerivDenom_monotoneOn :
    MonotoneOn atkinsonLogIncrementDerivDenom (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by simpa using hx
  have hy0 : 0 < y := by simpa using hy
  have hxy1 : x + 1 ≤ y + 1 := by linarith
  have hxy_inv : (1 : ℝ) / y ≤ (1 : ℝ) / x := by
    exact one_div_le_one_div_of_le hx0 hxy
  have hL :
      atkinsonLogSlopeAux ((1 : ℝ) / x) ≤ atkinsonLogSlopeAux ((1 : ℝ) / y) := by
    exact atkinsonLogSlopeAux_antitoneOn
      (by simpa using (show 0 < (1 : ℝ) / y by positivity))
      (by simpa using (show 0 < (1 : ℝ) / x by positivity))
      hxy_inv
  have hLx_nonneg :
      0 ≤ atkinsonLogSlopeAux ((1 : ℝ) / x) := by
    exact (atkinsonLogSlopeAux_pos (by positivity : 0 < (1 : ℝ) / x)).le
  calc
    atkinsonLogIncrementDerivDenom x
        = (x + 1) * atkinsonLogSlopeAux ((1 : ℝ) / x) := by rfl
    _ ≤ (y + 1) * atkinsonLogSlopeAux ((1 : ℝ) / x) := by
          exact mul_le_mul_of_nonneg_right hxy1 hLx_nonneg
    _ ≤ (y + 1) * atkinsonLogSlopeAux ((1 : ℝ) / y) := by
          exact mul_le_mul_of_nonneg_left hL (by linarith : 0 ≤ y + 1)
    _ = atkinsonLogIncrementDerivDenom y := by rfl

private lemma atkinsonLogLogIncrement_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt
      (fun u : ℝ => Real.log (Real.log (1 + (1 : ℝ) / u)))
      (-(1 / atkinsonLogIncrementDerivDenom u)) u := by
  have hu_ne : u ≠ 0 := ne_of_gt hu
  have harg : HasDerivAt (fun v : ℝ => 1 + (1 : ℝ) / v) (-(u ^ 2)⁻¹) u := by
    simpa [one_div, add_comm, add_left_comm, add_assoc] using
      (hasDerivAt_inv hu_ne).const_add (1 : ℝ)
  have harg_ne : 1 + (1 : ℝ) / u ≠ 0 := by
    have : 0 < 1 + (1 : ℝ) / u := by positivity
    linarith
  have hinner :
      HasDerivAt
        (fun u : ℝ => Real.log (1 + (1 : ℝ) / u))
        ((-(u ^ 2)⁻¹) / (1 + (1 : ℝ) / u)) u := by
    exact harg.log harg_ne
  have hinner_pos :
      0 < Real.log (1 + (1 : ℝ) / u) := by
    apply Real.log_pos
    have hfrac : 0 < (1 : ℝ) / u := by positivity
    have : (1 : ℝ) < 1 + (1 : ℝ) / u := by linarith
    simpa using this
  have houter :
      HasDerivAt
        (fun u : ℝ => Real.log (Real.log (1 + (1 : ℝ) / u)))
        (((( -(u ^ 2)⁻¹) / (1 + (1 : ℝ) / u)) / Real.log (1 + (1 : ℝ) / u))) u := by
    exact hinner.log hinner_pos.ne'
  have hcalc :
      (((-(u ^ 2)⁻¹) / (1 + (1 : ℝ) / u)) / Real.log (1 + (1 : ℝ) / u))
        = -(1 / atkinsonLogIncrementDerivDenom u) := by
    unfold atkinsonLogIncrementDerivDenom atkinsonLogSlopeAux
    have hu1_ne : u + 1 ≠ 0 := by linarith
    field_simp [hu_ne, hu1_ne, harg_ne, hinner_pos.ne']
  convert houter using 1
  exact hcalc.symm

private lemma atkinsonLogIncrementRatio_antitoneOn_atomic
    (r s : ℕ) (hrs : r ≤ s) :
    AntitoneOn
      (fun t : ℝ =>
        Real.log (1 + (1 : ℝ) / (t + r)) /
          Real.log (1 + (1 : ℝ) / (t + s)))
      (Set.Ioi 0) := by
  let F : ℝ → ℝ := fun t =>
    Real.log (Real.log (1 + (1 : ℝ) / (t + r)))
      - Real.log (Real.log (1 + (1 : ℝ) / (t + s)))
  have hF_diff : DifferentiableOn ℝ F (Set.Ioi 0) := by
    intro t ht
    have ht0 : 0 < t := by simpa using ht
    have htr : 0 < t + r := by positivity
    have hts : 0 < t + s := by positivity
    have hDr :
        HasDerivAt (fun t : ℝ => Real.log (Real.log (1 + (1 : ℝ) / (t + r))))
          (-(1 / atkinsonLogIncrementDerivDenom (t + r))) t := by
      simpa [F, add_comm, add_left_comm, add_assoc] using
        (atkinsonLogLogIncrement_hasDerivAt htr).comp t ((hasDerivAt_id t).add_const (r : ℝ))
    have hDs :
        HasDerivAt (fun t : ℝ => Real.log (Real.log (1 + (1 : ℝ) / (t + s))))
          (-(1 / atkinsonLogIncrementDerivDenom (t + s))) t := by
      simpa [F, add_comm, add_left_comm, add_assoc] using
        (atkinsonLogLogIncrement_hasDerivAt hts).comp t ((hasDerivAt_id t).add_const (s : ℝ))
    exact (hDr.sub hDs).differentiableAt.differentiableWithinAt
  have hF_anti : AntitoneOn F (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi (0 : ℝ))
    · exact hF_diff.continuousOn
    · simpa using hF_diff
    · intro t ht
      have ht0 : 0 < t := by simpa using ht
      have htr : 0 < t + r := by positivity
      have hts : 0 < t + s := by positivity
      have hDr :
          HasDerivAt (fun t : ℝ => Real.log (Real.log (1 + (1 : ℝ) / (t + r))))
            (-(1 / atkinsonLogIncrementDerivDenom (t + r))) t := by
        simpa [F, add_comm, add_left_comm, add_assoc] using
          (atkinsonLogLogIncrement_hasDerivAt htr).comp t ((hasDerivAt_id t).add_const (r : ℝ))
      have hDs :
          HasDerivAt (fun t : ℝ => Real.log (Real.log (1 + (1 : ℝ) / (t + s))))
            (-(1 / atkinsonLogIncrementDerivDenom (t + s))) t := by
        simpa [F, add_comm, add_left_comm, add_assoc] using
          (atkinsonLogLogIncrement_hasDerivAt hts).comp t ((hasDerivAt_id t).add_const (s : ℝ))
      have hden_mono :
          atkinsonLogIncrementDerivDenom (t + r)
            ≤ atkinsonLogIncrementDerivDenom (t + s) := by
        have htrs : t + r ≤ t + s := by
          have hrsR : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrs
          linarith
        exact atkinsonLogIncrementDerivDenom_monotoneOn
          (by simpa using htr)
          (by simpa using hts)
          htrs
      have hrec :
          (1 : ℝ) / atkinsonLogIncrementDerivDenom (t + s)
            ≤ (1 : ℝ) / atkinsonLogIncrementDerivDenom (t + r) := by
        exact one_div_le_one_div_of_le
          (atkinsonLogIncrementDerivDenom_pos htr) hden_mono
      have hderivF : deriv F t = (-(1 / atkinsonLogIncrementDerivDenom (t + r))) -
          (-(1 / atkinsonLogIncrementDerivDenom (t + s))) := by
        simpa [F] using (hDr.sub hDs).deriv
      rw [hderivF]
      linarith
  intro x hx y hy hxy
  have hFxy : F y ≤ F x := hF_anti hx hy hxy
  have hx_num_pos :
      0 < Real.log (1 + (1 : ℝ) / (x + r)) := by
    apply Real.log_pos
    have hx0' : 0 < x := by simpa using hx
    have hfrac : 0 < (1 : ℝ) / (x + r) := by positivity
    have : (1 : ℝ) < 1 + (1 : ℝ) / (x + r) := by linarith
    simpa using this
  have hx_den_pos :
      0 < Real.log (1 + (1 : ℝ) / (x + s)) := by
    apply Real.log_pos
    have hx0' : 0 < x := by simpa using hx
    have hfrac : 0 < (1 : ℝ) / (x + s) := by positivity
    have : (1 : ℝ) < 1 + (1 : ℝ) / (x + s) := by linarith
    simpa using this
  have hy_num_pos :
      0 < Real.log (1 + (1 : ℝ) / (y + r)) := by
    apply Real.log_pos
    have hy0' : 0 < y := by simpa using hy
    have hfrac : 0 < (1 : ℝ) / (y + r) := by positivity
    have : (1 : ℝ) < 1 + (1 : ℝ) / (y + r) := by linarith
    simpa using this
  have hy_den_pos :
      0 < Real.log (1 + (1 : ℝ) / (y + s)) := by
    apply Real.log_pos
    have hy0' : 0 < y := by simpa using hy
    have hfrac : 0 < (1 : ℝ) / (y + s) := by positivity
    have : (1 : ℝ) < 1 + (1 : ℝ) / (y + s) := by linarith
    simpa using this
  have hx_repr :
      Real.exp (F x)
        = Real.log (1 + (1 : ℝ) / (x + r)) /
            Real.log (1 + (1 : ℝ) / (x + s)) := by
    unfold F
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hx_num_pos, Real.exp_neg,
      Real.exp_log hx_den_pos]
    ring_nf
  have hy_repr :
      Real.exp (F y)
        = Real.log (1 + (1 : ℝ) / (y + r)) /
            Real.log (1 + (1 : ℝ) / (y + s)) := by
    unfold F
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hy_num_pos, Real.exp_neg,
      Real.exp_log hy_den_pos]
    ring_nf
  calc
    Real.log (1 + (1 : ℝ) / (y + r)) / Real.log (1 + (1 : ℝ) / (y + s))
        = Real.exp (F y) := by rw [hy_repr]
    _ ≤ Real.exp (F x) := Real.exp_le_exp.mpr hFxy
    _ = Real.log (1 + (1 : ℝ) / (x + r)) / Real.log (1 + (1 : ℝ) / (x + s)) := by rw [hx_repr]

private lemma atkinsonUpperBoundaryWeightedCoeffProfile_antitoneOn_atomic
    (j : ℕ) (hj : 1 ≤ j) :
    AntitoneOn (atkinsonUpperBoundaryWeightedCoeffProfile j) (Set.Ioi 0) := by
  let inc : ℕ → ℝ → ℝ := fun r t => Real.log (1 + (1 : ℝ) / (t + r))
  let ratioSum : ℝ → ℝ := fun t =>
    Finset.sum (Finset.range j) (fun r => inc r t / inc j t)
  have hinc_pos : ∀ {r : ℕ} {t : ℝ}, 0 < t → 0 < inc r t := by
    intro r t ht
    unfold inc
    apply Real.log_pos
    have hfrac : 0 < (1 : ℝ) / (t + r) := by positivity
    have : (1 : ℝ) < 1 + (1 : ℝ) / (t + r) := by linarith
    simpa using this
  have hden_pos : ∀ {t : ℝ}, 0 < t → 0 < Real.log (1 + (j : ℝ) / t) := by
    intro t ht
    apply Real.log_pos
    have hj' : (0 : ℝ) < j := by exact_mod_cast hj
    have hfrac : 0 < (j : ℝ) / t := by positivity
    have : (1 : ℝ) < 1 + (j : ℝ) / t := by linarith
    simpa using this
  have hratioSum_antitone : AntitoneOn ratioSum (Set.Ioi 0) := by
    intro x hx y hy hxy
    unfold ratioSum
    refine Finset.sum_le_sum ?_
    intro r hr
    exact atkinsonLogIncrementRatio_antitoneOn_atomic r j
      (Nat.le_of_lt (Finset.mem_range.mp hr)) hx hy hxy
  have hratioSum_eq :
      ∀ {t : ℝ}, 0 < t → ratioSum t = Real.log (1 + (j : ℝ) / t) / inc j t := by
    intro t ht
    unfold ratioSum
    calc
      Finset.sum (Finset.range j) (fun r => inc r t / inc j t)
          = (Finset.sum (Finset.range j) fun r => inc r t) / inc j t := by
              simp [div_eq_mul_inv, Finset.sum_mul]
      _ = Real.log (1 + (j : ℝ) / t) / inc j t := by
            rw [atkinsonLogIncrement_sum j ht]
  intro x hx y hy hxy
  have hx0 : 0 < x := by simpa using hx
  have hy0 : 0 < y := by simpa using hy
  have hSxy : ratioSum y ≤ ratioSum x := hratioSum_antitone hx hy hxy
  have hSx_pos : 0 < ratioSum x := by
    rw [hratioSum_eq hx0]
    exact div_pos (hden_pos hx0) (hinc_pos hx0)
  have hSy_pos : 0 < ratioSum y := by
    rw [hratioSum_eq hy0]
    exact div_pos (hden_pos hy0) (hinc_pos hy0)
  have hInv : 1 / ratioSum x ≤ 1 / ratioSum y := by
    exact one_div_le_one_div_of_le hSy_pos hSxy
  have hx_eq :
      atkinsonUpperBoundaryWeightedCoeffProfile j x = 1 - 1 / ratioSum x := by
    unfold atkinsonUpperBoundaryWeightedCoeffProfile
    change 1 - inc j x / Real.log (1 + (j : ℝ) / x) = 1 - 1 / ratioSum x
    rw [hratioSum_eq hx0]
    field_simp [ne_of_gt (hden_pos hx0), ne_of_gt (hinc_pos (r := j) hx0)]
  have hy_eq :
      atkinsonUpperBoundaryWeightedCoeffProfile j y = 1 - 1 / ratioSum y := by
    unfold atkinsonUpperBoundaryWeightedCoeffProfile
    change 1 - inc j y / Real.log (1 + (j : ℝ) / y) = 1 - 1 / ratioSum y
    rw [hratioSum_eq hy0]
    field_simp [ne_of_gt (hden_pos hy0), ne_of_gt (hinc_pos (r := j) hy0)]
  rw [hx_eq, hy_eq]
  linarith

private lemma atkinsonLogPrefixRatio_antitoneOn_atomic
    (r j : ℕ) (hr : 1 ≤ r) (hrj : r ≤ j) :
    AntitoneOn
      (fun t : ℝ =>
        Real.log (1 + (r : ℝ) / t) /
          Real.log (1 + (j : ℝ) / t))
      (Set.Ioi 0) := by
  let inc : ℕ → ℝ → ℝ := fun u t => Real.log (1 + (1 : ℝ) / (t + u))
  let prefSum : ℕ → ℝ → ℝ := fun m t =>
    Finset.sum (Finset.range m) (fun u => inc u t)
  let tail : ℝ → ℝ := fun t =>
    Finset.sum (Finset.Ico r j) (fun u => inc u t)
  have hinc_pos : ∀ {u : ℕ} {t : ℝ}, 0 < t → 0 < inc u t := by
    intro u t ht
    unfold inc
    apply Real.log_pos
    have hfrac : 0 < (1 : ℝ) / (t + u) := by positivity
    have : (1 : ℝ) < 1 + (1 : ℝ) / (t + u) := by linarith
    simpa using this
  have hprefix_eq :
      ∀ (m : ℕ) {t : ℝ}, 0 < t →
        prefSum m t = Real.log (1 + (m : ℝ) / t) := by
    intro m t ht
    simpa [prefSum, inc] using atkinsonLogIncrement_sum m ht
  have hprefix_pos :
      ∀ {m : ℕ} {t : ℝ}, 1 ≤ m → 0 < t → 0 < prefSum m t := by
    intro m t hm ht
    rw [hprefix_eq m ht]
    apply Real.log_pos
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hfrac : 0 < (m : ℝ) / t := by positivity
    have : (1 : ℝ) < 1 + (m : ℝ) / t := by linarith
    simpa using this
  have hprefix_split : ∀ t : ℝ, prefSum j t = prefSum r t + tail t := by
    intro t
    unfold prefSum tail
    rw [← Finset.sum_range_add_sum_Ico (fun u => inc u t) hrj]
  intro x hx y hy hxy
  have hx0 : 0 < x := by simpa using hx
  have hy0 : 0 < y := by simpa using hy
  have hcross :
      prefSum r y * tail x ≤ prefSum r x * tail y := by
    calc
      prefSum r y * tail x
          =
        ∑ u ∈ Finset.range r, ∑ v ∈ Finset.Ico r j, inc u y * inc v x := by
            simp [prefSum, tail, mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum, Finset.sum_mul]
      _ ≤
        ∑ u ∈ Finset.range r, ∑ v ∈ Finset.Ico r j, inc u x * inc v y := by
            refine Finset.sum_le_sum ?_
            intro u hu
            refine Finset.sum_le_sum ?_
            intro v hv
            have huv : u ≤ v := by
              exact le_trans (Nat.le_of_lt (Finset.mem_range.mp hu)) (Finset.mem_Ico.mp hv).1
            have hratio :=
              atkinsonLogIncrementRatio_antitoneOn_atomic u v huv hx hy hxy
            have hvx_pos : 0 < inc v x := hinc_pos hx0
            have hvy_pos : 0 < inc v y := hinc_pos hy0
            have hcross_uv : inc u y * inc v x ≤ inc u x * inc v y := by
              simpa [inc, mul_assoc, mul_left_comm, mul_comm] using
                (div_le_div_iff₀ (hinc_pos hy0) (hinc_pos hx0)).1 hratio
            simpa [mul_assoc, mul_left_comm, mul_comm] using hcross_uv
      _ = prefSum r x * tail y := by
            simpa [prefSum, tail, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm,
              mul_assoc] using
              (Finset.sum_comm
                (s := Finset.range r)
                (t := Finset.Ico r j)
                (f := fun u v => inc u x * inc v y))
  have hj_pos : 1 ≤ j := le_trans hr hrj
  have hratio_cross :
      prefSum r y * prefSum j x ≤ prefSum r x * prefSum j y := by
    rw [hprefix_split x, hprefix_split y]
    nlinarith [hcross]
  have hden_y_pos : 0 < prefSum j y := hprefix_pos hj_pos hy0
  have hden_x_pos : 0 < prefSum j x := hprefix_pos hj_pos hx0
  have hratio :
      prefSum r y / prefSum j y ≤ prefSum r x / prefSum j x := by
    exact (div_le_div_iff₀ hden_y_pos hden_x_pos).2 hratio_cross
  calc
    Real.log (1 + (r : ℝ) / y) / Real.log (1 + (j : ℝ) / y)
        = prefSum r y / prefSum j y := by
            rw [← hprefix_eq r hy0, ← hprefix_eq j hy0]
    _ ≤ prefSum r x / prefSum j x := hratio
    _ = Real.log (1 + (r : ℝ) / x) / Real.log (1 + (j : ℝ) / x) := by
          rw [← hprefix_eq r hx0, ← hprefix_eq j hx0]

private lemma atkinsonUpperBoundaryWeightedCoeff_eq_profile
    (n j : ℕ) (hj : 1 ≤ j) :
    atkinsonUpperBoundaryWeightedCoeff n j
      = atkinsonUpperBoundaryWeightedCoeffProfile j ((n : ℝ) + 1) := by
  have hphase_pos :
      0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j hj (by omega)
  have hstep := atkinsonShiftedRelativePhase_step (n + j) j (by omega)
  have hratio :
      atkinsonUpperBoundaryStepCoeff n j
        = 1 + atkinsonShiftedRelativePhase (n + j + 1) 1 /
            atkinsonShiftedRelativePhase (n + j) j := by
    unfold atkinsonUpperBoundaryStepCoeff
    have hneq : atkinsonShiftedRelativePhase (n + j) j ≠ 0 := ne_of_gt hphase_pos
    field_simp [hneq]
    linarith
  have hphi1 :
      atkinsonShiftedRelativePhase (n + j + 1) 1
        = Real.log (1 + (1 : ℝ) / (((n + j : ℕ) : ℝ) + 1)) := by
    unfold atkinsonShiftedRelativePhase
    norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
    have hneq : ((((n + j : ℕ) : ℝ) + 1) : ℝ) ≠ 0 := by positivity
    field_simp [hneq]
    ring_nf
  have hphij :
      atkinsonShiftedRelativePhase (n + j) j
        = Real.log (1 + (j : ℝ) / (((n : ℕ) : ℝ) + 1)) := by
    unfold atkinsonShiftedRelativePhase
    have hsub : n + j - j = n := by omega
    rw [show (((n + j : ℕ) : ℝ) + 1) / ((((n + j - j : ℕ) : ℝ) + 1))
          = (((n + j : ℕ) : ℝ) + 1) / (((n : ℕ) : ℝ) + 1) by simpa [hsub]]
    have hneq : ((((n : ℕ) : ℝ) + 1) : ℝ) ≠ 0 := by positivity
    have hcast :
        (((n + j : ℕ) : ℝ) + 1) = (((n : ℕ) : ℝ) + 1) + j := by
      norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
    rw [show ((((n + j : ℕ) : ℝ) + 1) / (((n : ℕ) : ℝ) + 1))
          = 1 + (j : ℝ) / (((n : ℕ) : ℝ) + 1) by
            rw [hcast]
            field_simp [hneq]]
  unfold atkinsonUpperBoundaryWeightedCoeff atkinsonUpperBoundaryWeightedCoeffProfile
  rw [hratio, hphi1, hphij]
  simp [div_eq_mul_inv]
  ring_nf

private lemma atkinsonUpperBoundaryWeightedCoeff_antitone
    (j : ℕ) (hj : 1 ≤ j) :
    Antitone (fun n => atkinsonUpperBoundaryWeightedCoeff n j) := by
  intro m n hmn
  change atkinsonUpperBoundaryWeightedCoeff n j ≤ atkinsonUpperBoundaryWeightedCoeff m j
  rw [atkinsonUpperBoundaryWeightedCoeff_eq_profile n j hj,
    atkinsonUpperBoundaryWeightedCoeff_eq_profile m j hj]
  exact atkinsonUpperBoundaryWeightedCoeffProfile_antitoneOn_atomic j hj
    (by positivity : 0 < ((m : ℝ) + 1))
    (by positivity : 0 < ((n : ℝ) + 1))
    (by exact_mod_cast Nat.succ_le_succ hmn)

private lemma atkinsonUpperBoundaryStepCoeff_monotone
    (j : ℕ) (hj : 1 ≤ j) :
    Monotone (fun n => atkinsonUpperBoundaryStepCoeff n j) := by
  intro m n hmn
  have hweight :=
    atkinsonUpperBoundaryWeightedCoeff_antitone j hj hmn
  unfold atkinsonUpperBoundaryWeightedCoeff at hweight
  linarith

private lemma atkinsonUpperBoundaryStepCoeff_inv_nonneg
    (n j : ℕ) (hj : 1 ≤ j) :
    0 ≤ 1 / atkinsonUpperBoundaryStepCoeff n j := by
  exact one_div_nonneg.mpr (atkinsonUpperBoundaryStepCoeff_nonneg n j hj)

private lemma atkinsonUpperBoundaryStepCoeff_inv_le_one
    (n j : ℕ) (hj : 1 ≤ j) :
    1 / atkinsonUpperBoundaryStepCoeff n j ≤ 1 := by
  calc
    1 / atkinsonUpperBoundaryStepCoeff n j ≤ 1 / (1 : ℝ) := by
      exact one_div_le_one_div_of_le
        (by positivity : (0 : ℝ) < 1)
        (atkinsonUpperBoundaryStepCoeff_one_le n j hj)
    _ = 1 := by norm_num

private lemma atkinsonUpperBoundaryStepCoeff_inv_antitone
    (j : ℕ) (hj : 1 ≤ j) :
    Antitone (fun n => 1 / atkinsonUpperBoundaryStepCoeff n j) := by
  intro m n hmn
  exact one_div_le_one_div_of_le
    (atkinsonUpperBoundaryStepCoeff_pos m j hj)
    (atkinsonUpperBoundaryStepCoeff_monotone j hj hmn)

private lemma atkinsonLowerBoundary_step_inv
    (n j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
    atkinsonWeightedResonantBlockMode (n + (j + 1)) 0 *
        atkinsonShiftedSinglePrimitive (n + (j + 1)) (j + 1) 0
      =
    (((1 / atkinsonUpperBoundaryStepCoeff n j : ℝ) : ℂ)) *
      (atkinsonWeightedResonantBlockMode (n + j) 1 *
        atkinsonShiftedSinglePrimitive (n + j) j 1) := by
  have hstep := atkinson_upper_boundary_step n j hj hjn
  have hcoeff_ne : atkinsonUpperBoundaryStepCoeff n j ≠ 0 := by
    exact ne_of_gt (atkinsonUpperBoundaryStepCoeff_pos n j hj)
  calc
    atkinsonWeightedResonantBlockMode (n + (j + 1)) 0 *
          atkinsonShiftedSinglePrimitive (n + (j + 1)) (j + 1) 0
        =
      ((((1 / atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) *
        ((((atkinsonUpperBoundaryStepCoeff n j : ℝ) : ℂ)) *
          (atkinsonWeightedResonantBlockMode (n + (j + 1)) 0 *
            atkinsonShiftedSinglePrimitive (n + (j + 1)) (j + 1) 0)) := by
              rw [← mul_assoc]
              have hmul :
                  ((((1 / atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) *
                      (((atkinsonUpperBoundaryStepCoeff n j : ℝ) : ℂ))
                    = 1 := by
                rw [← Complex.ofReal_mul]
                congr 1
                field_simp [hcoeff_ne]
              rw [hmul, one_mul]
    _ =
      ((((1 / atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) *
        (atkinsonWeightedResonantBlockMode (n + j) 1 *
          atkinsonShiftedSinglePrimitive (n + j) j 1) := by
              simpa [mul_assoc] using
                congrArg
                  (fun z =>
                    ((((1 / atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) * z)
                  hstep.symm

private lemma atkinson_complete_prefix_eq_sum_range (n a : ℕ) :
    ∫ t in Ioc (hardyStart (n + 1)) (hardyStart (n + 1 + a)), hardyCos n t
      =
    ∑ q ∈ Finset.range a,
      ∫ t in Ioc (hardyStart (n + 1 + q)) (hardyStart (n + 1 + q + 1)), hardyCos n t := by
  induction a with
  | zero =>
      simp
  | succ a ih =>
      have hab : hardyStart (n + 1) ≤ hardyStart (n + 1 + a) := by
        exact hardyStart_mono (by omega)
      have hbc : hardyStart (n + 1 + a) ≤ hardyStart (n + 1 + a + 1) := by
        exact hardyStart_mono (Nat.le_succ _)
      calc
        ∫ t in Ioc (hardyStart (n + 1)) (hardyStart (n + 1 + (a + 1))), hardyCos n t
            =
          (∫ t in Ioc (hardyStart (n + 1)) (hardyStart (n + 1 + a)), hardyCos n t)
            + ∫ t in Ioc (hardyStart (n + 1 + a)) (hardyStart (n + 1 + a + 1)), hardyCos n t := by
              simpa [Nat.add_assoc, add_left_comm, add_comm] using
                hardyCos_ioc_integral_split n hab hbc
        _ =
          (∑ q ∈ Finset.range a,
              ∫ t in Ioc (hardyStart (n + 1 + q)) (hardyStart (n + 1 + q + 1)),
                hardyCos n t)
            + ∫ t in Ioc (hardyStart (n + 1 + a)) (hardyStart (n + 1 + a + 1)),
                hardyCos n t := by
                  rw [ih]
        _ =
          ∑ q ∈ Finset.range (a + 1),
            ∫ t in Ioc (hardyStart (n + 1 + q)) (hardyStart (n + 1 + q + 1)),
              hardyCos n t := by
                rw [Finset.sum_range_succ]

private lemma atkinson_shift_sum_eq_Icc (n J : ℕ) :
    ∑ q ∈ Finset.range J, atkinsonShiftedCompleteCell n (q + 1)
      =
    ∑ j ∈ Finset.Icc 1 J, atkinsonShiftedCompleteCell n j := by
  refine Finset.sum_bij' (fun q _ => q + 1) (fun j _ => j - 1) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    simp [Finset.mem_range, Finset.mem_Icc] at hq ⊢
    omega
  · intro j hj
    simp [Finset.mem_range, Finset.mem_Icc] at hj ⊢
    omega
  · intro q hq
    simpa using Nat.succ_pred_eq_of_pos (Nat.succ_pos q)
  · intro j hj
    simpa using Nat.sub_add_cancel ((Finset.mem_Icc.mp hj).1)
  · intro q hq
    rfl

private lemma atkinson_weighted_complete_integral_eq_shift_sum (n N : ℕ) (hnN : n < N - 1) :
    atkinsonModeWeight n *
        ∫ t in Ioc (hardyStart (n + 1))
          (hardyStart (min (2 * n + 1) (N - 1))), hardyCos n t
      =
    ∑ j ∈ Finset.Icc 1 (min n (N - n - 2)), atkinsonShiftedCompleteCell n j := by
  let J : ℕ := min n (N - n - 2)
  have hupper : n + 1 + J = min (2 * n + 1) (N - 1) := by
    dsimp [J]
    omega
  calc
    atkinsonModeWeight n *
        ∫ t in Ioc (hardyStart (n + 1))
          (hardyStart (min (2 * n + 1) (N - 1))), hardyCos n t
      =
    atkinsonModeWeight n *
        ∫ t in Ioc (hardyStart (n + 1)) (hardyStart (n + 1 + J)), hardyCos n t := by
          rw [hupper]
    _ = ∑ q ∈ Finset.range J, atkinsonShiftedCompleteCell n (q + 1) := by
          rw [atkinson_complete_prefix_eq_sum_range n J, Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro q hq
          simp [atkinsonShiftedCompleteCell, Nat.add_assoc, add_left_comm, add_comm]
    _ = ∑ j ∈ Finset.Icc 1 J, atkinsonShiftedCompleteCell n j := by
          exact atkinson_shift_sum_eq_Icc n J

private lemma atkinson_sum_Icc_pad (f : ℕ → ℝ) {J K : ℕ} (hJK : J ≤ K) :
    ∑ j ∈ Finset.Icc 1 J, f j
      =
    ∑ j ∈ Finset.Icc 1 K, (if j ≤ J then f j else 0) := by
  calc
    ∑ j ∈ Finset.Icc 1 J, f j
        = ∑ j ∈ Finset.Icc 1 J, (if j ≤ J then f j else 0) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [(Finset.mem_Icc.mp hj).2]
    _ = ∑ j ∈ Finset.Icc 1 K, (if j ≤ J then f j else 0) := by
          exact Finset.sum_subset
            (by
              intro j hj
              exact Finset.mem_Icc.mpr
                ⟨(Finset.mem_Icc.mp hj).1, le_trans (Finset.mem_Icc.mp hj).2 hJK⟩)
            (by
              intro j hjK hjJ
              have hjK' := Finset.mem_Icc.mp hjK
              have hnot : ¬ j ≤ J := by
                intro hjle
                exact hjJ (Finset.mem_Icc.mpr ⟨hjK'.1, hjle⟩)
              simp [hnot])

private lemma atkinson_harmonic_Icc_le_one_add_log (J : ℕ) (hJ : 1 ≤ J) :
    ∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / j ≤ 1 + Real.log (J : ℝ) := by
  have hsum : ∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / j = (harmonic J : ℝ) := by
    norm_num [harmonic_eq_sum_Icc, one_div]
  rw [hsum]
  simpa using harmonic_floor_le_one_add_log (J : ℝ) (by exact_mod_cast hJ)

private lemma atkinson_blockOmega_continuous (n : ℕ) :
    Continuous (Aristotle.StationaryPhaseMainMode.blockOmega n) := by
  have htheta : Continuous ThetaDerivAsymptotic.thetaDeriv :=
    continuous_iff_continuousAt.mpr fun t => (ThetaDerivMonotone.thetaDeriv_hasDerivAt t).continuousAt
  unfold Aristotle.StationaryPhaseMainMode.blockOmega
  exact ((htheta.comp (blockCoord_continuous n)).sub continuous_const).mul
    (blockJacobian_continuous n)

private theorem atkinsonShiftedPacketPhase_integral_bound (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    ‖∫ u in (0 : ℝ)..1, atkinsonShiftedPacketPhase k j u‖ ≤ 3 / (4 * Real.pi * j) := by
  have hm_pos : 0 < 4 * Real.pi * j := by positivity
  have hBound :=
    Aristotle.ComplexVdC.complex_vdc_angular
      (atkinsonShiftedPacketPhase k j) (atkinsonShiftedPacketOmega k j) (0 : ℝ) 1 (4 * Real.pi * j)
      (by norm_num) hm_pos
      (fun u hu => atkinsonShiftedPacketPhase_hasDerivAt k j u)
      (fun u hu => by simpa using (le_of_eq (atkinson_norm_shiftedPacketPhase k j u)))
      (atkinson_differentiable_shiftedPacketOmega k j)
      (atkinson_continuous_deriv_shiftedPacketOmega k j)
      (atkinsonShiftedPacketOmega_lower k j hj hjk)
      (fun u hu => by
        rw [atkinson_deriv_shiftedPacketOmega]
        have hphase_nonneg : 0 ≤ atkinsonShiftedRelativePhase k j := by
          exact le_of_lt (atkinsonShiftedRelativePhase_pos k j hj hjk)
        nlinarith [Real.pi_pos, hphase_nonneg])
  simpa [atkinsonShiftedPacketPhase] using hBound

private theorem atkinsonWeightedResonantBlockMode_deriv_bound_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ k : ℕ, N0 ≤ k →
      ∀ u ∈ Icc (0 : ℝ) 1,
        ‖Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega k u : ℝ) : ℂ) *
            atkinsonWeightedResonantBlockMode k u‖
          ≤ C * atkinsonModeWeight k := by
  obtain ⟨C0, hC0, N0, hOmega⟩ :=
    Aristotle.StationaryPhaseMainMode.blockOmega_linear_model_eventually
  let C : ℝ := C0 + 4 * Real.pi + 1
  refine ⟨C, by
    dsimp [C]
    positivity, N0, ?_⟩
  intro k hk u hu
  have hω := hOmega k hk u hu
  have hω_bound : |Aristotle.StationaryPhaseMainMode.blockOmega k u| ≤ C := by
    dsimp [C]
    have hlin : |4 * Real.pi * u| ≤ 4 * Real.pi := by
      have hnonneg : 0 ≤ 4 * Real.pi * u := by
        nlinarith [hu.1, Real.pi_pos]
      rw [abs_of_nonneg hnonneg]
      nlinarith [Real.pi_pos, hu.1, hu.2]
    have htri :
        |Aristotle.StationaryPhaseMainMode.blockOmega k u|
          ≤ |Aristotle.StationaryPhaseMainMode.blockOmega k u - 4 * Real.pi * u| + |4 * Real.pi * u| := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, Real.norm_eq_abs] using
        (norm_add_le (Aristotle.StationaryPhaseMainMode.blockOmega k u - 4 * Real.pi * u) (4 * Real.pi * u))
    calc
      |Aristotle.StationaryPhaseMainMode.blockOmega k u|
          ≤ |Aristotle.StationaryPhaseMainMode.blockOmega k u - 4 * Real.pi * u| + |4 * Real.pi * u| := htri
      _ ≤ C0 / ((k : ℝ) + 1) + 4 * Real.pi := by
            gcongr
      _ ≤ C0 + 4 * Real.pi := by
            have hk1_pos : 0 < (k : ℝ) + 1 := by positivity
            have hfrac : C0 / ((k : ℝ) + 1) ≤ C0 := by
              have hC0_nonneg : 0 ≤ C0 := le_of_lt hC0
              exact (div_le_iff₀ hk1_pos).2 (by nlinarith)
            linarith
      _ ≤ C := by
            dsimp [C]
            linarith
  rw [atkinsonWeightedResonantBlockMode_deriv_norm]
  exact mul_le_mul_of_nonneg_right hω_bound (le_of_lt (atkinsonModeWeight_pos k))

private lemma atkinson_inverse_phase_core_eq_lowerBoundaryTerm
    (n j : ℕ) (hj : 1 ≤ j) :
    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n j)
      =
    atkinsonWeightedResonantBlockMode (n + j) 0 *
      atkinsonShiftedSinglePrimitive (n + j) j 0 := by
  have hphase_pos :
      0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j hj (by omega)
  have hphase_ne : (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt hphase_pos
  have hmul :
      ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)))
        =
      (1 : ℂ) := by
        rw [← Complex.ofReal_mul]
        congr 1
        field_simp [ne_of_gt hphase_pos]
  unfold atkinsonShiftedSingleBoundaryCore
  calc
    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            (atkinsonWeightedResonantBlockMode (n + j) 0 *
              atkinsonShiftedSinglePrimitive (n + j) j 0)))
        =
      ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ))) *
        (atkinsonWeightedResonantBlockMode (n + j) 0 *
          atkinsonShiftedSinglePrimitive (n + j) j 0) := by
            ring
    _ =
      atkinsonWeightedResonantBlockMode (n + j) 0 *
        atkinsonShiftedSinglePrimitive (n + j) j 0 := by
          rw [hmul, one_mul]

private theorem atkinson_lower_boundary_prefix_head_norm
    (j : ℕ) (hj : 1 ≤ j) :
    ‖∑ n ∈ Finset.range 1,
        atkinsonWeightedResonantBlockMode (n + j) 0 *
          atkinsonShiftedSinglePrimitive (n + j) j 0‖
      =
    1 / Real.log ((j : ℝ) + 1) := by
  calc
    ‖∑ n ∈ Finset.range 1,
        atkinsonWeightedResonantBlockMode (n + j) 0 *
          atkinsonShiftedSinglePrimitive (n + j) j 0‖
      =
    ‖atkinsonWeightedResonantBlockMode j 0 *
        atkinsonShiftedSinglePrimitive j j 0‖ := by
          simp
    _ = atkinsonModeWeight 0 / atkinsonShiftedRelativePhase j j := by
          simpa using atkinsonLowerBoundaryTerm_norm 0 j hj
    _ = 1 / atkinsonShiftedRelativePhase j j := by
          simp [atkinsonModeWeight]
    _ = 1 / Real.log ((j : ℝ) + 1) := by
          rw [atkinsonShiftedRelativePhase_eq_sub_logs]
          simp

private theorem atkinson_inverse_phase_core_prefix_head_norm
    (j : ℕ) (hj : 1 ≤ j) :
    ‖∑ n ∈ Finset.range 1,
        ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n j)‖
      =
    1 / Real.log ((j : ℝ) + 1) := by
  calc
    ‖∑ n ∈ Finset.range 1,
        ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n j)‖
      =
    ‖∑ n ∈ Finset.range 1,
        atkinsonWeightedResonantBlockMode (n + j) 0 *
          atkinsonShiftedSinglePrimitive (n + j) j 0‖ := by
          refine congrArg norm ?_
          refine Finset.sum_congr rfl ?_
          intro n hn
          exact atkinson_inverse_phase_core_eq_lowerBoundaryTerm n j hj
    _ = 1 / Real.log ((j : ℝ) + 1) := atkinson_lower_boundary_prefix_head_norm j hj

private noncomputable def atkinsonLowerBoundaryShiftKernel
    (n j r : ℕ) : ℝ :=
  atkinsonShiftedRelativePhase (n + r) r / atkinsonShiftedRelativePhase (n + j) j

private lemma atkinsonLowerBoundaryShiftKernel_eq_profile
    (n j r : ℕ) :
    atkinsonLowerBoundaryShiftKernel n j r
      =
    Real.log (1 + (r : ℝ) / ((n : ℝ) + 1)) /
      Real.log (1 + (j : ℝ) / ((n : ℝ) + 1)) := by
  unfold atkinsonLowerBoundaryShiftKernel atkinsonShiftedRelativePhase
  have hn_ne : (((n : ℕ) : ℝ) + 1) ≠ 0 := by positivity
  have hnum :
      (((n + r : ℕ) : ℝ) + 1) / ((((n + r - r : ℕ) : ℝ) + 1))
        =
      1 + (r : ℝ) / ((n : ℝ) + 1) := by
    have hsub : n + r - r = n := by omega
    rw [show ((((n + r - r : ℕ) : ℝ) + 1)) = ((n : ℝ) + 1) by simpa [hsub]]
    have hcast : (((n + r : ℕ) : ℝ) + 1) = ((n : ℝ) + 1) + r := by
      norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
    rw [hcast]
    field_simp [hn_ne]
  have hden :
      (((n + j : ℕ) : ℝ) + 1) / ((((n + j - j : ℕ) : ℝ) + 1))
        =
      1 + (j : ℝ) / ((n : ℝ) + 1) := by
    have hsub : n + j - j = n := by omega
    rw [show ((((n + j - j : ℕ) : ℝ) + 1)) = ((n : ℝ) + 1) by simpa [hsub]]
    have hcast : (((n + j : ℕ) : ℝ) + 1) = ((n : ℝ) + 1) + j := by
      norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
    rw [hcast]
    field_simp [hn_ne]
  rw [hnum, hden]

lemma atkinsonLowerBoundaryShiftKernel_nonneg
    (n j r : ℕ) (hr : 1 ≤ r) (hrj : r ≤ j) :
    0 ≤ atkinsonLowerBoundaryShiftKernel n j r := by
  unfold atkinsonLowerBoundaryShiftKernel
  exact div_nonneg
    (le_of_lt (atkinsonShiftedRelativePhase_pos (n + r) r hr (by omega)))
    (le_of_lt (atkinsonShiftedRelativePhase_pos (n + j) j (le_trans hr hrj) (by omega)))

lemma atkinsonLowerBoundaryShiftKernel_self
    (n j : ℕ) (hj : 1 ≤ j) :
    atkinsonLowerBoundaryShiftKernel n j j = 1 := by
  unfold atkinsonLowerBoundaryShiftKernel
  have hphase_pos :
      0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j hj (by omega)
  field_simp [ne_of_gt hphase_pos]

lemma atkinsonLowerBoundaryShiftKernel_antitone
    (j r : ℕ) (hr : 1 ≤ r) (hrj : r ≤ j) :
    Antitone (fun n => atkinsonLowerBoundaryShiftKernel n j r) := by
  intro m n hmn
  simpa [atkinsonLowerBoundaryShiftKernel_eq_profile] using
    (atkinsonLogPrefixRatio_antitoneOn_atomic r j hr hrj
      (by positivity : 0 < ((m : ℕ) : ℝ) + 1)
      (by positivity : 0 < ((n : ℕ) : ℝ) + 1)
      (by exact_mod_cast Nat.succ_le_succ hmn))

lemma atkinsonLowerBoundaryShiftKernel_le_two_mul_div
    (n j r : ℕ) (hr : 1 ≤ r) (hrj : r ≤ j) (hjn : j ≤ n) :
    atkinsonLowerBoundaryShiftKernel n j r ≤ 2 * r / j := by
  unfold atkinsonLowerBoundaryShiftKernel
  have hnum_le :
      atkinsonShiftedRelativePhase (n + r) r ≤ (r : ℝ) / ((n : ℝ) + 1) := by
    simpa [Nat.add_assoc, add_left_comm, add_comm, show n + r - r = n by omega] using
      atkinsonShiftedRelativePhase_upper (n + r) r hr (by omega)
  have hden_le :
      (j : ℝ) / ((((n + j : ℕ) : ℝ) + 1)) ≤ atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_lower (n + j) j (le_trans hr hrj) (by omega)
  have hnum_nonneg :
      0 ≤ atkinsonShiftedRelativePhase (n + r) r := by
    exact le_of_lt <| atkinsonShiftedRelativePhase_pos (n + r) r hr (by omega)
  have hj_nat_pos : 0 < j := by
    omega
  have hj_div_pos : 0 < (j : ℝ) / ((((n + j : ℕ) : ℝ) + 1)) := by
    exact div_pos (by exact_mod_cast hj_nat_pos) (by positivity)
  calc
    atkinsonShiftedRelativePhase (n + r) r / atkinsonShiftedRelativePhase (n + j) j
        ≤
      atkinsonShiftedRelativePhase (n + r) r /
        ((j : ℝ) / ((((n + j : ℕ) : ℝ) + 1))) := by
          exact div_le_div_of_nonneg_left hnum_nonneg hj_div_pos hden_le
    _ ≤ ((r : ℝ) / ((n : ℝ) + 1)) /
          ((j : ℝ) / ((((n + j : ℕ) : ℝ) + 1))) := by
            exact div_le_div_of_nonneg_right hnum_le hj_div_pos.le
    _ = ((((n + j : ℕ) : ℝ) + 1) / ((n : ℝ) + 1)) * ((r : ℝ) / j) := by
          have hj_ne : (j : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hj_nat_pos)
          have hn_ne : ((n : ℝ) + 1) ≠ 0 := by positivity
          field_simp [hj_ne, hn_ne]
    _ ≤ 2 * ((r : ℝ) / j) := by
          have hratio :
              ((((n + j : ℕ) : ℝ) + 1) / ((n : ℝ) + 1)) ≤ 2 := by
            have hmul : (((n + j : ℕ) : ℝ) + 1) ≤ 2 * ((n : ℝ) + 1) := by
              exact_mod_cast (by omega : n + j + 1 ≤ 2 * (n + 1))
            exact (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2 <| by nlinarith
          have hdiv_nonneg : 0 ≤ (r : ℝ) / j := by positivity
          nlinarith
    _ = 2 * r / j := by ring

private lemma atkinsonLowerBoundaryShiftKernel_step_mul
    (n j r : ℕ) (hr : 1 ≤ r) (hrj : r ≤ j) :
    atkinsonLowerBoundaryShiftKernel n (j + 1) r
      =
    (1 / atkinsonUpperBoundaryStepCoeff n j) *
      atkinsonLowerBoundaryShiftKernel n j r := by
  have hr_phase_pos :
      0 < atkinsonShiftedRelativePhase (n + r) r :=
    atkinsonShiftedRelativePhase_pos (n + r) r hr (by omega)
  have hj_phase_pos :
      0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j (by omega) (by omega)
  have hj1_phase_pos :
      0 < atkinsonShiftedRelativePhase (n + j + 1) (j + 1) := by
    exact atkinsonShiftedRelativePhase_pos (n + j + 1) (j + 1)
      (Nat.succ_le_succ (Nat.zero_le j)) (by omega)
  have hcoeff :
      1 / atkinsonUpperBoundaryStepCoeff n j
        =
      atkinsonShiftedRelativePhase (n + j) j /
        atkinsonShiftedRelativePhase (n + j + 1) (j + 1) := by
    unfold atkinsonUpperBoundaryStepCoeff
    field_simp [ne_of_gt hj_phase_pos, ne_of_gt hj1_phase_pos]
  calc
    atkinsonLowerBoundaryShiftKernel n (j + 1) r
      =
    atkinsonShiftedRelativePhase (n + r) r /
      atkinsonShiftedRelativePhase (n + j + 1) (j + 1) := by
        rfl
    _ =
    (atkinsonShiftedRelativePhase (n + j) j /
        atkinsonShiftedRelativePhase (n + j + 1) (j + 1)) *
      (atkinsonShiftedRelativePhase (n + r) r /
        atkinsonShiftedRelativePhase (n + j) j) := by
          field_simp [ne_of_gt hr_phase_pos, ne_of_gt hj_phase_pos, ne_of_gt hj1_phase_pos]
    _ = (1 / atkinsonUpperBoundaryStepCoeff n j) *
        atkinsonLowerBoundaryShiftKernel n j r := by
          rw [← hcoeff]
          rfl

private lemma atkinsonShiftedRelativePhase_one_upper
    (k : ℕ) :
    atkinsonShiftedRelativePhase (k + 1) 1 ≤ 1 / ((k : ℝ) + 1) := by
  have hphi1 :
      atkinsonShiftedRelativePhase (k + 1) 1
        = Real.log ((((k : ℕ) : ℝ) + 2) / (((k : ℕ) : ℝ) + 1)) := by
    unfold atkinsonShiftedRelativePhase
    norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
  calc
    atkinsonShiftedRelativePhase (k + 1) 1
      = Real.log ((((k : ℕ) : ℝ) + 2) / (((k : ℕ) : ℝ) + 1)) := hphi1
    _ ≤ ((((k : ℕ) : ℝ) + 2) / (((k : ℕ) : ℝ) + 1)) - 1 := by
          exact Real.log_le_sub_one_of_pos (by positivity)
    _ = 1 / ((k : ℝ) + 1) := by
          field_simp [show (((k : ℕ) : ℝ) + 1) ≠ 0 by positivity]
          ring

private lemma atkinsonLowerBoundaryShiftKernel_first_le_two_div
    (n j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
    atkinsonLowerBoundaryShiftKernel n j 1 ≤ 2 / j := by
  unfold atkinsonLowerBoundaryShiftKernel
  have hnum_le :
      atkinsonShiftedRelativePhase (n + 1) 1 ≤ 1 / ((n : ℝ) + 1) := by
    simpa [Nat.add_assoc, add_left_comm, add_comm] using
      atkinsonShiftedRelativePhase_one_upper n
  have hden_le :
      (j : ℝ) / ((((n + j : ℕ) : ℝ) + 1)) ≤ atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_lower (n + j) j hj (by omega)
  have hnum_nonneg :
      0 ≤ atkinsonShiftedRelativePhase (n + 1) 1 := by
    exact le_of_lt <|
      atkinsonShiftedRelativePhase_pos (n + 1) 1 (by norm_num) (by omega)
  have hj_div_pos : 0 < (j : ℝ) / ((((n + j : ℕ) : ℝ) + 1)) := by positivity
  calc
    atkinsonShiftedRelativePhase (n + 1) 1 / atkinsonShiftedRelativePhase (n + j) j
        ≤ atkinsonShiftedRelativePhase (n + 1) 1 /
            ((j : ℝ) / ((((n + j : ℕ) : ℝ) + 1))) := by
              exact div_le_div_of_nonneg_left hnum_nonneg hj_div_pos hden_le
    _ ≤ (1 / ((n : ℝ) + 1)) /
            ((j : ℝ) / ((((n + j : ℕ) : ℝ) + 1))) := by
              exact div_le_div_of_nonneg_right hnum_le hj_div_pos.le
    _ = ((((n + j : ℕ) : ℝ) + 1) / ((n : ℝ) + 1)) / j := by
          field_simp [show (j : ℝ) ≠ 0 by positivity, show ((n : ℝ) + 1) ≠ 0 by positivity]
    _ ≤ (2 : ℝ) / j := by
          refine div_le_div_of_nonneg_right ?_ (by positivity : (0 : ℝ) ≤ j)
          have hratio :
              (((n + j : ℕ) : ℝ) + 1) / ((n : ℝ) + 1) ≤ 2 := by
            have hmul : (((n + j : ℕ) : ℝ) + 1) ≤ 2 * ((n : ℝ) + 1) := by
              exact_mod_cast (by omega : n + j + 1 ≤ 2 * (n + 1))
            have hden_pos : 0 < (n : ℝ) + 1 := by positivity
            exact (div_le_iff₀ hden_pos).2 <| by nlinarith
          simpa using hratio

private lemma atkinsonLowerBoundaryShiftKernel_step_sub
    (n j r : ℕ) (hr : 1 ≤ r) (hrj : r < j) :
    atkinsonLowerBoundaryShiftKernel n j (r + 1)
      - atkinsonLowerBoundaryShiftKernel n j r
        =
    atkinsonShiftedRelativePhase (n + r + 1) 1 /
      atkinsonShiftedRelativePhase (n + j) j := by
  have hr1_phase_pos :
      0 < atkinsonShiftedRelativePhase (n + r + 1) (r + 1) := by
    exact atkinsonShiftedRelativePhase_pos (n + r + 1) (r + 1)
      (Nat.succ_le_succ (Nat.zero_le r)) (by omega)
  have hj_phase_pos :
      0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j (by omega) (by omega)
  have hstep := atkinsonShiftedRelativePhase_step (n + r) r (by omega)
  have hstep' :
      atkinsonShiftedRelativePhase (n + r + 1) (r + 1)
        - atkinsonShiftedRelativePhase (n + r) r
      =
      atkinsonShiftedRelativePhase (n + r + 1) 1 := by
    linarith
  have hstep'' :
      atkinsonShiftedRelativePhase (n + (r + 1)) (r + 1)
        - atkinsonShiftedRelativePhase (n + r) r
      =
      atkinsonShiftedRelativePhase (n + r + 1) 1 := by
    simpa [Nat.add_assoc] using hstep'
  have hj_phase_ne : atkinsonShiftedRelativePhase (n + j) j ≠ 0 := ne_of_gt hj_phase_pos
  calc
    atkinsonLowerBoundaryShiftKernel n j (r + 1)
        - atkinsonLowerBoundaryShiftKernel n j r
      =
    (atkinsonShiftedRelativePhase (n + (r + 1)) (r + 1)
        - atkinsonShiftedRelativePhase (n + r) r) /
      atkinsonShiftedRelativePhase (n + j) j := by
          unfold atkinsonLowerBoundaryShiftKernel
          field_simp [hj_phase_ne]
    _ =
      atkinsonShiftedRelativePhase (n + r + 1) 1 /
        atkinsonShiftedRelativePhase (n + j) j := by
          rw [hstep'']

private lemma atkinsonLowerBoundaryShiftKernel_step_sub_le_two_div
    (n j r : ℕ) (hr : 1 ≤ r) (hrj : r < j) (hjn : j ≤ n) :
    atkinsonLowerBoundaryShiftKernel n j (r + 1)
      - atkinsonLowerBoundaryShiftKernel n j r
        ≤ 2 / j := by
  rw [atkinsonLowerBoundaryShiftKernel_step_sub n j r hr hrj]
  have hnum_le :
      atkinsonShiftedRelativePhase (n + r + 1) 1 ≤ 1 / (((n + r : ℕ) : ℝ) + 1) := by
    simpa [Nat.add_assoc, add_left_comm, add_comm] using
      atkinsonShiftedRelativePhase_one_upper (n + r)
  have hden_le :
      (j : ℝ) / ((((n + j : ℕ) : ℝ) + 1)) ≤ atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_lower (n + j) j (by omega) (by omega)
  have hnum_nonneg :
      0 ≤ atkinsonShiftedRelativePhase (n + r + 1) 1 := by
    exact le_of_lt <|
      atkinsonShiftedRelativePhase_pos (n + r + 1) 1 (by norm_num) (by omega)
  have hj_nat_pos : 0 < j := by
    omega
  have hj_div_pos : 0 < (j : ℝ) / ((((n + j : ℕ) : ℝ) + 1)) := by
    exact div_pos (by exact_mod_cast hj_nat_pos) (by positivity)
  calc
    atkinsonShiftedRelativePhase (n + r + 1) 1 /
        atkinsonShiftedRelativePhase (n + j) j
      ≤
    atkinsonShiftedRelativePhase (n + r + 1) 1 /
        ((j : ℝ) / ((((n + j : ℕ) : ℝ) + 1))) := by
          exact div_le_div_of_nonneg_left hnum_nonneg hj_div_pos hden_le
    _ ≤ (1 / ((((n + r : ℕ) : ℝ) + 1))) /
          ((j : ℝ) / ((((n + j : ℕ) : ℝ) + 1))) := by
            exact div_le_div_of_nonneg_right hnum_le hj_div_pos.le
    _ = ((((n + j : ℕ) : ℝ) + 1) / ((((n + r : ℕ) : ℝ) + 1))) / j := by
          have hj_ne : (j : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hj_nat_pos)
          have hnr_ne : ((((n + r : ℕ) : ℝ) + 1) : ℝ) ≠ 0 := by positivity
          field_simp
            [hj_ne, hnr_ne]
    _ ≤ (2 : ℝ) / j := by
          refine div_le_div_of_nonneg_right ?_ (by positivity : (0 : ℝ) ≤ j)
          have hratio :
              (((n + j : ℕ) : ℝ) + 1) / ((((n + r : ℕ) : ℝ) + 1)) ≤ 2 := by
            have hmul :
                (((n + j : ℕ) : ℝ) + 1) ≤ 2 * ((((n + r : ℕ) : ℝ) + 1)) := by
              exact_mod_cast (by
                have hr_pos' : 1 ≤ r := hr
                omega : n + j + 1 ≤ 2 * (n + r + 1))
            have hden_pos : 0 < (((n + r : ℕ) : ℝ) + 1) := by positivity
            exact (div_le_iff₀ hden_pos).2 <| by nlinarith
          simpa using hratio

private lemma atkinsonLowerBoundaryShiftKernel_mul_stepCoeff_sub_one
    (n j r : ℕ) (hr : 1 ≤ r) (hrj : r < j) :
    atkinsonLowerBoundaryShiftKernel n j r
      * (atkinsonUpperBoundaryStepCoeff n r - 1)
        =
    atkinsonLowerBoundaryShiftKernel n j (r + 1)
      - atkinsonLowerBoundaryShiftKernel n j r := by
  have hr_phase_pos :
      0 < atkinsonShiftedRelativePhase (n + r) r :=
    atkinsonShiftedRelativePhase_pos (n + r) r hr (by omega)
  have hj_phase_pos :
      0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j (by omega) (by omega)
  have hratio :
      atkinsonUpperBoundaryStepCoeff n r - 1
        = atkinsonShiftedRelativePhase (n + r + 1) 1 /
            atkinsonShiftedRelativePhase (n + r) r :=
    atkinsonUpperBoundaryStepCoeff_sub_one_eq n r hr
  calc
    atkinsonLowerBoundaryShiftKernel n j r
        * (atkinsonUpperBoundaryStepCoeff n r - 1)
      =
    (atkinsonShiftedRelativePhase (n + r) r /
        atkinsonShiftedRelativePhase (n + j) j)
      * (atkinsonShiftedRelativePhase (n + r + 1) 1 /
        atkinsonShiftedRelativePhase (n + r) r) := by
          rw [hratio]
          rfl
    _ =
      atkinsonShiftedRelativePhase (n + r + 1) 1 /
        atkinsonShiftedRelativePhase (n + j) j := by
          field_simp [ne_of_gt hr_phase_pos, ne_of_gt hj_phase_pos]
    _ =
      atkinsonLowerBoundaryShiftKernel n j (r + 1)
        - atkinsonLowerBoundaryShiftKernel n j r := by
          rw [atkinsonLowerBoundaryShiftKernel_step_sub n j r hr hrj]

private lemma atkinsonLowerBoundaryShiftKernel_mul_stepCoeff_sub_one_le_two_div
    (n j r : ℕ) (hr : 1 ≤ r) (hrj : r < j) (hjn : j ≤ n) :
    atkinsonLowerBoundaryShiftKernel n j r
      * (atkinsonUpperBoundaryStepCoeff n r - 1)
        ≤ 2 / j := by
  rw [atkinsonLowerBoundaryShiftKernel_mul_stepCoeff_sub_one n j r hr hrj]
  exact atkinsonLowerBoundaryShiftKernel_step_sub_le_two_div n j r hr hrj hjn

/-- Kernel Weight Decay (Corrected Lemma 3 of CorePrefix decomposition).

  The original claim was `C_ker / (j * (n + j))`, but this is FALSE:
  the kernel difference `kernel(n+j, j, r+2) - kernel(n+j, j, r+1)`
  converges to `1/j` as `n → ∞` (not to 0). The correct bound is `O(1/j)`.

  Numerically: for j=3, n=1000, r=0, the difference ≈ 0.3333, while
  `1/(j*(n+j)) = 1/3009 ≈ 0.000332`, so no fixed `C_ker` makes the original bound work.

  This lemma states the correct `O(1/j)` bound with explicit constant 2.
  Proof: the kernel step `kernel(n, j, r+1) - kernel(n, j, r)` equals
  `phase(n+r+1, 1) / phase(n+j, j)` by `atkinsonLowerBoundaryShiftKernel_step_sub`,
  and this ratio is bounded by `2/j` via `atkinsonLowerBoundaryShiftKernel_step_sub_le_two_div`.
  The difference is nonneg (numerator and denominator of the ratio are both positive),
  so the absolute value equals the difference itself. -/
private lemma atkinsonLowerBoundaryShiftKernel_diff_le_two_div_j :
    ∀ j : ℕ, 3 ≤ j → ∀ n : ℕ, ∀ r ∈ Finset.range (j - 1),
      |atkinsonLowerBoundaryShiftKernel (n + j) j (r + 2)
        - atkinsonLowerBoundaryShiftKernel (n + j) j (r + 1)|
      ≤ 2 / (j : ℝ) := by
  intro j hj n r hr_mem
  have hr_lt : r < j - 1 := Finset.mem_range.mp hr_mem
  have hr1 : 1 ≤ r + 1 := Nat.succ_le_succ (Nat.zero_le r)
  have hr1j : r + 1 < j := by omega
  have hjnj : j ≤ n + j := Nat.le_add_left j n
  -- The step_sub formula (note: r+2 = (r+1)+1 definitionally for ℕ)
  have hdiff_eq := atkinsonLowerBoundaryShiftKernel_step_sub (n + j) j (r + 1) hr1 hr1j
  -- The difference is nonneg (ratio of positive phases)
  have hdiff_nonneg : 0 ≤ atkinsonLowerBoundaryShiftKernel (n + j) j (r + 2)
      - atkinsonLowerBoundaryShiftKernel (n + j) j (r + 1) := by
    -- r + 2 and (r + 1) + 1 are definitionally equal
    change 0 ≤ atkinsonLowerBoundaryShiftKernel (n + j) j ((r + 1) + 1)
        - atkinsonLowerBoundaryShiftKernel (n + j) j (r + 1)
    rw [hdiff_eq]
    exact div_nonneg
      (le_of_lt (atkinsonShiftedRelativePhase_pos _ 1 (by norm_num) (by omega)))
      (le_of_lt (atkinsonShiftedRelativePhase_pos _ j (by omega) (by omega)))
  rw [abs_of_nonneg hdiff_nonneg]
  -- Apply the existing O(1/j) bound
  change atkinsonLowerBoundaryShiftKernel (n + j) j ((r + 1) + 1)
      - atkinsonLowerBoundaryShiftKernel (n + j) j (r + 1) ≤ 2 / (j : ℝ)
  exact atkinsonLowerBoundaryShiftKernel_step_sub_le_two_div (n + j) j (r + 1) hr1 hr1j hjnj

-- The original claimed bound `C_ker / (j * (n + j))` is FALSE.
-- Proof by counterexample: for j = 3, as n → ∞,
--   kernel(n+3, 3, 2) - kernel(n+3, 3, 1)
--     = log(1 + 2/(n+4)) / log(1 + 3/(n+4)) - log(1 + 1/(n+4)) / log(1 + 3/(n+4))
--     → (2/3) - (1/3) = 1/3,
-- so `diff * j * (n+j) → (1/3) * 3 * n → ∞`.
-- No fixed C_ker satisfies the bound.

private lemma atkinsonComplex_sum_range_telescope
    (F : ℕ → ℂ) (m : ℕ) :
    ∑ r ∈ Finset.range m, (F (r + 1) - F r) = F m - F 0 := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

private lemma atkinsonComplex_sum_Ico_telescope
    (F : ℕ → ℂ) (p q : ℕ) (hpq : p ≤ q) :
    ∑ s ∈ Finset.Ico p q, (F (s + 1) - F s) = F q - F p := by
  let G : ℕ → ℂ := fun t => F (p + t)
  calc
    ∑ s ∈ Finset.Ico p q, (F (s + 1) - F s)
        = ∑ t ∈ Finset.range (q - p), (G (t + 1) - G t) := by
            rw [Finset.sum_Ico_eq_sum_range]
            refine Finset.sum_congr rfl ?_
            intro t ht
            simp [G, Nat.add_assoc, add_left_comm, add_comm]
    _ = G (q - p) - G 0 := atkinsonComplex_sum_range_telescope G (q - p)
    _ = F q - F p := by
          simp [G, hpq, Nat.add_assoc, add_left_comm, add_comm]

private lemma atkinsonComplex_weighted_sum_eq_backward_tails
    (a b : ℕ → ℂ) (m : ℕ) :
    ∑ r ∈ Finset.range m, a r * b r
      =
    a 0 * ∑ r ∈ Finset.range m, b r
      +
    ∑ r ∈ Finset.range m,
        (a (r + 1) - a r) * ∑ s ∈ Finset.Ico (r + 1) m, b s := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have htail :
          ∑ r ∈ Finset.range (m + 1),
              (a (r + 1) - a r) * ∑ s ∈ Finset.Ico (r + 1) (m + 1), b s
            =
          (∑ r ∈ Finset.range m,
              (a (r + 1) - a r) * ∑ s ∈ Finset.Ico (r + 1) m, b s)
            +
          ∑ r ∈ Finset.range m, (a (r + 1) - a r) * b m := by
        rw [Finset.sum_range_succ]
        have hlast :
            (a (m + 1) - a m) * ∑ s ∈ Finset.Ico (m + 1) (m + 1), b s = 0 := by
          simp
        rw [hlast, add_zero]
        calc
          ∑ r ∈ Finset.range m,
              (a (r + 1) - a r) * ∑ s ∈ Finset.Ico (r + 1) (m + 1), b s
            =
          ∑ r ∈ Finset.range m,
              (a (r + 1) - a r) * (∑ s ∈ Finset.Ico (r + 1) m, b s + b m) := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                have hrm : r + 1 ≤ m := Nat.succ_le_of_lt (Finset.mem_range.mp hr)
                rw [Nat.Ico_succ_right_eq_insert_Ico hrm, Finset.sum_insert]
                · ring
                · simp
          _ =
          ∑ r ∈ Finset.range m,
              ((a (r + 1) - a r) * ∑ s ∈ Finset.Ico (r + 1) m, b s
                + (a (r + 1) - a r) * b m) := by
                  refine Finset.sum_congr rfl ?_
                  intro r hr
                  ring
          _ =
          (∑ r ∈ Finset.range m,
              (a (r + 1) - a r) * ∑ s ∈ Finset.Ico (r + 1) m, b s)
            +
          ∑ r ∈ Finset.range m, (a (r + 1) - a r) * b m := by
                rw [Finset.sum_add_distrib]
      have hmterm :
          a m * b m
            =
          a 0 * b m + ∑ r ∈ Finset.range m, (a (r + 1) - a r) * b m := by
        have htel := atkinsonComplex_sum_range_telescope a m
        calc
          a m * b m
            =
          (a 0 + ∑ r ∈ Finset.range m, (a (r + 1) - a r)) * b m := by
              congr 1
              calc
                a m = a 0 + (a m - a 0) := by ring
                _ = a 0 + ∑ r ∈ Finset.range m, (a (r + 1) - a r) := by
                      rw [← htel]
          _ = a 0 * b m + (∑ r ∈ Finset.range m, (a (r + 1) - a r)) * b m := by
                ring
          _ = a 0 * b m + ∑ r ∈ Finset.range m, (a (r + 1) - a r) * b m := by
                rw [Finset.sum_mul]
      rw [Finset.sum_range_succ, htail, hmterm]
      ring

private lemma atkinsonLowerBoundary_shiftBoundary_step
    (n j r : ℕ) (hj : 1 ≤ j) (hr : 1 ≤ r) :
    ((((atkinsonLowerBoundaryShiftKernel n j r : ℝ) : ℂ)) *
        atkinsonResonantShiftedBoundaryTerm n r)
      =
    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n (r + 1))
      -
    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n r) := by
  calc
    ((((atkinsonLowerBoundaryShiftKernel n j r : ℝ) : ℂ)) *
        atkinsonResonantShiftedBoundaryTerm n r)
        =
      ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          ((((atkinsonShiftedRelativePhase (n + r) r : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm n r)) := by
              unfold atkinsonLowerBoundaryShiftKernel
              rw [show
                (((atkinsonShiftedRelativePhase (n + r) r /
                    atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ))
                  =
                ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                  (((atkinsonShiftedRelativePhase (n + r) r : ℝ) : ℂ))) by
                    rw [← Complex.ofReal_mul]
                    congr 1
                    simp [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc]]
              ring
    _ =
      ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          (atkinsonShiftedSingleBoundaryCore n (r + 1) -
            atkinsonShiftedSingleBoundaryCore n r)) := by
              rw [atkinson_complex_mul_phase_eq_boundaryCore_diff n r hr]
    _ =
      ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n (r + 1))
        -
      ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n r) := by
            ring

private theorem atkinsonLowerBoundary_shiftBoundary_decomposition
    (n j : ℕ) (hj : 1 ≤ j) :
    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n j)
      =
    ((((atkinsonLowerBoundaryShiftKernel n j 1 : ℝ) : ℂ)) *
        ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n 1))
      +
    ∑ r ∈ Finset.range (j - 1),
        ((((atkinsonLowerBoundaryShiftKernel n j (r + 1) : ℝ) : ℂ)) *
          atkinsonResonantShiftedBoundaryTerm n (r + 1)) := by
  have hhead :
      ((((atkinsonLowerBoundaryShiftKernel n j 1 : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n 1))
        =
      ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n 1) := by
    have hphase1_pos :
        0 < atkinsonShiftedRelativePhase (n + 1) 1 := by
      exact atkinsonShiftedRelativePhase_pos (n + 1) 1 (by norm_num) (by omega)
    have hmul1 :
        (((atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
            (((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ))
          =
        (1 : ℂ) := by
          rw [← Complex.ofReal_mul]
          congr 1
          field_simp [ne_of_gt hphase1_pos]
    unfold atkinsonLowerBoundaryShiftKernel
    rw [show
      (((atkinsonShiftedRelativePhase (n + 1) 1 /
          atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ))
        =
      ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        (((atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ))) by
          rw [← Complex.ofReal_mul]
          congr 1
          simp [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc]]
    calc
      ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            (((atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ))) *
          ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n 1)
          =
        ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          ((((atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
            (((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n 1)) := by
              ring
      _ =
        ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n 1) := by
            rw [hmul1]
            simp
  have hsum :
      ∑ r ∈ Finset.range (j - 1),
          ((((atkinsonLowerBoundaryShiftKernel n j (r + 1) : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm n (r + 1))
        =
      ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n j)
        -
      ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n 1) := by
            let F : ℕ → ℂ := fun r =>
              ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                atkinsonShiftedSingleBoundaryCore n (r + 1))
            calc
              ∑ r ∈ Finset.range (j - 1),
                  ((((atkinsonLowerBoundaryShiftKernel n j (r + 1) : ℝ) : ℂ)) *
                    atkinsonResonantShiftedBoundaryTerm n (r + 1))
                  =
                ∑ r ∈ Finset.range (j - 1), (F (r + 1) - F r) := by
                    refine Finset.sum_congr rfl ?_
                    intro r hr
                    dsimp [F]
                    simpa [Nat.add_assoc] using
                      atkinsonLowerBoundary_shiftBoundary_step n j (r + 1) hj
                        (Nat.succ_le_succ (Nat.zero_le r))
              _ = F (j - 1) - F 0 := atkinsonComplex_sum_range_telescope F (j - 1)
              _ =
                ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                    atkinsonShiftedSingleBoundaryCore n j)
                  -
                ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                    atkinsonShiftedSingleBoundaryCore n 1) := by
                      dsimp [F]
                      rw [show j - 1 + 1 = j by omega]
  calc
    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n j)
      =
    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n 1)
      +
    ∑ r ∈ Finset.range (j - 1),
        ((((atkinsonLowerBoundaryShiftKernel n j (r + 1) : ℝ) : ℂ)) *
          atkinsonResonantShiftedBoundaryTerm n (r + 1)) := by
            rw [hsum]
            ring
    _ =
      ((((atkinsonLowerBoundaryShiftKernel n j 1 : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n 1))
        +
      ∑ r ∈ Finset.range (j - 1),
          ((((atkinsonLowerBoundaryShiftKernel n j (r + 1) : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm n (r + 1)) := by
              rw [← hhead]

private theorem atkinsonShiftedInversePhaseCorePrefix_eq_shiftBoundaryDecomposition
    (N j : ℕ) (hj : 1 ≤ j) :
    ∑ k ∈ Finset.range N,
        ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + j) j)
      =
    (∑ k ∈ Finset.range N,
        ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase (k + j + 1) 1 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) 1)))
      +
    ∑ k ∈ Finset.range N,
        ∑ r ∈ Finset.range (j - 1),
          ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm (k + j) (r + 1)) := by
  calc
    ∑ k ∈ Finset.range N,
        ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + j) j)
        =
      ∑ k ∈ Finset.range N,
        (((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase (k + j + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) 1))
          +
          (∑ r ∈ Finset.range (j - 1),
            ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
              atkinsonResonantShiftedBoundaryTerm (k + j) (r + 1)))) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                simpa [Nat.add_assoc, add_left_comm, add_comm] using
                  atkinsonLowerBoundary_shiftBoundary_decomposition (k + j) j hj
    _ =
      (∑ k ∈ Finset.range N,
          ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase (k + j + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) 1)))
        +
      ∑ k ∈ Finset.range N,
          ∑ r ∈ Finset.range (j - 1),
            ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
              atkinsonResonantShiftedBoundaryTerm (k + j) (r + 1)) := by
                rw [Finset.sum_add_distrib]

private lemma atkinsonShiftBoundary_remainder_abel_reorder
    (N j : ℕ) :
    let headTail : ℕ → ℂ := fun k =>
      ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
        ∑ s ∈ Finset.range (j - 1),
          atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1))
    let incTail : ℕ → ℕ → ℂ := fun k r =>
      (((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 2)
            - atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
          ∑ s ∈ Finset.Ico (r + 1) (j - 1),
            atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1)))
    ∑ k ∈ Finset.range N,
        ∑ r ∈ Finset.range (j - 1),
          ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm (k + j) (r + 1))
      =
    (∑ k ∈ Finset.range N, headTail k)
      +
    ∑ r ∈ Finset.range (j - 1),
        ∑ k ∈ Finset.range N, incTail k r := by
  intro headTail incTail
  calc
    ∑ k ∈ Finset.range N,
        ∑ r ∈ Finset.range (j - 1),
          ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm (k + j) (r + 1))
      =
    ∑ k ∈ Finset.range N,
        (headTail k + ∑ r ∈ Finset.range (j - 1), incTail k r) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                simp only [headTail, incTail]
                simpa [Nat.add_assoc, add_left_comm, add_comm] using
                  atkinsonComplex_weighted_sum_eq_backward_tails
                    (a := fun r =>
                      (((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)))
                    (b := fun r =>
                      atkinsonResonantShiftedBoundaryTerm (k + j) (r + 1))
                    (m := j - 1)
    _ =
      (∑ k ∈ Finset.range N,
          headTail k)
        +
      ∑ k ∈ Finset.range N,
          ∑ r ∈ Finset.range (j - 1), incTail k r := by
                    rw [Finset.sum_add_distrib]
    _ =
      (∑ k ∈ Finset.range N,
          headTail k)
        +
      ∑ r ∈ Finset.range (j - 1),
          ∑ k ∈ Finset.range N, incTail k r := by
                    rw [Finset.sum_comm]

theorem atkinsonShiftedInversePhaseCorePrefix_eq_shiftBoundaryAbelDecomposition
    (N j : ℕ) (hj : 1 ≤ j) :
    let headCore : ℕ → ℂ := fun k =>
      ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
        ((((1 / atkinsonShiftedRelativePhase (k + j + 1) 1 : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + j) 1))
    let headTail : ℕ → ℂ := fun k =>
      ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
        ∑ s ∈ Finset.range (j - 1),
          atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1))
    let incTail : ℕ → ℕ → ℂ := fun k r =>
      (((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 2)
            - atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
          ∑ s ∈ Finset.Ico (r + 1) (j - 1),
            atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1)))
    ∑ k ∈ Finset.range N,
        ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + j) j)
      =
    (∑ k ∈ Finset.range N, headCore k)
      +
    (∑ k ∈ Finset.range N, headTail k)
      +
    ∑ r ∈ Finset.range (j - 1),
        ∑ k ∈ Finset.range N, incTail k r := by
  intro headCore headTail incTail
  calc
    ∑ k ∈ Finset.range N,
        ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + j) j)
      =
    (∑ k ∈ Finset.range N, headCore k)
      +
    ∑ k ∈ Finset.range N,
        ∑ r ∈ Finset.range (j - 1),
          ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm (k + j) (r + 1)) := by
              simp only [headCore]
              simpa [Finset.sum_add_distrib] using
                atkinsonShiftedInversePhaseCorePrefix_eq_shiftBoundaryDecomposition N j hj
    _ =
      (∑ k ∈ Finset.range N, headCore k)
        +
      ((∑ k ∈ Finset.range N, headTail k)
        +
        ∑ r ∈ Finset.range (j - 1),
            ∑ k ∈ Finset.range N, incTail k r) := by
              congr 1
              simp only [headTail, incTail]
              exact atkinsonShiftBoundary_remainder_abel_reorder N j
    _ =
      (∑ k ∈ Finset.range N, headCore k)
        +
      (∑ k ∈ Finset.range N, headTail k)
        +
      ∑ r ∈ Finset.range (j - 1),
          ∑ k ∈ Finset.range N, incTail k r := by
            ring

private lemma atkinsonResonantShiftedBoundaryTerm_eq_inversePhaseCoreGap
    (n j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
    atkinsonResonantShiftedBoundaryTerm n j
      =
    ((((1 / atkinsonShiftedRelativePhase (n + (j + 1)) (j + 1) : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n (j + 1))
      -
    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n j)
      +
    ((((atkinsonUpperBoundaryStepCoeff n j - 1 : ℝ) : ℂ)) *
      ((((1 / atkinsonShiftedRelativePhase (n + (j + 1)) (j + 1) : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n (j + 1))) := by
  have hnext :=
    atkinson_inverse_phase_core_eq_lowerBoundaryTerm n (j + 1)
      (Nat.succ_le_succ (Nat.zero_le j))
  have hcurr := atkinson_inverse_phase_core_eq_lowerBoundaryTerm n j hj
  have hstep :
      atkinsonWeightedResonantBlockMode (n + j) 1 * atkinsonShiftedSinglePrimitive (n + j) j 1
        =
      (((atkinsonUpperBoundaryStepCoeff n j : ℝ) : ℂ)) *
          (atkinsonWeightedResonantBlockMode (n + (j + 1)) 0 *
            atkinsonShiftedSinglePrimitive (n + (j + 1)) (j + 1) 0) := by
    simpa [Nat.add_assoc, add_left_comm, add_comm] using
      atkinson_upper_boundary_step n j hj hjn
  unfold atkinsonResonantShiftedBoundaryTerm
  rw [hstep, ← hnext, ← hcurr]
  let x : ℂ :=
    ((((1 / atkinsonShiftedRelativePhase (n + (j + 1)) (j + 1) : ℝ) : ℂ)) *
      atkinsonShiftedSingleBoundaryCore n (j + 1))
  let y : ℂ :=
    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
      atkinsonShiftedSingleBoundaryCore n j)
  have hcoeff :
      (((atkinsonUpperBoundaryStepCoeff n j : ℝ) : ℂ)) * x - y
        =
      x - y + ((((atkinsonUpperBoundaryStepCoeff n j - 1 : ℝ) : ℂ)) * x) := by
          simp [x, y]
          ring
  simpa [x, y, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcoeff

private lemma atkinsonResonantShiftedBoundaryTail_eq_inversePhaseCoreGap
    (n p q : ℕ) (hp : 1 ≤ p) (hpq : p ≤ q) (hqn : q ≤ n + 1) :
    ∑ s ∈ Finset.Ico p q, atkinsonResonantShiftedBoundaryTerm n s
      =
    ((((1 / atkinsonShiftedRelativePhase (n + q) q : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n q)
      -
    ((((1 / atkinsonShiftedRelativePhase (n + p) p : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n p)
      +
    ∑ s ∈ Finset.Ico p q,
      ((((atkinsonUpperBoundaryStepCoeff n s - 1 : ℝ) : ℂ)) *
        ((((1 / atkinsonShiftedRelativePhase (n + (s + 1)) (s + 1) : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n (s + 1))) := by
  let F : ℕ → ℂ := fun s =>
    ((((1 / atkinsonShiftedRelativePhase (n + s) s : ℝ) : ℂ)) *
      atkinsonShiftedSingleBoundaryCore n s)
  let E : ℕ → ℂ := fun s =>
    ((((atkinsonUpperBoundaryStepCoeff n s - 1 : ℝ) : ℂ)) * F (s + 1))
  calc
    ∑ s ∈ Finset.Ico p q, atkinsonResonantShiftedBoundaryTerm n s
      =
    ∑ s ∈ Finset.Ico p q, ((F (s + 1) - F s) + E s) := by
        refine Finset.sum_congr rfl ?_
        intro s hs
        have hs_pos : 1 ≤ s := le_trans hp (Finset.mem_Ico.mp hs).1
        have hs_le_n : s ≤ n := by
          have hs_lt_q : s < q := (Finset.mem_Ico.mp hs).2
          omega
        simp only [F, E]
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          atkinsonResonantShiftedBoundaryTerm_eq_inversePhaseCoreGap n s hs_pos hs_le_n
    _ =
      (∑ s ∈ Finset.Ico p q, (F (s + 1) - F s))
        + ∑ s ∈ Finset.Ico p q, E s := by
            rw [Finset.sum_add_distrib]
    _ =
      (F q - F p)
        + ∑ s ∈ Finset.Ico p q, E s := by
            rw [atkinsonComplex_sum_Ico_telescope F p q hpq]
    _ =
      ((((1 / atkinsonShiftedRelativePhase (n + q) q : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n q)
        -
      ((((1 / atkinsonShiftedRelativePhase (n + p) p : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n p)
        +
      ∑ s ∈ Finset.Ico p q,
        ((((atkinsonUpperBoundaryStepCoeff n s - 1 : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase (n + (s + 1)) (s + 1) : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n (s + 1))) := by
              simp only [F, E, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

private lemma atkinsonResonantShiftedBoundary_fullTail_eq_inversePhaseCoreGap
    (n j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n + 1) :
    ∑ s ∈ Finset.range (j - 1),
        atkinsonResonantShiftedBoundaryTerm n (s + 1)
      =
    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n j)
      -
    ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n 1)
      +
    ∑ s ∈ Finset.range (j - 1),
      ((((atkinsonUpperBoundaryStepCoeff n (s + 1) - 1 : ℝ) : ℂ)) *
        ((((1 / atkinsonShiftedRelativePhase (n + (s + 2)) (s + 2) : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n (s + 2))) := by
  simpa [Finset.sum_Ico_eq_sum_range, Nat.add_assoc, add_left_comm, add_comm] using
    atkinsonResonantShiftedBoundaryTail_eq_inversePhaseCoreGap n 1 j
      (by norm_num) hj hjn

private lemma atkinsonResonantShiftedBoundary_backwardTail_eq_inversePhaseCoreGap
    (n j r : ℕ) (hrj : r + 2 ≤ j) (hjn : j ≤ n + 1) :
    ∑ s ∈ Finset.Ico (r + 1) (j - 1),
        atkinsonResonantShiftedBoundaryTerm n (s + 1)
      =
    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n j)
      -
    ((((1 / atkinsonShiftedRelativePhase (n + (r + 2)) (r + 2) : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n (r + 2))
      +
    ∑ s ∈ Finset.Ico (r + 1) (j - 1),
      ((((atkinsonUpperBoundaryStepCoeff n (s + 1) - 1 : ℝ) : ℂ)) *
        ((((1 / atkinsonShiftedRelativePhase (n + (s + 2)) (s + 2) : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n (s + 2))) := by
  simpa [Finset.sum_Ico_eq_sum_range, Nat.add_assoc, add_left_comm, add_comm,
    show j - (r + 2) = j - 1 - (r + 1) by omega] using
    atkinsonResonantShiftedBoundaryTail_eq_inversePhaseCoreGap n (r + 2) j
      (by omega) hrj hjn


/-! ### Resonant Boundary Tail Bound (Lemma 4 of CorePrefix decomposition)

Bounds the sum of resonant boundary terms in the gap layers:
  ∃ C_res > 0, ∀ j ≥ 3, ∀ n, j ≤ n + 1 → ∀ r, r + 2 ≤ j →
    ‖∑ s ∈ Ico (r+1) (j-1), boundaryTerm(n, s+1)‖ ≤ C_res * √(n+j)

The proof uses the telescoping identity
  `atkinsonResonantShiftedBoundary_backwardTail_eq_inversePhaseCoreGap`,
which decomposes the sum into two endpoint terms and a correction sum.
Each endpoint has norm ≤ modeWeight(n)/phase(n+s,s), and the correction
terms gain a factor of |stepCoeff-1| ≤ 1/(s+1).
-/

/-- Generalized upper boundary step without the unnecessary `j ≤ n` hypothesis.
    The identity holds for all `j ≥ 1` since `j ≤ n + j` is trivially true. -/
private lemma atkinson_upper_boundary_step_general
    (n j : ℕ) (hj : 1 ≤ j) :
    atkinsonWeightedResonantBlockMode (n + j) 1 * atkinsonShiftedSinglePrimitive (n + j) j 1
      =
    (((atkinsonUpperBoundaryStepCoeff n j : ℝ) : ℂ)) *
        (atkinsonWeightedResonantBlockMode (n + j + 1) 0 *
          atkinsonShiftedSinglePrimitive (n + j + 1) (j + 1) 0) := by
  simpa [atkinsonUpperBoundaryStepCoeff] using
    atkinsonWeightedResonantBlockMode_one_mul_shiftedSinglePrimitive_step
      (n + j) j hj (by omega)

/-- Generalized boundary term decomposition without `j ≤ n`.
    Each boundary term decomposes as: next endpoint - current endpoint + correction. -/
private lemma atkinsonResonantShiftedBoundaryTerm_eq_inversePhaseCoreGap_general
    (n j : ℕ) (hj : 1 ≤ j) :
    atkinsonResonantShiftedBoundaryTerm n j
      =
    ((((1 / atkinsonShiftedRelativePhase (n + (j + 1)) (j + 1) : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n (j + 1))
      -
    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n j)
      +
    ((((atkinsonUpperBoundaryStepCoeff n j - 1 : ℝ) : ℂ)) *
      ((((1 / atkinsonShiftedRelativePhase (n + (j + 1)) (j + 1) : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n (j + 1))) := by
  have hnext :=
    atkinson_inverse_phase_core_eq_lowerBoundaryTerm n (j + 1)
      (Nat.succ_le_succ (Nat.zero_le j))
  have hcurr := atkinson_inverse_phase_core_eq_lowerBoundaryTerm n j hj
  have hstep :
      atkinsonWeightedResonantBlockMode (n + j) 1 * atkinsonShiftedSinglePrimitive (n + j) j 1
        =
      (((atkinsonUpperBoundaryStepCoeff n j : ℝ) : ℂ)) *
          (atkinsonWeightedResonantBlockMode (n + (j + 1)) 0 *
            atkinsonShiftedSinglePrimitive (n + (j + 1)) (j + 1) 0) := by
    simpa [Nat.add_assoc, add_left_comm, add_comm] using
      atkinson_upper_boundary_step_general n j hj
  unfold atkinsonResonantShiftedBoundaryTerm
  rw [hstep, ← hnext, ← hcurr]
  let x : ℂ :=
    ((((1 / atkinsonShiftedRelativePhase (n + (j + 1)) (j + 1) : ℝ) : ℂ)) *
      atkinsonShiftedSingleBoundaryCore n (j + 1))
  let y : ℂ :=
    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
      atkinsonShiftedSingleBoundaryCore n j)
  have hcoeff :
      (((atkinsonUpperBoundaryStepCoeff n j : ℝ) : ℂ)) * x - y
        =
      x - y + ((((atkinsonUpperBoundaryStepCoeff n j - 1 : ℝ) : ℂ)) * x) := by
          simp [x, y]
          ring
  simpa [x, y, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcoeff

/-- Generalized telescoping identity for the backward tail without the `q ≤ n + 1` hypothesis.
    The sum telescopes into two endpoint terms plus a correction sum for all `1 ≤ p ≤ q`. -/
private lemma atkinsonResonantShiftedBoundaryTail_eq_inversePhaseCoreGap_general
    (n p q : ℕ) (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∑ s ∈ Finset.Ico p q, atkinsonResonantShiftedBoundaryTerm n s
      =
    ((((1 / atkinsonShiftedRelativePhase (n + q) q : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n q)
      -
    ((((1 / atkinsonShiftedRelativePhase (n + p) p : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n p)
      +
    ∑ s ∈ Finset.Ico p q,
      ((((atkinsonUpperBoundaryStepCoeff n s - 1 : ℝ) : ℂ)) *
        ((((1 / atkinsonShiftedRelativePhase (n + (s + 1)) (s + 1) : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n (s + 1))) := by
  let F : ℕ → ℂ := fun s =>
    ((((1 / atkinsonShiftedRelativePhase (n + s) s : ℝ) : ℂ)) *
      atkinsonShiftedSingleBoundaryCore n s)
  let E : ℕ → ℂ := fun s =>
    ((((atkinsonUpperBoundaryStepCoeff n s - 1 : ℝ) : ℂ)) * F (s + 1))
  calc
    ∑ s ∈ Finset.Ico p q, atkinsonResonantShiftedBoundaryTerm n s
      =
    ∑ s ∈ Finset.Ico p q, ((F (s + 1) - F s) + E s) := by
        refine Finset.sum_congr rfl ?_
        intro s hs
        have hs_pos : 1 ≤ s := le_trans hp (Finset.mem_Ico.mp hs).1
        simp only [F, E]
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          atkinsonResonantShiftedBoundaryTerm_eq_inversePhaseCoreGap_general n s hs_pos
    _ =
      (∑ s ∈ Finset.Ico p q, (F (s + 1) - F s))
        + ∑ s ∈ Finset.Ico p q, E s := by
            rw [Finset.sum_add_distrib]
    _ =
      (F q - F p)
        + ∑ s ∈ Finset.Ico p q, E s := by
            rw [atkinsonComplex_sum_Ico_telescope F p q hpq]
    _ =
      ((((1 / atkinsonShiftedRelativePhase (n + q) q : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n q)
        -
      ((((1 / atkinsonShiftedRelativePhase (n + p) p : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n p)
        +
      ∑ s ∈ Finset.Ico p q,
        ((((atkinsonUpperBoundaryStepCoeff n s - 1 : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase (n + (s + 1)) (s + 1) : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n (s + 1))) := by
              simp only [F, E, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Generalized backward tail identity without `j ≤ n + 1`. -/
private lemma atkinsonResonantShiftedBoundary_backwardTail_general
    (n j r : ℕ) (hrj : r + 2 ≤ j) :
    ∑ s ∈ Finset.Ico (r + 1) (j - 1),
        atkinsonResonantShiftedBoundaryTerm n (s + 1)
      =
    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n j)
      -
    ((((1 / atkinsonShiftedRelativePhase (n + (r + 2)) (r + 2) : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n (r + 2))
      +
    ∑ s ∈ Finset.Ico (r + 1) (j - 1),
      ((((atkinsonUpperBoundaryStepCoeff n (s + 1) - 1 : ℝ) : ℂ)) *
        ((((1 / atkinsonShiftedRelativePhase (n + (s + 2)) (s + 2) : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n (s + 2))) := by
  simpa [Finset.sum_Ico_eq_sum_range, Nat.add_assoc, add_left_comm, add_comm,
    show j - (r + 2) = j - 1 - (r + 1) by omega] using
    atkinsonResonantShiftedBoundaryTail_eq_inversePhaseCoreGap_general n (r + 2) j
      (by omega) hrj

/-- Norm of (1/phase) * boundaryCore endpoint term. -/
private lemma atkinsonInversePhaseBoundaryCore_norm
    (n s : ℕ) (hs : 1 ≤ s) :
    ‖((((1 / atkinsonShiftedRelativePhase (n + s) s : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n s)‖
      = atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + s) s := by
  have hphase_pos : 0 < atkinsonShiftedRelativePhase (n + s) s :=
    atkinsonShiftedRelativePhase_pos (n + s) s hs (by omega)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (le_of_lt (div_pos one_pos hphase_pos)),
    atkinsonShiftedSingleBoundaryCore_norm n s hs,
    one_div]
  ring

private lemma atkinsonInversePhaseBoundaryCore_norm_le
    (n s : ℕ) (hs : 1 ≤ s) :
    ‖((((1 / atkinsonShiftedRelativePhase (n + s) s : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n s)‖
      ≤ Real.sqrt (↑n + 1) / ↑s + 1 / Real.sqrt (↑n + 1) := by
  -- Substitute the norm expression from atkinsonInversePhaseBoundaryCore_norm.
  have h_norm : ‖(1 / atkinsonShiftedRelativePhase (n + s) s : ℝ) * atkinsonShiftedSingleBoundaryCore n s‖ = atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + s) s := by
    convert atkinsonInversePhaseBoundaryCore_norm n s hs using 1;
  -- Using the lower bound for the denominator, we get:
  have h_div : atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + s) s ≤ atkinsonModeWeight n * ((n + s + 1) / s) := by
    rw [ div_eq_mul_inv ];
    gcongr;
    · exact atkinsonModeWeight_nonneg n;
    · convert atkinsonShiftedRelativePhase_inv_upper ( n + s ) s hs ( by linarith ) using 1 ; ring;
      norm_cast;
  -- Using the definition of `atkinsonModeWeight`, we have:
  have h_modeWeight : atkinsonModeWeight n = 1 / Real.sqrt (n + 1) := by
    unfold atkinsonModeWeight; norm_num [ Real.sqrt_eq_rpow, Real.rpow_neg ( by positivity : ( 0 : ℝ ) ≤ n + 1 ) ] ;
  convert h_norm.le.trans h_div using 1 ; rw [ h_modeWeight ] ; ring;
  -- Combine like terms and simplify the expression.
  field_simp
  ring;
  rw [ Real.sq_sqrt ( by positivity ) ]

private lemma atkinsonInversePhaseBoundaryCore_le_sqrt
    (n j s : ℕ) (hj : 3 ≤ j) (hjn : j ≤ n + 1) (hs : 2 ≤ s) (hsj : s ≤ j) :
    ‖((((1 / atkinsonShiftedRelativePhase (n + s) s : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n s)‖
      ≤ Real.sqrt (↑(n + j)) := by
  rw [ atkinsonInversePhaseBoundaryCore_norm ];
  · -- Applying the lemma `atkinsonInversePhaseBoundaryCore_norm_le` and simplifying.
    have h_simplified : (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * (n + s + 1) / s ≤ Real.sqrt (n + j) := by
      have h_simplified : ((n + s + 1) : ℝ) / (s * Real.sqrt (n + 1)) ≤ Real.sqrt (n + j) := by
        have h_simplified : (n + s + 1 : ℝ) ^ 2 ≤ s ^ 2 * (n + j) * (n + 1) := by
          norm_cast; ring_nf at *; nlinarith [ Nat.mul_le_mul_left n hj, Nat.mul_le_mul_left n hs, Nat.mul_le_mul_left n hsj ] ;
        exact Real.le_sqrt_of_sq_le ( by rw [ div_pow, mul_pow, Real.sq_sqrt <| by positivity ] ; rw [ div_le_iff₀ <| by positivity ] ; linarith );
      convert h_simplified using 1 ; rw [ Real.sqrt_eq_rpow, Real.rpow_neg ( by positivity ) ] ; ring;
    convert h_simplified.trans' _ using 1;
    · norm_cast;
    · convert atkinsonShiftedRelativePhase_inv_upper ( n + s ) s ( by linarith ) ( by linarith ) |> fun x => mul_le_mul_of_nonneg_left x ( atkinsonModeWeight_nonneg n ) using 1 ; ring!;
      unfold atkinsonModeWeight; push_cast; ring;
  · linarith

private lemma atkinsonResonantBoundaryCorrection_le_sqrt
    (n j r : ℕ) (hj : 3 ≤ j) (hjn : j ≤ n + 1) (hrj : r + 2 ≤ j) :
    ‖∑ s ∈ Finset.Ico (r + 1) (j - 1),
      ((((atkinsonUpperBoundaryStepCoeff n (s + 1) - 1 : ℝ) : ℂ)) *
        ((((1 / atkinsonShiftedRelativePhase (n + (s + 2)) (s + 2) : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n (s + 2)))‖
      ≤ 2 * Real.sqrt (↑(n + j)) := by
  refine' le_trans ( norm_sum_le _ _ ) _;
  -- Apply the bound from atkinsonUpperBoundaryStepCoeff_sub_one_le and atkinsonInversePhaseBoundaryCore_norm_le.
  have h_term_bound : ∀ s ∈ Finset.Ico (r + 1) (j - 1), ‖(atkinsonUpperBoundaryStepCoeff n (s + 1) - 1 : ℝ) * ((1 / atkinsonShiftedRelativePhase (n + (s + 2)) (s + 2) : ℝ) * atkinsonShiftedSingleBoundaryCore n (s + 2))‖ ≤ (1 / (s + 1) : ℝ) * (Real.sqrt (n + 1) / (s + 2) + 1 / Real.sqrt (n + 1)) := by
    intros s hs
    have h_step_coeff : ‖(atkinsonUpperBoundaryStepCoeff n (s + 1) - 1 : ℝ)‖ ≤ 1 / (s + 1) := by
      norm_num +zetaDelta at *;
      rw [ abs_of_nonneg ( sub_nonneg_of_le <| atkinsonUpperBoundaryStepCoeff_one_le _ _ <| by linarith ) ] ; exact le_trans ( atkinsonUpperBoundaryStepCoeff_sub_one_le _ _ <| by linarith ) <| by norm_num;
    have h_inv_phase_core : ‖(1 / atkinsonShiftedRelativePhase (n + (s + 2)) (s + 2) : ℝ) * atkinsonShiftedSingleBoundaryCore n (s + 2)‖ ≤ Real.sqrt (n + 1) / (s + 2) + 1 / Real.sqrt (n + 1) := by
      convert atkinsonInversePhaseBoundaryCore_norm_le n ( s + 2 ) ( by linarith [ Finset.mem_Ico.mp hs ] ) using 1 ; norm_num [ add_assoc ]
    exact (by
    simpa only [ norm_mul, Complex.norm_real ] using mul_le_mul h_step_coeff h_inv_phase_core ( by positivity ) ( by positivity ));
  refine' le_trans ( Finset.sum_le_sum h_term_bound ) _ |> le_trans <| _;
  exact ( Real.sqrt ( n + 1 ) / 2 + ( j - 2 ) / Real.sqrt ( n + 1 ) );
  · -- The sum of the first part is a telescoping series, which simplifies to $\sqrt{n+1}/2$.
    have h_telescope : ∑ s ∈ Finset.Ico (r + 1) (j - 1), (1 / (s + 1) : ℝ) * (Real.sqrt (n + 1) / (s + 2)) = Real.sqrt (n + 1) * (1 / (r + 2) - 1 / j) := by
      have h_telescope : ∀ {a b : ℕ}, a ≤ b → ∑ s ∈ Finset.Ico a b, (1 / (s + 1) : ℝ) * (Real.sqrt (n + 1) / (s + 2)) = Real.sqrt (n + 1) * (1 / (a + 1) - 1 / (b + 1)) := by
        intros a b hab; induction hab <;> simp_all +decide [ Finset.sum_Ico_succ_top ] ; ring;
        -- Combine like terms and simplify the expression.
        field_simp
        ring;
      convert h_telescope ( show r + 1 ≤ j - 1 from Nat.le_sub_one_of_lt ( by linarith ) ) using 2 ; cases j <;> norm_num at * ; ring;
    simp_all +decide [ mul_add, Finset.sum_add_distrib ];
    refine' add_le_add _ _;
    · exact le_trans ( mul_le_mul_of_nonneg_left ( sub_le_self _ <| by positivity ) <| Real.sqrt_nonneg _ ) <| by rw [ div_eq_mul_inv ] ; exact mul_le_mul_of_nonneg_left ( inv_le_of_inv_le₀ ( by positivity ) <| by linarith [ show ( j : ℝ ) ≥ r + 2 by norm_cast ] ) <| Real.sqrt_nonneg _;
    · refine' le_trans ( Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_right ( inv_le_one_of_one_le₀ <| by linarith ) <| inv_nonneg.2 <| Real.sqrt_nonneg _ ) _ ; norm_num [ div_eq_mul_inv ];
      exact mul_le_mul_of_nonneg_right ( by rw [ Nat.cast_sub <| by omega, Nat.cast_sub <| by omega ] ; push_cast ; linarith ) <| inv_nonneg.2 <| Real.sqrt_nonneg _;
  · rw [ add_div', div_le_iff₀ ] <;> norm_num <;> try positivity;
    nlinarith only [ show ( j : ℝ ) ≤ n + 1 by norm_cast, show ( 3 : ℝ ) ≤ j by norm_cast, Real.sqrt_nonneg ( n + 1 ), Real.sqrt_nonneg ( n + j ), Real.mul_self_sqrt ( show ( n:ℝ ) + 1 ≥ 0 by positivity ), Real.mul_self_sqrt ( show ( n:ℝ ) + j ≥ 0 by positivity ), Real.sqrt_le_sqrt ( show ( n:ℝ ) + 1 ≤ n + j by norm_cast; linarith ) ]

/-- **Resonant Boundary Tail Bound (Lemma 4)**.
    The sum of resonant boundary terms in the gap layers is bounded by C·√(n+j).

    Uses the telescoping identity to decompose into two endpoints plus a correction.
    Each endpoint has norm ≤ √(n+j) and the correction sum is ≤ 2·√(n+j). -/
theorem atkinsonResonantShiftedBoundaryTail_bound :
    ∃ C_res > 0, ∀ j : ℕ, 3 ≤ j → ∀ n : ℕ, j ≤ n + 1 → ∀ r : ℕ, r + 2 ≤ j →
      ‖∑ s ∈ Finset.Ico (r + 1) (j - 1),
          atkinsonResonantShiftedBoundaryTerm n (s + 1)‖
        ≤ C_res * Real.sqrt (↑(n + j)) := by
  refine ⟨4, by positivity, ?_⟩
  intro j hj n hjn r hrj
  have htelescope := atkinsonResonantShiftedBoundary_backwardTail_general n j r hrj
  rw [htelescope]
  calc
    ‖((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n j)
        -
      ((((1 / atkinsonShiftedRelativePhase (n + (r + 2)) (r + 2) : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n (r + 2))
        +
      ∑ s ∈ Finset.Ico (r + 1) (j - 1),
        ((((atkinsonUpperBoundaryStepCoeff n (s + 1) - 1 : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase (n + (s + 2)) (s + 2) : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n (s + 2)))‖
      ≤
    ‖((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n j)‖
      +
    ‖((((1 / atkinsonShiftedRelativePhase (n + (r + 2)) (r + 2) : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n (r + 2))‖
      +
    ‖∑ s ∈ Finset.Ico (r + 1) (j - 1),
        ((((atkinsonUpperBoundaryStepCoeff n (s + 1) - 1 : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase (n + (s + 2)) (s + 2) : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n (s + 2)))‖ := by
          linarith [norm_add_le
              ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ) *
                  atkinsonShiftedSingleBoundaryCore n j) -
               ((1 / atkinsonShiftedRelativePhase (n + (r + 2)) (r + 2) : ℝ) : ℂ) *
                  atkinsonShiftedSingleBoundaryCore n (r + 2))
              (∑ s ∈ Finset.Ico (r + 1) (j - 1),
                (((atkinsonUpperBoundaryStepCoeff n (s + 1) - 1 : ℝ) : ℂ) *
                  (((1 / atkinsonShiftedRelativePhase (n + (s + 2)) (s + 2) : ℝ) : ℂ) *
                    atkinsonShiftedSingleBoundaryCore n (s + 2)))),
            norm_sub_le
              (((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ) *
                atkinsonShiftedSingleBoundaryCore n j)
              (((1 / atkinsonShiftedRelativePhase (n + (r + 2)) (r + 2) : ℝ) : ℂ) *
                atkinsonShiftedSingleBoundaryCore n (r + 2))]
    _ ≤ Real.sqrt (↑(n + j)) + Real.sqrt (↑(n + j)) + 2 * Real.sqrt (↑(n + j)) := by
          exact add_le_add (add_le_add
            (atkinsonInversePhaseBoundaryCore_le_sqrt n j j hj hjn (by omega) le_rfl)
            (atkinsonInversePhaseBoundaryCore_le_sqrt n j (r + 2) hj hjn (by omega) hrj))
            (atkinsonResonantBoundaryCorrection_le_sqrt n j r hj hjn hrj)
    _ = 4 * Real.sqrt (↑(n + j)) := by ring


private theorem atkinsonShiftedInversePhaseCore_step
    (n j : ℕ) (hj : 1 ≤ j) :
    ((((1 / atkinsonShiftedRelativePhase (n + (j + 1)) (j + 1) : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n (j + 1))
      =
    ((((1 / atkinsonUpperBoundaryStepCoeff n j : ℝ) : ℂ)) *
        atkinsonResonantShiftedBoundaryTerm n j)
      +
    ((((1 / atkinsonUpperBoundaryStepCoeff n j : ℝ) : ℂ)) *
        ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n j)) := by
  have hK :
      atkinsonLowerBoundaryShiftKernel n (j + 1) j
        = 1 / atkinsonUpperBoundaryStepCoeff n j := by
    rw [atkinsonLowerBoundaryShiftKernel_step_mul n j j hj le_rfl,
      atkinsonLowerBoundaryShiftKernel_self n j hj, mul_one]
  have hcoeff :
      1 / atkinsonUpperBoundaryStepCoeff n j
        =
      atkinsonShiftedRelativePhase (n + j) j /
        atkinsonShiftedRelativePhase (n + (j + 1)) (j + 1) := by
    simpa [atkinsonLowerBoundaryShiftKernel, Nat.add_assoc] using hK.symm
  have hphase_j_pos :
      0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j hj (by omega)
  have hphase_j1_pos :
      0 < atkinsonShiftedRelativePhase (n + (j + 1)) (j + 1) := by
    exact atkinsonShiftedRelativePhase_pos (n + (j + 1)) (j + 1)
      (Nat.succ_le_succ (Nat.zero_le j)) (by omega)
  have hsecond :
      ((((1 / atkinsonShiftedRelativePhase (n + (j + 1)) (j + 1) : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n j)
        =
      ((((1 / atkinsonUpperBoundaryStepCoeff n j : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n j)) := by
    rw [show
      (((1 / atkinsonShiftedRelativePhase (n + (j + 1)) (j + 1) : ℝ) : ℂ))
        =
      ((((1 / atkinsonUpperBoundaryStepCoeff n j : ℝ) : ℂ)) *
        (((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ))) by
          rw [← Complex.ofReal_mul]
          congr 1
          rw [hcoeff]
          field_simp [ne_of_gt hphase_j_pos, ne_of_gt hphase_j1_pos]]
    ring
  have hstep :=
    atkinsonLowerBoundary_shiftBoundary_step n (j + 1) j
      (Nat.succ_le_succ (Nat.zero_le j)) hj
  calc
    ((((1 / atkinsonShiftedRelativePhase (n + (j + 1)) (j + 1) : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n (j + 1))
      =
    (((((1 / atkinsonShiftedRelativePhase (n + (j + 1)) (j + 1) : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n (j + 1))
        -
        ((((1 / atkinsonShiftedRelativePhase (n + (j + 1)) (j + 1) : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n j))
      +
      ((((1 / atkinsonShiftedRelativePhase (n + (j + 1)) (j + 1) : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n j) := by
          ring
    _ =
      ((((atkinsonLowerBoundaryShiftKernel n (j + 1) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm n j)
          +
      ((((1 / atkinsonShiftedRelativePhase (n + (j + 1)) (j + 1) : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n j) := by
              rw [hstep]
    _ =
      ((((1 / atkinsonUpperBoundaryStepCoeff n j : ℝ) : ℂ)) *
          atkinsonResonantShiftedBoundaryTerm n j)
        +
      ((((1 / atkinsonShiftedRelativePhase (n + (j + 1)) (j + 1) : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n j) := by
          rw [hK]
    _ =
      ((((1 / atkinsonUpperBoundaryStepCoeff n j : ℝ) : ℂ)) *
          atkinsonResonantShiftedBoundaryTerm n j)
        +
      ((((1 / atkinsonUpperBoundaryStepCoeff n j : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n j)) := by
              rw [hsecond]

private theorem atkinsonShiftedInversePhaseCorePrefix_succ_eq
    (N j : ℕ) (hj : 1 ≤ j) :
    ∑ k ∈ Finset.range N,
        ((((1 / atkinsonShiftedRelativePhase
            (k + ((j + 1) + (j + 1))) (j + 1) : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + (j + 1)) (j + 1))
      =
    (∑ k ∈ Finset.range N,
        ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
          atkinsonResonantShiftedBoundaryTerm (k + (j + 1)) j))
      +
    ∑ k ∈ Finset.range N,
        ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase
              (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j)) := by
  calc
    ∑ k ∈ Finset.range N,
        ((((1 / atkinsonShiftedRelativePhase
            (k + ((j + 1) + (j + 1))) (j + 1) : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + (j + 1)) (j + 1))
      =
    ∑ k ∈ Finset.range N,
        (((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm (k + (j + 1)) j)
          +
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase
                (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                simpa [Nat.add_assoc, add_left_comm, add_comm] using
                  atkinsonShiftedInversePhaseCore_step (k + (j + 1)) j hj
    _ =
      (∑ k ∈ Finset.range N,
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm (k + (j + 1)) j))
        +
      ∑ k ∈ Finset.range N,
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase
                (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j)) := by
                rw [Finset.sum_add_distrib]

private theorem atkinson_large_modes_complete_resonant_packet_row_lower_boundary_sum_bound_atomic_of_prefix
    (hprefix :
      ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            atkinsonWeightedResonantBlockMode (n + j) 0 *
              atkinsonShiftedSinglePrimitive (n + j) j 0‖
          ≤ C_complete * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j)) :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then
            atkinsonWeightedResonantBlockMode (n + j) 0 *
              atkinsonShiftedSinglePrimitive (n + j) j 0
          else 0)‖
        ≤ C_complete * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨Cp, hCp, hprefix'⟩ := hprefix
  refine ⟨2 * Cp, by positivity, ?_⟩
  intro j hj M
  let base : ℕ → ℂ := fun n =>
    atkinsonWeightedResonantBlockMode (n + j) 0 *
      atkinsonShiftedSinglePrimitive (n + j) j 0
  let target : ℝ := Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j
  by_cases hMj : M ≤ j
  · have hzero :
        ∑ n ∈ Finset.range M, (if j ≤ n then base n else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnlt : n < j := lt_of_lt_of_le (Finset.mem_range.mp hn) hMj
      simp [base, hnlt.not_ge]
    have hnonneg : 0 ≤ (2 * Cp) * target := by positivity
    simpa [base, target, hzero] using hnonneg
  · have hJM : j ≤ M := le_of_lt (lt_of_not_ge hMj)
    have hsum :
        ∑ n ∈ Finset.range M, (if j ≤ n then base n else 0)
          =
        ∑ n ∈ Finset.Ico j M, base n := by
      calc
        ∑ n ∈ Finset.range M, (if j ≤ n then base n else 0)
            =
        (∑ n ∈ Finset.range j, (if j ≤ n then base n else 0))
          + ∑ n ∈ Finset.Ico j M, (if j ≤ n then base n else 0) := by
            simpa using
              (Finset.sum_range_add_sum_Ico (fun n => if j ≤ n then base n else 0) hJM).symm
        _ = ∑ n ∈ Finset.Ico j M, (if j ≤ n then base n else 0) := by
              have hprefix_zero :
                  ∑ n ∈ Finset.range j, (if j ≤ n then base n else 0) = 0 := by
                    apply Finset.sum_eq_zero
                    intro n hn
                    simp [base, (Finset.mem_range.mp hn).not_ge]
              rw [hprefix_zero, zero_add]
        _ = ∑ n ∈ Finset.Ico j M, base n := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              simp [base, (Finset.mem_Ico.mp hn).1]
    have hsplit :
        ∑ n ∈ Finset.Ico j M, base n
          =
        (∑ n ∈ Finset.range M, base n) - ∑ n ∈ Finset.range j, base n := by
      rw [Finset.sum_Ico_eq_sub _ hJM]
    have hprefix_M :
        ‖∑ n ∈ Finset.range M, base n‖
          ≤ Cp * target := by
      have hraw := hprefix' j hj (M - 1)
      calc
        ‖∑ n ∈ Finset.range M, base n‖
            ≤ Cp * (Real.sqrt (((M - 1 + j : ℕ) : ℝ) + 1) / j) := by
              simpa [base, show M - 1 + 1 = M by omega, Nat.add_assoc, add_left_comm, add_comm] using
                hraw
        _ = Cp * (Real.sqrt ((M + j : ℕ) : ℝ) / j) := by
              have hM : (M - 1 + j : ℕ) + 1 = M + j := by omega
              have hM' : (((M - 1 + j : ℕ) : ℝ) + 1) = ((M + j : ℕ) : ℝ) := by
                exact_mod_cast hM
              rw [hM']
        _ ≤ Cp * target := by
              refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hCp)
              exact div_le_div_of_nonneg_right
                (Real.sqrt_le_sqrt (by linarith))
                (by positivity : (0 : ℝ) ≤ j)
    have hprefix_j :
        ‖∑ n ∈ Finset.range j, base n‖
          ≤ Cp * target := by
      have hraw := hprefix' j hj (j - 1)
      have hj_le : ((j - 1 + j : ℕ) : ℝ) + 1 ≤ (((M + j : ℕ) : ℝ) + 1) := by
        exact_mod_cast (by omega : (j - 1 + j) + 1 ≤ M + j + 1)
      calc
        ‖∑ n ∈ Finset.range j, base n‖
            ≤ Cp * (Real.sqrt (((j - 1 + j : ℕ) : ℝ) + 1) / j) := by
              simpa [base, show j - 1 + 1 = j by omega, Nat.add_assoc, add_left_comm, add_comm] using
                hraw
        _ ≤ Cp * target := by
              refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hCp)
              exact div_le_div_of_nonneg_right
                (Real.sqrt_le_sqrt hj_le)
                (by positivity : (0 : ℝ) ≤ j)
    calc
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then
            atkinsonWeightedResonantBlockMode (n + j) 0 *
              atkinsonShiftedSinglePrimitive (n + j) j 0
          else 0)‖
        = ‖∑ n ∈ Finset.Ico j M, base n‖ := by
            rw [hsum]
      _ = ‖(∑ n ∈ Finset.range M, base n) - ∑ n ∈ Finset.range j, base n‖ := by
            rw [hsplit]
      _ ≤ ‖∑ n ∈ Finset.range M, base n‖ + ‖∑ n ∈ Finset.range j, base n‖ := by
            exact norm_sub_le _ _
      _ ≤ Cp * target + Cp * target := by
            exact add_le_add hprefix_M hprefix_j
      _ = (2 * Cp) * target := by ring

private theorem atkinson_large_modes_complete_resonant_packet_row_lower_boundary_sum_bound_atomic_of_inverse_phase_core
    (hinv :
      ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n j)‖
          ≤ C_complete * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j)) :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then
            atkinsonWeightedResonantBlockMode (n + j) 0 *
              atkinsonShiftedSinglePrimitive (n + j) j 0
          else 0)‖
        ≤ C_complete * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  apply
    atkinson_large_modes_complete_resonant_packet_row_lower_boundary_sum_bound_atomic_of_prefix
  rcases hinv with ⟨C_complete, hC_complete, hCinv⟩
  refine ⟨C_complete, hC_complete, ?_⟩
  intro j hj M
  calc
    ‖∑ n ∈ Finset.range (M + 1),
        atkinsonWeightedResonantBlockMode (n + j) 0 *
          atkinsonShiftedSinglePrimitive (n + j) j 0‖
      =
    ‖∑ n ∈ Finset.range (M + 1),
        ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n j)‖ := by
          refine congrArg norm ?_
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [atkinson_inverse_phase_core_eq_lowerBoundaryTerm n j hj]
    _ ≤ C_complete * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
          exact hCinv j hj M

private theorem atkinson_large_modes_complete_resonant_packet_row_lower_boundary_sum_bound_atomic_of_shifted_inverse_phase_core
    (hinv :
      ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ N : ℕ,
        ‖∑ k ∈ Finset.range N,
            ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) j)‖
          ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)) :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then
            atkinsonWeightedResonantBlockMode (n + j) 0 *
              atkinsonShiftedSinglePrimitive (n + j) j 0
          else 0)‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_complete, hC_complete, hshift⟩ := hinv
  refine ⟨C_complete, hC_complete, ?_⟩
  intro j hj M
  by_cases hMj : M ≤ j
  · have hzero :
        ∑ n ∈ Finset.range M,
            (if j ≤ n then
              atkinsonWeightedResonantBlockMode (n + j) 0 *
                atkinsonShiftedSinglePrimitive (n + j) j 0
            else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnlt : n < j := lt_of_lt_of_le (Finset.mem_range.mp hn) hMj
      simp [hnlt.not_ge]
    have hnonneg :
        0 ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
      apply mul_nonneg
      · exact mul_nonneg (le_of_lt hC_complete) (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega))
      · positivity
    simpa [hzero] using hnonneg
  · have hJM : j ≤ M := le_of_lt (lt_of_not_ge hMj)
    let N : ℕ := M - j
    have hM : N + j = M := by
      dsimp [N]
      omega
    have hsum :
        ∑ n ∈ Finset.range M,
            (if j ≤ n then
              atkinsonWeightedResonantBlockMode (n + j) 0 *
                atkinsonShiftedSinglePrimitive (n + j) j 0
            else 0)
          =
        ∑ k ∈ Finset.range N,
            ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) j) := by
      calc
        ∑ n ∈ Finset.range M,
            (if j ≤ n then
              atkinsonWeightedResonantBlockMode (n + j) 0 *
                atkinsonShiftedSinglePrimitive (n + j) j 0
            else 0)
          =
        ∑ n ∈ Finset.Ico j M,
            atkinsonWeightedResonantBlockMode (n + j) 0 *
              atkinsonShiftedSinglePrimitive (n + j) j 0 := by
              calc
                ∑ n ∈ Finset.range M,
                    (if j ≤ n then
                      atkinsonWeightedResonantBlockMode (n + j) 0 *
                        atkinsonShiftedSinglePrimitive (n + j) j 0
                    else 0)
                    =
                (∑ n ∈ Finset.range j,
                    (if j ≤ n then
                      atkinsonWeightedResonantBlockMode (n + j) 0 *
                        atkinsonShiftedSinglePrimitive (n + j) j 0
                    else 0))
                  +
                ∑ n ∈ Finset.Ico j M,
                    (if j ≤ n then
                      atkinsonWeightedResonantBlockMode (n + j) 0 *
                        atkinsonShiftedSinglePrimitive (n + j) j 0
                    else 0) := by
                      simpa using
                        (Finset.sum_range_add_sum_Ico
                          (fun n =>
                            if j ≤ n then
                              atkinsonWeightedResonantBlockMode (n + j) 0 *
                                atkinsonShiftedSinglePrimitive (n + j) j 0
                            else 0)
                          hJM).symm
                _ =
                ∑ n ∈ Finset.Ico j M,
                    (if j ≤ n then
                      atkinsonWeightedResonantBlockMode (n + j) 0 *
                        atkinsonShiftedSinglePrimitive (n + j) j 0
                    else 0) := by
                      have hprefix_zero :
                          ∑ n ∈ Finset.range j,
                              (if j ≤ n then
                                atkinsonWeightedResonantBlockMode (n + j) 0 *
                                  atkinsonShiftedSinglePrimitive (n + j) j 0
                              else 0) = 0 := by
                            apply Finset.sum_eq_zero
                            intro n hn
                            simp [(Finset.mem_range.mp hn).not_ge]
                      rw [hprefix_zero, zero_add]
                _ =
                ∑ n ∈ Finset.Ico j M,
                    atkinsonWeightedResonantBlockMode (n + j) 0 *
                      atkinsonShiftedSinglePrimitive (n + j) j 0 := by
                      refine Finset.sum_congr rfl ?_
                      intro n hn
                      simp [(Finset.mem_Ico.mp hn).1]
        _ =
        ∑ k ∈ Finset.range N,
            atkinsonWeightedResonantBlockMode ((k + j) + j) 0 *
              atkinsonShiftedSinglePrimitive ((k + j) + j) j 0 := by
              rw [← hM]
              simpa [N, Nat.add_assoc, add_left_comm, add_comm] using
                (Finset.sum_Ico_eq_sum_range
                  (f := fun n =>
                    atkinsonWeightedResonantBlockMode (n + j) 0 *
                      atkinsonShiftedSinglePrimitive (n + j) j 0)
                  (m := j) (n := j + N))
        _ =
        ∑ k ∈ Finset.range N,
            ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) j) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              rw [← atkinson_inverse_phase_core_eq_lowerBoundaryTerm (k + j) j hj]
              simp [Nat.add_assoc, add_left_comm, add_comm]
    have hmain := hshift j hj N
    have htarget :
        Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j
          ≤ Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j := by
      rw [hM]
      exact div_le_div_of_nonneg_right
        (Real.sqrt_le_sqrt (by
          exact_mod_cast (by omega : M + 1 ≤ M + j + 1)))
        (by positivity : (0 : ℝ) ≤ j)
    calc
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then
            atkinsonWeightedResonantBlockMode (n + j) 0 *
              atkinsonShiftedSinglePrimitive (n + j) j 0
          else 0)‖
        =
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) j)‖ := by
            rw [hsum]
      _ ≤ C_complete * Real.log (↑j + 1) *
              (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := hmain
      _ ≤ C_complete * Real.log (↑j + 1) *
              (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
            apply mul_le_mul_of_nonneg_left htarget
            exact mul_nonneg (le_of_lt hC_complete)
              (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega))

private theorem atkinsonShiftedInversePhaseCorePrefix_tail_bound_of_hinv
    (hinv :
      ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ N : ℕ,
        ‖∑ k ∈ Finset.range N,
            ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) j)‖
          ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)) :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase
              (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j)‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨Cl, hCl, hlower⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_lower_boundary_sum_bound_atomic_of_shifted_inverse_phase_core
      hinv
  refine ⟨2 * Real.sqrt 2 * Cl, by positivity, ?_⟩
  intro j hj N
  let J : ℕ := j + 1
  let rowFn : ℕ → ℂ := fun n =>
    if j ≤ n then
      atkinsonWeightedResonantBlockMode (n + j) 0 *
        atkinsonShiftedSinglePrimitive (n + j) j 0
    else 0
  let target : ℝ := Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j
  have hsum :
      ∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase
              (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j)
        =
      ∑ n ∈ Finset.Ico J (J + N), rowFn n := by
    have hJN' : j + (N + 1) - (j + 1) = N := by
      omega
    calc
      ∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase
              (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j)
        =
      ∑ n ∈ Finset.Ico J (J + N),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n j) := by
              simpa [J, hJN', Nat.add_assoc, add_left_comm, add_comm] using
                (Finset.sum_Ico_eq_sum_range
                  (f := fun n =>
                    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                      atkinsonShiftedSingleBoundaryCore n j))
                  (m := J) (n := J + N)).symm
      _ =
      ∑ n ∈ Finset.Ico J (J + N), rowFn n := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        have hJn : J ≤ n := (Finset.mem_Ico.mp hn).1
        have hjn : j ≤ n := le_trans (Nat.le_succ j) hJn
        rw [atkinson_inverse_phase_core_eq_lowerBoundaryTerm n j hj]
        simp [rowFn, hjn]
  have hsplit :
      ∑ n ∈ Finset.Ico J (J + N), rowFn n
        =
      (∑ n ∈ Finset.range (J + N), rowFn n)
        - ∑ n ∈ Finset.range J, rowFn n := by
          rw [Finset.sum_Ico_eq_sub _ (Nat.le_add_right J N)]
  have hupper_raw :
      ‖∑ n ∈ Finset.range (J + N), rowFn n‖
        ≤ Cl * Real.log (↑j + 1) * (Real.sqrt ((((J + N) + j : ℕ) : ℝ) + 1) / j) := by
          simpa [rowFn, J, Nat.add_assoc, add_left_comm, add_comm] using
            hlower j hj (J + N)
  have hupper_target :
      Real.sqrt ((((J + N) + j : ℕ) : ℝ) + 1) / j ≤ Real.sqrt 2 * target := by
    have hle :
        ((((J + N) + j : ℕ) : ℝ) + 1) ≤ 2 * ((((N + j : ℕ) : ℝ) + 1) : ℝ) := by
      exact_mod_cast (by
        dsimp [J]
        omega : (J + N) + j + 1 ≤ 2 * (N + j + 1))
    calc
      Real.sqrt ((((J + N) + j : ℕ) : ℝ) + 1) / j
          ≤ Real.sqrt (2 * ((((N + j : ℕ) : ℝ) + 1))) / j := by
              exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hle)
                (by positivity : (0 : ℝ) ≤ j)
      _ = (Real.sqrt 2 * Real.sqrt ((((N + j : ℕ) : ℝ) + 1))) / j := by
            have hsqrt_eq :
                Real.sqrt (2 * ((((N + j : ℕ) : ℝ) + 1)))
                  = Real.sqrt 2 * Real.sqrt ((((N + j : ℕ) : ℝ) + 1)) := by
                    simpa using
                      (Real.sqrt_mul
                        (by positivity : 0 ≤ (2 : ℝ))
                        (by positivity : 0 ≤ ((((N + j : ℕ) : ℝ) + 1))))
            rw [hsqrt_eq]
      _ = Real.sqrt 2 * target := by
            unfold target
            ring
  have hupper :
      ‖∑ n ∈ Finset.range (J + N), rowFn n‖ ≤ Real.sqrt 2 * Cl * Real.log (↑j + 1) * target := by
    calc
      ‖∑ n ∈ Finset.range (J + N), rowFn n‖
          ≤ Cl * Real.log (↑j + 1) * (Real.sqrt ((((J + N) + j : ℕ) : ℝ) + 1) / j) := hupper_raw
      _ ≤ Cl * Real.log (↑j + 1) * (Real.sqrt 2 * target) := by
            exact mul_le_mul_of_nonneg_left hupper_target
              (mul_nonneg (le_of_lt hCl) (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)))
      _ = Real.sqrt 2 * Cl * Real.log (↑j + 1) * target := by ring
  have hlower_raw :
      ‖∑ n ∈ Finset.range J, rowFn n‖
        ≤ Cl * Real.log (↑j + 1) * (Real.sqrt (((J + j : ℕ) : ℝ) + 1) / j) := by
          simpa [rowFn, J, Nat.add_assoc, add_left_comm, add_comm] using
            hlower j hj J
  have hlower_target :
      Real.sqrt (((J + j : ℕ) : ℝ) + 1) / j ≤ Real.sqrt 2 * target := by
    have hle :
        (((J + j : ℕ) : ℝ) + 1) ≤ 2 * ((((N + j : ℕ) : ℝ) + 1) : ℝ) := by
      exact_mod_cast (by
        dsimp [J]
        omega : J + j + 1 ≤ 2 * (N + j + 1))
    calc
      Real.sqrt (((J + j : ℕ) : ℝ) + 1) / j
          ≤ Real.sqrt (2 * ((((N + j : ℕ) : ℝ) + 1))) / j := by
              exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hle)
                (by positivity : (0 : ℝ) ≤ j)
      _ = (Real.sqrt 2 * Real.sqrt ((((N + j : ℕ) : ℝ) + 1))) / j := by
            have hsqrt_eq :
                Real.sqrt (2 * ((((N + j : ℕ) : ℝ) + 1)))
                  = Real.sqrt 2 * Real.sqrt ((((N + j : ℕ) : ℝ) + 1)) := by
                    simpa using
                      (Real.sqrt_mul
                        (by positivity : 0 ≤ (2 : ℝ))
                        (by positivity : 0 ≤ ((((N + j : ℕ) : ℝ) + 1))))
            rw [hsqrt_eq]
      _ = Real.sqrt 2 * target := by
            unfold target
            ring
  have hlower_tail :
      ‖∑ n ∈ Finset.range J, rowFn n‖ ≤ Real.sqrt 2 * Cl * Real.log (↑j + 1) * target := by
    calc
      ‖∑ n ∈ Finset.range J, rowFn n‖
          ≤ Cl * Real.log (↑j + 1) * (Real.sqrt (((J + j : ℕ) : ℝ) + 1) / j) := hlower_raw
      _ ≤ Cl * Real.log (↑j + 1) * (Real.sqrt 2 * target) := by
            exact mul_le_mul_of_nonneg_left hlower_target
              (mul_nonneg (le_of_lt hCl) (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)))
      _ = Real.sqrt 2 * Cl * Real.log (↑j + 1) * target := by ring
  calc
    ‖∑ k ∈ Finset.range N,
        ((((1 / atkinsonShiftedRelativePhase
            (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j)‖
      = ‖∑ n ∈ Finset.Ico J (J + N), rowFn n‖ := by
          rw [hsum]
    _ = ‖(∑ n ∈ Finset.range (J + N), rowFn n) - ∑ n ∈ Finset.range J, rowFn n‖ := by
          rw [hsplit]
    _ ≤ ‖∑ n ∈ Finset.range (J + N), rowFn n‖ + ‖∑ n ∈ Finset.range J, rowFn n‖ := by
          exact norm_sub_le _ _
    _ ≤ Real.sqrt 2 * Cl * Real.log (↑j + 1) * target +
          Real.sqrt 2 * Cl * Real.log (↑j + 1) * target := by
          exact add_le_add hupper hlower_tail
    _ = (2 * Real.sqrt 2 * Cl) * Real.log (↑j + 1) * target := by
          ring

private theorem atkinsonShiftedInversePhaseCorePrefix_upper_weighted_bound_of_hinv
    (hinv :
      ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ N : ℕ,
        ‖∑ k ∈ Finset.range N,
            ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) j)‖
          ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)) :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((atkinsonUpperBoundaryWeightedCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase
                (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨Ct, hCt, htail⟩ := atkinsonShiftedInversePhaseCorePrefix_tail_bound_of_hinv hinv
  refine ⟨2 * Ct, by positivity, ?_⟩
  intro j hj N
  let J : ℕ := j + 1
  let target : ℝ := Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j
  by_cases hN : N = 0
  · have hnonneg : 0 ≤ (2 * Ct) * Real.log (↑j + 1) * target := by
      apply mul_nonneg
      · exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega))
      · positivity
    simpa [hN, target] using hnonneg
  · obtain ⟨n0, hn0 : N = n0 + 1⟩ := Nat.exists_eq_succ_of_ne_zero hN
    let baseFn : ℕ → ℂ := fun k =>
      ((((1 / atkinsonShiftedRelativePhase
          (k + (J + j)) j : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore (k + J) j)
    let C0 : ℝ := Ct * Real.log (↑j + 1) * target
    let aRe : ℕ → ℝ := fun k => (baseFn k).re
    let aIm : ℕ → ℝ := fun k => (baseFn k).im
    let b : ℕ → ℝ := fun k => atkinsonUpperBoundaryWeightedCoeff (k + J) j
    have hpartial_re : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aRe m| ≤ C0 := by
      intro k hk
      have hbound := htail j hj (k + 1)
      have htarget_k :
          Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / j ≤ target := by
        unfold target
        exact div_le_div_of_nonneg_right
          (Real.sqrt_le_sqrt (by
            exact_mod_cast (by omega : (k + 1 + j) + 1 ≤ (N + j) + 1)))
          (by positivity : (0 : ℝ) ≤ j)
      calc
        |∑ m ∈ Finset.range (k + 1), aRe m|
            = |(∑ m ∈ Finset.range (k + 1), baseFn m).re| := by
                simp [aRe]
        _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_re_le_norm _
        _ ≤ Ct * Real.log (↑j + 1) * (Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / j) := by
              simpa [baseFn, J, Nat.add_assoc, add_left_comm, add_comm] using hbound
        _ ≤ Ct * Real.log (↑j + 1) * target := by
              exact mul_le_mul_of_nonneg_left htarget_k
                (mul_nonneg (le_of_lt hCt) (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)))
        _ = C0 := by
              rfl
    have hpartial_im : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aIm m| ≤ C0 := by
      intro k hk
      have hbound := htail j hj (k + 1)
      have htarget_k :
          Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / j ≤ target := by
        unfold target
        exact div_le_div_of_nonneg_right
          (Real.sqrt_le_sqrt (by
            exact_mod_cast (by omega : (k + 1 + j) + 1 ≤ (N + j) + 1)))
          (by positivity : (0 : ℝ) ≤ j)
      calc
        |∑ m ∈ Finset.range (k + 1), aIm m|
            = |(∑ m ∈ Finset.range (k + 1), baseFn m).im| := by
                simp [aIm]
        _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_im_le_norm _
        _ ≤ Ct * Real.log (↑j + 1) * (Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / j) := by
              simpa [baseFn, J, Nat.add_assoc, add_left_comm, add_comm] using hbound
        _ ≤ Ct * Real.log (↑j + 1) * target := by
              exact mul_le_mul_of_nonneg_left htarget_k
                (mul_nonneg (le_of_lt hCt) (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)))
        _ = C0 := by
              rfl
    have hb_nonneg : ∀ k ≤ n0, 0 ≤ b k := by
      intro k hk
      exact atkinsonUpperBoundaryWeightedCoeff_nonneg (k + J) j hj
    have hb_anti : ∀ k < n0, b (k + 1) ≤ b k := by
      intro k hk
      exact atkinsonUpperBoundaryWeightedCoeff_antitone j hj (by omega : k + J ≤ k + 1 + J)
    have hb_one : b 0 ≤ 1 := by
      simpa [b, J] using atkinsonUpperBoundaryWeightedCoeff_le_one J j hj
    have hb0_nonneg : 0 ≤ b 0 := hb_nonneg 0 (by omega)
    have hC0_nonneg : 0 ≤ C0 := by
      unfold C0 target
      apply mul_nonneg
      · exact mul_nonneg (le_of_lt hCt) (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega))
      · positivity
    have hsum_re :
        (∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re
          =
        ∑ k ∈ Finset.range (n0 + 1), aRe k * b k := by
          simp [aRe, b, baseFn, mul_comm, mul_left_comm, mul_assoc]
    have hsum_im :
        (∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im
          =
        ∑ k ∈ Finset.range (n0 + 1), aIm k * b k := by
          simp [aIm, b, baseFn, mul_comm, mul_left_comm, mul_assoc]
    have hre :
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re| ≤ C0 := by
      have habel :=
        AbelSummation.abel_summation_bound aRe b n0 C0 hpartial_re hb_nonneg hb_anti
      have habel' :
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re| ≤ C0 * b 0 := by
        simpa [hsum_re] using habel
      have hmul : C0 * b 0 ≤ C0 := by
        nlinarith [hC0_nonneg, hb0_nonneg, hb_one]
      exact habel'.trans hmul
    have him :
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| ≤ C0 := by
      have habel :=
        AbelSummation.abel_summation_bound aIm b n0 C0 hpartial_im hb_nonneg hb_anti
      have habel' :
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| ≤ C0 * b 0 := by
        simpa [hsum_im] using habel
      have hmul : C0 * b 0 ≤ C0 := by
        nlinarith [hC0_nonneg, hb0_nonneg, hb_one]
      exact habel'.trans hmul
    have hnorm :
        ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖ ≤ 2 * C0 := by
      calc
        ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖
            ≤
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
            +
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| := by
              exact Complex.norm_le_abs_re_add_abs_im _
        _ ≤ C0 + C0 := add_le_add hre him
        _ = 2 * C0 := by ring
    calc
      ‖∑ k ∈ Finset.range N,
          ((((atkinsonUpperBoundaryWeightedCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase
                (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖
        = ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖ := by
              simpa [hn0, b, baseFn, J, Nat.add_assoc, add_left_comm, add_comm]
      _ ≤ 2 * C0 := hnorm
      _ = (2 * Ct) * Real.log (↑j + 1) * target := by
            unfold C0
            ring

/-- Reciprocal-step-coefficient weighted boundary-core prefix bound obtained by
Abel summation from the same-shift tail control
`atkinsonShiftedInversePhaseCorePrefix_tail_bound_of_hinv`.

The weight satisfies the Abel conditions:
* nonneg  (`atkinsonUpperBoundaryStepCoeff_inv_nonneg`)
* antitone (`atkinsonUpperBoundaryStepCoeff_inv_antitone`)
* ≤ 1     (`atkinsonUpperBoundaryStepCoeff_inv_le_one`)

This is the reciprocal-weight analogue of
`atkinsonShiftedInversePhaseCorePrefix_upper_weighted_bound_of_hinv`, which
uses the complementary weight `2 - atkinsonUpperBoundaryStepCoeff`. -/
private theorem atkinsonShiftedInversePhaseCorePrefix_recipStepCoeff_weighted_bound_of_hinv
    (hinv :
      ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ N : ℕ,
        ‖∑ k ∈ Finset.range N,
            ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) j)‖
          ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)) :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase
                (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨Ct, hCt, htail⟩ := atkinsonShiftedInversePhaseCorePrefix_tail_bound_of_hinv hinv
  refine ⟨2 * Ct, by positivity, ?_⟩
  intro j hj N
  let J : ℕ := j + 1
  let target : ℝ := Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j
  by_cases hN : N = 0
  · have hnonneg : 0 ≤ (2 * Ct) * Real.log (↑j + 1) * target := by
      apply mul_nonneg
      · exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega))
      · positivity
    simpa [hN, target] using hnonneg
  · obtain ⟨n0, hn0 : N = n0 + 1⟩ := Nat.exists_eq_succ_of_ne_zero hN
    let baseFn : ℕ → ℂ := fun k =>
      ((((1 / atkinsonShiftedRelativePhase
          (k + (J + j)) j : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore (k + J) j)
    let C0 : ℝ := Ct * Real.log (↑j + 1) * target
    let aRe : ℕ → ℝ := fun k => (baseFn k).re
    let aIm : ℕ → ℝ := fun k => (baseFn k).im
    let b : ℕ → ℝ := fun k => 1 / atkinsonUpperBoundaryStepCoeff (k + J) j
    have hpartial_re : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aRe m| ≤ C0 := by
      intro k hk
      have hbound := htail j hj (k + 1)
      have htarget_k :
          Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / j ≤ target := by
        unfold target
        exact div_le_div_of_nonneg_right
          (Real.sqrt_le_sqrt (by
            exact_mod_cast (by omega : (k + 1 + j) + 1 ≤ (N + j) + 1)))
          (by positivity : (0 : ℝ) ≤ j)
      calc
        |∑ m ∈ Finset.range (k + 1), aRe m|
            = |(∑ m ∈ Finset.range (k + 1), baseFn m).re| := by
                simp [aRe]
        _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_re_le_norm _
        _ ≤ Ct * Real.log (↑j + 1) * (Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / j) := by
              simpa [baseFn, J, Nat.add_assoc, add_left_comm, add_comm] using hbound
        _ ≤ Ct * Real.log (↑j + 1) * target := by
              exact mul_le_mul_of_nonneg_left htarget_k
                (mul_nonneg (le_of_lt hCt) (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)))
        _ = C0 := by
              rfl
    have hpartial_im : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aIm m| ≤ C0 := by
      intro k hk
      have hbound := htail j hj (k + 1)
      have htarget_k :
          Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / j ≤ target := by
        unfold target
        exact div_le_div_of_nonneg_right
          (Real.sqrt_le_sqrt (by
            exact_mod_cast (by omega : (k + 1 + j) + 1 ≤ (N + j) + 1)))
          (by positivity : (0 : ℝ) ≤ j)
      calc
        |∑ m ∈ Finset.range (k + 1), aIm m|
            = |(∑ m ∈ Finset.range (k + 1), baseFn m).im| := by
                simp [aIm]
        _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_im_le_norm _
        _ ≤ Ct * Real.log (↑j + 1) * (Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / j) := by
              simpa [baseFn, J, Nat.add_assoc, add_left_comm, add_comm] using hbound
        _ ≤ Ct * Real.log (↑j + 1) * target := by
              exact mul_le_mul_of_nonneg_left htarget_k
                (mul_nonneg (le_of_lt hCt) (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)))
        _ = C0 := by
              rfl
    have hb_nonneg : ∀ k ≤ n0, 0 ≤ b k := by
      intro k hk
      exact atkinsonUpperBoundaryStepCoeff_inv_nonneg (k + J) j hj
    have hb_anti : ∀ k < n0, b (k + 1) ≤ b k := by
      intro k hk
      exact atkinsonUpperBoundaryStepCoeff_inv_antitone j hj (by omega : k + J ≤ k + 1 + J)
    have hb_one : b 0 ≤ 1 := by
      simpa [b, J] using atkinsonUpperBoundaryStepCoeff_inv_le_one J j hj
    have hb0_nonneg : 0 ≤ b 0 := hb_nonneg 0 (by omega)
    have hC0_nonneg : 0 ≤ C0 := by
      unfold C0 target
      apply mul_nonneg
      · exact mul_nonneg (le_of_lt hCt) (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega))
      · positivity
    have hsum_re :
        (∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re
          =
        ∑ k ∈ Finset.range (n0 + 1), aRe k * b k := by
          simp [aRe, b, baseFn, mul_comm, mul_left_comm, mul_assoc]
    have hsum_im :
        (∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im
          =
        ∑ k ∈ Finset.range (n0 + 1), aIm k * b k := by
          simp [aIm, b, baseFn, mul_comm, mul_left_comm, mul_assoc]
    have hre :
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re| ≤ C0 := by
      have habel :=
        AbelSummation.abel_summation_bound aRe b n0 C0 hpartial_re hb_nonneg hb_anti
      have habel' :
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re| ≤ C0 * b 0 := by
        simpa [hsum_re] using habel
      have hmul : C0 * b 0 ≤ C0 := by
        nlinarith [hC0_nonneg, hb0_nonneg, hb_one]
      exact habel'.trans hmul
    have him :
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| ≤ C0 := by
      have habel :=
        AbelSummation.abel_summation_bound aIm b n0 C0 hpartial_im hb_nonneg hb_anti
      have habel' :
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| ≤ C0 * b 0 := by
        simpa [hsum_im] using habel
      have hmul : C0 * b 0 ≤ C0 := by
        nlinarith [hC0_nonneg, hb0_nonneg, hb_one]
      exact habel'.trans hmul
    have hnorm :
        ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖ ≤ 2 * C0 := by
      calc
        ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖
            ≤
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
            +
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| := by
              exact Complex.norm_le_abs_re_add_abs_im _
        _ ≤ C0 + C0 := add_le_add hre him
        _ = 2 * C0 := by ring
    calc
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase
                (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖
        = ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖ := by
              simpa [hn0, b, baseFn, J, Nat.add_assoc, add_left_comm, add_comm]
      _ ≤ 2 * C0 := hnorm
      _ = (2 * Ct) * Real.log (↑j + 1) * target := by
            unfold C0
            ring

/-! Local handoff from the same-shift tail helper:
`atkinsonShiftedInversePhaseCorePrefix_tail_bound_of_hinv` gives the diagonal
row control, and this theorem packages the `stepCoeff - 1` correction row that
the weighted `Ico` transport needs. It is the smallest honest bridge from the
5859 helper block to the next-shift seam. -/
private theorem atkinsonShiftedInversePhaseCorePrefix_stepCoeff_sub_one_bound_of_hinv
    (hinv :
      ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ N : ℕ,
        ‖∑ k ∈ Finset.range N,
            ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) j)‖
          ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)) :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j - 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase
                (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨Ct, hCt, htail⟩ := atkinsonShiftedInversePhaseCorePrefix_tail_bound_of_hinv hinv
  obtain ⟨Cw, hCw, hweighted⟩ :=
    atkinsonShiftedInversePhaseCorePrefix_upper_weighted_bound_of_hinv hinv
  refine ⟨Ct + Cw, by positivity, ?_⟩
  intro j hj N
  let J : ℕ := j + 1
  let baseFn : ℕ → ℂ := fun k =>
    ((((1 / atkinsonShiftedRelativePhase
        (k + (J + j)) j : ℝ) : ℂ)) *
      atkinsonShiftedSingleBoundaryCore (k + J) j)
  have hdecomp :
      ∑ k ∈ Finset.range N,
          ((((atkinsonUpperBoundaryStepCoeff (k + J) j - 1 : ℝ) : ℂ)) * baseFn k)
        =
      (∑ k ∈ Finset.range N, baseFn k)
        -
      ∑ k ∈ Finset.range N,
          ((((atkinsonUpperBoundaryWeightedCoeff (k + J) j : ℝ) : ℂ)) * baseFn k) := by
            calc
              ∑ k ∈ Finset.range N,
                  ((((atkinsonUpperBoundaryStepCoeff (k + J) j - 1 : ℝ) : ℂ)) * baseFn k)
                =
              ∑ k ∈ Finset.range N,
                  (baseFn k - ((((atkinsonUpperBoundaryWeightedCoeff (k + J) j : ℝ) : ℂ)) * baseFn k)) := by
                    refine Finset.sum_congr rfl ?_
                    intro k hk
                    have hcoeff :
                        (((atkinsonUpperBoundaryStepCoeff (k + J) j - 1 : ℝ) : ℂ))
                          =
                        (1 : ℂ)
                          - (((atkinsonUpperBoundaryWeightedCoeff (k + J) j : ℝ) : ℂ)) := by
                            unfold atkinsonUpperBoundaryWeightedCoeff
                            norm_num
                            ring
                    rw [hcoeff]
                    ring
              _ =
              (∑ k ∈ Finset.range N, baseFn k)
                -
              ∑ k ∈ Finset.range N,
                  ((((atkinsonUpperBoundaryWeightedCoeff (k + J) j : ℝ) : ℂ)) * baseFn k) := by
                    rw [Finset.sum_sub_distrib]
  let target : ℝ := Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j
  calc
    ‖∑ k ∈ Finset.range N,
        ((((atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j - 1 : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase
              (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖
      =
    ‖(∑ k ∈ Finset.range N, baseFn k)
        -
      ∑ k ∈ Finset.range N,
          ((((atkinsonUpperBoundaryWeightedCoeff (k + J) j : ℝ) : ℂ)) * baseFn k)‖ := by
            simpa [baseFn, J, Nat.add_assoc, add_left_comm, add_comm] using congrArg norm hdecomp
    _ ≤ ‖∑ k ∈ Finset.range N, baseFn k‖
          + ‖∑ k ∈ Finset.range N,
                ((((atkinsonUpperBoundaryWeightedCoeff (k + J) j : ℝ) : ℂ)) * baseFn k)‖ := by
            exact norm_sub_le _ _
    _ ≤ Ct * Real.log (↑j + 1) * target + Cw * Real.log (↑j + 1) * target := by
          refine add_le_add ?_ ?_
          · simpa [baseFn, target, J, Nat.add_assoc, add_left_comm, add_comm] using htail j hj N
          · simpa [baseFn, target, J, Nat.add_assoc, add_left_comm, add_comm] using
              hweighted j hj N
    _ = (Ct + Cw) * Real.log (↑j + 1) * target := by
          ring

/-! Native `Ico` transport for the weighted row handoff. This is the local
weighted-tail theorem that should sit immediately after the same-shift tail
helper block, with only the compact `stepCoeff - 1` lemma above it. -/
private theorem atkinsonShiftedInversePhaseCorePrefix_stepCoeff_sub_one_Ico_tail_bound_of_hinv
    (hinv :
      ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ N : ℕ,
        ‖∑ k ∈ Finset.range N,
            ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) j)‖
          ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)) :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ N : ℕ,
      ‖∑ n ∈ Finset.Ico (j + 1) (j + 1 + N),
          ((((atkinsonUpperBoundaryStepCoeff n j - 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n j))‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨Cerror, hCerror, herror⟩ :=
    atkinsonShiftedInversePhaseCorePrefix_stepCoeff_sub_one_bound_of_hinv hinv
  refine ⟨Cerror, hCerror, ?_⟩
  intro j hj N
  have hJN : j + 1 + N - (j + 1) = N := by
    omega
  calc
    ‖∑ n ∈ Finset.Ico (j + 1) (j + 1 + N),
        ((((atkinsonUpperBoundaryStepCoeff n j - 1 : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n j))‖
      =
    ‖∑ k ∈ Finset.range N,
        ((((atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j - 1 : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase
              (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖ := by
            let f : ℕ → ℂ := fun n =>
              ((((atkinsonUpperBoundaryStepCoeff n j - 1 : ℝ) : ℂ)) *
                ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                  atkinsonShiftedSingleBoundaryCore n j))
            have hsum :
                ∑ n ∈ Finset.Ico (j + 1) (j + 1 + N), f n
                  =
                ∑ k ∈ Finset.range N, f (k + (j + 1)) := by
                  rw [Finset.sum_Ico_eq_sum_range]
                  rw [hJN]
                  refine Finset.sum_congr rfl ?_
                  intro k hk
                  simp [f, Nat.add_assoc, add_left_comm, add_comm]
            simpa [f, Nat.add_assoc, add_left_comm, add_comm] using congrArg norm hsum
    _ ≤ Cerror * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
          exact herror j hj N

/-- Native `Ico`-coordinate wrapper for the weighted `stepCoeff - 1` tail
bound. This exposes the smaller first-leaf surface directly in terms of the
upper endpoint `U`. -/
private theorem atkinsonShiftedInversePhaseCorePrefix_stepCoeff_sub_one_Ico_tail_bound_native_of_hinv
    (hinv :
      ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ N : ℕ,
        ‖∑ k ∈ Finset.range N,
            ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) j)‖
          ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)) :
    ∃ C_err > 0, ∀ j : ℕ, 1 ≤ j → ∀ U : ℕ, j + 1 ≤ U →
      ‖∑ n ∈ Finset.Ico (j + 1) U,
          ((((atkinsonUpperBoundaryStepCoeff n j - 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n j))‖
        ≤ C_err * Real.log (↑j + 1) * (Real.sqrt ((U : ℝ) + 1) / j) := by
  obtain ⟨C, hC, hbound⟩ :=
    atkinsonShiftedInversePhaseCorePrefix_stepCoeff_sub_one_Ico_tail_bound_of_hinv hinv
  refine ⟨C, hC, ?_⟩
  intro j hj U hU
  set N := U - (j + 1) with hN_def
  have hU_eq : j + 1 + N = U := by
    omega
  have hNj_eq : (N + j : ℕ) + 1 = U := by
    omega
  have hNj_cast : (((N + j : ℕ) : ℝ) + 1) = (U : ℝ) := by
    exact_mod_cast hNj_eq
  calc
    ‖∑ n ∈ Finset.Ico (j + 1) U,
        ((((atkinsonUpperBoundaryStepCoeff n j - 1 : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n j))‖
      = ‖∑ n ∈ Finset.Ico (j + 1) (j + 1 + N),
          ((((atkinsonUpperBoundaryStepCoeff n j - 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n j))‖ := by
            rw [hU_eq]
    _ ≤ C * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := hbound j hj N
    _ = C * Real.log (↑j + 1) * (Real.sqrt (U : ℝ) / j) := by
          rw [hNj_cast]
    _ ≤ C * Real.log (↑j + 1) * (Real.sqrt ((U : ℝ) + 1) / j) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (le_of_lt hC) (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)))
          exact div_le_div_of_nonneg_right
            (Real.sqrt_le_sqrt (by
              linarith [show (0 : ℝ) ≤ (U : ℝ) from Nat.cast_nonneg U]))
            (by positivity : (0 : ℝ) ≤ j)

/-- Current packaged second-leaf surface after the constructive `K, J` /
additive Step 3 / anchored `Ico` ladder.

The remaining analytic content is now exactly the fixed-shift inverse-phase
cell prefix bound, i.e. the row-integral cell itself after repackaging the
correction ladder. -/
class AtkinsonShiftedInversePhaseCellPrefixBoundHyp : Prop where
  bound :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ m : ℕ,
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j)

/-- A stronger no-log inverse-phase cell-prefix estimate can be packaged into the
current public class by paying a universal `1 / log 2` factor. This is the
exact tracked theorem-content leaf sitting below
`AtkinsonShiftedInversePhaseCellPrefixBoundHyp`. -/
theorem atkinson_shiftedInversePhaseCellPrefixBound_of_no_log
    (hshift :
      ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonResonantShiftedPhaseWeightedCell n j)‖
          ≤ C_complete * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j)) :
    AtkinsonShiftedInversePhaseCellPrefixBoundHyp := by
  obtain ⟨C_complete, hC_complete, hshift'⟩ := hshift
  refine ⟨C_complete / Real.log 2, by positivity, ?_⟩
  intro j hj m
  let target : ℝ := Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j
  have htarget_nonneg : 0 ≤ target := by
    dsimp [target]
    positivity
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le : Real.log 2 ≤ Real.log (↑j + 1) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast show 2 ≤ j + 1 by omega)
  calc
    ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
        ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonResonantShiftedPhaseWeightedCell n j)‖
      ≤ C_complete * target := hshift' j hj m
    _ = (C_complete / Real.log 2) * (Real.log 2 * target) := by
          field_simp [show Real.log 2 ≠ 0 by positivity]
    _ ≤ (C_complete / Real.log 2) * (Real.log (↑j + 1) * target) := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · exact mul_le_mul_of_nonneg_right hlog2_le htarget_nonneg
          · exact div_nonneg (le_of_lt hC_complete) (le_of_lt hlog2_pos)
    _ = (C_complete / Real.log 2) * Real.log (↑j + 1) * target := by ring
    _ = (C_complete / Real.log 2) * Real.log (↑j + 1) *
          (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
          rfl

/-- Reduction theorem for the remaining inverse-phase cell-prefix leaf.

To close `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`, it is enough to prove
the stronger no-log estimate uniformly for all sufficiently large shifts `j`,
and then patch the finitely many small shifts with individual constants. -/
private theorem atkinson_shiftedInversePhaseCellPrefix_no_log_of_eventual_and_finite_patch
    {J0 : ℕ}
    (hevent :
      ∃ Cevent > 0, ∀ j : ℕ, J0 ≤ j → 1 ≤ j → ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonResonantShiftedPhaseWeightedCell n j)‖
          ≤ Cevent * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j))
    (hpatch :
      ∀ j : ℕ, 1 ≤ j → j < J0 →
        ∃ Cj > 0, ∀ m : ℕ,
          ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
              ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                atkinsonResonantShiftedPhaseWeightedCell n j)‖
            ≤ Cj * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j)) :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ m : ℕ,
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)‖
        ≤ C_complete * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨Cevent, hCevent_pos, hlarge⟩ := hevent
  let Cpatch : ℕ → ℝ := fun j =>
    if hj : 1 ≤ j ∧ j < J0 then Classical.choose (hpatch j hj.1 hj.2) else 0
  let Csmall : ℝ := Finset.sum (Finset.range J0) Cpatch
  have hCpatch_nonneg : ∀ k : ℕ, 0 ≤ Cpatch k := by
    intro k
    dsimp [Cpatch]
    split_ifs with hcond
    · exact le_of_lt (Classical.choose_spec (hpatch k hcond.1 hcond.2)).1
    · exact le_rfl
  refine ⟨Cevent + Csmall, add_pos_of_pos_of_nonneg hCevent_pos ?_, ?_⟩
  · unfold Csmall
    exact Finset.sum_nonneg (by intro j hj; exact hCpatch_nonneg j)
  · intro j hj m
    by_cases hJ0 : J0 ≤ j
    · calc
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonResonantShiftedPhaseWeightedCell n j)‖
          ≤ Cevent * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := hlarge j hJ0 hj m
        _ ≤ (Cevent + Csmall) * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
              gcongr
              exact le_add_of_nonneg_right (Finset.sum_nonneg (by intro k hk; exact hCpatch_nonneg k))
    · have hj_lt : j < J0 := lt_of_not_ge hJ0
      have hsmallj := hpatch j hj hj_lt
      have hCpatch_eq : Cpatch j = Classical.choose hsmallj := by
        dsimp [Cpatch]
        simp [hj, hj_lt, and_assoc]
      have hCpatch_le : Cpatch j ≤ Csmall := by
        unfold Csmall
        exact Finset.single_le_sum (by
          intro k hk
          exact hCpatch_nonneg k) (Finset.mem_range.mpr hj_lt)
      obtain ⟨hCj_pos, hCj⟩ := Classical.choose_spec hsmallj
      calc
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonResonantShiftedPhaseWeightedCell n j)‖
          ≤ Classical.choose hsmallj * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := hCj m
        _ = Cpatch j * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by rw [hCpatch_eq]
        _ ≤ Csmall * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
              gcongr
        _ ≤ (Cevent + Csmall) * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
              have htarget_nonneg : 0 ≤ Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j := by
                positivity
              nlinarith [htarget_nonneg, hCevent_pos]

private theorem atkinson_shiftedInversePhaseCellPrefixBound_of_eventual_and_finite_patch
    {J0 : ℕ}
    (hevent :
      ∃ Cevent > 0, ∀ j : ℕ, J0 ≤ j → 1 ≤ j → ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonResonantShiftedPhaseWeightedCell n j)‖
          ≤ Cevent * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j))
    (hpatch :
      ∀ j : ℕ, 1 ≤ j → j < J0 →
        ∃ Cj > 0, ∀ m : ℕ,
          ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
              ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                atkinsonResonantShiftedPhaseWeightedCell n j)‖
            ≤ Cj * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j)) :
    AtkinsonShiftedInversePhaseCellPrefixBoundHyp := by
  exact
    atkinson_shiftedInversePhaseCellPrefixBound_of_no_log
      (atkinson_shiftedInversePhaseCellPrefix_no_log_of_eventual_and_finite_patch
        hevent hpatch)

/-- Concrete `J0 = 3` specialization of the remaining inverse-phase cell-prefix
leaf.

Once the large-shift no-log theorem is proved from `j ≥ 3`, only the two native
fixed shifts `j = 1, 2` remain to patch. This keeps the unresolved public leaf
aligned with the existing split-shift architecture used elsewhere in the file. -/
private theorem atkinson_shiftedInversePhaseCellPrefixBound_of_eventual_j3_and_j1_j2
    (hevent :
      ∃ Cevent > 0, ∀ j : ℕ, 3 ≤ j → 1 ≤ j → ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonResonantShiftedPhaseWeightedCell n j)‖
          ≤ Cevent * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j))
    (hj1 :
      ∃ C1 > 0, ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico ((1 : ℕ) - 1) (m + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + (1 : ℕ)) (1 : ℕ) : ℝ) : ℂ)) *
              atkinsonResonantShiftedPhaseWeightedCell n (1 : ℕ))‖
          ≤ C1 * (Real.sqrt (((m + (1 : ℕ) : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)))
    (hj2 :
      ∃ C2 > 0, ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico ((2 : ℕ) - 1) (m + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + (2 : ℕ)) (2 : ℕ) : ℝ) : ℂ)) *
              atkinsonResonantShiftedPhaseWeightedCell n (2 : ℕ))‖
          ≤ C2 * (Real.sqrt (((m + (2 : ℕ) : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ))) :
    AtkinsonShiftedInversePhaseCellPrefixBoundHyp := by
  refine
    atkinson_shiftedInversePhaseCellPrefixBound_of_eventual_and_finite_patch
      (J0 := 3) ?_ ?_
  · obtain ⟨Cevent, hCevent, hlarge⟩ := hevent
    refine ⟨Cevent, hCevent, ?_⟩
    intro j hj_ge hj m
    exact hlarge j hj_ge hj m
  · intro j hj hj_lt
    have hj_cases : j = 1 ∨ j = 2 := by omega
    rcases hj_cases with rfl | rfl
    · simpa using hj1
    · simpa using hj2

/-- Fixed-shift inverse-phase cell prefixes reduce to the corresponding
boundary and correction prefixes.

This is the honest fixed-shift form of the public leaf. For any concrete shift,
once the two exact pieces from
`atkinsonResonantShiftedCell_eq_boundary_minus_correction` are controlled at
the target `sqrt / j` scale, the inverse-phase cell prefix follows
immediately. -/
private theorem atkinson_shiftedInversePhaseCellPrefix_no_log_fixedShift_of_boundary_and_correction
    (j : ℕ) (hj : 1 ≤ j)
    (hbdry :
      ∃ C_bdry > 0, ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            atkinsonResonantShiftedBoundaryTerm n j‖
          ≤ C_bdry * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j))
    (hcorr :
      ∃ C_corr > 0, ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            atkinsonResonantShiftedCorrectionTerm n j‖
          ≤ C_corr * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j)) :
    ∃ C_cell > 0, ∀ m : ℕ,
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)‖
        ≤ C_cell * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_bdry, hC_bdry, hbdry'⟩ := hbdry
  obtain ⟨C_corr, hC_corr, hcorr'⟩ := hcorr
  refine ⟨C_bdry + C_corr, by positivity, ?_⟩
  intro m
  let target : ℝ := Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j
  have hsum :
      ∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)
        =
      (∑ n ∈ Finset.Ico (j - 1) (m + 1),
          atkinsonResonantShiftedBoundaryTerm n j)
        -
      ∑ n ∈ Finset.Ico (j - 1) (m + 1),
        atkinsonResonantShiftedCorrectionTerm n j := by
    calc
      ∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)
        =
      ∑ n ∈ Finset.Ico (j - 1) (m + 1),
        (atkinsonResonantShiftedBoundaryTerm n j
          - atkinsonResonantShiftedCorrectionTerm n j) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            have hphase_pos :
                0 < atkinsonShiftedRelativePhase (n + j) j :=
              atkinsonShiftedRelativePhase_pos (n + j) j hj (by omega)
            have hone :
                (1 / atkinsonShiftedRelativePhase (n + j) j) *
                    atkinsonShiftedRelativePhase (n + j) j
                  = (1 : ℝ) := by
                    field_simp [ne_of_gt hphase_pos]
            calc
              ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                  atkinsonResonantShiftedPhaseWeightedCell n j)
                =
              ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u := by
                    unfold atkinsonResonantShiftedPhaseWeightedCell
                    have hmul :
                        (((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                            (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ))
                          = (1 : ℂ) := by
                            exact_mod_cast hone
                    calc
                      (((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                          ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                            ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u)
                        =
                      ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                          (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ))) *
                        ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u := by
                              rw [mul_assoc]
                      _ = ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u := by
                              rw [hmul, one_mul]
              _ = atkinsonResonantShiftedBoundaryTerm n j
                    - atkinsonResonantShiftedCorrectionTerm n j := by
                    exact atkinsonResonantShiftedCell_eq_boundary_minus_correction n j hj
      _ =
      (∑ n ∈ Finset.Ico (j - 1) (m + 1),
          atkinsonResonantShiftedBoundaryTerm n j)
        -
      ∑ n ∈ Finset.Ico (j - 1) (m + 1),
        atkinsonResonantShiftedCorrectionTerm n j := by
            rw [Finset.sum_sub_distrib]
  rw [hsum]
  calc
    ‖(∑ n ∈ Finset.Ico (j - 1) (m + 1),
          atkinsonResonantShiftedBoundaryTerm n j)
        -
      ∑ n ∈ Finset.Ico (j - 1) (m + 1),
        atkinsonResonantShiftedCorrectionTerm n j‖
      ≤ ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            atkinsonResonantShiftedBoundaryTerm n j‖
          +
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            atkinsonResonantShiftedCorrectionTerm n j‖ := by
            exact norm_sub_le _ _
    _ ≤ C_bdry * target + C_corr * target := by
          exact add_le_add (hbdry' m) (hcorr' m)
    _ = (C_bdry + C_corr) * target := by
          ring

/-- Exact large-`j` reduction for the remaining inverse-phase-cell leaf.

For shifts `j ≥ 3`, the no-log inverse-phase cell-prefix estimate is equivalent
to bounding the two explicit pieces already exposed by the pointwise identity
`cell = boundary - correction`. This keeps the next proof pass on concrete
prefix bounds instead of the packaged class surface. -/
private theorem atkinson_shiftedInversePhaseCellPrefix_no_log_j3_of_boundary_and_correction
    (hbdry :
      ∃ C_bdry > 0, ∀ j : ℕ, 3 ≤ j → ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            atkinsonResonantShiftedBoundaryTerm n j‖
          ≤ C_bdry * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j))
    (hcorr :
      ∃ C_corr > 0, ∀ j : ℕ, 3 ≤ j → ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            atkinsonResonantShiftedCorrectionTerm n j‖
          ≤ C_corr * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j)) :
    ∃ Cevent > 0, ∀ j : ℕ, 3 ≤ j → 1 ≤ j → ∀ m : ℕ,
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)‖
        ≤ Cevent * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_bdry, hC_bdry, hbdry'⟩ := hbdry
  obtain ⟨C_corr, hC_corr, hcorr'⟩ := hcorr
  refine ⟨C_bdry + C_corr, by positivity, ?_⟩
  intro j hj3 hj1 m
  let target : ℝ := Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j
  have hIco_eq :
      ∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)
        =
      (∑ n ∈ Finset.Ico (j - 1) (m + 1),
          atkinsonResonantShiftedBoundaryTerm n j)
        -
      ∑ n ∈ Finset.Ico (j - 1) (m + 1),
          atkinsonResonantShiftedCorrectionTerm n j := by
    calc
      ∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)
        =
      ∑ n ∈ Finset.Ico (j - 1) (m + 1),
          (atkinsonResonantShiftedBoundaryTerm n j
            - atkinsonResonantShiftedCorrectionTerm n j) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              have hphase_pos :
                  0 < atkinsonShiftedRelativePhase (n + j) j :=
                atkinsonShiftedRelativePhase_pos (n + j) j hj1 (by omega)
              have hone :
                  (1 / atkinsonShiftedRelativePhase (n + j) j) *
                      atkinsonShiftedRelativePhase (n + j) j
                    = (1 : ℝ) := by
                      field_simp [ne_of_gt hphase_pos]
              calc
                ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                    atkinsonResonantShiftedPhaseWeightedCell n j)
                  =
                ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u := by
                      unfold atkinsonResonantShiftedPhaseWeightedCell
                      have hmul :
                          (((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                              (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ))
                            = (1 : ℂ) := by
                              exact_mod_cast hone
                      calc
                        (((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                            ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                              ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u)
                          =
                        ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                            (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ))) *
                          ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u := by
                            rw [mul_assoc]
                        _ = ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u := by
                            rw [hmul, one_mul]
                _ = atkinsonResonantShiftedBoundaryTerm n j
                      - atkinsonResonantShiftedCorrectionTerm n j := by
                      exact atkinsonResonantShiftedCell_eq_boundary_minus_correction n j hj1
      _ =
      (∑ n ∈ Finset.Ico (j - 1) (m + 1),
          atkinsonResonantShiftedBoundaryTerm n j)
        -
      ∑ n ∈ Finset.Ico (j - 1) (m + 1),
          atkinsonResonantShiftedCorrectionTerm n j := by
            rw [Finset.sum_sub_distrib]
  rw [hIco_eq]
  calc
    ‖(∑ n ∈ Finset.Ico (j - 1) (m + 1),
          atkinsonResonantShiftedBoundaryTerm n j)
        -
      ∑ n ∈ Finset.Ico (j - 1) (m + 1),
          atkinsonResonantShiftedCorrectionTerm n j‖
      ≤ ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            atkinsonResonantShiftedBoundaryTerm n j‖
          +
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            atkinsonResonantShiftedCorrectionTerm n j‖ := by
            exact norm_sub_le _ _
    _ ≤ C_bdry * target + C_corr * target := by
          exact add_le_add (hbdry' j hj3 m) (hcorr' j hj3 m)
    _ = (C_bdry + C_corr) * target := by
          ring

/-- Exact large-`j` reduction of the remaining public leaf to the genuine row
tail plus the isolated first cell.

This is a more faithful direct decomposition than bounding boundary and
correction separately: the `Ico (j - 1) (m + 1)` cell prefix splits into the
singleton `n = j - 1` head term and the honest row tail `n ≥ j`, whose range
form is exactly what `atkinsonResonantShiftedRowIntegral_eq_inversePhaseCellSum`
controls. -/
private theorem atkinson_shiftedInversePhaseCellPrefix_no_log_j3_of_rowIntegral_and_head
    {J0 : ℕ}
    (hrow :
      ∃ C_row > 0, ∀ j : ℕ, J0 ≤ j → 3 ≤ j → 1 ≤ j → ∀ M : ℕ,
        ‖∫ u in Ioc (0 : ℝ) 1,
            ∑ n ∈ Finset.range M,
              (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0)‖
          ≤ C_row * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j))
    (hhead :
      ∃ C_head > 0, ∀ j : ℕ, J0 ≤ j → 3 ≤ j → 1 ≤ j → ∀ m : ℕ, j - 1 ≤ m →
        ‖((((1 / atkinsonShiftedRelativePhase ((j - 1) + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell (j - 1) j)‖
          ≤ C_head * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j)) :
    ∃ Cevent > 0, ∀ j : ℕ, J0 ≤ j → 3 ≤ j → 1 ≤ j → ∀ m : ℕ,
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)‖
        ≤ Cevent * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_row, hC_row, hrow'⟩ := hrow
  obtain ⟨C_head, hC_head, hhead'⟩ := hhead
  refine ⟨C_head + 4 * C_row, by positivity, ?_⟩
  intro j hJ0 hj3 hj1 m
  let target : ℝ := Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j
  let cellFn : ℕ → ℂ := fun n =>
    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
      atkinsonResonantShiftedPhaseWeightedCell n j)
  by_cases hnonempty : j - 1 ≤ m
  · have hsplit :
        ∑ n ∈ Finset.Ico (j - 1) (m + 1), cellFn n
          =
        cellFn (j - 1) + ∑ n ∈ Finset.Ico j (m + 1), cellFn n := by
      have hset :
          Finset.Ico (j - 1) (m + 1)
            =
          ({j - 1} : Finset ℕ) ∪ Finset.Ico j (m + 1) := by
        ext x
        constructor <;> intro hx
        · rcases Finset.mem_Ico.mp hx with ⟨hx1, hx2⟩
          by_cases hxj : x = j - 1
          · exact Finset.mem_union.mpr <| Or.inl (by simpa [hxj])
          · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_Ico.mpr (by omega)
        · rcases Finset.mem_union.mp hx with hx | hx
          · simp at hx
            subst hx
            exact Finset.mem_Ico.mpr (by omega)
          · rcases Finset.mem_Ico.mp hx with ⟨hx1, hx2⟩
            exact Finset.mem_Ico.mpr (by omega)
      have hdisj :
          Disjoint ({j - 1} : Finset ℕ) (Finset.Ico j (m + 1)) := by
        refine Finset.disjoint_left.mpr ?_
        intro x hx1 hx2
        simp at hx1
        subst hx1
        rcases Finset.mem_Ico.mp hx2 with ⟨hx2l, hx2r⟩
        omega
      rw [hset, Finset.sum_union hdisj, Finset.sum_singleton]
    have htail_eq :
        ∑ n ∈ Finset.Ico j (m + 1), cellFn n
          =
        ∑ n ∈ Finset.range (m + 1),
          (if j ≤ n then cellFn n else 0) := by
      rw [← Finset.sum_filter]
      congr 1
      ext x
      constructor <;> intro hx <;>
        simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx ⊢ <;> omega
    have htail_raw :
        ‖∑ n ∈ Finset.Ico j (m + 1), cellFn n‖
          ≤ C_row * (Real.sqrt (((m + 1 + j : ℕ) : ℝ) + 1) / j) := by
      rw [htail_eq]
      calc
        ‖∑ n ∈ Finset.range (m + 1), (if j ≤ n then cellFn n else 0)‖
            =
          ‖∫ u in Ioc (0 : ℝ) 1,
              ∑ n ∈ Finset.range (m + 1),
                (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0)‖ := by
                  congr 1
                  symm
                  calc
                    ∫ u in Ioc (0 : ℝ) 1,
                        ∑ n ∈ Finset.range (m + 1),
                          (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0)
                      =
                    ∑ n ∈ Finset.range (m + 1),
                      ∫ u in Ioc (0 : ℝ) 1,
                        (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0) := by
                            rw [MeasureTheory.integral_finset_sum]
                            intro n hn
                            by_cases hjn : j ≤ n
                            · simpa [hjn] using
                                (atkinsonResonantShiftedRowSummand_continuous n j).integrableOn_Ioc
                            · simp [hjn]
                    _ =
                    ∑ n ∈ Finset.range (m + 1),
                      (if j ≤ n then cellFn n else 0) := by
                          refine Finset.sum_congr rfl ?_
                          intro n hn
                          by_cases hjn : j ≤ n
                          · simp [hjn, cellFn]
                            have hphase_pos :
                                0 < atkinsonShiftedRelativePhase (n + j) j :=
                              atkinsonShiftedRelativePhase_pos (n + j) j hj1 (by omega)
                            have hone :
                                (1 / atkinsonShiftedRelativePhase (n + j) j) *
                                    atkinsonShiftedRelativePhase (n + j) j
                                  = (1 : ℝ) := by
                                    field_simp [ne_of_gt hphase_pos]
                            have hcell_eq :
                                cellFn n
                                  =
                                ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u := by
                                  unfold cellFn atkinsonResonantShiftedPhaseWeightedCell
                                  have hmul :
                                      (((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                                          (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ))
                                        = (1 : ℂ) := by
                                          exact_mod_cast hone
                                  calc
                                    (((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                                        ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                                          ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u)
                                      =
                                    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                                        (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ))) *
                                      ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u := by
                                        rw [mul_assoc]
                                    _ = ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u := by
                                        rw [hmul, one_mul]
                            simpa [cellFn] using hcell_eq.symm
                          · simp [hjn]
        _ ≤ C_row * (Real.sqrt (((m + 1 + j : ℕ) : ℝ) + 1) / j) := hrow' j hJ0 hj3 hj1 (m + 1)
    have htail :
        ‖∑ n ∈ Finset.Ico j (m + 1), cellFn n‖
          ≤ 4 * C_row * target := by
      have hsqrt_mono :
          Real.sqrt (((m + 1 + j : ℕ) : ℝ) + 1) / j ≤ 4 * target := by
        have hle :
            (((m + 1 + j : ℕ) : ℝ) + 1) ≤ 16 * ((((m + j : ℕ) : ℝ) + 1) : ℝ) := by
          exact_mod_cast (by omega : (m + 1 + j) + 1 ≤ 16 * (m + j + 1))
        calc
          Real.sqrt (((m + 1 + j : ℕ) : ℝ) + 1) / j
              ≤ Real.sqrt (16 * ((((m + j : ℕ) : ℝ) + 1))) / j := by
                  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hle)
                    (by positivity : (0 : ℝ) ≤ j)
          _ = (4 * Real.sqrt ((((m + j : ℕ) : ℝ) + 1))) / j := by
                have hsqrt_eq :
                    Real.sqrt (16 * ((((m + j : ℕ) : ℝ) + 1)))
                      = 4 * Real.sqrt ((((m + j : ℕ) : ℝ) + 1)) := by
                        have hsqrt_mul :
                            Real.sqrt (16 * ((((m + j : ℕ) : ℝ) + 1)))
                              = Real.sqrt (16 : ℝ) * Real.sqrt ((((m + j : ℕ) : ℝ) + 1)) := by
                                simpa using
                                  (Real.sqrt_mul
                                    (by positivity : 0 ≤ (16 : ℝ))
                                    (by positivity : 0 ≤ ((((m + j : ℕ) : ℝ) + 1))))
                        rw [hsqrt_mul]
                        norm_num
                rw [hsqrt_eq]
          _ = 4 * target := by
                unfold target
                ring
      calc
        ‖∑ n ∈ Finset.Ico j (m + 1), cellFn n‖
            ≤ C_row * (Real.sqrt (((m + 1 + j : ℕ) : ℝ) + 1) / j) := htail_raw
        _ ≤ C_row * (4 * target) := by
              exact mul_le_mul_of_nonneg_left hsqrt_mono (le_of_lt hC_row)
        _ = 4 * C_row * target := by ring
    have hhead_term :
        ‖cellFn (j - 1)‖ ≤ C_head * target := by
      simpa [cellFn, target, Nat.add_assoc, add_left_comm, add_comm] using
        hhead' j hJ0 hj3 hj1 m hnonempty
    calc
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1), cellFn n‖
          = ‖cellFn (j - 1) + ∑ n ∈ Finset.Ico j (m + 1), cellFn n‖ := by
              rw [hsplit]
      _ ≤ ‖cellFn (j - 1)‖ + ‖∑ n ∈ Finset.Ico j (m + 1), cellFn n‖ := by
              exact norm_add_le _ _
      _ ≤ C_head * target + 4 * C_row * target := by
              exact add_le_add hhead_term htail
      _ = (C_head + 4 * C_row) * target := by
              ring
  · have hIco_empty : Finset.Ico (j - 1) (m + 1) = ∅ := by
      ext x
      constructor <;> intro hx
      · rcases Finset.mem_Ico.mp hx with ⟨hx1, hx2⟩
        omega
      · simp at hx
    rw [hIco_empty, Finset.sum_empty, norm_zero]
    positivity

private theorem atkinsonResonantShiftedBoundary_recipStepCoeff_weighted_bound_atomic :
    (∃ C_bdry > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)‖
        ≤ C_bdry * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j)) →
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm (k + (j + 1)) j)‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
  intro hbdryRow
  obtain ⟨Cbdry, hCbdry, hbdry⟩ :=
    hbdryRow
  refine ⟨8 * Cbdry / Real.log 2, by positivity, ?_⟩
  intro j hj N
  let J : ℕ := j + 1
  let target : ℝ := Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j
  by_cases hN : N = 0
  · have hnonneg : 0 ≤ (8 * Cbdry / Real.log 2) * Real.log (↑j + 1) * target := by
      apply mul_nonneg
      · exact mul_nonneg (div_nonneg (by positivity) (Real.log_nonneg (by norm_num)))
          (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega))
      · positivity
    simpa [hN, target] using hnonneg
  · obtain ⟨n0, hn0 : N = n0 + 1⟩ := Nat.exists_eq_succ_of_ne_zero hN
    let baseFn : ℕ → ℂ := fun k => atkinsonResonantShiftedBoundaryTerm (k + J) j
    let C0 : ℝ := 2 * Cbdry * (Real.sqrt 2 * target)
    let aRe : ℕ → ℝ := fun k => (baseFn k).re
    let aIm : ℕ → ℝ := fun k => (baseFn k).im
    let b : ℕ → ℝ := fun k => 1 / atkinsonUpperBoundaryStepCoeff (k + J) j
    have hpartial : ∀ k ≤ n0, ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ ≤ C0 := by
      intro k hk
      have hIcoRange :
          ∑ n ∈ Finset.Ico J (J + (k + 1)), atkinsonResonantShiftedBoundaryTerm n j
            =
          ∑ m ∈ Finset.range (k + 1), baseFn m := by
        have htmp :=
          (Finset.sum_Ico_eq_sum_range
            (f := fun n => atkinsonResonantShiftedBoundaryTerm n j)
            (m := J) (n := J + (k + 1)))
        rw [show J + (k + 1) - J = k + 1 by omega] at htmp
        simpa [baseFn, J, Nat.add_assoc, add_left_comm, add_comm] using htmp
      have hIcoSubIf :
          ∑ n ∈ Finset.Ico J (J + (k + 1)),
              (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)
            =
          (∑ n ∈ Finset.range (J + (k + 1)),
              (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0))
            -
          ∑ n ∈ Finset.range J,
              (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0) := by
        simpa [Nat.add_assoc, add_left_comm, add_comm] using
          (Finset.sum_Ico_eq_sub
            (f := fun n => if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)
            (Nat.le_add_right J (k + 1)))
      have hIcoSub :
          ∑ n ∈ Finset.Ico J (J + (k + 1)), atkinsonResonantShiftedBoundaryTerm n j
            =
          (∑ n ∈ Finset.range (J + (k + 1)),
              (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0))
            -
          ∑ n ∈ Finset.range J,
              (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0) := by
        calc
          ∑ n ∈ Finset.Ico J (J + (k + 1)), atkinsonResonantShiftedBoundaryTerm n j
              =
            ∑ n ∈ Finset.Ico J (J + (k + 1)),
              (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0) := by
                refine Finset.sum_congr rfl ?_
                intro n hn
                have hnJ : J ≤ n := (Finset.mem_Ico.mp hn).1
                have hjn : j ≤ n := by
                  dsimp [J] at hnJ
                  omega
                simp [hjn]
          _ =
            (∑ n ∈ Finset.range (J + (k + 1)),
                (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0))
              -
            ∑ n ∈ Finset.range J,
                (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0) := hIcoSubIf
      have hsum :
          ∑ m ∈ Finset.range (k + 1), baseFn m
            =
          (∑ n ∈ Finset.range (J + k + 1),
              (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0))
            -
          ∑ n ∈ Finset.range J,
              (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0) := by
        calc
          ∑ m ∈ Finset.range (k + 1), baseFn m
              =
            ∑ n ∈ Finset.Ico J (J + k + 1), atkinsonResonantShiftedBoundaryTerm n j := by
                simpa [Nat.add_assoc] using hIcoRange.symm
          _ =
            (∑ n ∈ Finset.range (J + k + 1),
                (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0))
              -
            ∑ n ∈ Finset.range J,
                (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0) := by
                simpa [Nat.add_assoc] using hIcoSub
      have hbig1 :
          ‖∑ n ∈ Finset.range (J + k + 1),
              (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)‖
            ≤ Cbdry * (Real.sqrt (((J + k + 1 + j : ℕ) : ℝ) + 1) / j) := by
        simpa [J, Nat.add_assoc, add_left_comm, add_comm] using
          hbdry j hj (J + k + 1)
      have hbig0 :
          ‖∑ n ∈ Finset.range J,
              (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)‖
            ≤ Cbdry * (Real.sqrt (((J + j : ℕ) : ℝ) + 1) / j) := by
        simpa [J, Nat.add_assoc, add_left_comm, add_comm] using hbdry j hj J
      have htarget1 :
          Real.sqrt (((J + k + 1 + j : ℕ) : ℝ) + 1) / j ≤ Real.sqrt 2 * target := by
        have hle_nat : J + k + 1 + j + 1 ≤ 2 * (N + j + 1) := by
          dsimp [J]
          omega
        have hle :
            (((J + k + 1 + j : ℕ) : ℝ) + 1) ≤ 2 * ((((N + j : ℕ) : ℝ) + 1) : ℝ) := by
          exact_mod_cast hle_nat
        calc
          Real.sqrt (((J + k + 1 + j : ℕ) : ℝ) + 1) / j
              ≤ Real.sqrt (2 * ((((N + j : ℕ) : ℝ) + 1))) / j := by
                  exact div_le_div_of_nonneg_right
                    (Real.sqrt_le_sqrt hle)
                    (by positivity : (0 : ℝ) ≤ j)
          _ = (Real.sqrt 2 * Real.sqrt ((((N + j : ℕ) : ℝ) + 1))) / j := by
                have hsqrt_eq :
                    Real.sqrt (2 * ((((N + j : ℕ) : ℝ) + 1)))
                      = Real.sqrt 2 * Real.sqrt ((((N + j : ℕ) : ℝ) + 1)) := by
                      simpa using
                        (Real.sqrt_mul
                          (by positivity : 0 ≤ (2 : ℝ))
                          (by positivity : 0 ≤ ((((N + j : ℕ) : ℝ) + 1))))
                rw [hsqrt_eq]
          _ = Real.sqrt 2 * target := by
                unfold target
                ring
      have htarget0 :
          Real.sqrt (((J + j : ℕ) : ℝ) + 1) / j ≤ Real.sqrt 2 * target := by
        have hle_nat : J + j + 1 ≤ 2 * (N + j + 1) := by
          dsimp [J]
          omega
        have hle :
            (((J + j : ℕ) : ℝ) + 1) ≤ 2 * ((((N + j : ℕ) : ℝ) + 1) : ℝ) := by
          exact_mod_cast hle_nat
        calc
          Real.sqrt (((J + j : ℕ) : ℝ) + 1) / j
              ≤ Real.sqrt (2 * ((((N + j : ℕ) : ℝ) + 1))) / j := by
                  exact div_le_div_of_nonneg_right
                    (Real.sqrt_le_sqrt hle)
                    (by positivity : (0 : ℝ) ≤ j)
          _ = (Real.sqrt 2 * Real.sqrt ((((N + j : ℕ) : ℝ) + 1))) / j := by
                have hsqrt_eq :
                    Real.sqrt (2 * ((((N + j : ℕ) : ℝ) + 1)))
                      = Real.sqrt 2 * Real.sqrt ((((N + j : ℕ) : ℝ) + 1)) := by
                      simpa using
                        (Real.sqrt_mul
                          (by positivity : 0 ≤ (2 : ℝ))
                          (by positivity : 0 ≤ ((((N + j : ℕ) : ℝ) + 1))))
                rw [hsqrt_eq]
          _ = Real.sqrt 2 * target := by
                unfold target
                ring
      calc
        ‖∑ m ∈ Finset.range (k + 1), baseFn m‖
            ≤
          ‖∑ n ∈ Finset.range (J + k + 1),
              (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)‖
            +
          ‖∑ n ∈ Finset.range J,
              (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)‖ := by
              rw [hsum]
              exact norm_sub_le _ _
        _ ≤ Cbdry * (Real.sqrt (((J + k + 1 + j : ℕ) : ℝ) + 1) / j)
              + Cbdry * (Real.sqrt (((J + j : ℕ) : ℝ) + 1) / j) := by
              exact add_le_add hbig1 hbig0
        _ ≤ Cbdry * (Real.sqrt 2 * target) + Cbdry * (Real.sqrt 2 * target) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left htarget1 (le_of_lt hCbdry))
                (mul_le_mul_of_nonneg_left htarget0 (le_of_lt hCbdry))
        _ = C0 := by
              unfold C0
              ring
    have hpartial_re : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aRe m| ≤ C0 := by
      intro k hk
      calc
        |∑ m ∈ Finset.range (k + 1), aRe m|
            = |(∑ m ∈ Finset.range (k + 1), baseFn m).re| := by
                simp [aRe]
        _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_re_le_norm _
        _ ≤ C0 := hpartial k hk
    have hpartial_im : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aIm m| ≤ C0 := by
      intro k hk
      calc
        |∑ m ∈ Finset.range (k + 1), aIm m|
            = |(∑ m ∈ Finset.range (k + 1), baseFn m).im| := by
                simp [aIm]
        _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_im_le_norm _
        _ ≤ C0 := hpartial k hk
    have hb_nonneg : ∀ k ≤ n0, 0 ≤ b k := by
      intro k hk
      exact atkinsonUpperBoundaryStepCoeff_inv_nonneg (k + J) j hj
    have hb_anti : ∀ k < n0, b (k + 1) ≤ b k := by
      intro k hk
      exact atkinsonUpperBoundaryStepCoeff_inv_antitone j hj (by omega : k + J ≤ k + 1 + J)
    have hb_one : b 0 ≤ 1 := by
      simpa [b, J] using atkinsonUpperBoundaryStepCoeff_inv_le_one J j hj
    have hb0_nonneg : 0 ≤ b 0 := hb_nonneg 0 (by omega)
    have hC0_nonneg : 0 ≤ C0 := by
      unfold C0 target
      positivity
    have hsum_re :
        (∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re
          =
        ∑ k ∈ Finset.range (n0 + 1), aRe k * b k := by
          simp [aRe, b, baseFn, mul_comm, mul_left_comm, mul_assoc]
    have hsum_im :
        (∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im
          =
        ∑ k ∈ Finset.range (n0 + 1), aIm k * b k := by
          simp [aIm, b, baseFn, mul_comm, mul_left_comm, mul_assoc]
    have hre :
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re| ≤ C0 := by
      have habel :=
        AbelSummation.abel_summation_bound aRe b n0 C0 hpartial_re hb_nonneg hb_anti
      have habel' :
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re| ≤ C0 * b 0 := by
        simpa [hsum_re] using habel
      have hmul : C0 * b 0 ≤ C0 := by
        nlinarith [hC0_nonneg, hb0_nonneg, hb_one]
      exact habel'.trans hmul
    have him :
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| ≤ C0 := by
      have habel :=
        AbelSummation.abel_summation_bound aIm b n0 C0 hpartial_im hb_nonneg hb_anti
      have habel' :
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| ≤ C0 * b 0 := by
        simpa [hsum_im] using habel
      have hmul : C0 * b 0 ≤ C0 := by
        nlinarith [hC0_nonneg, hb0_nonneg, hb_one]
      exact habel'.trans hmul
    have hnorm :
        ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖ ≤ 2 * C0 := by
      calc
        ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖
            ≤
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
            +
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| := by
              exact Complex.norm_le_abs_re_add_abs_im _
        _ ≤ C0 + C0 := add_le_add hre him
        _ = 2 * C0 := by ring
    have hsqrt2_le2 : Real.sqrt 2 ≤ (2 : ℝ) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
    calc
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm (k + (j + 1)) j)‖
        = ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖ := by
            simpa [hn0, b, baseFn, J, Nat.add_assoc, add_left_comm, add_comm]
      _ ≤ 2 * C0 := hnorm
      _ = 4 * Real.sqrt 2 * Cbdry * target := by
            unfold C0
            ring
      _ ≤ 8 * Cbdry * target := by
            gcongr
            nlinarith [hsqrt2_le2]
      _ ≤ (8 * Cbdry / Real.log 2) * Real.log (↑j + 1) * target := by
            have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
            have hlog_ge : Real.log 2 ≤ Real.log (↑j + 1) :=
              Real.log_le_log (by norm_num) (by exact_mod_cast show 2 ≤ j + 1 by omega)
            have htarget_nn : 0 ≤ target := by positivity
            calc 8 * Cbdry * target
                = 8 * Cbdry / Real.log 2 * Real.log 2 * target := by
                    field_simp [hlog2_pos.ne']
              _ ≤ 8 * Cbdry / Real.log 2 * Real.log (↑j + 1) * target := by
                    gcongr
              _ = (8 * Cbdry / Real.log 2) * Real.log (↑j + 1) * target := by ring

/-- Current packaged first-leaf surface for the large-mode lower-boundary row bound.
The intended next reduction is the smaller weighted error-row theorem, but the helper
chain in this file is presently organized around this shifted inverse-phase-core prefix
package. -/
class AtkinsonShiftedInversePhaseCorePrefixBoundHyp : Prop where
  bound :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) j)‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)

variable [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]

/-- Smaller weighted first-leaf surface in native `Ico` coordinates. This is
the honest detached weighted error-row theorem extracted from the stronger raw
inverse-phase-core prefix package. -/
theorem atkinson_upperBoundaryStepCoeffSubOne_weighted_shiftedInversePhaseCoreTail_bound_atomic :
    ∃ C_err > 0, ∀ j : ℕ, 1 ≤ j → ∀ U : ℕ, j + 1 ≤ U →
      ‖∑ n ∈ Finset.Ico (j + 1) U,
          ((((atkinsonUpperBoundaryStepCoeff n j - 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n j))‖
        ≤ C_err * Real.log (↑j + 1) * (Real.sqrt ((U : ℝ) + 1) / j) :=
  atkinsonShiftedInversePhaseCorePrefix_stepCoeff_sub_one_Ico_tail_bound_native_of_hinv
    AtkinsonShiftedInversePhaseCorePrefixBoundHyp.bound

/-- Thin wrapper around the native weighted `Ico` tail bound. The current
stronger first-leaf package implies this smaller boundary immediately. -/
class AtkinsonWeightedIcoTailBoundHyp : Prop where
  bound :
    ∃ C_err > 0, ∀ j : ℕ, 1 ≤ j → ∀ U : ℕ, j + 1 ≤ U →
      ‖∑ n ∈ Finset.Ico (j + 1) U,
          ((((atkinsonUpperBoundaryStepCoeff n j - 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n j))‖
        ≤ C_err * Real.log (↑j + 1) * (Real.sqrt ((U : ℝ) + 1) / j)

instance : AtkinsonWeightedIcoTailBoundHyp :=
  ⟨atkinson_upperBoundaryStepCoeffSubOne_weighted_shiftedInversePhaseCoreTail_bound_atomic⟩

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
private theorem atkinson_weightedIcoTail_succ_shift_bound
    [AtkinsonWeightedIcoTailBoundHyp] :
    ∃ C_err > 0, ∀ j : ℕ, 1 ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j - 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase
                (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖
        ≤ C_err * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C, hC, hbound⟩ := AtkinsonWeightedIcoTailBoundHyp.bound
  refine ⟨Real.sqrt 2 * C, by positivity, ?_⟩
  intro j hj N
  let U : ℕ := j + 1 + N
  let target : ℝ := Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j
  have hU : j + 1 ≤ U := by
    dsimp [U]
    omega
  have hsum :
      ∑ n ∈ Finset.Ico (j + 1) U,
          ((((atkinsonUpperBoundaryStepCoeff n j - 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n j))
        =
      ∑ k ∈ Finset.range N,
          ((((atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j - 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase
                (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hUN : U - (j + 1) = N := by
      dsimp [U]
      omega
    rw [hUN]
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [U, Nat.add_assoc, add_left_comm, add_comm]
  have htarget :
      Real.sqrt ((U : ℝ) + 1) / j ≤ Real.sqrt 2 * target := by
    have hle_nat : U + 1 ≤ 2 * (N + j + 1) := by
      dsimp [U]
      omega
    have hle :
        ((U : ℝ) + 1) ≤ 2 * ((((N + j : ℕ) : ℝ) + 1) : ℝ) := by
      exact_mod_cast hle_nat
    calc
      Real.sqrt ((U : ℝ) + 1) / j
          ≤ Real.sqrt (2 * ((((N + j : ℕ) : ℝ) + 1))) / j := by
              exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hle)
                (by positivity : (0 : ℝ) ≤ j)
      _ = (Real.sqrt 2 * Real.sqrt ((((N + j : ℕ) : ℝ) + 1))) / j := by
            have hsqrt_eq :
                Real.sqrt (2 * ((((N + j : ℕ) : ℝ) + 1)))
                  = Real.sqrt 2 * Real.sqrt ((((N + j : ℕ) : ℝ) + 1)) := by
                    simpa using
                      (Real.sqrt_mul
                        (by positivity : 0 ≤ (2 : ℝ))
                        (by positivity : 0 ≤ ((((N + j : ℕ) : ℝ) + 1))))
            rw [hsqrt_eq]
      _ = Real.sqrt 2 * target := by
            unfold target
            ring
  calc
    ‖∑ k ∈ Finset.range N,
        ((((atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j - 1 : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase
              (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖
      =
    ‖∑ n ∈ Finset.Ico (j + 1) U,
        ((((atkinsonUpperBoundaryStepCoeff n j - 1 : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n j))‖ := by
            rw [hsum]
    _ ≤ C * Real.log (↑j + 1) * (Real.sqrt ((U : ℝ) + 1) / j) := by
          exact hbound j hj U hU
    _ ≤ C * Real.log (↑j + 1) * (Real.sqrt 2 * target) := by
          exact mul_le_mul_of_nonneg_left htarget
            (mul_nonneg (le_of_lt hC) (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)))
    _ = (Real.sqrt 2 * C) * Real.log (↑j + 1) * target := by
          ring

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
private theorem atkinson_weightedIcoTail_reindexed_tail_bound
    [AtkinsonWeightedIcoTailBoundHyp] :
    ∃ C_err > 0, ∀ j : ℕ, 1 ≤ j → ∀ r : ℕ, 1 ≤ r → r + 1 ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((atkinsonUpperBoundaryStepCoeff (k + j) r - 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase (k + (j + r)) r : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) r))‖
        ≤ C_err * Real.log (↑r + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / r) := by
  obtain ⟨C, hC, hbound⟩ := atkinson_weightedIcoTail_succ_shift_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro j hj r hr hrj N
  let O : ℕ := j - (r + 1)
  let baseFn : ℕ → ℂ := fun m =>
    ((((atkinsonUpperBoundaryStepCoeff (m + (r + 1)) r - 1 : ℝ) : ℂ)) *
      ((((1 / atkinsonShiftedRelativePhase
          (m + ((r + 1) + r)) r : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore (m + (r + 1)) r))
  let target : ℝ := Real.sqrt (((N + j : ℕ) : ℝ) + 1) / r
  have hj_eq : j = O + (r + 1) := by
    dsimp [O]
    omega
  have hsum :
      ∑ k ∈ Finset.range N,
          ((((atkinsonUpperBoundaryStepCoeff (k + j) r - 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase (k + (j + r)) r : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) r))
        =
      ∑ m ∈ Finset.Ico O (O + N), baseFn m := by
    rw [hj_eq]
    rw [Finset.sum_Ico_eq_sum_range]
    have hON : O + N - O = N := by
      dsimp [O]
      omega
    rw [hON]
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [baseFn, O, Nat.add_assoc, add_left_comm, add_comm]
  have hsplit :
      ∑ m ∈ Finset.Ico O (O + N), baseFn m
        =
      (∑ m ∈ Finset.range (O + N), baseFn m) - ∑ m ∈ Finset.range O, baseFn m := by
          rw [Finset.sum_Ico_eq_sub _ (Nat.le_add_right O N)]
  have hlog_r_nonneg : 0 ≤ Real.log (↑r + 1) :=
    Real.log_nonneg (by exact_mod_cast show 1 ≤ r + 1 by omega)
  have hmain :
      ‖∑ m ∈ Finset.range (O + N), baseFn m‖ ≤ C * Real.log (↑r + 1) * target := by
    have hraw := hbound r hr (O + N)
    calc
      ‖∑ m ∈ Finset.range (O + N), baseFn m‖
          ≤ C * Real.log (↑r + 1) * (Real.sqrt (((O + N + r : ℕ) : ℝ) + 1) / r) := by
              simpa [baseFn, Nat.add_assoc, add_left_comm, add_comm] using hraw
      _ = C * Real.log (↑r + 1) * (Real.sqrt ((N + j : ℕ) : ℝ) / r) := by
            have hOj : (O + N + r : ℕ) + 1 = N + j := by
              dsimp [O]
              omega
            have hOj' : (((O + N + r : ℕ) : ℝ) + 1) = ((N + j : ℕ) : ℝ) := by
              exact_mod_cast hOj
            rw [hOj']
      _ ≤ C * Real.log (↑r + 1) * target := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg (le_of_lt hC) hlog_r_nonneg)
            exact div_le_div_of_nonneg_right
              (Real.sqrt_le_sqrt (by linarith))
              (by positivity : (0 : ℝ) ≤ r)
  have hhead :
      ‖∑ m ∈ Finset.range O, baseFn m‖ ≤ C * Real.log (↑r + 1) * target := by
    have hraw := hbound r hr O
    have hOj_le : ((O + r : ℕ) : ℝ) + 1 ≤ (((N + j : ℕ) : ℝ) + 1) := by
      have hnat : O + r + 1 ≤ N + j + 1 := by
        dsimp [O]
        omega
      exact_mod_cast hnat
    calc
      ‖∑ m ∈ Finset.range O, baseFn m‖
          ≤ C * Real.log (↑r + 1) * (Real.sqrt (((O + r : ℕ) : ℝ) + 1) / r) := by
              simpa [baseFn, Nat.add_assoc, add_left_comm, add_comm] using hraw
      _ ≤ C * Real.log (↑r + 1) * target := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg (le_of_lt hC) hlog_r_nonneg)
            exact div_le_div_of_nonneg_right
              (Real.sqrt_le_sqrt hOj_le)
              (by positivity : (0 : ℝ) ≤ r)
  calc
    ‖∑ k ∈ Finset.range N,
        ((((atkinsonUpperBoundaryStepCoeff (k + j) r - 1 : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase (k + (j + r)) r : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) r))‖
      = ‖∑ m ∈ Finset.Ico O (O + N), baseFn m‖ := by
          rw [hsum]
    _ = ‖(∑ m ∈ Finset.range (O + N), baseFn m) - ∑ m ∈ Finset.range O, baseFn m‖ := by
          rw [hsplit]
    _ ≤ ‖∑ m ∈ Finset.range (O + N), baseFn m‖ + ‖∑ m ∈ Finset.range O, baseFn m‖ := by
          exact norm_sub_le _ _
    _ ≤ C * Real.log (↑r + 1) * target + C * Real.log (↑r + 1) * target := by
          exact add_le_add hmain hhead
    _ = (2 * C) * Real.log (↑r + 1) * target := by
          ring

/-- Current packaged first-lane bridge after the weighted `Ico` tail
reindexing: an Abel-in-`k` bound for the kernel-weighted shifted error rows at
shift `r + 1`.

This is the one-shift-lower surface extracted from the older prefix package.
The exact transported remainder from
`atkinsonShiftedInversePhaseCorePrefix_eq_shiftBoundaryAbelDecomposition`
actually lands one shift higher, on the `r + 2` inverse-phase core with the
same `stepCoeff (r + 1) - 1` factor.  The earlier attempt to package that
auxiliary next-shift surface as a separate class was removed because it mixed
`kernel(r + 1)` with `core(r + 2)` and then incorrectly fed the second term into
a shift-`r + 1` core bound.  The live bridge below stays on the honest
successor identity instead. -/
class AtkinsonKernelWeightedIcoTailAbelBoundHyp : Prop where
  bound :
    ∃ C_err > 0, ∀ j : ℕ, 1 ≤ j → ∀ r : ℕ, 1 ≤ r → r + 2 ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
            ((((atkinsonUpperBoundaryStepCoeff (k + j) (r + 1) - 1 : ℝ) : ℂ)) *
              ((((1 / atkinsonShiftedRelativePhase (k + (j + (r + 1))) (r + 1) : ℝ) : ℂ)) *
                atkinsonShiftedSingleBoundaryCore (k + j) (r + 1))))‖
        ≤ C_err * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)

/-- Honest transported first-lane remainder surface exposed by the exact
Abel decomposition. After rewriting the backward tails by
`atkinsonResonantShiftedBoundary_backwardTail_eq_inversePhaseCoreGap`, the
weighted remainder sits on the next shift `r + 2` and includes the `r = 0`
row. This is the actual theorem-first boundary below the current compatibility
package `AtkinsonKernelWeightedIcoTailAbelBoundHyp`. -/
private theorem atkinson_shiftedInversePhaseCore_reindexed_tail_bound
    [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] :
    ∃ C > 0, ∀ j : ℕ, 1 ≤ j → ∀ s : ℕ, 1 ≤ s → s ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + s)) s : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) s)‖
        ≤ C * Real.log (↑s + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / s) := by
  obtain ⟨C, hC, hbound⟩ := AtkinsonShiftedInversePhaseCorePrefixBoundHyp.bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro j hj s hs hsj N
  let O : ℕ := j - s
  let baseFn : ℕ → ℂ := fun m =>
    ((((1 / atkinsonShiftedRelativePhase (m + (s + s)) s : ℝ) : ℂ)) *
      atkinsonShiftedSingleBoundaryCore (m + s) s)
  let target : ℝ := Real.sqrt (((N + j : ℕ) : ℝ) + 1) / s
  have hj_eq : j = O + s := by
    dsimp [O]
    omega
  have hsum :
      ∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + s)) s : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) s)
        =
      ∑ m ∈ Finset.Ico O (O + N), baseFn m := by
    rw [hj_eq]
    rw [Finset.sum_Ico_eq_sum_range]
    have hON : O + N - O = N := by
      dsimp [O]
      omega
    rw [hON]
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [baseFn, O, Nat.add_assoc, add_left_comm, add_comm]
  have hsplit :
      ∑ m ∈ Finset.Ico O (O + N), baseFn m
        =
      (∑ m ∈ Finset.range (O + N), baseFn m) - ∑ m ∈ Finset.range O, baseFn m := by
          rw [Finset.sum_Ico_eq_sub _ (Nat.le_add_right O N)]
  have hlog_s_nonneg : 0 ≤ Real.log (↑s + 1) :=
    Real.log_nonneg (by exact_mod_cast show 1 ≤ s + 1 by omega)
  have hmain :
      ‖∑ m ∈ Finset.range (O + N), baseFn m‖ ≤ C * Real.log (↑s + 1) * target := by
    have hraw := hbound s hs (O + N)
    calc
      ‖∑ m ∈ Finset.range (O + N), baseFn m‖
          ≤ C * Real.log (↑s + 1) * (Real.sqrt (((O + N + s : ℕ) : ℝ) + 1) / s) := by
              simpa [baseFn, Nat.add_assoc, add_left_comm, add_comm] using hraw
      _ = C * Real.log (↑s + 1) * target := by
            have hOj : O + N + s = N + j := by dsimp [O]; omega
            show C * Real.log (↑s + 1) * (Real.sqrt (((O + N + s : ℕ) : ℝ) + 1) / ↑s) =
                 C * Real.log (↑s + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / ↑s)
            rw [show (O + N + s : ℕ) = (N + j : ℕ) from hOj]
  have hhead :
      ‖∑ m ∈ Finset.range O, baseFn m‖ ≤ C * Real.log (↑s + 1) * target := by
    have hraw := hbound s hs O
    have hOj_le : ((O + s : ℕ) : ℝ) + 1 ≤ (((N + j : ℕ) : ℝ) + 1) := by
      have hnat : O + s + 1 ≤ N + j + 1 := by
        dsimp [O]
        omega
      exact_mod_cast hnat
    calc
      ‖∑ m ∈ Finset.range O, baseFn m‖
          ≤ C * Real.log (↑s + 1) * (Real.sqrt (((O + s : ℕ) : ℝ) + 1) / s) := by
              simpa [baseFn, Nat.add_assoc, add_left_comm, add_comm] using hraw
      _ ≤ C * Real.log (↑s + 1) * target := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg (le_of_lt hC) hlog_s_nonneg)
            exact div_le_div_of_nonneg_right
              (Real.sqrt_le_sqrt hOj_le)
              (by positivity : (0 : ℝ) ≤ s)
  calc
    ‖∑ k ∈ Finset.range N,
        ((((1 / atkinsonShiftedRelativePhase (k + (j + s)) s : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + j) s)‖
      = ‖∑ m ∈ Finset.Ico O (O + N), baseFn m‖ := by
          rw [hsum]
    _ = ‖(∑ m ∈ Finset.range (O + N), baseFn m) - ∑ m ∈ Finset.range O, baseFn m‖ := by
          rw [hsplit]
    _ ≤ ‖∑ m ∈ Finset.range (O + N), baseFn m‖ + ‖∑ m ∈ Finset.range O, baseFn m‖ := by
          exact norm_sub_le _ _
    _ ≤ C * Real.log (↑s + 1) * target + C * Real.log (↑s + 1) * target := by
          exact add_le_add hmain hhead
    _ = (2 * C) * Real.log (↑s + 1) * target := by
          ring

private theorem atkinson_kernelWeightedShiftedInversePhaseCore_abel_bound_atomic
    [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] :
    ∃ C_err > 0, ∀ j : ℕ, 1 ≤ j → ∀ s : ℕ, 1 ≤ s → s ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((atkinsonLowerBoundaryShiftKernel (k + j) j s : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase (k + (j + s)) s : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) s))‖
        ≤ C_err * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C, hC, hshifted⟩ := atkinson_shiftedInversePhaseCore_reindexed_tail_bound
  refine ⟨4 * C, by positivity, ?_⟩
  intro j hj s hs hsj N
  by_cases hN : N = 0
  · have hnonneg :
        0 ≤ (4 * C) * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
      apply mul_nonneg
      · exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega))
      · positivity
    simpa [hN] using hnonneg
  · obtain ⟨n0, hn0 : N = n0 + 1⟩ := Nat.exists_eq_succ_of_ne_zero hN
    let baseFn : ℕ → ℂ := fun k =>
      ((((1 / atkinsonShiftedRelativePhase (k + (j + s)) s : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore (k + j) s)
    let C0 : ℝ := C * Real.log (↑s + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / s)
    let aRe : ℕ → ℝ := fun k => (baseFn k).re
    let aIm : ℕ → ℝ := fun k => (baseFn k).im
    let b : ℕ → ℝ := fun k => atkinsonLowerBoundaryShiftKernel (k + j) j s
    have hlog_s_nonneg : 0 ≤ Real.log (↑s + 1) :=
      Real.log_nonneg (by exact_mod_cast show 1 ≤ s + 1 by omega)
    have hpartial_re : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aRe m| ≤ C0 := by
      intro k hk
      have hbound := hshifted j hj s hs hsj (k + 1)
      have htarget_k :
          Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / s
            ≤ Real.sqrt (((N + j : ℕ) : ℝ) + 1) / s := by
        exact div_le_div_of_nonneg_right
          (Real.sqrt_le_sqrt (by
            exact_mod_cast (by omega : (k + 1 + j) + 1 ≤ (N + j) + 1)))
          (by positivity : (0 : ℝ) ≤ s)
      calc
        |∑ m ∈ Finset.range (k + 1), aRe m|
            = |(∑ m ∈ Finset.range (k + 1), baseFn m).re| := by
                simp [aRe]
        _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_re_le_norm _
        _ ≤ C * Real.log (↑s + 1) * (Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / s) := by
              simpa [baseFn, Nat.add_assoc, add_left_comm, add_comm] using hbound
        _ ≤ C * Real.log (↑s + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / s) := by
              exact mul_le_mul_of_nonneg_left htarget_k
                (mul_nonneg (le_of_lt hC) hlog_s_nonneg)
        _ = C0 := by
              rfl
    have hpartial_im : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aIm m| ≤ C0 := by
      intro k hk
      have hbound := hshifted j hj s hs hsj (k + 1)
      have htarget_k :
          Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / s
            ≤ Real.sqrt (((N + j : ℕ) : ℝ) + 1) / s := by
        exact div_le_div_of_nonneg_right
          (Real.sqrt_le_sqrt (by
            exact_mod_cast (by omega : (k + 1 + j) + 1 ≤ (N + j) + 1)))
          (by positivity : (0 : ℝ) ≤ s)
      calc
        |∑ m ∈ Finset.range (k + 1), aIm m|
            = |(∑ m ∈ Finset.range (k + 1), baseFn m).im| := by
                simp [aIm]
        _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_im_le_norm _
        _ ≤ C * Real.log (↑s + 1) * (Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / s) := by
              simpa [baseFn, Nat.add_assoc, add_left_comm, add_comm] using hbound
        _ ≤ C * Real.log (↑s + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / s) := by
              exact mul_le_mul_of_nonneg_left htarget_k
                (mul_nonneg (le_of_lt hC) hlog_s_nonneg)
        _ = C0 := by
              rfl
    have hb_nonneg : ∀ k ≤ n0, 0 ≤ b k := by
      intro k hk
      simpa [b, Nat.add_assoc, add_left_comm, add_comm] using
        atkinsonLowerBoundaryShiftKernel_nonneg (k + j) j s hs hsj
    have hb_anti : ∀ k < n0, b (k + 1) ≤ b k := by
      intro k hk
      simpa [b, Nat.add_assoc, add_left_comm, add_comm] using
        (atkinsonLowerBoundaryShiftKernel_antitone j s hs hsj
          (by omega : k + j ≤ k + 1 + j))
    have hb_head : b 0 ≤ 2 * s / j := by
      simpa [b, Nat.add_assoc, add_left_comm, add_comm] using
        atkinsonLowerBoundaryShiftKernel_le_two_mul_div j j s hs hsj le_rfl
    have hsum_re :
        (∑ k ∈ Finset.range (n0 + 1),
            ((((b k : ℝ) : ℂ)) * baseFn k)).re
          =
        ∑ k ∈ Finset.range (n0 + 1), aRe k * b k := by
          simp [aRe, b, baseFn, mul_comm, mul_left_comm, mul_assoc]
    have hsum_im :
        (∑ k ∈ Finset.range (n0 + 1),
            ((((b k : ℝ) : ℂ)) * baseFn k)).im
          =
        ∑ k ∈ Finset.range (n0 + 1), aIm k * b k := by
          simp [aIm, b, baseFn, mul_comm, mul_left_comm, mul_assoc]
    have hre :
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
          ≤ (2 * C) * Real.log (↑s + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
      have habel :=
        AbelSummation.abel_summation_bound aRe b n0 C0 hpartial_re hb_nonneg hb_anti
      calc
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
            = |∑ k ∈ Finset.range (n0 + 1), aRe k * b k| := by
                rw [hsum_re]
        _ ≤ C0 * b 0 := habel
        _ ≤ C0 * (2 * s / j) := by
              gcongr
        _ = (2 * C) * Real.log (↑s + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
              unfold C0
              field_simp [show ((s : ℕ) : ℝ) ≠ 0 by positivity, show (j : ℝ) ≠ 0 by positivity]
    have him :
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im|
          ≤ (2 * C) * Real.log (↑s + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
      have habel :=
        AbelSummation.abel_summation_bound aIm b n0 C0 hpartial_im hb_nonneg hb_anti
      calc
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im|
            = |∑ k ∈ Finset.range (n0 + 1), aIm k * b k| := by
                rw [hsum_im]
        _ ≤ C0 * b 0 := habel
        _ ≤ C0 * (2 * s / j) := by
              gcongr
        _ = (2 * C) * Real.log (↑s + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
              unfold C0
              field_simp [show ((s : ℕ) : ℝ) ≠ 0 by positivity, show (j : ℝ) ≠ 0 by positivity]
    have hlog_le : Real.log (↑s + 1) ≤ Real.log (↑j + 1) :=
      Real.log_le_log (by positivity) (by exact_mod_cast show s + 1 ≤ j + 1 by omega)
    have hnorm :
        ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖
          ≤ (4 * C) * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
      calc
        ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖
            ≤
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
            +
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| := by
              exact Complex.norm_le_abs_re_add_abs_im _
        _ ≤ (2 * C) * Real.log (↑s + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)
              +
            (2 * C) * Real.log (↑s + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
                exact add_le_add hre him
        _ = (4 * C) * Real.log (↑s + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
              ring
        _ ≤ (4 * C) * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
              gcongr
    calc
      ‖∑ k ∈ Finset.range N,
          ((((atkinsonLowerBoundaryShiftKernel (k + j) j s : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase (k + (j + s)) s : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) s))‖
        = ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖ := by
            simpa [hn0, b, baseFn, Nat.add_assoc, add_left_comm, add_comm]
      _ ≤ (4 * C) * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := hnorm

/-- Kernel-weighted next-shift Abel bound: the shifted inverse-phase core
at shift `r + 2` weighted by kernel(`r + 1`) · (stepCoeff(`r + 1`) − 1).

The proof uses the identity
  kernel(r+1) * (stepCoeff(r+1) - 1) = kernel(r+2) - kernel(r+1)
to decompose the sum into two kernel-weighted inverse-phase-core sums (one
with kernel at shift `r + 2`, the other at `r + 1`), both with phase/core
at the honest shift `r + 2`.  Each piece is bounded by Abel summation with
partial-sum bounds from `atkinson_shiftedInversePhaseCore_reindexed_tail_bound`
at shift `r + 2`. -/
class AtkinsonKernelWeightedNextShiftAbelBoundHyp : Prop where
  bound :
    ∃ C_err > 0, ∀ j : ℕ, 3 ≤ j → ∀ r : ℕ, r + 2 ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
            ((((atkinsonUpperBoundaryStepCoeff (k + j) (r + 1) - 1 : ℝ) : ℂ)) *
              ((((1 / atkinsonShiftedRelativePhase
                  (k + (j + (r + 2))) (r + 2) : ℝ) : ℂ)) *
                atkinsonShiftedSingleBoundaryCore (k + j) (r + 2))))‖
        ≤ C_err * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)

private theorem atkinson_kernelWeightedNextShift_abel_bound_atomic
    [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] :
    AtkinsonKernelWeightedNextShiftAbelBoundHyp := by
  constructor
  obtain ⟨C, hC, hshifted⟩ := atkinson_shiftedInversePhaseCore_reindexed_tail_bound
  refine ⟨8 * C, by positivity, ?_⟩
  intro j hj3 r hrj N
  have hj : 1 ≤ j := by omega
  have hr1 : 1 ≤ r + 1 := by omega
  have hr2 : 1 ≤ r + 2 := by omega
  have hr1j : r + 1 ≤ j := by omega
  have hr2j : r + 2 ≤ j := hrj
  have hr1_lt_j : r + 1 < j := by omega
  by_cases hN : N = 0
  · have hnonneg : 0 ≤ (8 * C) * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
      apply mul_nonneg
      · exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega))
      · positivity
    simpa [hN] using hnonneg
  obtain ⟨n0, hn0 : N = n0 + 1⟩ := Nat.exists_eq_succ_of_ne_zero hN
  -- baseFn: the inner (1/phase) × core at shift r+2
  let baseFn : ℕ → ℂ := fun k =>
    ((((1 / atkinsonShiftedRelativePhase (k + (j + (r + 2))) (r + 2) : ℝ) : ℂ)) *
      atkinsonShiftedSingleBoundaryCore (k + j) (r + 2))
  have hlog_r2_nonneg : 0 ≤ Real.log (↑(r + 2) + 1) :=
    Real.log_nonneg (by exact_mod_cast show 1 ≤ r + 2 + 1 by omega)
  let C0 : ℝ := C * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / (r + 2))
  let aRe : ℕ → ℝ := fun k => (baseFn k).re
  let aIm : ℕ → ℝ := fun k => (baseFn k).im
  -- Partial-sum bounds for baseFn via atkinson_shiftedInversePhaseCore_reindexed_tail_bound
  have hpartial_re : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aRe m| ≤ C0 := by
    intro k hk
    have hbound := hshifted j hj (r + 2) hr2 hr2j (k + 1)
    have htarget_k :
        Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / (r + 2)
          ≤ Real.sqrt (((N + j : ℕ) : ℝ) + 1) / (r + 2) := by
      exact div_le_div_of_nonneg_right
        (Real.sqrt_le_sqrt (by
          exact_mod_cast (by omega : (k + 1 + j) + 1 ≤ (N + j) + 1)))
        (by positivity : (0 : ℝ) ≤ r + 2)
    calc
      |∑ m ∈ Finset.range (k + 1), aRe m|
          = |(∑ m ∈ Finset.range (k + 1), baseFn m).re| := by
              simp [aRe]
      _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_re_le_norm _
      _ ≤ C * Real.log (↑(r + 2) + 1) * (Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / (r + 2)) := by
            simpa [baseFn, Nat.add_assoc, add_left_comm, add_comm] using hbound
      _ ≤ C * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / (r + 2)) := by
            exact mul_le_mul_of_nonneg_left htarget_k
              (mul_nonneg (le_of_lt hC) hlog_r2_nonneg)
      _ = C0 := by rfl
  have hpartial_im : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aIm m| ≤ C0 := by
    intro k hk
    have hbound := hshifted j hj (r + 2) hr2 hr2j (k + 1)
    have htarget_k :
        Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / (r + 2)
          ≤ Real.sqrt (((N + j : ℕ) : ℝ) + 1) / (r + 2) := by
      exact div_le_div_of_nonneg_right
        (Real.sqrt_le_sqrt (by
          exact_mod_cast (by omega : (k + 1 + j) + 1 ≤ (N + j) + 1)))
        (by positivity : (0 : ℝ) ≤ r + 2)
    calc
      |∑ m ∈ Finset.range (k + 1), aIm m|
          = |(∑ m ∈ Finset.range (k + 1), baseFn m).im| := by
              simp [aIm]
      _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_im_le_norm _
      _ ≤ C * Real.log (↑(r + 2) + 1) * (Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / (r + 2)) := by
            simpa [baseFn, Nat.add_assoc, add_left_comm, add_comm] using hbound
      _ ≤ C * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / (r + 2)) := by
            exact mul_le_mul_of_nonneg_left htarget_k
              (mul_nonneg (le_of_lt hC) hlog_r2_nonneg)
      _ = C0 := by rfl
  -- Abel-summation for kernel(r+2) × baseFn
  let b₂ : ℕ → ℝ := fun k => atkinsonLowerBoundaryShiftKernel (k + j) j (r + 2)
  have hb₂_nonneg : ∀ k ≤ n0, 0 ≤ b₂ k := by
    intro k hk
    simpa [b₂, Nat.add_assoc, add_left_comm, add_comm] using
      atkinsonLowerBoundaryShiftKernel_nonneg (k + j) j (r + 2) hr2 hr2j
  have hb₂_anti : ∀ k < n0, b₂ (k + 1) ≤ b₂ k := by
    intro k hk
    simpa [b₂, Nat.add_assoc, add_left_comm, add_comm] using
      (atkinsonLowerBoundaryShiftKernel_antitone j (r + 2) hr2 hr2j
        (by omega : k + j ≤ k + 1 + j))
  have hb₂_head : b₂ 0 ≤ 2 * (r + 2) / j := by
    simpa [b₂, Nat.add_assoc, add_left_comm, add_comm] using
      atkinsonLowerBoundaryShiftKernel_le_two_mul_div j j (r + 2) hr2 hr2j le_rfl
  -- Abel-summation for kernel(r+1) × baseFn
  let b₁ : ℕ → ℝ := fun k => atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1)
  have hb₁_nonneg : ∀ k ≤ n0, 0 ≤ b₁ k := by
    intro k hk
    simpa [b₁, Nat.add_assoc, add_left_comm, add_comm] using
      atkinsonLowerBoundaryShiftKernel_nonneg (k + j) j (r + 1) hr1 hr1j
  have hb₁_anti : ∀ k < n0, b₁ (k + 1) ≤ b₁ k := by
    intro k hk
    simpa [b₁, Nat.add_assoc, add_left_comm, add_comm] using
      (atkinsonLowerBoundaryShiftKernel_antitone j (r + 1) hr1 hr1j
        (by omega : k + j ≤ k + 1 + j))
  have hb₁_head : b₁ 0 ≤ 2 * (r + 1) / j := by
    simpa [b₁, Nat.add_assoc, add_left_comm, add_comm] using
      atkinsonLowerBoundaryShiftKernel_le_two_mul_div j j (r + 1) hr1 hr1j le_rfl
  -- Sum identities: real/imag decomposition
  have hsum₂_re :
      (∑ k ∈ Finset.range (n0 + 1), ((((b₂ k : ℝ) : ℂ)) * baseFn k)).re
        =
      ∑ k ∈ Finset.range (n0 + 1), aRe k * b₂ k := by
        simp [aRe, b₂, baseFn, mul_comm, mul_left_comm, mul_assoc]
  have hsum₂_im :
      (∑ k ∈ Finset.range (n0 + 1), ((((b₂ k : ℝ) : ℂ)) * baseFn k)).im
        =
      ∑ k ∈ Finset.range (n0 + 1), aIm k * b₂ k := by
        simp [aIm, b₂, baseFn, mul_comm, mul_left_comm, mul_assoc]
  have hsum₁_re :
      (∑ k ∈ Finset.range (n0 + 1), ((((b₁ k : ℝ) : ℂ)) * baseFn k)).re
        =
      ∑ k ∈ Finset.range (n0 + 1), aRe k * b₁ k := by
        simp [aRe, b₁, baseFn, mul_comm, mul_left_comm, mul_assoc]
  have hsum₁_im :
      (∑ k ∈ Finset.range (n0 + 1), ((((b₁ k : ℝ) : ℂ)) * baseFn k)).im
        =
      ∑ k ∈ Finset.range (n0 + 1), aIm k * b₁ k := by
        simp [aIm, b₁, baseFn, mul_comm, mul_left_comm, mul_assoc]
  -- Bound ‖∑ kernel(r+2) × baseFn‖
  have hnorm₂ :
      ‖∑ k ∈ Finset.range (n0 + 1), ((((b₂ k : ℝ) : ℂ)) * baseFn k)‖
        ≤ (4 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
    have hre : |(∑ k ∈ Finset.range (n0 + 1), ((((b₂ k : ℝ) : ℂ)) * baseFn k)).re|
        ≤ (2 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
      have habel :=
        AbelSummation.abel_summation_bound aRe b₂ n0 C0 hpartial_re hb₂_nonneg hb₂_anti
      calc
        |(∑ k ∈ Finset.range (n0 + 1), ((((b₂ k : ℝ) : ℂ)) * baseFn k)).re|
            = |∑ k ∈ Finset.range (n0 + 1), aRe k * b₂ k| := by rw [hsum₂_re]
        _ ≤ C0 * b₂ 0 := habel
        _ ≤ C0 * (2 * (r + 2) / j) := by gcongr
        _ = (2 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
              unfold C0
              field_simp [show ((r + 2 : ℕ) : ℝ) ≠ 0 by positivity,
                show (j : ℝ) ≠ 0 by positivity]
    have him : |(∑ k ∈ Finset.range (n0 + 1), ((((b₂ k : ℝ) : ℂ)) * baseFn k)).im|
        ≤ (2 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
      have habel :=
        AbelSummation.abel_summation_bound aIm b₂ n0 C0 hpartial_im hb₂_nonneg hb₂_anti
      calc
        |(∑ k ∈ Finset.range (n0 + 1), ((((b₂ k : ℝ) : ℂ)) * baseFn k)).im|
            = |∑ k ∈ Finset.range (n0 + 1), aIm k * b₂ k| := by rw [hsum₂_im]
        _ ≤ C0 * b₂ 0 := habel
        _ ≤ C0 * (2 * (r + 2) / j) := by gcongr
        _ = (2 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
              unfold C0
              field_simp [show ((r + 2 : ℕ) : ℝ) ≠ 0 by positivity,
                show (j : ℝ) ≠ 0 by positivity]
    calc
      ‖∑ k ∈ Finset.range (n0 + 1), ((((b₂ k : ℝ) : ℂ)) * baseFn k)‖
          ≤ |(∑ k ∈ Finset.range (n0 + 1), ((((b₂ k : ℝ) : ℂ)) * baseFn k)).re|
            + |(∑ k ∈ Finset.range (n0 + 1), ((((b₂ k : ℝ) : ℂ)) * baseFn k)).im| :=
              Complex.norm_le_abs_re_add_abs_im _
      _ ≤ (2 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)
            + (2 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) :=
              add_le_add hre him
      _ = (4 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by ring
  -- Bound ‖∑ kernel(r+1) × baseFn‖
  have hnorm₁ :
      ‖∑ k ∈ Finset.range (n0 + 1), ((((b₁ k : ℝ) : ℂ)) * baseFn k)‖
        ≤ (4 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
    have hre : |(∑ k ∈ Finset.range (n0 + 1), ((((b₁ k : ℝ) : ℂ)) * baseFn k)).re|
        ≤ (2 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
      have habel :=
        AbelSummation.abel_summation_bound aRe b₁ n0 C0 hpartial_re hb₁_nonneg hb₁_anti
      calc
        |(∑ k ∈ Finset.range (n0 + 1), ((((b₁ k : ℝ) : ℂ)) * baseFn k)).re|
            = |∑ k ∈ Finset.range (n0 + 1), aRe k * b₁ k| := by rw [hsum₁_re]
        _ ≤ C0 * b₁ 0 := habel
        _ ≤ C0 * (2 * (r + 1) / j) := by gcongr
        _ ≤ C0 * (2 * (r + 2) / j) := by
              gcongr
              norm_cast
        _ = (2 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
              unfold C0
              field_simp [show ((r + 2 : ℕ) : ℝ) ≠ 0 by positivity,
                show (j : ℝ) ≠ 0 by positivity]
    have him : |(∑ k ∈ Finset.range (n0 + 1), ((((b₁ k : ℝ) : ℂ)) * baseFn k)).im|
        ≤ (2 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
      have habel :=
        AbelSummation.abel_summation_bound aIm b₁ n0 C0 hpartial_im hb₁_nonneg hb₁_anti
      calc
        |(∑ k ∈ Finset.range (n0 + 1), ((((b₁ k : ℝ) : ℂ)) * baseFn k)).im|
            = |∑ k ∈ Finset.range (n0 + 1), aIm k * b₁ k| := by rw [hsum₁_im]
        _ ≤ C0 * b₁ 0 := habel
        _ ≤ C0 * (2 * (r + 1) / j) := by gcongr
        _ ≤ C0 * (2 * (r + 2) / j) := by
              gcongr
              norm_cast
        _ = (2 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
              unfold C0
              field_simp [show ((r + 2 : ℕ) : ℝ) ≠ 0 by positivity,
                show (j : ℝ) ≠ 0 by positivity]
    calc
      ‖∑ k ∈ Finset.range (n0 + 1), ((((b₁ k : ℝ) : ℂ)) * baseFn k)‖
          ≤ |(∑ k ∈ Finset.range (n0 + 1), ((((b₁ k : ℝ) : ℂ)) * baseFn k)).re|
            + |(∑ k ∈ Finset.range (n0 + 1), ((((b₁ k : ℝ) : ℂ)) * baseFn k)).im| :=
              Complex.norm_le_abs_re_add_abs_im _
      _ ≤ (2 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)
            + (2 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) :=
              add_le_add hre him
      _ = (4 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by ring
  -- Rewrite the original sum using the kernel identity
  have hrewrite : ∀ k : ℕ,
      ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
        ((((atkinsonUpperBoundaryStepCoeff (k + j) (r + 1) - 1 : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase (k + (j + (r + 2))) (r + 2) : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) (r + 2))))
        =
      ((((b₂ k : ℝ) : ℂ)) * baseFn k) - ((((b₁ k : ℝ) : ℂ)) * baseFn k) := by
    intro k
    have hident :=
      atkinsonLowerBoundaryShiftKernel_mul_stepCoeff_sub_one (k + j) j (r + 1) hr1 hr1_lt_j
    simp only [b₁, b₂, baseFn]
    have : ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) *
              (atkinsonUpperBoundaryStepCoeff (k + j) (r + 1) - 1) : ℝ) : ℂ)))
        = ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
            (((atkinsonUpperBoundaryStepCoeff (k + j) (r + 1) - 1 : ℝ) : ℂ))) := by
      push_cast; ring
    rw [hident] at this
    have hsub : ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1 + 1) -
            atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)))
        = ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 2) : ℝ) : ℂ)) -
            ((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) := by
      push_cast; ring
    rw [show r + 1 + 1 = r + 2 from by omega] at hsub
    calc
      ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
          ((((atkinsonUpperBoundaryStepCoeff (k + j) (r + 1) - 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase (k + (j + (r + 2))) (r + 2) : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) (r + 2))))
        = ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
            ((((atkinsonUpperBoundaryStepCoeff (k + j) (r + 1) - 1 : ℝ) : ℂ)))) *
          ((((1 / atkinsonShiftedRelativePhase (k + (j + (r + 2))) (r + 2) : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) (r + 2)) := by ring
      _ = ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) *
              (atkinsonUpperBoundaryStepCoeff (k + j) (r + 1) - 1) : ℝ) : ℂ))) *
            ((((1 / atkinsonShiftedRelativePhase (k + (j + (r + 2))) (r + 2) : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) (r + 2)) := by push_cast; ring
      _ = ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 2) -
              atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ))) *
            ((((1 / atkinsonShiftedRelativePhase (k + (j + (r + 2))) (r + 2) : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) (r + 2)) := by rw [hident]
      _ = (((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 2) : ℝ) : ℂ)) -
              (((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)))) *
            ((((1 / atkinsonShiftedRelativePhase (k + (j + (r + 2))) (r + 2) : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) (r + 2)) := by push_cast; ring
      _ = ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 2) : ℝ) : ℂ)) *
              ((((1 / atkinsonShiftedRelativePhase (k + (j + (r + 2))) (r + 2) : ℝ) : ℂ)) *
                atkinsonShiftedSingleBoundaryCore (k + j) (r + 2)))
            - ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
              ((((1 / atkinsonShiftedRelativePhase (k + (j + (r + 2))) (r + 2) : ℝ) : ℂ)) *
                atkinsonShiftedSingleBoundaryCore (k + j) (r + 2))) := by ring
      _ = ((((b₂ k : ℝ) : ℂ)) * baseFn k) - ((((b₁ k : ℝ) : ℂ)) * baseFn k) := by rfl
  -- Final calc chain
  calc
    ‖∑ k ∈ Finset.range N,
        ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
          ((((atkinsonUpperBoundaryStepCoeff (k + j) (r + 1) - 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase
                (k + (j + (r + 2))) (r + 2) : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) (r + 2))))‖
      = ‖∑ k ∈ Finset.range (n0 + 1),
          (((((b₂ k : ℝ) : ℂ)) * baseFn k) - ((((b₁ k : ℝ) : ℂ)) * baseFn k))‖ := by
            rw [hn0]; congr 1; exact Finset.sum_congr rfl (fun k _ => hrewrite k)
    _ = ‖(∑ k ∈ Finset.range (n0 + 1), ((((b₂ k : ℝ) : ℂ)) * baseFn k))
          - ∑ k ∈ Finset.range (n0 + 1), ((((b₁ k : ℝ) : ℂ)) * baseFn k)‖ := by
            rw [Finset.sum_sub_distrib]
    _ ≤ ‖∑ k ∈ Finset.range (n0 + 1), ((((b₂ k : ℝ) : ℂ)) * baseFn k)‖
        + ‖∑ k ∈ Finset.range (n0 + 1), ((((b₁ k : ℝ) : ℂ)) * baseFn k)‖ :=
            norm_sub_le _ _
    _ ≤ (4 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)
        + (4 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) :=
            add_le_add hnorm₂ hnorm₁
    _ = (8 * C) * Real.log (↑(r + 2) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by ring
    _ ≤ (8 * C) * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
          gcongr <;> exact_mod_cast show r + 2 + 1 ≤ j + 1 by omega

/-- Exported name for the honest next-shift Abel bridge coming from the stronger
shifted inverse-phase-core prefix package.

`CorePrefixDirect` and later recovery files should consume this theorem or the
class it returns, rather than reaching into Atkinson's private kernel internals. -/
theorem atkinson_kernelWeightedNextShift_abel_bound_of_shiftedInversePhaseCore
    [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] :
    AtkinsonKernelWeightedNextShiftAbelBoundHyp :=
  atkinson_kernelWeightedNextShift_abel_bound_atomic

/-- Leaf hypothesis for the shifted inverse-phase-core prefix bound at small
shifts (`j = 1, 2`).  The honest large-shift bridge below starts at `j = 3`, so
these two finite cases must be supplied independently.  They are the only
additional leaf surface introduced by the first-lane split-shift bridge. -/
class AtkinsonSmallShiftPrefixBoundHyp : Prop where
  bound :
    ∃ C_small > 0, ∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) j)‖
        ≤ C_small * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)

/- Fixed-shift reindex helper from the native inverse-phase-core prefix surface
to the shifted `k + j` prefix surface consumed by `AtkinsonSmallShiftPrefixBoundHyp`.

This theorem is purely combinatorial/support-level: it rewrites the shifted row as
an `Ico` slice of the native prefix and bounds that slice by the difference of two
native prefixes. -/
omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
private theorem atkinson_shiftedInversePhaseCorePrefix_bound_shifted_of_native_fixedShift
    (j : ℕ) (hj : 1 ≤ j)
    (hnative :
      ∃ C > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n j)‖
          ≤ C * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / (j : ℝ))) :
    ∃ C > 0, ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) j)‖
        ≤ C * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / (j : ℝ)) := by
  obtain ⟨C, hC, hprefix⟩ := hnative
  refine ⟨2 * Real.sqrt 2 * C, by positivity, ?_⟩
  intro N
  let base : ℕ → ℂ := fun n =>
    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
      atkinsonShiftedSingleBoundaryCore n j)
  let target : ℝ := Real.sqrt (((N + j : ℕ) : ℝ) + 1) / (j : ℝ)
  have hsum :
      ∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) j)
        =
      ∑ n ∈ Finset.Ico j (j + N), base n := by
    calc
      ∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) j)
          = ∑ k ∈ Finset.range N, base (k + j) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              simp [base, Nat.add_assoc, add_left_comm, add_comm]
      _ = ∑ n ∈ Finset.Ico j (j + N), base n := by
            simpa [Nat.add_assoc, add_left_comm, add_comm] using
              (Finset.sum_Ico_eq_sum_range (f := base) (m := j) (n := j + N)).symm
  have hsplit :
      ∑ n ∈ Finset.Ico j (j + N), base n
        =
      (∑ n ∈ Finset.range (j + N), base n) - ∑ n ∈ Finset.range j, base n := by
          rw [Finset.sum_Ico_eq_sub _ (Nat.le_add_right j N)]
  have hmain :
      ‖∑ n ∈ Finset.range (j + N), base n‖ ≤ Real.sqrt 2 * C * target := by
    have hraw := hprefix (N + j - 1)
    have hrange : j + N = 1 + (N + j - 1) := by
      have hpos : 0 < N + j := by omega
      have hsuccpred : (N + j - 1) + 1 = N + j := by
        simpa [Nat.succ_eq_add_one, Nat.pred_eq_sub_one] using Nat.succ_pred_eq_of_pos hpos
      simpa [Nat.add_assoc, add_left_comm, add_comm] using hsuccpred.symm
    have htarget :
        Real.sqrt (((N + j - 1 + j : ℕ) : ℝ) + 1) / (j : ℝ) ≤ Real.sqrt 2 * target := by
      have hle_nat : (N + j - 1 + j) + 1 ≤ 2 * (N + j + 1) := by
        omega
      have hle :
          ((((N + j - 1 + j : ℕ) : ℝ) + 1)) ≤ 2 * ((((N + j : ℕ) : ℝ) + 1) : ℝ) := by
        exact_mod_cast hle_nat
      calc
        Real.sqrt (((N + j - 1 + j : ℕ) : ℝ) + 1) / (j : ℝ)
            ≤ Real.sqrt (2 * ((((N + j : ℕ) : ℝ) + 1))) / j := by
                exact div_le_div_of_nonneg_right
                  (Real.sqrt_le_sqrt hle)
                  (by positivity : (0 : ℝ) ≤ j)
        _ = (Real.sqrt 2 * Real.sqrt ((((N + j : ℕ) : ℝ) + 1))) / j := by
              have hsqrt_eq :
                  Real.sqrt (2 * ((((N + j : ℕ) : ℝ) + 1)))
                    = Real.sqrt 2 * Real.sqrt ((((N + j : ℕ) : ℝ) + 1)) := by
                      simpa using
                        (Real.sqrt_mul
                          (by positivity : 0 ≤ (2 : ℝ))
                          (by positivity : 0 ≤ ((((N + j : ℕ) : ℝ) + 1))))
              rw [hsqrt_eq]
        _ = Real.sqrt 2 * target := by
              unfold target
              ring
    calc
      ‖∑ n ∈ Finset.range (j + N), base n‖
          = ‖∑ n ∈ Finset.range (1 + (N + j - 1)), base n‖ := by
              rw [hrange]
      _ 
          ≤ C * (Real.sqrt (((N + j - 1 + j : ℕ) : ℝ) + 1) / (j : ℝ)) := by
              simpa [base, Nat.add_assoc,
                add_left_comm, add_comm] using hraw
      _ ≤ C * (Real.sqrt 2 * target) := by
            exact mul_le_mul_of_nonneg_left htarget (le_of_lt hC)
      _ = Real.sqrt 2 * C * target := by ring
  have hhead :
      ‖∑ n ∈ Finset.range j, base n‖ ≤ Real.sqrt 2 * C * target := by
    have hraw := hprefix (j - 1)
    have htarget :
        Real.sqrt (((j - 1 + j : ℕ) : ℝ) + 1) / (j : ℝ) ≤ Real.sqrt 2 * target := by
      have hle_nat : (j - 1 + j) + 1 ≤ 2 * (N + j + 1) := by
        omega
      have hle :
          ((((j - 1 + j : ℕ) : ℝ) + 1)) ≤ 2 * ((((N + j : ℕ) : ℝ) + 1) : ℝ) := by
        exact_mod_cast hle_nat
      calc
        Real.sqrt (((j - 1 + j : ℕ) : ℝ) + 1) / (j : ℝ)
            ≤ Real.sqrt (2 * ((((N + j : ℕ) : ℝ) + 1))) / j := by
                exact div_le_div_of_nonneg_right
                  (Real.sqrt_le_sqrt hle)
                  (by positivity : (0 : ℝ) ≤ j)
        _ = (Real.sqrt 2 * Real.sqrt ((((N + j : ℕ) : ℝ) + 1))) / j := by
              have hsqrt_eq :
                  Real.sqrt (2 * ((((N + j : ℕ) : ℝ) + 1)))
                    = Real.sqrt 2 * Real.sqrt ((((N + j : ℕ) : ℝ) + 1)) := by
                      simpa using
                        (Real.sqrt_mul
                          (by positivity : 0 ≤ (2 : ℝ))
                          (by positivity : 0 ≤ ((((N + j : ℕ) : ℝ) + 1))))
              rw [hsqrt_eq]
        _ = Real.sqrt 2 * target := by
              unfold target
              ring
    calc
      ‖∑ n ∈ Finset.range j, base n‖
          ≤ C * (Real.sqrt (((j - 1 + j : ℕ) : ℝ) + 1) / (j : ℝ)) := by
              simpa [base, show j - 1 + 1 = j by omega, Nat.add_assoc,
                add_left_comm, add_comm] using hraw
      _ ≤ C * (Real.sqrt 2 * target) := by
            exact mul_le_mul_of_nonneg_left htarget (le_of_lt hC)
      _ = Real.sqrt 2 * C * target := by ring
  calc
    ‖∑ k ∈ Finset.range N,
        ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + j) j)‖
      = ‖∑ n ∈ Finset.Ico j (j + N), base n‖ := by
          rw [hsum]
    _ = ‖(∑ n ∈ Finset.range (j + N), base n) - ∑ n ∈ Finset.range j, base n‖ := by
          rw [hsplit]
    _ ≤ ‖∑ n ∈ Finset.range (j + N), base n‖ + ‖∑ n ∈ Finset.range j, base n‖ := by
          exact norm_sub_le _ _
    _ ≤ Real.sqrt 2 * C * target + Real.sqrt 2 * C * target := by
          exact add_le_add hmain hhead
    _ = (2 * Real.sqrt 2 * C) * target := by
          ring

/-- Native finite-shift leaves (`j = 1`, `j = 2`) imply the shifted small-shift
prefix package used by the split first-lane bridge. This keeps the honest
frontier at the native leaves while preserving the existing downstream class
surface. -/
private theorem atkinson_smallShiftPrefixBound_of_native_j1_j2
    (hj1 :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ)))
    (hj2 :
      ∃ C2 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 2) 2 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 2)‖
          ≤ C2 * (Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (2 : ℝ))) :
    AtkinsonSmallShiftPrefixBoundHyp := by
  constructor
  have hj1' :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)) := by
    simpa using hj1
  have hj2' :
      ∃ C2 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 2) 2 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 2)‖
          ≤ C2 * (Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)) := by
    simpa using hj2
  obtain ⟨C1, hC1, hshift1⟩ :=
    atkinson_shiftedInversePhaseCorePrefix_bound_shifted_of_native_fixedShift 1 (by norm_num) hj1'
  obtain ⟨C2, hC2, hshift2⟩ :=
    atkinson_shiftedInversePhaseCorePrefix_bound_shifted_of_native_fixedShift 2 (by norm_num) hj2'
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(C1 + C2) / Real.log 2, by positivity, ?_⟩
  intro j hj hj2 N
  have hj_cases : j = 1 ∨ j = 2 := by omega
  rcases hj_cases with rfl | rfl
  · have hlog_ge : Real.log 2 ≤ Real.log (↑(1 : ℕ) + 1) := by norm_num
    calc
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (1 + 1)) 1 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + 1) 1)‖
        ≤ C1 * (Real.sqrt (((N + 1 : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)) := by
            simpa using hshift1 N
      _ ≤ (C1 + C2) * (Real.sqrt (((N + 1 : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)) := by
            gcongr; linarith
      _ = (C1 + C2) / Real.log 2 * Real.log 2 *
            (Real.sqrt (((N + 1 : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)) := by
            rw [div_mul_cancel₀]; exact ne_of_gt hlog2_pos
      _ ≤ (C1 + C2) / Real.log 2 * Real.log (↑(1 : ℕ) + 1) *
            (Real.sqrt (((N + 1 : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)) := by
            norm_num
  · have hlog_ge : Real.log 2 ≤ Real.log (↑(2 : ℕ) + 1) := by
      exact Real.log_le_log (by positivity) (by norm_num)
    calc
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (2 + 2)) 2 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + 2) 2)‖
        ≤ C2 * (Real.sqrt (((N + 2 : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)) := by
            simpa using hshift2 N
      _ ≤ (C1 + C2) * (Real.sqrt (((N + 2 : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)) := by
            gcongr; linarith
      _ = (C1 + C2) / Real.log 2 * Real.log 2 *
            (Real.sqrt (((N + 2 : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)) := by
            rw [div_mul_cancel₀]; exact ne_of_gt hlog2_pos
      _ ≤ (C1 + C2) / Real.log 2 * Real.log (↑(2 : ℕ) + 1) *
            (Real.sqrt (((N + 2 : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)) := by
            gcongr

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
private theorem atkinson_smallShiftPrefixBound_of_native_j1_j2_clean
    (hj1 :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ)))
    (hj2 :
      ∃ C2 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 2) 2 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 2)‖
          ≤ C2 * (Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (2 : ℝ))) :
    AtkinsonSmallShiftPrefixBoundHyp := by
  constructor
  have hj1' :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)) := by
    simpa using hj1
  have hj2' :
      ∃ C2 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 2) 2 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 2)‖
          ≤ C2 * (Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)) := by
    simpa using hj2
  obtain ⟨C1, hC1, hshift1⟩ :=
    atkinson_shiftedInversePhaseCorePrefix_bound_shifted_of_native_fixedShift 1 (by norm_num) hj1'
  obtain ⟨C2, hC2, hshift2⟩ :=
    atkinson_shiftedInversePhaseCorePrefix_bound_shifted_of_native_fixedShift 2 (by norm_num) hj2'
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(C1 + C2) / Real.log 2, by positivity, ?_⟩
  intro j hj hj2 N
  have hj_cases : j = 1 ∨ j = 2 := by omega
  rcases hj_cases with rfl | rfl
  · have hlog_ge : Real.log 2 ≤ Real.log (↑(1 : ℕ) + 1) := by norm_num
    calc
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (1 + 1)) 1 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + 1) 1)‖
        ≤ C1 * (Real.sqrt (((N + 1 : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)) := by
            simpa using hshift1 N
      _ ≤ (C1 + C2) * (Real.sqrt (((N + 1 : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)) := by
            gcongr; linarith
      _ = (C1 + C2) / Real.log 2 * Real.log 2 *
            (Real.sqrt (((N + 1 : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)) := by
            rw [div_mul_cancel₀]; exact ne_of_gt hlog2_pos
      _ ≤ (C1 + C2) / Real.log 2 * Real.log (↑(1 : ℕ) + 1) *
            (Real.sqrt (((N + 1 : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)) := by
            norm_num
  · have hlog_ge : Real.log 2 ≤ Real.log (↑(2 : ℕ) + 1) := by
      exact Real.log_le_log (by positivity) (by norm_num)
    calc
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (2 + 2)) 2 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + 2) 2)‖
        ≤ C2 * (Real.sqrt (((N + 2 : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)) := by
            simpa using hshift2 N
      _ ≤ (C1 + C2) * (Real.sqrt (((N + 2 : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)) := by
            gcongr; linarith
      _ = (C1 + C2) / Real.log 2 * Real.log 2 *
            (Real.sqrt (((N + 2 : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)) := by
            rw [div_mul_cancel₀]; exact ne_of_gt hlog2_pos
      _ ≤ (C1 + C2) / Real.log 2 * Real.log (↑(2 : ℕ) + 1) *
            (Real.sqrt (((N + 2 : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)) := by
            gcongr

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
/-- Patch-ready local successor step for the large-shift seam.

This thin wrapper fills the `hbdry` slot from the live reciprocal-step
boundary-row theorem `atkinsonResonantShiftedBoundary_recipStepCoeff_weighted_bound_atomic`,
at the cost of a uniform factor `2` when converting the natural `/ j` scale to
the successor `/ (j + 1)` scale. -/
private theorem atkinson_largeShiftPrefix_succ_boundary_bound_atomic
    (hbdryRow :
      ∃ C_bdry > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
        ‖∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)‖
          ≤ C_bdry * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j)) :
    ∃ C_bdry > 0, ∀ j : ℕ, 2 ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm (k + (j + 1)) j)‖
        ≤ C_bdry * Real.log (↑j + 1) * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)) := by
  obtain ⟨C_complete, hC_complete, hcomplete⟩ :=
    atkinsonResonantShiftedBoundary_recipStepCoeff_weighted_bound_atomic hbdryRow
  refine ⟨2 * C_complete, by positivity, ?_⟩
  intro j hj N
  have hlog_j_nonneg : 0 ≤ Real.log (↑j + 1) :=
    Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)
  have hbdry :
      ∀ N : ℕ,
        ‖∑ k ∈ Finset.range N,
            ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
              atkinsonResonantShiftedBoundaryTerm (k + (j + 1)) j)‖
          ≤ (2 * C_complete) * Real.log (↑j + 1) *
              (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)) := by
    intro N
    have hj_pos : (0 : ℝ) < j := by positivity
    have hj1_pos : (0 : ℝ) < (j + 1 : ℝ) := by positivity
    have hrecip :
        ‖∑ k ∈ Finset.range N,
            ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
              atkinsonResonantShiftedBoundaryTerm (k + (j + 1)) j)‖
          ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
      exact hcomplete j (by omega) N
    have hfrac :
        (1 : ℝ) / j ≤ (2 : ℝ) / (j + 1 : ℝ) := by
      rw [div_le_div_iff₀ hj_pos hj1_pos]
      have htwoj : ((j + 1 : ℕ) : ℝ) ≤ 2 * (j : ℝ) := by
        exact_mod_cast (show j + 1 ≤ 2 * j by omega)
      simpa using htwoj
    have htarget_j_to_succ :
        Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j
          ≤
        2 * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)) := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt (((N + j : ℕ) : ℝ) + 1) := by positivity
      have hle_nat : N + j ≤ N + (j + 1) := by omega
      have hle_cast : ((N + j : ℕ) : ℝ) ≤ ((N + (j + 1) : ℕ) : ℝ) := by
        exact_mod_cast hle_nat
      have hsqrt_le :
          Real.sqrt (((N + j : ℕ) : ℝ) + 1)
            ≤
          Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) := by
        refine Real.sqrt_le_sqrt ?_
        linarith
      calc
        Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j
            = Real.sqrt (((N + j : ℕ) : ℝ) + 1) * ((1 : ℝ) / j) := by ring
        _ ≤ Real.sqrt (((N + j : ℕ) : ℝ) + 1) * ((2 : ℝ) / (j + 1)) := by
              gcongr
        _ ≤ Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) * ((2 : ℝ) / (j + 1)) := by
              gcongr
        _ = 2 * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)) := by
              ring
    calc
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm (k + (j + 1)) j)‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := hrecip
      _ ≤ C_complete * Real.log (↑j + 1) *
            (2 * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1))) := by
              gcongr
      _ = (2 * C_complete) * Real.log (↑j + 1) *
            (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)) := by
              ring
  exact hbdry N

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
/-- Patch-ready local successor step for the large-shift seam.

This thin wrapper fills the `hbdry` slot from the live reciprocal-step
boundary-row theorem `atkinsonResonantShiftedBoundary_recipStepCoeff_weighted_bound_atomic`,
at the cost of a uniform factor `2` when converting the natural `/ j` scale to
the successor `/ (j + 1)` scale. -/
private theorem atkinson_largeShiftPrefix_succ_affine_step
    (γ : ℝ)
    (hbdryRow :
      ∃ C_bdry > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
        ‖∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)‖
          ≤ C_bdry * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j))
    (htail :
      ∀ C_prev : ℝ, 0 < C_prev →
      ∀ j : ℕ, 2 ≤ j →
        (∀ N : ℕ,
          ‖∑ k ∈ Finset.range N,
              ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
                atkinsonShiftedSingleBoundaryCore (k + j) j)‖
            ≤ C_prev * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)) →
        ∀ N : ℕ,
          ‖∑ k ∈ Finset.range N,
              ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
                ((((1 / atkinsonShiftedRelativePhase
                    (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
                  atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖
            ≤ γ * C_prev *
                (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1))) :
    ∃ C_bdry > 0, ∀ C_prev : ℝ, 0 < C_prev →
      ∀ j : ℕ, 2 ≤ j →
        (∀ N : ℕ,
          ‖∑ k ∈ Finset.range N,
              ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
                atkinsonShiftedSingleBoundaryCore (k + j) j)‖
            ≤ C_prev * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)) →
        ∀ N : ℕ,
          ‖∑ k ∈ Finset.range N,
              ((((1 / atkinsonShiftedRelativePhase
                  (k + ((j + 1) + (j + 1))) (j + 1) : ℝ) : ℂ)) *
                atkinsonShiftedSingleBoundaryCore (k + (j + 1)) (j + 1))‖
            ≤ (γ * C_prev + C_bdry * Real.log (↑j + 1)) *
                (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)) := by
  obtain ⟨C_bdry, hC_bdry, hbdry⟩ :=
    atkinson_largeShiftPrefix_succ_boundary_bound_atomic hbdryRow
  refine ⟨C_bdry, hC_bdry, ?_⟩
  intro C_prev hC_prev j hj hprev N
  calc
    ‖∑ k ∈ Finset.range N,
        ((((1 / atkinsonShiftedRelativePhase
            (k + ((j + 1) + (j + 1))) (j + 1) : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + (j + 1)) (j + 1))‖
      =
    ‖(∑ k ∈ Finset.range N,
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm (k + (j + 1)) j))
        +
        ∑ k ∈ Finset.range N,
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase
                (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖ := by
          rw [atkinsonShiftedInversePhaseCorePrefix_succ_eq N j (by omega)]
    _ ≤
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm (k + (j + 1)) j)‖
        +
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase
                (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖ := by
          exact norm_add_le _ _
    _ ≤
      C_bdry * Real.log (↑j + 1) * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1))
        +
      γ * C_prev * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)) := by
          exact add_le_add (hbdry j hj N) ((htail C_prev hC_prev j hj hprev) N)
    _ = (γ * C_prev + C_bdry * Real.log (↑j + 1)) *
          (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)) := by
          ring

/-- Patch-ready local successor step for the large-shift seam.

It packages the exact summed successor identity
`atkinsonShiftedInversePhaseCorePrefix_succ_eq` into the affine estimate needed
just before `AtkinsonLargeShiftPrefixBoundHyp`. The only remaining analytic
inputs are:
* a strict/local bound for the reciprocal-step weighted predecessor tail
* a bound for the reciprocal-step weighted boundary row. -/
private theorem atkinson_largeShiftPrefix_succ_affine_step_of_boundary
    (j : ℕ) (hj : 2 ≤ j)
    (γ C_prev C_bdry : ℝ)
    (htail :
      ∀ N : ℕ,
        ‖∑ k ∈ Finset.range N,
            ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
              ((((1 / atkinsonShiftedRelativePhase
                  (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
                atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖
          ≤ γ * C_prev *
              (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)))
    (hbdry :
      ∀ N : ℕ,
        ‖∑ k ∈ Finset.range N,
            ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
              atkinsonResonantShiftedBoundaryTerm (k + (j + 1)) j)‖
          ≤ C_bdry * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1))) :
    ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase
              (k + ((j + 1) + (j + 1))) (j + 1) : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + (j + 1)) (j + 1))‖
        ≤ (γ * C_prev + C_bdry) *
            (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)) := by
  intro N
  calc
    ‖∑ k ∈ Finset.range N,
        ((((1 / atkinsonShiftedRelativePhase
            (k + ((j + 1) + (j + 1))) (j + 1) : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + (j + 1)) (j + 1))‖
      =
    ‖(∑ k ∈ Finset.range N,
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm (k + (j + 1)) j))
        +
        ∑ k ∈ Finset.range N,
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase
                (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖ := by
          rw [atkinsonShiftedInversePhaseCorePrefix_succ_eq N j (by omega)]
    _ ≤
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm (k + (j + 1)) j)‖
        +
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase
                (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖ := by
          exact norm_add_le _ _
    _ ≤
      C_bdry * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1))
        +
      γ * C_prev * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)) := by
          exact add_le_add (hbdry N) (htail N)
    _ = (γ * C_prev + C_bdry) *
          (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)) := by
          ring

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
/-- Local predecessor-tail input for
`atkinson_largeShiftPrefix_succ_affine_step_of_boundary` at the successor
geometry used by the large-shift bridge.

Given the predecessor prefix bound `C_prev · √(N + j + 1) / j` at shift `j`,
the reciprocal-step-coefficient weighted tail is bounded by
`8 · C_prev · √(N + (j + 1) + 1) / (j + 1)`.

The proof uses Abel summation with the weight `1/stepCoeff`, which is
antitone, nonneg, and ≤ 1. The factor 8 arises as
  2 (Ico tail → two prefix evaluations)
  × 2 (Complex norm ≤ |re| + |im|)
  × 2 (scale conversion 1/j ≤ 2/(j + 1) for j ≥ 1). -/
private theorem atkinson_largeShiftPrefix_succ_htail_of_nextShift_and_smallShift
    (C_prev : ℝ) (hC_prev : 0 < C_prev)
    (j : ℕ) (hj : 2 ≤ j)
    (hprev :
      ∀ N : ℕ,
        ‖∑ k ∈ Finset.range N,
            ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) j)‖
          ≤ C_prev * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)) :
    ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase
                (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖
        ≤ 8 * C_prev *
            (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)) := by
  intro N
  let J : ℕ := j + 1
  let target : ℝ := Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)
  by_cases hN : N = 0
  · have hnonneg : 0 ≤ 8 * C_prev * target := by positivity
    simpa [hN, target] using hnonneg
  · obtain ⟨n0, hn0 : N = n0 + 1⟩ := Nat.exists_eq_succ_of_ne_zero hN
    -- The base oscillatory function (predecessor tail summand)
    let baseFn : ℕ → ℂ := fun k =>
      ((((1 / atkinsonShiftedRelativePhase
          (k + (J + j)) j : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore (k + J) j)
    -- Uniform bound on partial sums of the base, at /j scale.
    -- The tail partial sum ∑_{m<k+1} baseFn m = prefix(k+2) - prefix(1),
    -- where prefix(M) is the predecessor prefix at length M.
    let C0 : ℝ := 2 * C_prev * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / j)
    let aRe : ℕ → ℝ := fun k => (baseFn k).re
    let aIm : ℕ → ℝ := fun k => (baseFn k).im
    let b : ℕ → ℝ := fun k => 1 / atkinsonUpperBoundaryStepCoeff (k + J) j
    -- Partial sums of baseFn = predecessor prefix(k+2) − prefix(1).
    -- Each prefix value is bounded by C_prev · √((M+j)+1)/j, so the
    -- difference is bounded by 2 · C_prev · √((N+(j+1))+1)/j.
    have hpartial_norm : ∀ k ≤ n0,
        ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ ≤ C0 := by
      intro k hk
      -- Rewrite ∑_{m<k+1} baseFn m as prefix(k+2) - prefix(1)
      have hprev_k2 :=  hprev (k + 2)
      have hprev_1  :=  hprev 1
      -- prefix(k+2) bound: sqrt((k+2+j)+1)/j ≤ sqrt((N+(j+1))+1)/j
      have hsqrt_k2 : Real.sqrt (((k + 2 + j : ℕ) : ℝ) + 1) ≤
          Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) := by
        exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : (k + 2 + j) + 1 ≤ (N + (j + 1)) + 1))
      -- prefix(1) bound: sqrt((1+j)+1)/j ≤ sqrt((N+(j+1))+1)/j
      have hsqrt_1 : Real.sqrt (((1 + j : ℕ) : ℝ) + 1) ≤
          Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) := by
        exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : (1 + j) + 1 ≤ (N + (j + 1)) + 1))
      -- baseFn m is the predecessor summand at index m+1.
      -- Bound directly: ‖∑_{m<k+1} baseFn(m)‖ ≤ hprev(k+2) + hprev(1) ≤ C0.
      -- Key: ∑_{m<k+1} baseFn(m) = ∑_{n ∈ Ico 1 (k+2)} predecessor_summand(n).
      let f : ℕ → ℂ := fun m =>
        ((((1 / atkinsonShiftedRelativePhase (m + (j + j)) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (m + j) j)
      have hbaseFn_f : ∀ m : ℕ, baseFn m = f (m + 1) := by
        intro m
        simp [baseFn, f, J, Nat.add_assoc, add_left_comm, add_comm]
      -- ∑_{m<k+1} baseFn(m) = ∑_{m<k+2} f(m) - f(0)
      -- via Finset.sum_range_succ' on ∑_{m<k+2} f(m)
      have hprefixSplit :
          ∑ n ∈ Finset.range (k + 2), f n
            = (∑ m ∈ Finset.range (k + 1), f (m + 1)) + f 0 := by
        rw [show k + 2 = (k + 1) + 1 from by omega]
        exact Finset.sum_range_succ' f (k + 1)
      have hbaseFn_sum :
          ∑ m ∈ Finset.range (k + 1), baseFn m
            = ∑ m ∈ Finset.range (k + 1), f (m + 1) :=
        Finset.sum_congr rfl (fun m _ => hbaseFn_f m)
      have hf0_bound : ‖f 0‖ ≤ C_prev * (Real.sqrt (((1 + j : ℕ) : ℝ) + 1) / j) := by
        have h1 := hprev_1
        simp only [f, Finset.sum_range_one] at h1
        exact h1
      calc
        ‖∑ m ∈ Finset.range (k + 1), baseFn m‖
          = ‖∑ m ∈ Finset.range (k + 1), f (m + 1)‖ := by rw [hbaseFn_sum]
        _ = ‖(∑ n ∈ Finset.range (k + 2), f n) - f 0‖ := by
                rw [hprefixSplit]; ring_nf
        _ ≤ ‖∑ n ∈ Finset.range (k + 2), f n‖ + ‖f 0‖ := norm_sub_le _ _
        _ ≤ C_prev * (Real.sqrt (((k + 2 + j : ℕ) : ℝ) + 1) / j)
              + C_prev * (Real.sqrt (((1 + j : ℕ) : ℝ) + 1) / j) :=
                    add_le_add hprev_k2 hf0_bound
        _ ≤ C_prev * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / j)
              + C_prev * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / j) := by
                    gcongr
        _ = C0 := by unfold C0; ring
    have hpartial_re : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aRe m| ≤ C0 := by
      intro k hk
      calc
        |∑ m ∈ Finset.range (k + 1), aRe m|
            = |(∑ m ∈ Finset.range (k + 1), baseFn m).re| := by simp [aRe]
        _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_re_le_norm _
        _ ≤ C0 := hpartial_norm k hk
    have hpartial_im : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aIm m| ≤ C0 := by
      intro k hk
      calc
        |∑ m ∈ Finset.range (k + 1), aIm m|
            = |(∑ m ∈ Finset.range (k + 1), baseFn m).im| := by simp [aIm]
        _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_im_le_norm _
        _ ≤ C0 := hpartial_norm k hk
    have hb_nonneg : ∀ k ≤ n0, 0 ≤ b k := by
      intro k hk
      exact atkinsonUpperBoundaryStepCoeff_inv_nonneg (k + J) j (by omega)
    have hb_anti : ∀ k < n0, b (k + 1) ≤ b k := by
      intro k hk
      exact atkinsonUpperBoundaryStepCoeff_inv_antitone j (by omega) (by omega : k + J ≤ k + 1 + J)
    have hb_one : b 0 ≤ 1 := by
      simpa [b, J] using atkinsonUpperBoundaryStepCoeff_inv_le_one J j (by omega)
    have hb0_nonneg : 0 ≤ b 0 := hb_nonneg 0 (by omega)
    have hC0_nonneg : 0 ≤ C0 := by
      unfold C0; positivity
    have hsum_re :
        (∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re
          =
        ∑ k ∈ Finset.range (n0 + 1), aRe k * b k := by
          simp [aRe, b, baseFn, mul_comm, mul_left_comm, mul_assoc]
    have hsum_im :
        (∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im
          =
        ∑ k ∈ Finset.range (n0 + 1), aIm k * b k := by
          simp [aIm, b, baseFn, mul_comm, mul_left_comm, mul_assoc]
    have hre :
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
          ≤ C0 := by
      have habel :=
        AbelSummation.abel_summation_bound aRe b n0 C0 hpartial_re hb_nonneg hb_anti
      have habel' :
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
            ≤ C0 * b 0 := by
        simpa [hsum_re] using habel
      exact habel'.trans (by nlinarith [hC0_nonneg, hb0_nonneg, hb_one])
    have him :
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im|
          ≤ C0 := by
      have habel :=
        AbelSummation.abel_summation_bound aIm b n0 C0 hpartial_im hb_nonneg hb_anti
      have habel' :
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im|
            ≤ C0 * b 0 := by
        simpa [hsum_im] using habel
      exact habel'.trans (by nlinarith [hC0_nonneg, hb0_nonneg, hb_one])
    have hnorm :
        ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖
          ≤ 2 * C0 := by
      calc
        ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖
            ≤
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
            +
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| := by
              exact Complex.norm_le_abs_re_add_abs_im _
        _ ≤ C0 + C0 := add_le_add hre him
        _ = 2 * C0 := by ring
    -- Scale conversion: sqrt/(j) ≤ 2*sqrt/(j+1) for j ≥ 2.
    have hscale :
        4 * C_prev * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / j)
          ≤ 8 * C_prev * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)) := by
      have hj_pos : (0 : ℝ) < j := by positivity
      have hj1_pos : (0 : ℝ) < ((j : ℝ) + 1) := by positivity
      have hsqrt_nonneg : 0 ≤ Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) := by positivity
      have htwoj : ((j + 1 : ℕ) : ℝ) ≤ 2 * (j : ℝ) := by
        exact_mod_cast (show j + 1 ≤ 2 * j by omega)
      have hfrac : (1 : ℝ) / j ≤ (2 : ℝ) / (j + 1 : ℝ) := by
        rw [div_le_div_iff₀ hj_pos hj1_pos]
        simpa using htwoj
      have hsqrt_div :
          Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / j
            ≤ 2 * Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / ((j : ℝ) + 1) := by
        calc
          Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / j
              = Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) * (1 / j) := by ring
          _ ≤ Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) * (2 / ((j : ℝ) + 1)) := by
                exact mul_le_mul_of_nonneg_left hfrac hsqrt_nonneg
          _ = 2 * Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / ((j : ℝ) + 1) := by ring
      calc
        4 * C_prev * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / j)
            = 4 * C_prev * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / j) := rfl
        _ ≤ 4 * C_prev *
              (2 * Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / ((j : ℝ) + 1)) := by
                gcongr
        _ = 8 * C_prev * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / ((j : ℝ) + 1)) := by
                ring
        _ = 8 * C_prev * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)) := by
                push_cast; ring
    calc
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase
                (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖
        = ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖ := by
              simpa [hn0, b, baseFn, J, Nat.add_assoc, add_left_comm, add_comm]
      _ ≤ 2 * C0 := hnorm
      _ = 4 * C_prev * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / j) := by
              unfold C0; ring
      _ ≤ 8 * C_prev * (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)) := hscale

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
private theorem atkinson_largeShiftPrefix_succ_htail_hypothesis_gamma_eight :
    ∀ C_prev : ℝ, 0 < C_prev →
    ∀ j : ℕ, 2 ≤ j →
      (∀ N : ℕ,
        ‖∑ k ∈ Finset.range N,
            ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) j)‖
          ≤ C_prev * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)) →
      ∀ N : ℕ,
        ‖∑ k ∈ Finset.range N,
            ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
              ((((1 / atkinsonShiftedRelativePhase
                  (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
                atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖
          ≤ 8 * C_prev *
              (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)) := by
  intro C_prev hC_prev j hj hprev N
  exact atkinson_largeShiftPrefix_succ_htail_of_nextShift_and_smallShift
    C_prev hC_prev j hj hprev N

/-- Leaf hypothesis for the shifted inverse-phase-core prefix bound at large
shifts (`j ≥ 3`).  This is NOT the same as the old stronger class
`AtkinsonShiftedInversePhaseCorePrefixBoundHyp` (which covered all `j ≥ 1`) —
it only covers `j ≥ 3`.

The intended proof path is:
`AtkinsonSmallShiftPrefixBoundHyp`
→ `AtkinsonLargeShiftPrefixBoundHyp` via the explicit successor bridge below,
using the predecessor-tail and boundary-row wrappers built from
`atkinsonShiftedInversePhaseCorePrefix_succ_eq`.
That reduction is a genuine analytic theorem and is recorded separately. -/
class AtkinsonLargeShiftPrefixBoundHyp : Prop where
  bound :
    ∃ C_large > 0, ∀ j : ℕ, 3 ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) j)‖
        ≤ C_large * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)

private theorem atkinson_smallShiftPrefixBound_of_shiftedInversePhaseCorePrefix
    [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] :
    AtkinsonSmallShiftPrefixBoundHyp := by
  constructor
  obtain ⟨C, hC_pos, hC⟩ := AtkinsonShiftedInversePhaseCorePrefixBoundHyp.bound
  refine ⟨C, hC_pos, ?_⟩
  intro j hj hj2 N
  exact hC j hj N

private theorem atkinson_largeShiftPrefixBound_of_shiftedInversePhaseCorePrefix
    [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] :
    AtkinsonLargeShiftPrefixBoundHyp := by
  constructor
  obtain ⟨C, hC_pos, hC⟩ := AtkinsonShiftedInversePhaseCorePrefixBoundHyp.bound
  refine ⟨C, hC_pos, ?_⟩
  intro j hj N
  exact hC j (by omega) N

instance [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] :
    AtkinsonSmallShiftPrefixBoundHyp :=
  atkinson_smallShiftPrefixBound_of_shiftedInversePhaseCorePrefix

instance [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] :
    AtkinsonLargeShiftPrefixBoundHyp :=
  atkinson_largeShiftPrefixBound_of_shiftedInversePhaseCorePrefix

/- Uniform induction package from the honest next-shift error surface plus the
small-shift leaf package.

This theorem isolates the exact induction wrapper we need once the local
one-step theorem is available: if a single constant `C` propagates from shift
`j` to shift `j + 1` for every `j ≥ 2`, then the `j = 2` small-shift leaf
closes all large shifts `j ≥ 3`. -/
omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
private theorem atkinson_largeShiftPrefixBound_atomic_of_nextShift
    [AtkinsonSmallShiftPrefixBoundHyp]
    (γ : ℝ)
    (hγ_lt_one : γ < 1)
    (hbdryRow :
      ∃ C_bdry > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
        ‖∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)‖
          ≤ C_bdry * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j))
    (htail :
      ∀ C_prev : ℝ, 0 < C_prev →
      ∀ j : ℕ, 2 ≤ j →
        (∀ N : ℕ,
          ‖∑ k ∈ Finset.range N,
              ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
                atkinsonShiftedSingleBoundaryCore (k + j) j)‖
            ≤ C_prev * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)) →
        ∀ N : ℕ,
          ‖∑ k ∈ Finset.range N,
              ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
                ((((1 / atkinsonShiftedRelativePhase
                    (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
                  atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖
            ≤ γ * C_prev *
                (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1)))
    :
    AtkinsonLargeShiftPrefixBoundHyp := by
  obtain ⟨C_small, hC_small_pos, hC_small⟩ := AtkinsonSmallShiftPrefixBoundHyp.bound
  obtain ⟨C_bdry, hC_bdry_pos, hsucc'⟩ :=
    atkinson_largeShiftPrefix_succ_affine_step γ hbdryRow htail
  let C_large : ℝ := max C_small (C_bdry / (1 - γ))
  have hC_large_pos : 0 < C_large := by
    exact lt_of_lt_of_le hC_small_pos (le_max_left _ _)
  have hfixed : γ * C_large + C_bdry ≤ C_large := by
    have h1mγ_pos : 0 < 1 - γ := sub_pos.mpr hγ_lt_one
    have hquot_le : C_bdry / (1 - γ) ≤ C_large := le_max_right _ _
    have hbdry_le : C_bdry ≤ C_large * (1 - γ) := by
      have hmul :=
        mul_le_mul_of_nonneg_right hquot_le (le_of_lt h1mγ_pos)
      have hcancel : C_bdry / (1 - γ) * (1 - γ) = C_bdry := by
        field_simp [h1mγ_pos.ne']
      simpa [hcancel] using hmul
    nlinarith [hbdry_le]
  have hind :
      ∀ j : ℕ, 2 ≤ j → ∀ N : ℕ,
        ‖∑ k ∈ Finset.range N,
            ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) j)‖
          ≤ C_large * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
    intro j hj
    refine Nat.le_induction ?_ ?_ j hj
    · intro N
      calc
        ‖∑ k ∈ Finset.range N,
            ((((1 / atkinsonShiftedRelativePhase (k + (2 + 2)) 2 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + 2) 2)‖
          ≤ C_small * Real.log (↑(2 : ℕ) + 1) *
              (Real.sqrt (((N + 2 : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)) := by
              exact hC_small 2 (by omega) (by omega) N
        _ ≤ C_large * Real.log (↑(2 : ℕ) + 1) *
              (Real.sqrt (((N + 2 : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)) := by
              gcongr
              exact le_max_left _ _
    · intro j hj ih N
      have hlog_j_pos : 0 < Real.log (↑j + 1) := by
        rw [Real.log_pos_iff (by positivity)]
        exact_mod_cast show 1 < j + 1 by omega
      have hnext :=
        hsucc' (C_large * Real.log (↑j + 1)) (mul_pos hC_large_pos hlog_j_pos)
          j hj (fun N' => ih N') N
      have htarget_nonneg :
          0 ≤ Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / ((j : ℝ) + 1) := by
        simpa [Nat.cast_add]
          using
            (show
              0 ≤ Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (((j + 1 : ℕ) : ℝ)) by
                positivity)
      -- hnext : ... ≤ (γ * (C_large * log(j+1)) + C_bdry * log(j+1)) * (sqrt/(j+1))
      --       = (γ * C_large + C_bdry) * log(j+1) * (sqrt/(j+1))
      have hstep :
        ‖∑ k ∈ Finset.range N,
            ((((1 / atkinsonShiftedRelativePhase
                (k + ((j + 1) + (j + 1))) (j + 1) : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + (j + 1)) (j + 1))‖
          ≤ (γ * C_large + C_bdry) * Real.log (↑j + 1) *
              (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / ((j : ℝ) + 1)) := by
              have h : (γ * (C_large * Real.log (↑j + 1)) + C_bdry * Real.log (↑j + 1))
                  = (γ * C_large + C_bdry) * Real.log (↑j + 1) := by ring
              simpa [Nat.cast_add, h] using hnext
      have hstep' :
          ‖∑ k ∈ Finset.range N,
              ((((1 / atkinsonShiftedRelativePhase
                  (k + ((j + 1) + (j + 1))) (j + 1) : ℝ) : ℂ)) *
                atkinsonShiftedSingleBoundaryCore (k + (j + 1)) (j + 1))‖
            ≤ C_large * Real.log (↑j + 1) *
                (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / ((j : ℝ) + 1)) := by
        calc _ ≤ (γ * C_large + C_bdry) * Real.log (↑j + 1) *
                    (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / ((j : ℝ) + 1)) := hstep
          _ ≤ C_large * Real.log (↑j + 1) *
                  (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / ((j : ℝ) + 1)) := by
              gcongr
      have hlog_mono : Real.log (↑j + 1) ≤ Real.log ((↑j : ℝ) + 1 + 1) := by
        exact Real.log_le_log (by positivity) (by linarith)
      calc _ ≤ C_large * Real.log (↑j + 1) *
                  (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / ((j : ℝ) + 1)) := hstep'
        _ ≤ C_large * Real.log ((↑j : ℝ) + 1 + 1) *
                (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / ((j : ℝ) + 1)) := by
            gcongr
        _ = C_large * Real.log (↑(j + 1 : ℕ) + 1) *
                (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (↑(j + 1 : ℕ))) := by
            push_cast; ring_nf
  refine ⟨C_large, hC_large_pos, ?_⟩
  intro j hj N
  exact hind j (by omega) N

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
private theorem atkinson_inversePhaseCorePrefix_bound_large_j_of_contracting_nextShift
    [AtkinsonSmallShiftPrefixBoundHyp]
    (γ : ℝ) (hγ_lt_one : γ < 1)
    (hbdryRow :
      ∃ C_bdry > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
        ‖∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)‖
          ≤ C_bdry * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j))
    (htail :
      ∀ C_prev : ℝ, 0 < C_prev →
      ∀ j : ℕ, 2 ≤ j →
        (∀ N : ℕ,
          ‖∑ k ∈ Finset.range N,
              ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
                atkinsonShiftedSingleBoundaryCore (k + j) j)‖
            ≤ C_prev * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)) →
        ∀ N : ℕ,
          ‖∑ k ∈ Finset.range N,
              ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
                ((((1 / atkinsonShiftedRelativePhase
                    (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
                  atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖
            ≤ γ * C_prev *
                (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1))) :
    ∃ C > 0, ∀ j : ℕ, 3 ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) j)‖
        ≤ C * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) :=
  (atkinson_largeShiftPrefixBound_atomic_of_nextShift γ hγ_lt_one hbdryRow htail).bound

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
private theorem atkinson_kernelWeightedIcoTail_abel_bound_atomic
    [AtkinsonWeightedIcoTailBoundHyp] :
    ∃ C_err > 0, ∀ j : ℕ, 1 ≤ j → ∀ r : ℕ, 1 ≤ r → r + 2 ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
            ((((atkinsonUpperBoundaryStepCoeff (k + j) (r + 1) - 1 : ℝ) : ℂ)) *
              ((((1 / atkinsonShiftedRelativePhase (k + (j + (r + 1))) (r + 1) : ℝ) : ℂ)) *
                atkinsonShiftedSingleBoundaryCore (k + j) (r + 1))))‖
        ≤ C_err * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C, hC, hweighted⟩ := atkinson_weightedIcoTail_reindexed_tail_bound
  refine ⟨4 * C, by positivity, ?_⟩
  intro j hj r hr hrj N
  have hr1_pos : 1 ≤ r + 1 := by
    omega
  have hr1j_le : r + 1 ≤ j := by
    omega
  by_cases hN : N = 0
  · have hnonneg :
        0 ≤ (4 * C) * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
      apply mul_nonneg
      · apply mul_nonneg; positivity
        exact Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)
      · positivity
    simpa [hN] using hnonneg
  · obtain ⟨n0, hn0 : N = n0 + 1⟩ := Nat.exists_eq_succ_of_ne_zero hN
    let baseFn : ℕ → ℂ := fun k =>
      ((((atkinsonUpperBoundaryStepCoeff (k + j) (r + 1) - 1 : ℝ) : ℂ)) *
        ((((1 / atkinsonShiftedRelativePhase (k + (j + (r + 1))) (r + 1) : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + j) (r + 1)))
    let C0 : ℝ := C * Real.log (↑(r + 1) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / (r + 1))
    let aRe : ℕ → ℝ := fun k => (baseFn k).re
    let aIm : ℕ → ℝ := fun k => (baseFn k).im
    let b : ℕ → ℝ := fun k => atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1)
    have hpartial_re : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aRe m| ≤ C0 := by
      intro k hk
      have hbound := hweighted j hj (r + 1) hr1_pos hrj (k + 1)
      have htarget_k :
          Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / (r + 1)
            ≤ Real.sqrt (((N + j : ℕ) : ℝ) + 1) / (r + 1) := by
        exact div_le_div_of_nonneg_right
          (Real.sqrt_le_sqrt (by
            exact_mod_cast (by omega : (k + 1 + j) + 1 ≤ (N + j) + 1)))
          (by positivity : (0 : ℝ) ≤ r + 1)
      calc
        |∑ m ∈ Finset.range (k + 1), aRe m|
            = |(∑ m ∈ Finset.range (k + 1), baseFn m).re| := by
                simp [aRe]
        _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_re_le_norm _
        _ ≤ C * Real.log (↑(r + 1) + 1) * (Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / (r + 1)) := by
              simpa [baseFn, Nat.add_assoc, add_left_comm, add_comm] using hbound
        _ ≤ C * Real.log (↑(r + 1) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / (r + 1)) := by
              exact mul_le_mul_of_nonneg_left htarget_k
                (mul_nonneg (le_of_lt hC)
                  (Real.log_nonneg (by exact_mod_cast show 1 ≤ (r + 1 : ℕ) + 1 by omega)))
        _ = C0 := by
              rfl
    have hpartial_im : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aIm m| ≤ C0 := by
      intro k hk
      have hbound := hweighted j hj (r + 1) hr1_pos hrj (k + 1)
      have htarget_k :
          Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / (r + 1)
            ≤ Real.sqrt (((N + j : ℕ) : ℝ) + 1) / (r + 1) := by
        exact div_le_div_of_nonneg_right
          (Real.sqrt_le_sqrt (by
            exact_mod_cast (by omega : (k + 1 + j) + 1 ≤ (N + j) + 1)))
          (by positivity : (0 : ℝ) ≤ r + 1)
      calc
        |∑ m ∈ Finset.range (k + 1), aIm m|
            = |(∑ m ∈ Finset.range (k + 1), baseFn m).im| := by
                simp [aIm]
        _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_im_le_norm _
        _ ≤ C * Real.log (↑(r + 1) + 1) * (Real.sqrt (((k + 1 + j : ℕ) : ℝ) + 1) / (r + 1)) := by
              simpa [baseFn, Nat.add_assoc, add_left_comm, add_comm] using hbound
        _ ≤ C * Real.log (↑(r + 1) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / (r + 1)) := by
              exact mul_le_mul_of_nonneg_left htarget_k
                (mul_nonneg (le_of_lt hC)
                  (Real.log_nonneg (by exact_mod_cast show 1 ≤ (r + 1 : ℕ) + 1 by omega)))
        _ = C0 := by
              rfl
    have hb_nonneg : ∀ k ≤ n0, 0 ≤ b k := by
      intro k hk
      simpa [b, Nat.add_assoc, add_left_comm, add_comm] using
        atkinsonLowerBoundaryShiftKernel_nonneg (k + j) j (r + 1) hr1_pos hr1j_le
    have hb_anti : ∀ k < n0, b (k + 1) ≤ b k := by
      intro k hk
      simpa [b, Nat.add_assoc, add_left_comm, add_comm] using
        (atkinsonLowerBoundaryShiftKernel_antitone j (r + 1) hr1_pos hr1j_le
          (by omega : k + j ≤ k + 1 + j))
    have hb_head : b 0 ≤ 2 * (r + 1) / j := by
      simpa [b, Nat.add_assoc, add_left_comm, add_comm] using
        atkinsonLowerBoundaryShiftKernel_le_two_mul_div j j (r + 1) hr1_pos hr1j_le le_rfl
    have hsum_re :
        (∑ k ∈ Finset.range (n0 + 1),
            ((((b k : ℝ) : ℂ)) * baseFn k)).re
          =
        ∑ k ∈ Finset.range (n0 + 1), aRe k * b k := by
          simp [aRe, b, baseFn, mul_comm, mul_left_comm, mul_assoc]
    have hsum_im :
        (∑ k ∈ Finset.range (n0 + 1),
            ((((b k : ℝ) : ℂ)) * baseFn k)).im
          =
        ∑ k ∈ Finset.range (n0 + 1), aIm k * b k := by
          simp [aIm, b, baseFn, mul_comm, mul_left_comm, mul_assoc]
    have hlog_r_nonneg : 0 ≤ Real.log (↑(r + 1) + 1) :=
      Real.log_nonneg (by exact_mod_cast show 1 ≤ (r + 1 : ℕ) + 1 by omega)
    have hre :
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
          ≤ (2 * C) * Real.log (↑(r + 1) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
      have habel :=
        AbelSummation.abel_summation_bound aRe b n0 C0 hpartial_re hb_nonneg hb_anti
      calc
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
            = |∑ k ∈ Finset.range (n0 + 1), aRe k * b k| := by
                rw [hsum_re]
        _ ≤ C0 * b 0 := habel
        _ ≤ C0 * (2 * (r + 1) / j) := by
              gcongr
        _ = (2 * C) * Real.log (↑(r + 1) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
              unfold C0
              field_simp [show ((r + 1 : ℕ) : ℝ) ≠ 0 by positivity, show (j : ℝ) ≠ 0 by positivity]
    have him :
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im|
          ≤ (2 * C) * Real.log (↑(r + 1) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
      have habel :=
        AbelSummation.abel_summation_bound aIm b n0 C0 hpartial_im hb_nonneg hb_anti
      calc
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im|
            = |∑ k ∈ Finset.range (n0 + 1), aIm k * b k| := by
                rw [hsum_im]
        _ ≤ C0 * b 0 := habel
        _ ≤ C0 * (2 * (r + 1) / j) := by
              gcongr
        _ = (2 * C) * Real.log (↑(r + 1) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
              unfold C0
              field_simp [show ((r + 1 : ℕ) : ℝ) ≠ 0 by positivity, show (j : ℝ) ≠ 0 by positivity]
    have hnorm :
        ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖
          ≤ (4 * C) * Real.log (↑(r + 1) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
      calc
        ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖
            ≤
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
            +
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| := by
              exact Complex.norm_le_abs_re_add_abs_im _
        _ ≤ (2 * C) * Real.log (↑(r + 1) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)
              +
            (2 * C) * Real.log (↑(r + 1) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
                exact add_le_add hre him
        _ = (4 * C) * Real.log (↑(r + 1) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
              ring
    calc
      ‖∑ k ∈ Finset.range N,
          ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
            ((((atkinsonUpperBoundaryStepCoeff (k + j) (r + 1) - 1 : ℝ) : ℂ)) *
              ((((1 / atkinsonShiftedRelativePhase (k + (j + (r + 1))) (r + 1) : ℝ) : ℂ)) *
                atkinsonShiftedSingleBoundaryCore (k + j) (r + 1))))‖
        =
      ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖ := by
            simpa [hn0, b, baseFn, Nat.add_assoc, add_left_comm, add_comm]
      _ ≤ (4 * C) * Real.log (↑(r + 1) + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := hnorm
      _ ≤ (4 * C) * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
            gcongr

/-!
Explicit name for the exact shifted `r + 1` kernel-weighted Abel bridge.
This is just the class field above, but having a theorem name makes the
consumer-rewire target easier to reference from later reductions.
-/
omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
private theorem atkinson_shiftedInversePhaseCorePrefix_bound_of_splitShiftLeaves
    [AtkinsonSmallShiftPrefixBoundHyp]
    [AtkinsonLargeShiftPrefixBoundHyp] :
    AtkinsonShiftedInversePhaseCorePrefixBoundHyp := by
  constructor
  obtain ⟨C_small, hC_small_pos, hC_small⟩ := AtkinsonSmallShiftPrefixBoundHyp.bound
  obtain ⟨C_large, hC_large_pos, hC_large⟩ := AtkinsonLargeShiftPrefixBoundHyp.bound
  refine ⟨C_small + C_large, by positivity, ?_⟩
  intro j hj N
  by_cases hj2 : j ≤ 2
  · calc
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) j)‖
        ≤ C_small * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) :=
            hC_small j hj hj2 N
      _ ≤ (C_small + C_large) * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega))
            linarith

  · push_neg at hj2
    calc
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) j)‖
        ≤ C_large * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) :=
            hC_large j hj2 N
      _ ≤ (C_small + C_large) * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega))
            linarith

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
instance [AtkinsonSmallShiftPrefixBoundHyp]
    [AtkinsonLargeShiftPrefixBoundHyp] :
    AtkinsonShiftedInversePhaseCorePrefixBoundHyp :=
  atkinson_shiftedInversePhaseCorePrefix_bound_of_splitShiftLeaves

/-- Explicit name for the exact shifted `r + 1` kernel-weighted Abel bridge.
This is just the class field above, but having a theorem name makes the
consumer-rewire target easier to reference from later reductions. -/
private theorem atkinson_kernelWeightedIcoTail_abel_bound_shifted_rplus1
    [AtkinsonWeightedIcoTailBoundHyp] :
    AtkinsonKernelWeightedIcoTailAbelBoundHyp :=
  ⟨atkinson_kernelWeightedIcoTail_abel_bound_atomic⟩

instance [AtkinsonWeightedIcoTailBoundHyp] : AtkinsonKernelWeightedIcoTailAbelBoundHyp :=
  ⟨atkinson_kernelWeightedIcoTail_abel_bound_atomic⟩

variable [AtkinsonSmallShiftPrefixBoundHyp]
variable [AtkinsonLargeShiftPrefixBoundHyp]

/-!
Consumer-native lower-boundary row surface. This is the exact hypothesis
that the downstream boundary chain consumes, stated in the native
`mode × primitive` coordinates rather than the internal shifted prefix form.
-/
class AtkinsonLowerBoundaryRowBoundHyp : Prop where
  bound :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then
            atkinsonWeightedResonantBlockMode (n + j) 0 *
              atkinsonShiftedSinglePrimitive (n + j) j 0
          else 0)‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j)

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
instance [AtkinsonSmallShiftPrefixBoundHyp]
    [AtkinsonLargeShiftPrefixBoundHyp] :
    AtkinsonLowerBoundaryRowBoundHyp :=
  ⟨atkinson_large_modes_complete_resonant_packet_row_lower_boundary_sum_bound_atomic_of_shifted_inverse_phase_core
    (atkinson_shiftedInversePhaseCorePrefix_bound_of_splitShiftLeaves.bound)⟩

private theorem atkinson_large_modes_complete_resonant_packet_row_lower_boundary_sum_bound_atomic
    [AtkinsonLowerBoundaryRowBoundHyp] :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then
            atkinsonWeightedResonantBlockMode (n + j) 0 *
              atkinsonShiftedSinglePrimitive (n + j) j 0
          else 0)‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) :=
  AtkinsonLowerBoundaryRowBoundHyp.bound

private theorem atkinson_large_modes_complete_resonant_packet_row_upper_weighted_lower_sum_bound_atomic :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      ‖∑ n ∈ Finset.range M,
          (if j + 1 ≤ n then
            ((((2 - atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) *
              (atkinsonWeightedResonantBlockMode (n + (j + 1)) 0 *
                atkinsonShiftedSinglePrimitive (n + (j + 1)) (j + 1) 0)
          else 0)‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨Cl, hCl, hlower⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_lower_boundary_sum_bound_atomic
  refine ⟨4 * Real.sqrt 2 * Cl, by positivity, ?_⟩
  intro j hj M
  let J : ℕ := j + 1
  let coeff : ℕ → ℝ := fun n => atkinsonUpperBoundaryWeightedCoeff n j
  let baseFn : ℕ → ℂ := fun n =>
    atkinsonWeightedResonantBlockMode (n + J) 0 *
      atkinsonShiftedSinglePrimitive (n + J) J 0
  let target : ℝ := Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j
  change
    ‖∑ n ∈ Finset.range M,
        (if J ≤ n then ((((coeff n : ℝ) : ℂ)) * baseFn n) else 0)‖
      ≤ (4 * Real.sqrt 2 * Cl) * Real.log (↑j + 1) * target
  by_cases hJM : J ≤ M
  · let N : ℕ := M - J
    have hsum :
        ∑ n ∈ Finset.range M,
            (if J ≤ n then ((((coeff n : ℝ) : ℂ)) * baseFn n) else 0)
          =
        ∑ k ∈ Finset.range N, ((((coeff (k + J) : ℝ) : ℂ)) * baseFn (k + J)) := by
      have hprefix_zero :
          ∑ n ∈ Finset.range J,
              (if J ≤ n then ((((coeff n : ℝ) : ℂ)) * baseFn n) else 0)
            = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        simp [(Finset.mem_range.mp hn).not_ge]
      calc
        ∑ n ∈ Finset.range M,
            (if J ≤ n then ((((coeff n : ℝ) : ℂ)) * baseFn n) else 0)
            =
          (∑ n ∈ Finset.range J,
              (if J ≤ n then ((((coeff n : ℝ) : ℂ)) * baseFn n) else 0))
            +
          ∑ n ∈ Finset.Ico J M,
              (if J ≤ n then ((((coeff n : ℝ) : ℂ)) * baseFn n) else 0) := by
                simpa using
                  (Finset.sum_range_add_sum_Ico
                    (fun n => if J ≤ n then ((((coeff n : ℝ) : ℂ)) * baseFn n) else 0)
                    hJM).symm
        _ = ∑ n ∈ Finset.Ico J M,
              (if J ≤ n then ((((coeff n : ℝ) : ℂ)) * baseFn n) else 0) := by
                rw [hprefix_zero, zero_add]
        _ =
          ∑ n ∈ Finset.Ico J M, ((((coeff n : ℝ) : ℂ)) * baseFn n) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simp [(Finset.mem_Ico.mp hn).1]
        _ = ∑ k ∈ Finset.range N, ((((coeff (k + J) : ℝ) : ℂ)) * baseFn (k + J)) := by
            rw [Finset.sum_Ico_eq_sum_range]
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp [N, add_assoc, add_left_comm, add_comm]
    have htarget_J :
        Real.sqrt (((M + J : ℕ) : ℝ) + 1) / J ≤ Real.sqrt 2 * target := by
      have hle : (((M + J : ℕ) : ℝ) + 1) ≤ 2 * ((((M + j : ℕ) : ℝ) + 1) : ℝ) := by
        exact_mod_cast (by
          dsimp [J]
          omega : M + J + 1 ≤ 2 * (M + j + 1))
      calc
        Real.sqrt (((M + J : ℕ) : ℝ) + 1) / J
            ≤ Real.sqrt (2 * ((((M + j : ℕ) : ℝ) + 1))) / J := by
                exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hle)
                  (by positivity : (0 : ℝ) ≤ J)
        _ = (Real.sqrt 2 * Real.sqrt ((((M + j : ℕ) : ℝ) + 1))) / J := by
              have hsqrt_eq :
                  Real.sqrt (2 * ((((M + j : ℕ) : ℝ) + 1)))
                    = Real.sqrt 2 * Real.sqrt ((((M + j : ℕ) : ℝ) + 1)) := by
                      simpa using
                        (Real.sqrt_mul
                          (by positivity : 0 ≤ (2 : ℝ))
                          (by positivity : 0 ≤ ((((M + j : ℕ) : ℝ) + 1))))
              rw [hsqrt_eq]
        _ ≤ (Real.sqrt 2 * Real.sqrt ((((M + j : ℕ) : ℝ) + 1))) / j := by
              exact div_le_div_of_nonneg_left
                (show 0 ≤ Real.sqrt 2 * Real.sqrt ((((M + j : ℕ) : ℝ) + 1)) by positivity)
                (show (0 : ℝ) < j by positivity)
                (by
                  have hJgej : (j : ℝ) ≤ J := by
                    exact_mod_cast Nat.le_succ j
                  simpa [J] using hJgej)
        _ = Real.sqrt 2 * target := by
              dsimp [target]
              ring
    have hpartial_eq (K : ℕ) :
        ∑ k ∈ Finset.range K, baseFn (k + J)
          =
        ∑ n ∈ Finset.range (J + K), (if J ≤ n then baseFn n else 0) := by
      have hprefix_zero :
          ∑ n ∈ Finset.range J, (if J ≤ n then baseFn n else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        simp [(Finset.mem_range.mp hn).not_ge]
      calc
        ∑ k ∈ Finset.range K, baseFn (k + J)
            = ∑ n ∈ Finset.Ico J (J + K), baseFn n := by
                simpa [Nat.add_sub_cancel_left, add_assoc, add_left_comm, add_comm] using
                  (Finset.sum_Ico_eq_sum_range (f := baseFn) (m := J) (n := J + K)).symm
        _ = ∑ n ∈ Finset.Ico J (J + K), (if J ≤ n then baseFn n else 0) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              simp [(Finset.mem_Ico.mp hn).1]
        _ =
          (∑ n ∈ Finset.range J, (if J ≤ n then baseFn n else 0))
            + ∑ n ∈ Finset.Ico J (J + K), (if J ≤ n then baseFn n else 0) := by
                rw [hprefix_zero, zero_add]
        _ = ∑ n ∈ Finset.range (J + K), (if J ≤ n then baseFn n else 0) := by
              simpa using
                (Finset.sum_range_add_sum_Ico
                  (fun n => if J ≤ n then baseFn n else 0)
                  (Nat.le_add_right J K))
    have hlog_bound : Real.log (↑J + 1) ≤ 2 * Real.log (↑j + 1) := by
      have hjsq : (↑J + 1 : ℝ) ≤ (↑j + 1) ^ 2 := by
        simp only [J]
        push_cast
        have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
        nlinarith [sq_nonneg (j : ℝ)]
      calc
        Real.log (↑J + 1) ≤ Real.log ((↑j + 1) ^ 2) := by
              exact Real.log_le_log (by positivity) hjsq
        _ = 2 * Real.log (↑j + 1) := by
              rw [Real.log_pow]
              ring
    have hpartial_bound (K : ℕ) (hK : K ≤ N) :
        ‖∑ k ∈ Finset.range K, baseFn (k + J)‖ ≤ 2 * Real.sqrt 2 * Cl * Real.log (↑j + 1) * target := by
      have hJK_le_M : J + K ≤ M := by
        dsimp [N] at hK
        omega
      have hraw :
          ‖∑ n ∈ Finset.range (J + K), (if J ≤ n then baseFn n else 0)‖
            ≤ Cl * Real.log (↑J + 1) * (Real.sqrt ((((J + K) + J : ℕ) : ℝ) + 1) / J) := by
              simpa [baseFn, J, Nat.add_assoc, add_left_comm, add_comm] using
                hlower J (Nat.succ_le_succ (Nat.zero_le j)) (J + K)
      have htarget_K :
          Real.sqrt ((((J + K) + J : ℕ) : ℝ) + 1) / J ≤ Real.sqrt 2 * target := by
        have hle :
            ((((J + K) + J : ℕ) : ℝ) + 1) ≤ (((M + J : ℕ) : ℝ) + 1) := by
          exact_mod_cast (by omega : (J + K) + J + 1 ≤ M + J + 1)
        calc
          Real.sqrt ((((J + K) + J : ℕ) : ℝ) + 1) / J
              ≤ Real.sqrt (((M + J : ℕ) : ℝ) + 1) / J := by
                  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hle)
                    (by positivity : (0 : ℝ) ≤ J)
          _ ≤ Real.sqrt 2 * target := htarget_J
      calc
        ‖∑ k ∈ Finset.range K, baseFn (k + J)‖
            = ‖∑ n ∈ Finset.range (J + K), (if J ≤ n then baseFn n else 0)‖ := by
                rw [hpartial_eq K]
        _ ≤ Cl * Real.log (↑J + 1) * (Real.sqrt ((((J + K) + J : ℕ) : ℝ) + 1) / J) := hraw
        _ ≤ Cl * Real.log (↑J + 1) * (Real.sqrt 2 * target) := by
              have hlog_nn : 0 ≤ Real.log (↑J + 1) :=
                Real.log_nonneg (by exact_mod_cast show 1 ≤ J + 1 by omega)
              exact mul_le_mul_of_nonneg_left htarget_K (mul_nonneg hCl.le hlog_nn)
        _ ≤ Cl * (2 * Real.log (↑j + 1)) * (Real.sqrt 2 * target) := by
              have hsqrt_target_nn : 0 ≤ Real.sqrt 2 * target := by positivity
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hlog_bound hCl.le) hsqrt_target_nn
        _ = 2 * Real.sqrt 2 * Cl * Real.log (↑j + 1) * target := by ring
    by_cases hN : N = 0
    · have hM_eq : M = J := by
        dsimp [N] at hN
        omega
      have hzero :
          ∑ n ∈ Finset.range M,
            (if J ≤ n then ((((coeff n : ℝ) : ℂ)) * baseFn n) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        have hnlt : n < J := by simpa [hM_eq] using Finset.mem_range.mp hn
        simp [hnlt.not_ge]
      have hnonneg : 0 ≤ (4 * Real.sqrt 2 * Cl) * Real.log (↑j + 1) * target := by
        apply mul_nonneg
        apply mul_nonneg
        · positivity
        · exact Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)
        · positivity
      simpa [hzero] using hnonneg
    · obtain ⟨n0, hn0 : N = n0 + 1⟩ := Nat.exists_eq_succ_of_ne_zero hN
      let C0 : ℝ := 2 * Real.sqrt 2 * Cl * Real.log (↑j + 1) * target
      let aRe : ℕ → ℝ := fun k => (baseFn (k + J)).re
      let aIm : ℕ → ℝ := fun k => (baseFn (k + J)).im
      let b : ℕ → ℝ := fun k => coeff (k + J)
      have hpartial_re : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aRe m| ≤ C0 := by
        intro k hk
        have hbound := hpartial_bound (k + 1) (by
          rw [hn0]
          omega : k + 1 ≤ N)
        calc
          |∑ m ∈ Finset.range (k + 1), aRe m|
              = |(∑ m ∈ Finset.range (k + 1), baseFn (m + J)).re| := by
                  simp [aRe]
          _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn (m + J)‖ := Complex.abs_re_le_norm _
          _ ≤ C0 := hbound
      have hpartial_im : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aIm m| ≤ C0 := by
        intro k hk
        have hbound := hpartial_bound (k + 1) (by
          rw [hn0]
          omega : k + 1 ≤ N)
        calc
          |∑ m ∈ Finset.range (k + 1), aIm m|
              = |(∑ m ∈ Finset.range (k + 1), baseFn (m + J)).im| := by
                  simp [aIm]
          _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn (m + J)‖ := Complex.abs_im_le_norm _
          _ ≤ C0 := hbound
      have hb_nonneg : ∀ k ≤ n0, 0 ≤ b k := by
        intro k hk
        exact atkinsonUpperBoundaryWeightedCoeff_nonneg (k + J) j hj
      have hb_anti : ∀ k < n0, b (k + 1) ≤ b k := by
        intro k hk
        exact atkinsonUpperBoundaryWeightedCoeff_antitone j hj (by omega : k + J ≤ k + 1 + J)
      have hb_one : b 0 ≤ 1 := by
        simpa [b, coeff, J] using atkinsonUpperBoundaryWeightedCoeff_le_one J j hj
      have hsum_re :
          (∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn (k + J))).re
            =
          ∑ k ∈ Finset.range (n0 + 1), aRe k * b k := by
        simp [aRe, b, mul_comm, mul_left_comm, mul_assoc]
      have hsum_im :
          (∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn (k + J))).im
            =
          ∑ k ∈ Finset.range (n0 + 1), aIm k * b k := by
        simp [aIm, b, mul_comm, mul_left_comm, mul_assoc]
      have hC0_nonneg : 0 ≤ C0 := by
        apply mul_nonneg
        apply mul_nonneg
        · positivity
        · exact Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)
        · positivity
      have hre :
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn (k + J))).re| ≤ C0 := by
        have habel :=
          AbelSummation.abel_summation_bound aRe b n0 C0 hpartial_re hb_nonneg hb_anti
        calc
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn (k + J))).re|
              = |∑ k ∈ Finset.range (n0 + 1), aRe k * b k| := by rw [hsum_re]
          _ ≤ C0 * b 0 := habel
          _ ≤ C0 * 1 := by
                exact mul_le_mul_of_nonneg_left hb_one hC0_nonneg
          _ = C0 := by ring
      have him :
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn (k + J))).im| ≤ C0 := by
        have habel :=
          AbelSummation.abel_summation_bound aIm b n0 C0 hpartial_im hb_nonneg hb_anti
        calc
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn (k + J))).im|
              = |∑ k ∈ Finset.range (n0 + 1), aIm k * b k| := by rw [hsum_im]
          _ ≤ C0 * b 0 := habel
          _ ≤ C0 * 1 := by
                exact mul_le_mul_of_nonneg_left hb_one hC0_nonneg
          _ = C0 := by ring
      have hnorm :
          ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn (k + J))‖ ≤ 2 * C0 := by
        calc
          ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn (k + J))‖
              ≤
            |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn (k + J))).re|
              +
            |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn (k + J))).im| := by
                exact Complex.norm_le_abs_re_add_abs_im _
          _ ≤ C0 + C0 := add_le_add hre him
          _ = 2 * C0 := by ring
      have hmain :
          ‖∑ n ∈ Finset.range M,
              (if J ≤ n then ((((coeff n : ℝ) : ℂ)) * baseFn n) else 0)‖ ≤ 2 * C0 := by
        calc
          ‖∑ n ∈ Finset.range M,
              (if J ≤ n then ((((coeff n : ℝ) : ℂ)) * baseFn n) else 0)‖
              =
            ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn (k + J))‖ := by
              rw [hsum, hn0]
          _ ≤ 2 * C0 := hnorm
      calc
        ‖∑ n ∈ Finset.range M,
            (if J ≤ n then ((((coeff n : ℝ) : ℂ)) * baseFn n) else 0)‖
            ≤ 2 * C0 := hmain
        _ = (4 * Real.sqrt 2 * Cl) * Real.log (↑j + 1) * target := by
              unfold C0
              ring
  ·
    have hzero :
        ∑ n ∈ Finset.range M,
            (if J ≤ n then ((((coeff n : ℝ) : ℂ)) * baseFn n) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnlt : n < J := lt_of_lt_of_le (Finset.mem_range.mp hn) (Nat.not_le.mp hJM).le
      simp [hnlt.not_ge]
    have hnonneg : 0 ≤ (4 * Real.sqrt 2 * Cl) * Real.log (↑j + 1) * target := by
        apply mul_nonneg
        apply mul_nonneg
        · positivity
        · exact Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)
        · positivity
    simpa [hzero] using hnonneg

private theorem atkinson_large_modes_complete_resonant_packet_row_upper_boundary_sum_bound_atomic :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then
            atkinsonWeightedResonantBlockMode (n + j) 1 *
              atkinsonShiftedSinglePrimitive (n + j) j 1
          else 0)‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨Cl, hCl, hlower⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_lower_boundary_sum_bound_atomic
  obtain ⟨Cw, hCw, hweighted⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_upper_weighted_lower_sum_bound_atomic
  refine ⟨4 * Real.sqrt 2 * Cl + Cw + 4 / Real.log 2,
    by positivity, ?_⟩
  intro j hj M
  let J : ℕ := j + 1
  let upperFn : ℕ → ℂ := fun n =>
    if j ≤ n then
      atkinsonWeightedResonantBlockMode (n + j) 1 *
        atkinsonShiftedSinglePrimitive (n + j) j 1
    else 0
  let lowerFn : ℕ → ℂ := fun n =>
    if J ≤ n then
      atkinsonWeightedResonantBlockMode (n + J) 0 *
        atkinsonShiftedSinglePrimitive (n + J) J 0
    else 0
  let weightedFn : ℕ → ℂ := fun n =>
    if J ≤ n then
      ((((2 - atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) *
        (atkinsonWeightedResonantBlockMode (n + J) 0 *
          atkinsonShiftedSinglePrimitive (n + J) J 0)
    else 0
  let target : ℝ := Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j
  by_cases hJM : J ≤ M
  · let exc : ℂ :=
      atkinsonWeightedResonantBlockMode (j + j) 1 * atkinsonShiftedSinglePrimitive (j + j) j 1
    have hlower_prefix_zero : ∑ n ∈ Finset.range J, lowerFn n = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp [lowerFn, (Finset.mem_range.mp hn).not_ge]
    have hweighted_prefix_zero : ∑ n ∈ Finset.range J, weightedFn n = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp [weightedFn, (Finset.mem_range.mp hn).not_ge]
    have hsum_lower :
        ∑ n ∈ Finset.range M, lowerFn n = ∑ n ∈ Finset.Ico J M, lowerFn n := by
      have htmp := (Finset.sum_range_add_sum_Ico lowerFn hJM).symm
      rw [hlower_prefix_zero, zero_add] at htmp
      exact htmp
    have hsum_weighted :
        ∑ n ∈ Finset.range M, weightedFn n = ∑ n ∈ Finset.Ico J M, weightedFn n := by
      have htmp := (Finset.sum_range_add_sum_Ico weightedFn hJM).symm
      rw [hweighted_prefix_zero, zero_add] at htmp
      exact htmp
    have hprefix_zero : ∑ n ∈ Finset.range j, upperFn n = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp [upperFn, (Finset.mem_range.mp hn).not_ge]
    have hprefix_eq : ∑ n ∈ Finset.range J, upperFn n = exc := by
      rw [show J = j + 1 by rfl, Finset.sum_range_succ, hprefix_zero]
      simp [upperFn, exc]
    have hsplit_total :
        ∑ n ∈ Finset.range M, upperFn n = exc + ∑ n ∈ Finset.Ico J M, upperFn n := by
      calc
        ∑ n ∈ Finset.range M, upperFn n
            = (∑ n ∈ Finset.range J, upperFn n) + ∑ n ∈ Finset.Ico J M, upperFn n := by
                simpa using (Finset.sum_range_add_sum_Ico upperFn hJM).symm
        _ = exc + ∑ n ∈ Finset.Ico J M, upperFn n := by rw [hprefix_eq]
    have htail_eq :
        ∑ n ∈ Finset.Ico J M, upperFn n
          = (((2 : ℝ) : ℂ)) * (∑ n ∈ Finset.range M, lowerFn n)
              - ∑ n ∈ Finset.range M, weightedFn n := by
      calc
        ∑ n ∈ Finset.Ico J M, upperFn n
            =
          ∑ n ∈ Finset.Ico J M, ((((2 : ℝ) : ℂ)) * lowerFn n - weightedFn n) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              have hnJ : J ≤ n := (Finset.mem_Ico.mp hn).1
              have hjn : j ≤ n := by
                dsimp [J] at hnJ
                omega
              have hjlt : j < n := by
                dsimp [J] at hnJ
                omega
              have hstep := atkinson_upper_boundary_step n j hj hjn
              let base : ℂ :=
                atkinsonWeightedResonantBlockMode (n + J) 0 *
                  atkinsonShiftedSinglePrimitive (n + J) J 0
              calc
                upperFn n
                    = (((atkinsonUpperBoundaryStepCoeff n j : ℝ) : ℂ)) * base := by
                            simpa [upperFn, J, Nat.add_assoc, add_left_comm, add_comm, hjn, base] using hstep
                _ = ((((2 : ℝ) : ℂ)) - ((((2 - atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ))) * base := by
                      congr 1
                      norm_num
                _ = (((2 : ℝ) : ℂ)) * base
                      - ((((2 - atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) * base := by
                          ring
                _ = (((2 : ℝ) : ℂ)) * lowerFn n - weightedFn n := by
                      simp [lowerFn, weightedFn, J, hnJ, hjlt, base]
        _ = (((2 : ℝ) : ℂ)) * (∑ n ∈ Finset.Ico J M, lowerFn n)
              - ∑ n ∈ Finset.Ico J M, weightedFn n := by
                rw [Finset.sum_sub_distrib, Finset.mul_sum]
        _ = (((2 : ℝ) : ℂ)) * (∑ n ∈ Finset.range M, lowerFn n)
              - ∑ n ∈ Finset.range M, weightedFn n := by
                rw [← hsum_lower, ← hsum_weighted]
    have htarget_J :
        Real.sqrt (((M + J : ℕ) : ℝ) + 1) / J ≤ Real.sqrt 2 * target := by
      have hle : (((M + J : ℕ) : ℝ) + 1) ≤ 2 * ((((M + j : ℕ) : ℝ) + 1) : ℝ) := by
        exact_mod_cast (by
          dsimp [J]
          omega : M + J + 1 ≤ 2 * (M + j + 1))
      calc
        Real.sqrt (((M + J : ℕ) : ℝ) + 1) / J
            ≤ Real.sqrt (2 * ((((M + j : ℕ) : ℝ) + 1)) ) / J := by
                exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hle)
                  (by positivity : (0 : ℝ) ≤ J)
        _ = (Real.sqrt 2 * Real.sqrt ((((M + j : ℕ) : ℝ) + 1))) / J := by
              have hsqrt_eq :
                  Real.sqrt (2 * ((((M + j : ℕ) : ℝ) + 1)))
                    = Real.sqrt 2 * Real.sqrt ((((M + j : ℕ) : ℝ) + 1)) := by
                      simpa using
                        (Real.sqrt_mul
                          (by positivity : 0 ≤ (2 : ℝ))
                          (by positivity : 0 ≤ ((((M + j : ℕ) : ℝ) + 1))))
              rw [hsqrt_eq]
        _ ≤ (Real.sqrt 2 * Real.sqrt ((((M + j : ℕ) : ℝ) + 1))) / j := by
              exact div_le_div_of_nonneg_left
                (show 0 ≤ Real.sqrt 2 * Real.sqrt ((((M + j : ℕ) : ℝ) + 1)) by positivity)
                (show (0 : ℝ) < j by positivity)
                (by
                  have hJgej : (j : ℝ) ≤ J := by
                    exact_mod_cast Nat.le_succ j
                  simpa [J] using hJgej)
        _ = Real.sqrt 2 * target := by
              dsimp [target]
              ring
    have hlog_bound : Real.log (↑J + 1) ≤ 2 * Real.log (↑j + 1) := by
      have hjsq : (↑J + 1 : ℝ) ≤ (↑j + 1) ^ 2 := by
        simp only [J]
        push_cast
        have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
        nlinarith [sq_nonneg (j : ℝ)]
      calc
        Real.log (↑J + 1) ≤ Real.log ((↑j + 1) ^ 2) := by
              exact Real.log_le_log (by positivity) hjsq
        _ = 2 * Real.log (↑j + 1) := by
              rw [Real.log_pow]
              ring
    have hlower_bound :
        ‖∑ n ∈ Finset.range M, lowerFn n‖ ≤ 2 * Real.sqrt 2 * Cl * Real.log (↑j + 1) * target := by
      have hraw :
          ‖∑ n ∈ Finset.range M, lowerFn n‖
            ≤ Cl * Real.log (↑J + 1) * (Real.sqrt (((M + J : ℕ) : ℝ) + 1) / J) := by
              simpa [lowerFn, J] using
                hlower J (Nat.succ_le_succ (Nat.zero_le j)) M
      calc
        ‖∑ n ∈ Finset.range M, lowerFn n‖
            ≤ Cl * Real.log (↑J + 1) * (Real.sqrt (((M + J : ℕ) : ℝ) + 1) / J) := hraw
        _ ≤ Cl * Real.log (↑J + 1) * (Real.sqrt 2 * target) := by
              have hlog_nn : 0 ≤ Real.log (↑J + 1) :=
                Real.log_nonneg (by exact_mod_cast show 1 ≤ J + 1 by omega)
              exact mul_le_mul_of_nonneg_left htarget_J (mul_nonneg hCl.le hlog_nn)
        _ ≤ Cl * (2 * Real.log (↑j + 1)) * (Real.sqrt 2 * target) := by
              have hsqrt_target_nn : 0 ≤ Real.sqrt 2 * target := by positivity
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hlog_bound hCl.le) hsqrt_target_nn
        _ = 2 * Real.sqrt 2 * Cl * Real.log (↑j + 1) * target := by ring
    have hweighted_bound :
        ‖∑ n ∈ Finset.range M, weightedFn n‖ ≤ Cw * Real.log (↑j + 1) * target := by
      simpa [weightedFn, J, target] using hweighted j hj M
    have htail_bound :
        ‖∑ n ∈ Finset.Ico J M, upperFn n‖ ≤ (4 * Real.sqrt 2 * Cl + Cw) * Real.log (↑j + 1) * target := by
      calc
        ‖∑ n ∈ Finset.Ico J M, upperFn n‖
            = ‖(((2 : ℝ) : ℂ)) * (∑ n ∈ Finset.range M, lowerFn n)
                - ∑ n ∈ Finset.range M, weightedFn n‖ := by
                  rw [htail_eq]
        _ ≤ ‖(((2 : ℝ) : ℂ)) * (∑ n ∈ Finset.range M, lowerFn n)‖
              + ‖∑ n ∈ Finset.range M, weightedFn n‖ := norm_sub_le _ _
        _ = 2 * ‖∑ n ∈ Finset.range M, lowerFn n‖
              + ‖∑ n ∈ Finset.range M, weightedFn n‖ := by
                rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
        _ ≤ 2 * (2 * Real.sqrt 2 * Cl * Real.log (↑j + 1) * target) + Cw * Real.log (↑j + 1) * target := by
              nlinarith [hlower_bound, hweighted_bound]
        _ = (4 * Real.sqrt 2 * Cl + Cw) * Real.log (↑j + 1) * target := by ring
    have hphase_inv :
        1 / atkinsonShiftedRelativePhase (j + J) J ≤ 2 := by
      calc
        1 / atkinsonShiftedRelativePhase (j + J) J
            ≤ (((j + J : ℕ) : ℝ) + 1) / J := by
                simpa [J] using
                  atkinsonShiftedRelativePhase_inv_upper
                    (j + J) J (Nat.succ_le_succ (Nat.zero_le j)) (by omega)
        _ = (2 : ℝ) := by
              have hnum : (((j + J : ℕ) : ℝ) + 1) = 2 * J := by
                exact_mod_cast (by
                  dsimp [J]
                  omega : j + J + 1 = 2 * J)
              rw [hnum]
              field_simp [show (J : ℝ) ≠ 0 by positivity]
    have hweight_target :
        atkinsonModeWeight j ≤ target := by
      have hsqrtj :
          Real.sqrt (j + 1) ≤ Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
        have hcast_le : ((j : ℝ) + 1) ≤ (((M + j : ℕ) : ℝ) + 1) := by
          exact_mod_cast (Nat.succ_le_succ (Nat.le_add_left j M))
        exact Real.sqrt_le_sqrt hcast_le
      have hformula : atkinsonModeWeight j = Real.sqrt (j + 1) / (j + 1) := by
        apply (eq_div_iff (show ((j : ℝ) + 1) ≠ 0 by positivity)).2
        simpa [mul_comm] using atkinsonModeWeight_mul_succ_eq_sqrt j
      calc
        atkinsonModeWeight j = Real.sqrt (j + 1) / (j + 1) := hformula
        _ ≤ Real.sqrt (((M + j : ℕ) : ℝ) + 1) / (j + 1) := by
              exact div_le_div_of_nonneg_right hsqrtj (by positivity : (0 : ℝ) ≤ j + 1)
        _ ≤ Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j := by
              exact div_le_div_of_nonneg_left
                (show 0 ≤ Real.sqrt (((M + j : ℕ) : ℝ) + 1) by positivity)
                (show (0 : ℝ) < j by positivity)
                (by exact_mod_cast Nat.le_succ j)
        _ = target := by rfl
    have hphase_pos :
        0 < atkinsonShiftedRelativePhase (j + J) J := by
      exact atkinsonShiftedRelativePhase_pos
        (j + J) J (Nat.succ_le_succ (Nat.zero_le j)) (by omega)
    have hexc_bound : ‖exc‖ ≤ 4 * target := by
      have hstep := atkinson_upper_boundary_step j j hj le_rfl
      have hbase_norm :
          ‖atkinsonWeightedResonantBlockMode (j + j + 1) 0 *
              atkinsonShiftedSinglePrimitive (j + j + 1) (j + 1) 0‖
            = atkinsonModeWeight j / atkinsonShiftedRelativePhase (j + J) J := by
              simpa [J, Nat.add_assoc, add_left_comm, add_comm] using
                (atkinsonLowerBoundaryTerm_norm j J (Nat.succ_le_succ (Nat.zero_le j)))
      have hdiv_nonneg :
          0 ≤ atkinsonModeWeight j / atkinsonShiftedRelativePhase (j + J) J := by
        exact div_nonneg (atkinsonModeWeight_nonneg j) hphase_pos.le
      have hdiv_bound :
          atkinsonModeWeight j / atkinsonShiftedRelativePhase (j + J) J
            ≤ atkinsonModeWeight j * 2 := by
        calc
          atkinsonModeWeight j / atkinsonShiftedRelativePhase (j + J) J
              = atkinsonModeWeight j * (1 / atkinsonShiftedRelativePhase (j + J) J) := by ring
          _ ≤ atkinsonModeWeight j * 2 := by
                exact mul_le_mul_of_nonneg_left hphase_inv (atkinsonModeWeight_nonneg j)
      calc
        ‖exc‖ = atkinsonUpperBoundaryStepCoeff j j *
            (atkinsonModeWeight j / atkinsonShiftedRelativePhase (j + J) J) := by
                unfold exc
                rw [hstep, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg (atkinsonUpperBoundaryStepCoeff_nonneg j j hj), hbase_norm]
        _ = atkinsonUpperBoundaryStepCoeff j j *
            (atkinsonModeWeight j / atkinsonShiftedRelativePhase (j + J) J) := by
              rfl
        _ ≤ 2 * (atkinsonModeWeight j / atkinsonShiftedRelativePhase (j + J) J) := by
              exact mul_le_mul_of_nonneg_right
                (atkinsonUpperBoundaryStepCoeff_le_two j j hj) hdiv_nonneg
        _ ≤ 2 * (atkinsonModeWeight j * 2) := by
              exact mul_le_mul_of_nonneg_left hdiv_bound (by norm_num)
        _ = 4 * atkinsonModeWeight j := by ring
        _ ≤ 4 * target := by
              gcongr
    have hexc_log_bound : 4 * target ≤ (4 / Real.log 2) * Real.log (↑j + 1) * target := by
      have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hlog_ge : Real.log 2 ≤ Real.log (↑j + 1) := by
        exact Real.log_le_log (by norm_num) (by exact_mod_cast show 2 ≤ j + 1 by omega)
      have htarget_nn : 0 ≤ target := by positivity
      have h1_le : (1 : ℝ) ≤ Real.log (↑j + 1) / Real.log 2 := by
        rw [le_div_iff₀ hlog2_pos]
        linarith [hlog_ge]
      calc 4 * target
          = 4 * (1 * target) := by ring
        _ ≤ 4 * (Real.log (↑j + 1) / Real.log 2 * target) := by
              gcongr
        _ = (4 / Real.log 2) * Real.log (↑j + 1) * target := by ring
    calc
      ‖∑ n ∈ Finset.range M, upperFn n‖ = ‖exc + ∑ n ∈ Finset.Ico J M, upperFn n‖ := by
            rw [hsplit_total]
      _ ≤ ‖exc‖ + ‖∑ n ∈ Finset.Ico J M, upperFn n‖ := norm_add_le _ _
      _ ≤ 4 * target + (4 * Real.sqrt 2 * Cl + Cw) * Real.log (↑j + 1) * target := by
            exact add_le_add hexc_bound htail_bound
      _ ≤ (4 / Real.log 2) * Real.log (↑j + 1) * target
              + (4 * Real.sqrt 2 * Cl + Cw) * Real.log (↑j + 1) * target := by
            exact add_le_add hexc_log_bound le_rfl
      _ = (4 * Real.sqrt 2 * Cl + Cw + 4 / Real.log 2) * Real.log (↑j + 1) * target := by ring
  · have hMle : M ≤ j := by
      dsimp [J] at hJM
      omega
    have hzero : ∑ n ∈ Finset.range M, upperFn n = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnlt : n < j := lt_of_lt_of_le (Finset.mem_range.mp hn) hMle
      simp [upperFn, hnlt.not_ge]
    have hnonneg : 0 ≤ (4 * Real.sqrt 2 * Cl + Cw + 4 / Real.log 2) * Real.log (↑j + 1) * target := by
      apply mul_nonneg
      apply mul_nonneg
      · apply add_nonneg
        apply add_nonneg
        · positivity
        · exact hCw.le
        · exact div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le
      · exact Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)
      · positivity
    rw [hzero]
    simpa [target] using hnonneg

private theorem atkinson_large_modes_complete_resonant_packet_row_boundary_sum_bound_atomic :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨Cu, hCu, hupper⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_upper_boundary_sum_bound_atomic
  obtain ⟨Cl, hCl, hlower⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_lower_boundary_sum_bound_atomic
  refine ⟨Cu + Cl, by positivity, ?_⟩
  intro j hj M
  let su : ℂ :=
    ∑ n ∈ Finset.range M,
      (if j ≤ n then
        atkinsonWeightedResonantBlockMode (n + j) 1 * atkinsonShiftedSinglePrimitive (n + j) j 1
      else 0)
  let sl : ℂ :=
    ∑ n ∈ Finset.range M,
      (if j ≤ n then
        atkinsonWeightedResonantBlockMode (n + j) 0 * atkinsonShiftedSinglePrimitive (n + j) j 0
      else 0)
  have hsplit :
      ∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)
        =
      su - sl := by
    calc
      ∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)
          =
        ∑ n ∈ Finset.range M,
          ((if j ≤ n then
              atkinsonWeightedResonantBlockMode (n + j) 1 *
                atkinsonShiftedSinglePrimitive (n + j) j 1
            else 0)
            -
            (if j ≤ n then
              atkinsonWeightedResonantBlockMode (n + j) 0 *
                atkinsonShiftedSinglePrimitive (n + j) j 0
            else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              by_cases hjn : j ≤ n
              · simp [hjn, atkinsonResonantShiftedBoundaryTerm]
              · simp [hjn]
      _ = su - sl := by
            unfold su sl
            rw [Finset.sum_sub_distrib]
  have htarget_nonneg : 0 ≤ Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j := by positivity
  calc
    ‖∑ n ∈ Finset.range M,
        (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)‖
      = ‖su - sl‖ := by rw [hsplit]
    _ ≤ ‖su‖ + ‖sl‖ := norm_sub_le _ _
    _ ≤ Cu * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j)
          + Cl * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
            gcongr
            · exact hupper j hj M
            · exact hlower j hj M
    _ = (Cu + Cl) * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by ring

/-- A local head-term bound for the native `j = 1,2` boundary wrappers.
This duplicates the later generic helper only to avoid a forward dependency in
the wrapper section. -/
private lemma atkinsonUpperBoundaryTerm_norm_local
    (n j : ℕ) (hj : 1 ≤ j) :
    ‖atkinsonWeightedResonantBlockMode (n + j) 1 *
      atkinsonShiftedSinglePrimitive (n + j) j 1‖
      = atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + j) j := by
  have hjk : j ≤ n + j := by omega
  have hphase_pos : 0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j hj hjk
  have hstep := atkinsonShiftedSingleBoundaryCore_step n j hj
  have hnorm_bcore :=
    atkinsonShiftedSingleBoundaryCore_norm n (j + 1) (by omega : 1 ≤ j + 1)
  have h1 :
      ‖(((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        (atkinsonWeightedResonantBlockMode (n + j) 1 *
          atkinsonShiftedSinglePrimitive (n + j) j 1)‖
        = atkinsonModeWeight n := by
    rw [hstep]
    exact hnorm_bcore
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hphase_pos] at h1
  rw [eq_div_iff (ne_of_gt hphase_pos), mul_comm]
  exact h1

/-- A local head-term bound for the native `j = 1,2` boundary wrappers.
This duplicates the later generic helper only to avoid a forward dependency in
the wrapper section. -/
private lemma atkinsonBoundary_jMinusOne_le_local
    (j : ℕ) (hj : 1 ≤ j) (m : ℕ) :
    ‖atkinsonResonantShiftedBoundaryTerm (j - 1) j‖
      ≤ (2 / Real.log 2) * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
  have hjk : j ≤ (j - 1) + j := by omega
  have hbound :
      ‖atkinsonResonantShiftedBoundaryTerm (j - 1) j‖
        ≤ 2 * (atkinsonModeWeight (j - 1) /
              atkinsonShiftedRelativePhase ((j - 1) + j) j) := by
    unfold atkinsonResonantShiftedBoundaryTerm
    calc
      ‖atkinsonWeightedResonantBlockMode ((j - 1) + j) 1 *
            atkinsonShiftedSinglePrimitive ((j - 1) + j) j 1
          - atkinsonWeightedResonantBlockMode ((j - 1) + j) 0 *
            atkinsonShiftedSinglePrimitive ((j - 1) + j) j 0‖
        ≤ ‖atkinsonWeightedResonantBlockMode ((j - 1) + j) 1 *
              atkinsonShiftedSinglePrimitive ((j - 1) + j) j 1‖
            + ‖atkinsonWeightedResonantBlockMode ((j - 1) + j) 0 *
              atkinsonShiftedSinglePrimitive ((j - 1) + j) j 0‖ := norm_sub_le _ _
      _ = (atkinsonModeWeight (j - 1) /
              atkinsonShiftedRelativePhase ((j - 1) + j) j)
            + (atkinsonModeWeight (j - 1) /
              atkinsonShiftedRelativePhase ((j - 1) + j) j) := by
            rw [atkinsonUpperBoundaryTerm_norm_local (j - 1) j hj,
              atkinsonLowerBoundaryTerm_norm (j - 1) j hj]
      _ = 2 * (atkinsonModeWeight (j - 1) /
              atkinsonShiftedRelativePhase ((j - 1) + j) j) := by ring
  have hmw_mul := atkinsonModeWeight_mul_succ_eq_sqrt (j - 1)
  have hpred_cast : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hj
  rw [hpred_cast] at hmw_mul
  have hphase_eq :
      atkinsonShiftedRelativePhase ((j - 1) + j) j = Real.log 2 := by
    rw [atkinsonShiftedRelativePhase_eq_sub_logs]
    have hk_nat_nat : (j - 1 + j : ℕ) + 1 = 2 * j := by
      omega
    have hk_nat : (((j - 1 + j : ℕ) : ℝ) + 1) = 2 * (j : ℝ) := by
      exact_mod_cast hk_nat_nat
    have hk_sub_nat_nat : ((j - 1 + j - j : ℕ)) + 1 = j := by
      rw [Nat.add_sub_cancel_right, Nat.sub_add_cancel hj]
    have hk_sub_nat : ((((j - 1 + j - j : ℕ) : ℝ)) + 1) = (j : ℝ) := by
      exact_mod_cast hk_sub_nat_nat
    rw [hk_nat, hk_sub_nat]
    rw [← Real.log_div (by positivity : (2 : ℝ) * (j : ℝ) ≠ 0)
      (by positivity : (j : ℝ) ≠ 0)]
    congr 1
    field_simp
  have hsqrt_le :
      Real.sqrt (j : ℝ) ≤ Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
    have hsqrt_arg_nat : j ≤ m + j + 1 := by omega
    exact Real.sqrt_le_sqrt (by exact_mod_cast hsqrt_arg_nat)
  have hmw_eq :
      atkinsonModeWeight (j - 1) = Real.sqrt (j : ℝ) / j := by
    apply (eq_div_iff (show (j : ℝ) ≠ 0 by positivity)).2
    simpa [mul_comm] using hmw_mul
  have hdiv :
      Real.sqrt (j : ℝ) / j ≤ Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j := by
    have hinv_nonneg : 0 ≤ (1 / (j : ℝ)) := by positivity
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_right hsqrt_le hinv_nonneg
  calc
    ‖atkinsonResonantShiftedBoundaryTerm (j - 1) j‖
      ≤ 2 * (atkinsonModeWeight (j - 1) /
            atkinsonShiftedRelativePhase ((j - 1) + j) j) := hbound
    _ = (2 / Real.log 2) * (Real.sqrt (j : ℝ) / j) := by
          rw [hphase_eq, hmw_eq]
          ring
    _ ≤ (2 / Real.log 2) * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
          exact mul_le_mul_of_nonneg_left hdiv (by positivity)

/-- The `j = 1` boundary prefix for the inverse-phase cell leaf is already
available from the tracked boundary-row package, after adding back the isolated
`n = 0` head term. -/
private theorem atkinson_shiftedBoundaryPrefix_bound_j1 :
    ∃ C_bdry > 0, ∀ m : ℕ,
      ‖∑ n ∈ Finset.Ico ((1 : ℕ) - 1) (m + 1),
          atkinsonResonantShiftedBoundaryTerm n (1 : ℕ)‖
        ≤ C_bdry * (Real.sqrt (((m + (1 : ℕ) : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)) := by
  obtain ⟨C_bdry, hC_bdry, hbdry⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_boundary_sum_bound_atomic
  refine ⟨Real.sqrt 2 * C_bdry + 2 / Real.log 2, by positivity, ?_⟩
  intro m
  let target : ℝ := Real.sqrt (((m + (1 : ℕ) : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)
  have hhead :
      ‖atkinsonResonantShiftedBoundaryTerm 0 (1 : ℕ)‖
        ≤ (2 / Real.log 2) * target := by
    simpa [target] using
      atkinsonBoundary_jMinusOne_le_local (1 : ℕ) (by norm_num) m
  have htail_eq :
      ∑ n ∈ Finset.Ico (1 : ℕ) (m + 1), atkinsonResonantShiftedBoundaryTerm n (1 : ℕ)
        =
      ∑ n ∈ Finset.range (m + 1),
        (if (1 : ℕ) ≤ n then atkinsonResonantShiftedBoundaryTerm n (1 : ℕ) else 0) := by
    rw [← Finset.sum_filter]
    congr 1
    ext x
    constructor <;> intro hx <;>
      simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx ⊢ <;> omega
  have htail_raw :
      ‖∑ n ∈ Finset.Ico (1 : ℕ) (m + 1), atkinsonResonantShiftedBoundaryTerm n (1 : ℕ)‖
        ≤ C_bdry * Real.log (↑(1 : ℕ) + 1) *
            (Real.sqrt ((((m + 1 : ℕ) + (1 : ℕ) : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)) := by
    rw [htail_eq]
    exact hbdry (1 : ℕ) (by norm_num) (m + 1)
  have hsqrt_cmp :
      Real.sqrt ((((m + 1 : ℕ) + (1 : ℕ) : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)
        ≤ Real.sqrt 2 * target := by
    have hle :
        ((((m + 1 : ℕ) + (1 : ℕ) : ℕ) : ℝ) + 1)
          ≤ 2 * ((((m + (1 : ℕ) : ℕ) : ℝ) + 1) : ℝ) := by
      exact_mod_cast (by omega : (m + 1 + 1 : ℕ) + 1 ≤ 2 * (m + 1 + 1))
    calc
      Real.sqrt ((((m + 1 : ℕ) + (1 : ℕ) : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)
          ≤ Real.sqrt (2 * ((((m + (1 : ℕ) : ℕ) : ℝ) + 1) : ℝ)) / ((1 : ℕ) : ℝ) := by
              exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hle)
                (by positivity : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
      _ = Real.sqrt 2 * target := by
            have hsqrt_mul :
                Real.sqrt (2 * ((((m + (1 : ℕ) : ℕ) : ℝ) + 1) : ℝ))
                  = Real.sqrt 2 * Real.sqrt ((((m + (1 : ℕ) : ℕ) : ℝ) + 1) : ℝ) := by
                    simpa using
                      Real.sqrt_mul
                        (by positivity : 0 ≤ (2 : ℝ))
                        (by positivity : 0 ≤ ((((m + (1 : ℕ) : ℕ) : ℝ) + 1) : ℝ))
            rw [hsqrt_mul]
            simp [target]
  have htail :
      ‖∑ n ∈ Finset.Ico (1 : ℕ) (m + 1), atkinsonResonantShiftedBoundaryTerm n (1 : ℕ)‖
        ≤ Real.sqrt 2 * C_bdry * target := by
    have hlog2_le_one : Real.log (↑(1 : ℕ) + 1) ≤ 1 := by
      norm_num
      have h2le : (2 : ℝ) ≤ Real.exp 1 := by
        linarith [Real.add_one_le_exp (1 : ℝ)]
      exact (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).2 h2le
    calc
      ‖∑ n ∈ Finset.Ico (1 : ℕ) (m + 1), atkinsonResonantShiftedBoundaryTerm n (1 : ℕ)‖
          ≤ C_bdry * Real.log (↑(1 : ℕ) + 1) *
              (Real.sqrt ((((m + 1 : ℕ) + (1 : ℕ) : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)) := htail_raw
      _ ≤ C_bdry * Real.log (↑(1 : ℕ) + 1) * (Real.sqrt 2 * target) := by
            exact mul_le_mul_of_nonneg_left hsqrt_cmp
              (mul_nonneg (le_of_lt hC_bdry)
                (by positivity))
      _ ≤ C_bdry * 1 * (Real.sqrt 2 * target) := by
            gcongr
      _ = Real.sqrt 2 * C_bdry * target := by ring
  calc
    ‖∑ n ∈ Finset.Ico ((1 : ℕ) - 1) (m + 1),
        atkinsonResonantShiftedBoundaryTerm n (1 : ℕ)‖
      =
    ‖atkinsonResonantShiftedBoundaryTerm 0 (1 : ℕ)
        + ∑ n ∈ Finset.Ico (1 : ℕ) (m + 1), atkinsonResonantShiftedBoundaryTerm n (1 : ℕ)‖ := by
          have hsplit :
              ∑ n ∈ Finset.Ico ((1 : ℕ) - 1) (m + 1),
                  atkinsonResonantShiftedBoundaryTerm n (1 : ℕ)
                =
              atkinsonResonantShiftedBoundaryTerm 0 (1 : ℕ)
                + ∑ n ∈ Finset.Ico (1 : ℕ) (m + 1), atkinsonResonantShiftedBoundaryTerm n (1 : ℕ) := by
                    calc
                      ∑ n ∈ Finset.Ico ((1 : ℕ) - 1) (m + 1),
                          atkinsonResonantShiftedBoundaryTerm n (1 : ℕ)
                        =
                      ∑ n ∈ Finset.range (m + 1),
                          atkinsonResonantShiftedBoundaryTerm n (1 : ℕ) := by
                            simp
                      _ =
                      (∑ n ∈ Finset.range 1,
                          atkinsonResonantShiftedBoundaryTerm n (1 : ℕ))
                        +
                      ∑ n ∈ Finset.Ico 1 (m + 1),
                          atkinsonResonantShiftedBoundaryTerm n (1 : ℕ) := by
                            simpa using
                              (Finset.sum_range_add_sum_Ico
                                (fun n => atkinsonResonantShiftedBoundaryTerm n (1 : ℕ))
                                (show 1 ≤ m + 1 by omega)).symm
                      _ =
                      atkinsonResonantShiftedBoundaryTerm 0 (1 : ℕ)
                        +
                      ∑ n ∈ Finset.Ico 1 (m + 1),
                          atkinsonResonantShiftedBoundaryTerm n (1 : ℕ) := by
                            simp
          rw [hsplit]
    _ ≤ ‖atkinsonResonantShiftedBoundaryTerm 0 (1 : ℕ)‖
          + ‖∑ n ∈ Finset.Ico (1 : ℕ) (m + 1), atkinsonResonantShiftedBoundaryTerm n (1 : ℕ)‖ := by
            exact norm_add_le _ _
    _ ≤ (2 / Real.log 2) * target + Real.sqrt 2 * C_bdry * target := by
          exact add_le_add hhead htail
    _ = (Real.sqrt 2 * C_bdry + 2 / Real.log 2) * target := by ring

/-- The `j = 2` boundary prefix for the inverse-phase cell leaf is already
available from the tracked boundary-row package, after restoring the isolated
`n = 1` head term. -/
private theorem atkinson_shiftedBoundaryPrefix_bound_j2 :
    ∃ C_bdry > 0, ∀ m : ℕ,
      ‖∑ n ∈ Finset.Ico ((2 : ℕ) - 1) (m + 1),
          atkinsonResonantShiftedBoundaryTerm n (2 : ℕ)‖
        ≤ C_bdry * (Real.sqrt (((m + (2 : ℕ) : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)) := by
  obtain ⟨C_bdry, hC_bdry, hbdry⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_boundary_sum_bound_atomic
  refine ⟨Real.sqrt 2 * C_bdry * Real.log (↑(2 : ℕ) + 1) + 2 / Real.log 2,
    by positivity, ?_⟩
  intro m
  let target : ℝ := Real.sqrt (((m + (2 : ℕ) : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)
  have hhead :
      ‖atkinsonResonantShiftedBoundaryTerm ((2 : ℕ) - 1) (2 : ℕ)‖
        ≤ (2 / Real.log 2) * target := by
    simpa [target] using
      atkinsonBoundary_jMinusOne_le_local (2 : ℕ) (by norm_num) m
  have htail_eq :
      ∑ n ∈ Finset.Ico (2 : ℕ) (m + 1), atkinsonResonantShiftedBoundaryTerm n (2 : ℕ)
        =
      ∑ n ∈ Finset.range (m + 1),
        (if (2 : ℕ) ≤ n then atkinsonResonantShiftedBoundaryTerm n (2 : ℕ) else 0) := by
    rw [← Finset.sum_filter]
    congr 1
    ext x
    constructor <;> intro hx <;>
      simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx ⊢ <;> omega
  have htail_raw :
      ‖∑ n ∈ Finset.Ico (2 : ℕ) (m + 1), atkinsonResonantShiftedBoundaryTerm n (2 : ℕ)‖
        ≤ C_bdry * Real.log (↑(2 : ℕ) + 1) *
            (Real.sqrt ((((m + 1 : ℕ) + (2 : ℕ) : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)) := by
    rw [htail_eq]
    exact hbdry (2 : ℕ) (by norm_num) (m + 1)
  have hsqrt_cmp :
      Real.sqrt ((((m + 1 : ℕ) + (2 : ℕ) : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)
        ≤ Real.sqrt 2 * target := by
    have hle :
        ((((m + 1 : ℕ) + (2 : ℕ) : ℕ) : ℝ) + 1)
          ≤ 2 * ((((m + (2 : ℕ) : ℕ) : ℝ) + 1) : ℝ) := by
      exact_mod_cast (by omega : (m + 1 + 2 : ℕ) + 1 ≤ 2 * (m + 2 + 1))
    calc
      Real.sqrt ((((m + 1 : ℕ) + (2 : ℕ) : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)
          ≤ Real.sqrt (2 * ((((m + (2 : ℕ) : ℕ) : ℝ) + 1) : ℝ)) / ((2 : ℕ) : ℝ) := by
              exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hle)
                (by positivity : (0 : ℝ) ≤ ((2 : ℕ) : ℝ))
      _ = Real.sqrt 2 * target := by
            have hsqrt_mul :
                Real.sqrt (2 * ((((m + (2 : ℕ) : ℕ) : ℝ) + 1) : ℝ))
                  = Real.sqrt 2 * Real.sqrt ((((m + (2 : ℕ) : ℕ) : ℝ) + 1) : ℝ) := by
                    simpa using
                      Real.sqrt_mul
                        (by positivity : 0 ≤ (2 : ℝ))
                        (by positivity : 0 ≤ ((((m + (2 : ℕ) : ℕ) : ℝ) + 1) : ℝ))
            rw [hsqrt_mul]
            simp [target]
            ring
  have htail :
      ‖∑ n ∈ Finset.Ico (2 : ℕ) (m + 1), atkinsonResonantShiftedBoundaryTerm n (2 : ℕ)‖
        ≤ Real.sqrt 2 * C_bdry * Real.log (↑(2 : ℕ) + 1) * target := by
    calc
      ‖∑ n ∈ Finset.Ico (2 : ℕ) (m + 1), atkinsonResonantShiftedBoundaryTerm n (2 : ℕ)‖
          ≤ C_bdry * Real.log (↑(2 : ℕ) + 1) *
              (Real.sqrt ((((m + 1 : ℕ) + (2 : ℕ) : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)) := htail_raw
      _ ≤ C_bdry * Real.log (↑(2 : ℕ) + 1) * (Real.sqrt 2 * target) := by
            exact mul_le_mul_of_nonneg_left hsqrt_cmp
              (mul_nonneg (le_of_lt hC_bdry)
                (by positivity))
      _ = Real.sqrt 2 * C_bdry * Real.log (↑(2 : ℕ) + 1) * target := by ring
  have hsplit_norm :
      ‖∑ n ∈ Finset.Ico ((2 : ℕ) - 1) (m + 1),
          atkinsonResonantShiftedBoundaryTerm n (2 : ℕ)‖
        ≤ ‖atkinsonResonantShiftedBoundaryTerm ((2 : ℕ) - 1) (2 : ℕ)‖
            + ‖∑ n ∈ Finset.Ico (2 : ℕ) (m + 1), atkinsonResonantShiftedBoundaryTerm n (2 : ℕ)‖ := by
    by_cases hm0 : m = 0
    · subst hm0
      simp
    · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      have hset :
          Finset.Ico ((2 : ℕ) - 1) (m' + 1 + 1)
            = ({(2 : ℕ) - 1} : Finset ℕ) ∪ Finset.Ico (2 : ℕ) (m' + 1 + 1) := by
        ext x
        constructor <;> intro hx
        · rcases Finset.mem_Ico.mp hx with ⟨hx1, hx2⟩
          by_cases hxj : x = (2 : ℕ) - 1
          · exact Finset.mem_union.mpr <| Or.inl (by simpa [hxj])
          · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_Ico.mpr (by omega)
        · rcases Finset.mem_union.mp hx with hx | hx
          · simp at hx
            subst hx
            exact Finset.mem_Ico.mpr (by omega)
          · rcases Finset.mem_Ico.mp hx with ⟨hx1, hx2⟩
            exact Finset.mem_Ico.mpr (by omega)
      have hdisj :
          Disjoint ({(2 : ℕ) - 1} : Finset ℕ) (Finset.Ico (2 : ℕ) (m' + 1 + 1)) := by
        refine Finset.disjoint_left.mpr ?_
        intro x hx1 hx2
        simp at hx1
        subst hx1
        rcases Finset.mem_Ico.mp hx2 with ⟨hx2l, hx2r⟩
        omega
      rw [hset, Finset.sum_union hdisj, Finset.sum_singleton]
      exact norm_add_le _ _
  calc
    ‖∑ n ∈ Finset.Ico ((2 : ℕ) - 1) (m + 1),
        atkinsonResonantShiftedBoundaryTerm n (2 : ℕ)‖
      ≤ ‖atkinsonResonantShiftedBoundaryTerm ((2 : ℕ) - 1) (2 : ℕ)‖
          + ‖∑ n ∈ Finset.Ico (2 : ℕ) (m + 1), atkinsonResonantShiftedBoundaryTerm n (2 : ℕ)‖ := hsplit_norm
    _ ≤ (2 / Real.log 2) * target
          + Real.sqrt 2 * C_bdry * Real.log (↑(2 : ℕ) + 1) * target := by
            exact add_le_add hhead htail
    _ = (Real.sqrt 2 * C_bdry * Real.log (↑(2 : ℕ) + 1) + 2 / Real.log 2) * target := by
          ring

/-- The native `j = 1` inverse-phase cell patch reduces to a raw `j = 1`
correction-prefix bound once the boundary side is filled from tracked
infrastructure. -/
private theorem atkinson_shiftedInversePhaseCellPrefix_no_log_j1_of_correction
    (hcorr1 :
      ∃ C_corr > 0, ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico ((1 : ℕ) - 1) (m + 1),
            atkinsonResonantShiftedCorrectionTerm n (1 : ℕ)‖
          ≤ C_corr * (Real.sqrt (((m + (1 : ℕ) : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ))) :
    ∃ C1 > 0, ∀ m : ℕ,
      ‖∑ n ∈ Finset.Ico ((1 : ℕ) - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + (1 : ℕ)) (1 : ℕ) : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n (1 : ℕ))‖
        ≤ C1 * (Real.sqrt (((m + (1 : ℕ) : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)) := by
  simpa using
    atkinson_shiftedInversePhaseCellPrefix_no_log_fixedShift_of_boundary_and_correction
      (1 : ℕ) (by norm_num) atkinson_shiftedBoundaryPrefix_bound_j1 hcorr1

/-- The native `j = 2` inverse-phase cell patch reduces to a raw `j = 2`
correction-prefix bound once the boundary side is filled from tracked
infrastructure. -/
private theorem atkinson_shiftedInversePhaseCellPrefix_no_log_j2_of_correction
    (hcorr2 :
      ∃ C_corr > 0, ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico ((2 : ℕ) - 1) (m + 1),
            atkinsonResonantShiftedCorrectionTerm n (2 : ℕ)‖
          ≤ C_corr * (Real.sqrt (((m + (2 : ℕ) : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ))) :
    ∃ C2 > 0, ∀ m : ℕ,
      ‖∑ n ∈ Finset.Ico ((2 : ℕ) - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + (2 : ℕ)) (2 : ℕ) : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n (2 : ℕ))‖
        ≤ C2 * (Real.sqrt (((m + (2 : ℕ) : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ)) := by
  simpa using
    atkinson_shiftedInversePhaseCellPrefix_no_log_fixedShift_of_boundary_and_correction
      (2 : ℕ) (by norm_num) atkinson_shiftedBoundaryPrefix_bound_j2 hcorr2

/-- The remaining fixed-shift public leaf can be phrased directly in raw
correction-prefix terms.

Once the large-`j` inverse-phase cell theorem is available from `j ≥ 3`, the
two native fixed shifts no longer need separate cell-prefix arguments. Their
honest residual content is exactly the raw correction-prefix bounds consumed by
the two local reducers above. -/
private theorem
    atkinson_shiftedInversePhaseCellPrefixBound_of_eventual_j3_and_correction_j1_j2
    (hevent :
      ∃ Cevent > 0, ∀ j : ℕ, 3 ≤ j -> 1 ≤ j -> ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonResonantShiftedPhaseWeightedCell n j)‖
          ≤ Cevent * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j))
    (hcorr1 :
      ∃ C_corr > 0, ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico ((1 : ℕ) - 1) (m + 1),
            atkinsonResonantShiftedCorrectionTerm n (1 : ℕ)‖
          ≤ C_corr * (Real.sqrt (((m + (1 : ℕ) : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)))
    (hcorr2 :
      ∃ C_corr > 0, ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico ((2 : ℕ) - 1) (m + 1),
            atkinsonResonantShiftedCorrectionTerm n (2 : ℕ)‖
          ≤ C_corr * (Real.sqrt (((m + (2 : ℕ) : ℕ) : ℝ) + 1) / ((2 : ℕ) : ℝ))) :
    AtkinsonShiftedInversePhaseCellPrefixBoundHyp := by
  exact
    atkinson_shiftedInversePhaseCellPrefixBound_of_eventual_j3_and_j1_j2
      hevent
      (atkinson_shiftedInversePhaseCellPrefix_no_log_j1_of_correction hcorr1)
      (atkinson_shiftedInversePhaseCellPrefix_no_log_j2_of_correction hcorr2)

/-- Direct `Ico`-form remainder estimate for the aggregated Abel-contraction
block. This is the same bound as the preceding theorem, but stated in the tail
coordinates that the large-shift closure step naturally consumes. -/
private theorem atkinson_large_modes_complete_resonant_packet_row_upper_weighted_lower_remainder_bound_atomic :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      j + 1 ≤ M →
      ‖∑ n ∈ Finset.Ico (j + 1) M,
          ((((2 - atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) *
            (atkinsonWeightedResonantBlockMode (n + (j + 1)) 0 *
              atkinsonShiftedSinglePrimitive (n + (j + 1)) (j + 1) 0)‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_complete, hC_complete, hbound⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_upper_weighted_lower_sum_bound_atomic
  refine ⟨C_complete, hC_complete, ?_⟩
  intro j hj M hJM
  have hsum :
      ∑ n ∈ Finset.range M,
          (if j + 1 ≤ n then
            ((((2 - atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) *
              (atkinsonWeightedResonantBlockMode (n + (j + 1)) 0 *
                atkinsonShiftedSinglePrimitive (n + (j + 1)) (j + 1) 0)
          else 0)
        =
      ∑ n ∈ Finset.Ico (j + 1) M,
          ((((2 - atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) *
            (atkinsonWeightedResonantBlockMode (n + (j + 1)) 0 *
              atkinsonShiftedSinglePrimitive (n + (j + 1)) (j + 1) 0) := by
    calc
      ∑ n ∈ Finset.range M,
          (if j + 1 ≤ n then
            ((((2 - atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) *
              (atkinsonWeightedResonantBlockMode (n + (j + 1)) 0 *
                atkinsonShiftedSinglePrimitive (n + (j + 1)) (j + 1) 0)
          else 0)
        =
      (∑ n ∈ Finset.range (j + 1),
          (if j + 1 ≤ n then
            ((((2 - atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) *
              (atkinsonWeightedResonantBlockMode (n + (j + 1)) 0 *
                atkinsonShiftedSinglePrimitive (n + (j + 1)) (j + 1) 0)
          else 0))
        +
      ∑ n ∈ Finset.Ico (j + 1) M,
          (if j + 1 ≤ n then
            ((((2 - atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) *
              (atkinsonWeightedResonantBlockMode (n + (j + 1)) 0 *
                atkinsonShiftedSinglePrimitive (n + (j + 1)) (j + 1) 0)
          else 0) := by
            simpa using
              (Finset.sum_range_add_sum_Ico
                (fun n =>
                  if j + 1 ≤ n then
                    ((((2 - atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) *
                      (atkinsonWeightedResonantBlockMode (n + (j + 1)) 0 *
                        atkinsonShiftedSinglePrimitive (n + (j + 1)) (j + 1) 0)
                  else 0)
                hJM).symm
      _ =
      ∑ n ∈ Finset.Ico (j + 1) M,
          (if j + 1 ≤ n then
            ((((2 - atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) *
              (atkinsonWeightedResonantBlockMode (n + (j + 1)) 0 *
                atkinsonShiftedSinglePrimitive (n + (j + 1)) (j + 1) 0)
          else 0) := by
            have hprefix_zero :
                ∑ n ∈ Finset.range (j + 1),
                  (if j + 1 ≤ n then
                    ((((2 - atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) *
                      (atkinsonWeightedResonantBlockMode (n + (j + 1)) 0 *
                        atkinsonShiftedSinglePrimitive (n + (j + 1)) (j + 1) 0)
                  else 0) = 0 := by
              apply Finset.sum_eq_zero
              intro n hn
              simp [(Finset.mem_range.mp hn).not_ge]
            rw [hprefix_zero, zero_add]
      _ =
      ∑ n ∈ Finset.Ico (j + 1) M,
          ((((2 - atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) *
            (atkinsonWeightedResonantBlockMode (n + (j + 1)) 0 *
              atkinsonShiftedSinglePrimitive (n + (j + 1)) (j + 1) 0) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simp [(Finset.mem_Ico.mp hn).1]
  calc
    ‖∑ n ∈ Finset.Ico (j + 1) M,
        ((((2 - atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) *
          (atkinsonWeightedResonantBlockMode (n + (j + 1)) 0 *
            atkinsonShiftedSinglePrimitive (n + (j + 1)) (j + 1) 0)‖
      =
    ‖∑ n ∈ Finset.range M,
        (if j + 1 ≤ n then
          ((((2 - atkinsonUpperBoundaryStepCoeff n j) : ℝ) : ℂ)) *
            (atkinsonWeightedResonantBlockMode (n + (j + 1)) 0 *
              atkinsonShiftedSinglePrimitive (n + (j + 1)) (j + 1) 0)
         else 0)‖ := by
          rw [hsum]
    _ ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := hbound j hj M



omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
private theorem
    atkinson_large_modes_complete_resonant_packet_row_inversePhaseCellSum_bound_atomic_of_fixedShift_nontrivial
    {C_complete : ℝ}
    (hC_complete : 0 < C_complete)
    (hshift' :
      ∀ j : ℕ, 1 ≤ j → ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonResonantShiftedPhaseWeightedCell n j)‖
          ≤ C_complete * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j))
    (j M : ℕ) (hj : 1 ≤ j) (hJM : j ≤ M) :
    ‖∑ n ∈ Finset.range M,
        (if j ≤ n then
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)
         else 0)‖
      ≤ (2 * C_complete) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  let target : ℝ := Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j
  let cellFn : ℕ → ℂ := fun n =>
    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
      atkinsonResonantShiftedPhaseWeightedCell n j)
  have hsum :
      ∑ n ∈ Finset.range M,
          (if j ≤ n then cellFn n else 0)
        =
      ∑ n ∈ Finset.Ico j M, cellFn n := by
    calc
      ∑ n ∈ Finset.range M,
          (if j ≤ n then cellFn n else 0)
        =
      (∑ n ∈ Finset.range j,
          (if j ≤ n then cellFn n else 0))
        +
      ∑ n ∈ Finset.Ico j M,
          (if j ≤ n then cellFn n else 0) := by
            simpa using
              (Finset.sum_range_add_sum_Ico (fun n => if j ≤ n then cellFn n else 0) hJM).symm
      _ =
      ∑ n ∈ Finset.Ico j M,
          (if j ≤ n then cellFn n else 0) := by
            have hprefix_zero :
                ∑ n ∈ Finset.range j,
                    (if j ≤ n then cellFn n else 0) = 0 := by
                  apply Finset.sum_eq_zero
                  intro n hn
                  simp [(Finset.mem_range.mp hn).not_ge]
            rw [hprefix_zero, zero_add]
      _ =
      ∑ n ∈ Finset.Ico j M, cellFn n := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simp [(Finset.mem_Ico.mp hn).1]
  have hsplit :
      ∑ n ∈ Finset.Ico j M, cellFn n
        =
      (∑ n ∈ Finset.Ico (j - 1) M, cellFn n)
        - ∑ n ∈ Finset.Ico (j - 1) j, cellFn n := by
          calc
            ∑ n ∈ Finset.Ico j M, cellFn n
                =
            (∑ n ∈ Finset.range M, cellFn n)
              - ∑ n ∈ Finset.range j, cellFn n := by
                  rw [Finset.sum_Ico_eq_sub _ hJM]
            _ =
            ((∑ n ∈ Finset.range M, cellFn n)
                - ∑ n ∈ Finset.range (j - 1), cellFn n)
              -
            ((∑ n ∈ Finset.range j, cellFn n)
                - ∑ n ∈ Finset.range (j - 1), cellFn n) := by
                  ring
            _ =
            (∑ n ∈ Finset.Ico (j - 1) M, cellFn n)
              - ∑ n ∈ Finset.Ico (j - 1) j, cellFn n := by
                  rw [← Finset.sum_Ico_eq_sub _ (by omega : j - 1 ≤ M)]
                  rw [← Finset.sum_Ico_eq_sub _ (by omega : j - 1 ≤ j)]
  have hmain :
      ‖∑ n ∈ Finset.Ico (j - 1) M, cellFn n‖
        ≤ C_complete * target := by
    have hraw := hshift' j hj (M - 1)
    calc
      ‖∑ n ∈ Finset.Ico (j - 1) M, cellFn n‖
          ≤ C_complete * (Real.sqrt (((M - 1 + j : ℕ) : ℝ) + 1) / j) := by
            simpa [cellFn, show M - 1 + 1 = M by omega, Nat.add_assoc, add_left_comm, add_comm] using hraw
      _ = C_complete * (Real.sqrt ((M + j : ℕ) : ℝ) / j) := by
            have hM : (M - 1 + j : ℕ) + 1 = M + j := by omega
            have hM' : (((M - 1 + j : ℕ) : ℝ) + 1) = ((M + j : ℕ) : ℝ) := by
              exact_mod_cast hM
            rw [hM']
      _ ≤ C_complete * target := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC_complete)
            exact div_le_div_of_nonneg_right
              (Real.sqrt_le_sqrt (by linarith))
              (by positivity : (0 : ℝ) ≤ j)
  have hhead :
      ‖∑ n ∈ Finset.Ico (j - 1) j, cellFn n‖
        ≤ C_complete * target := by
    have hraw := hshift' j hj (j - 1)
    have hj_le : ((j - 1 + j : ℕ) : ℝ) + 1 ≤ (((M + j : ℕ) : ℝ) + 1) := by
      exact_mod_cast (by omega : (j - 1 + j) + 1 ≤ M + j + 1)
    calc
      ‖∑ n ∈ Finset.Ico (j - 1) j, cellFn n‖
          ≤ C_complete * (Real.sqrt (((j - 1 + j : ℕ) : ℝ) + 1) / j) := by
            simpa [cellFn, show j - 1 + 1 = j by omega, Nat.add_assoc, add_left_comm, add_comm] using hraw
      _ ≤ C_complete * target := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC_complete)
            exact div_le_div_of_nonneg_right
              (Real.sqrt_le_sqrt hj_le)
              (by positivity : (0 : ℝ) ≤ j)
  calc
    ‖∑ n ∈ Finset.range M,
        (if j ≤ n then cellFn n else 0)‖
        =
    ‖∑ n ∈ Finset.Ico j M, cellFn n‖ := by
          rw [hsum]
    _ =
      ‖(∑ n ∈ Finset.Ico (j - 1) M, cellFn n)
          - (∑ n ∈ Finset.Ico (j - 1) j, cellFn n)‖ := by
            rw [hsplit]
    _ ≤ ‖∑ n ∈ Finset.Ico (j - 1) M, cellFn n‖
          + ‖∑ n ∈ Finset.Ico (j - 1) j, cellFn n‖ := by
            exact norm_sub_le _ _
    _ ≤ C_complete * target + C_complete * target := by
          exact add_le_add hmain hhead
    _ = (2 * C_complete) * target := by
          ring

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
private lemma atkinson_inverse_phase_mul_phaseWeightedCell_eq_rowIntegral
    (n j : ℕ) (hj : 1 ≤ j) :
    ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
      atkinsonResonantShiftedPhaseWeightedCell n j)
      =
    ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u := by
  have hphase_pos :
      0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j hj (by omega)
  have hphase_ne : atkinsonShiftedRelativePhase (n + j) j ≠ 0 := ne_of_gt hphase_pos
  have hone :
      (1 / atkinsonShiftedRelativePhase (n + j) j) *
          atkinsonShiftedRelativePhase (n + j) j
        = (1 : ℝ) := by
    field_simp [hphase_ne]
  unfold atkinsonResonantShiftedPhaseWeightedCell
  have hmul :
      (((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ))
        = (1 : ℂ) := by
    exact_mod_cast hone
  calc
    (((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u)
        =
      ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          (((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ))) *
        ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u := by
          rw [mul_assoc]
    _ = ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u := by
          rw [hmul, one_mul]

/-- Upper-endpoint analogue of `atkinsonLowerBoundaryTerm_norm`. -/
private lemma atkinsonUpperBoundaryTerm_norm
    (n j : ℕ) (hj : 1 ≤ j) :
    ‖atkinsonWeightedResonantBlockMode (n + j) 1 *
      atkinsonShiftedSinglePrimitive (n + j) j 1‖
      = atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + j) j := by
  have hjk : j ≤ n + j := by omega
  have hphase_pos : 0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j hj hjk
  have hstep := atkinsonShiftedSingleBoundaryCore_step n j hj
  have hnorm_bcore :=
    atkinsonShiftedSingleBoundaryCore_norm n (j + 1) (by omega : 1 ≤ j + 1)
  have h1 :
      ‖(((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        (atkinsonWeightedResonantBlockMode (n + j) 1 *
          atkinsonShiftedSinglePrimitive (n + j) j 1)‖
        = atkinsonModeWeight n := by
    rw [hstep]
    exact hnorm_bcore
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hphase_pos] at h1
  rw [eq_div_iff (ne_of_gt hphase_pos), mul_comm]
  exact h1

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private lemma atkinsonUpperBoundaryTerm_norm_clean
    (n j : ℕ) (hj : 1 ≤ j) :
    ‖atkinsonWeightedResonantBlockMode (n + j) 1 *
      atkinsonShiftedSinglePrimitive (n + j) j 1‖
      = atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + j) j := by
  have hjk : j ≤ n + j := by omega
  have hphase_pos : 0 < atkinsonShiftedRelativePhase (n + j) j :=
    atkinsonShiftedRelativePhase_pos (n + j) j hj hjk
  have hstep := atkinsonShiftedSingleBoundaryCore_step n j hj
  have hnorm_bcore :=
    atkinsonShiftedSingleBoundaryCore_norm n (j + 1) (by omega : 1 ≤ j + 1)
  have h1 :
      ‖(((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        (atkinsonWeightedResonantBlockMode (n + j) 1 *
          atkinsonShiftedSinglePrimitive (n + j) j 1)‖
        = atkinsonModeWeight n := by
    rw [hstep]
    exact hnorm_bcore
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hphase_pos] at h1
  rw [eq_div_iff (ne_of_gt hphase_pos), mul_comm]
  exact h1

/-- Crude boundary-term norm bound used to extract the first term of the
shifted correction prefix. -/
private lemma atkinsonResonantShiftedBoundaryTerm_norm_le
    (n j : ℕ) (hj : 1 ≤ j) :
    ‖atkinsonResonantShiftedBoundaryTerm n j‖
      ≤ 2 * (atkinsonModeWeight n /
              atkinsonShiftedRelativePhase (n + j) j) := by
  unfold atkinsonResonantShiftedBoundaryTerm
  calc
    ‖atkinsonWeightedResonantBlockMode (n + j) 1 *
          atkinsonShiftedSinglePrimitive (n + j) j 1
        - atkinsonWeightedResonantBlockMode (n + j) 0 *
          atkinsonShiftedSinglePrimitive (n + j) j 0‖
      ≤ ‖atkinsonWeightedResonantBlockMode (n + j) 1 *
            atkinsonShiftedSinglePrimitive (n + j) j 1‖
          + ‖atkinsonWeightedResonantBlockMode (n + j) 0 *
            atkinsonShiftedSinglePrimitive (n + j) j 0‖ := norm_sub_le _ _
    _ = (atkinsonModeWeight n /
            atkinsonShiftedRelativePhase (n + j) j)
          + (atkinsonModeWeight n /
            atkinsonShiftedRelativePhase (n + j) j) := by
          rw [atkinsonUpperBoundaryTerm_norm n j hj, atkinsonLowerBoundaryTerm_norm n j hj]
    _ = 2 * (atkinsonModeWeight n /
              atkinsonShiftedRelativePhase (n + j) j) := by ring

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private lemma atkinsonResonantShiftedBoundaryTerm_norm_le_clean
    (n j : ℕ) (hj : 1 ≤ j) :
    ‖atkinsonResonantShiftedBoundaryTerm n j‖
      ≤ 2 * (atkinsonModeWeight n /
              atkinsonShiftedRelativePhase (n + j) j) := by
  unfold atkinsonResonantShiftedBoundaryTerm
  calc
    ‖atkinsonWeightedResonantBlockMode (n + j) 1 *
          atkinsonShiftedSinglePrimitive (n + j) j 1
        - atkinsonWeightedResonantBlockMode (n + j) 0 *
          atkinsonShiftedSinglePrimitive (n + j) j 0‖
      ≤ ‖atkinsonWeightedResonantBlockMode (n + j) 1 *
            atkinsonShiftedSinglePrimitive (n + j) j 1‖
          + ‖atkinsonWeightedResonantBlockMode (n + j) 0 *
            atkinsonShiftedSinglePrimitive (n + j) j 0‖ := norm_sub_le _ _
    _ = (atkinsonModeWeight n /
            atkinsonShiftedRelativePhase (n + j) j)
          + (atkinsonModeWeight n /
            atkinsonShiftedRelativePhase (n + j) j) := by
          rw [atkinsonUpperBoundaryTerm_norm_clean n j hj, atkinsonLowerBoundaryTerm_norm n j hj]
    _ = 2 * (atkinsonModeWeight n /
              atkinsonShiftedRelativePhase (n + j) j) := by ring

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private theorem atkinson_weighted_shifted_completeBlock_complex_bound_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ k : ℕ, N0 ≤ k →
      ∀ j : ℕ, 1 ≤ j → j ≤ (k + 1) / 2 →
        ‖(((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
          ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
            HardyCosSmooth.hardyCosExp (k - j) t)‖
          ≤ C * Real.sqrt ((k : ℝ) + 1) / j := by
  obtain ⟨Cω, hCω, N0, hderivBound⟩ := atkinsonWeightedResonantBlockMode_deriv_bound_eventually
  let C : ℝ := Real.sqrt 2 * (2 + Cω)
  refine ⟨C, by
    dsimp [C]
    positivity, N0, ?_⟩
  intro k hk j hj hj_half
  have hjk : j ≤ k := by omega
  have hmain :
      (((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
        ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
          HardyCosSmooth.hardyCosExp (k - j) t)
        =
      ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand (k - j) j u := by
    have hblock :=
      Aristotle.StationaryPhaseMainMode.hardyCosExp_completeBlock_eq_common_blockParamIntegral k j hj hjk
    calc
      (((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
        ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
          HardyCosSmooth.hardyCosExp (k - j) t)
          =
        (((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
          ∫ u in Ioc (0 : ℝ) 1,
            HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u) * blockJacobian k u) := by
              rw [hblock]
      _ =
        ∫ u in Ioc (0 : ℝ) 1,
          atkinsonComplexShiftedCompleteRowIntegrand (k - j) j u := by
            rw [← MeasureTheory.integral_const_mul]
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
            unfold atkinsonComplexShiftedCompleteRowIntegrand
            simpa [show (k - j) + j = k by omega]
      _ =
        ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand (k - j) j u := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
            exact atkinsonComplexShiftedCompleteRowIntegrand_eq_resonantCarrier_singlePacket (k - j) j u
  have hcell :=
    atkinsonResonantShiftedCell_eq_boundary_minus_correction (k - j) j hj
  have hIntBound :
      ‖atkinsonResonantShiftedCorrectionTerm (k - j) j‖
        ≤ Cω * atkinsonModeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
    have hprim0 :
        ‖atkinsonShiftedSinglePrimitive k j 0‖ ≤ Real.sqrt 2 * (((k : ℝ) + 1) / j) :=
      atkinsonShiftedSinglePrimitive_norm_bound k j hj hj_half 0
    have hprim1 :
        ‖atkinsonShiftedSinglePrimitive k j 1‖ ≤ Real.sqrt 2 * (((k : ℝ) + 1) / j) :=
      atkinsonShiftedSinglePrimitive_norm_bound k j hj hj_half 1
    have hnorm_f0 : ‖atkinsonWeightedResonantBlockMode k 0‖ = atkinsonModeWeight k :=
      atkinsonWeightedResonantBlockMode_norm k 0
    have hnorm_f1 : ‖atkinsonWeightedResonantBlockMode k 1‖ = atkinsonModeWeight k :=
      atkinsonWeightedResonantBlockMode_norm k 1
    calc
      ‖atkinsonResonantShiftedCorrectionTerm (k - j) j‖
          =
        ‖∫ u in (0 : ℝ)..1,
            (Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega k u : ℝ) : ℂ) *
              atkinsonWeightedResonantBlockMode k u) *
                atkinsonShiftedSinglePrimitive k j u‖ := by
                  simp [atkinsonResonantShiftedCorrectionTerm, show (k - j) + j = k by omega]
      _ ≤ ∫ u in (0 : ℝ)..1,
            ‖(Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega k u : ℝ) : ℂ) *
              atkinsonWeightedResonantBlockMode k u) *
                atkinsonShiftedSinglePrimitive k j u‖ := by
                  simpa [Real.norm_eq_abs] using
                    (intervalIntegral.norm_integral_le_integral_norm
                      (f := fun u =>
                        (Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega k u : ℝ) : ℂ) *
                          atkinsonWeightedResonantBlockMode k u) *
                            atkinsonShiftedSinglePrimitive k j u)
                      (by norm_num : (0 : ℝ) ≤ 1))
      _ ≤ ∫ u in (0 : ℝ)..1,
            Cω * atkinsonModeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
              let B : ℝ := Cω * atkinsonModeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j))
              have hcont : Continuous fun u : ℝ =>
                  ‖(Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega k u : ℝ) : ℂ) *
                      atkinsonWeightedResonantBlockMode k u) *
                    atkinsonShiftedSinglePrimitive k j u‖ := by
                exact ((continuous_const.mul
                  (Complex.continuous_ofReal.comp (atkinson_blockOmega_continuous k))).mul
                    (atkinsonWeightedResonantBlockMode_continuous k)).mul
                    (atkinsonShiftedSinglePrimitive_continuous k j) |>.norm
              have hlower_int :
                  IntervalIntegrable
                    (fun u =>
                      ‖(Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega k u : ℝ) : ℂ) *
                          atkinsonWeightedResonantBlockMode k u) *
                        atkinsonShiftedSinglePrimitive k j u‖)
                    volume (0 : ℝ) 1 := hcont.intervalIntegrable _ _
              have hupper_int :
                  IntervalIntegrable (fun _ : ℝ => B) volume (0 : ℝ) 1 := intervalIntegrable_const
              exact intervalIntegral.integral_mono_on
                (a := (0 : ℝ)) (b := 1)
                (f := fun u =>
                  ‖(Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega k u : ℝ) : ℂ) *
                      atkinsonWeightedResonantBlockMode k u) *
                    atkinsonShiftedSinglePrimitive k j u‖)
                (g := fun _ : ℝ => B)
                (hab := by norm_num) (hf := hlower_int) (hg := hupper_int) <| by
                  intro u hu
                  have hdu := hderivBound k hk u hu
                  have hGu := atkinsonShiftedSinglePrimitive_norm_bound k j hj hj_half u
                  calc
                    ‖(Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega k u : ℝ) : ℂ) *
                        atkinsonWeightedResonantBlockMode k u) *
                      atkinsonShiftedSinglePrimitive k j u‖
                        =
                      ‖Complex.I * ((Aristotle.StationaryPhaseMainMode.blockOmega k u : ℝ) : ℂ) *
                          atkinsonWeightedResonantBlockMode k u‖ *
                        ‖atkinsonShiftedSinglePrimitive k j u‖ := by
                          rw [norm_mul]
                    _ ≤ (Cω * atkinsonModeWeight k) * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
                          have hCω_nonneg : 0 ≤ Cω := le_of_lt hCω
                          exact mul_le_mul hdu hGu (norm_nonneg _) (mul_nonneg hCω_nonneg
                            (le_of_lt (atkinsonModeWeight_pos k)))
      _ = Cω * atkinsonModeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
            simp
  have hboundaryScale :
      atkinsonModeWeight (k - j) / atkinsonShiftedRelativePhase k j
        ≤ atkinsonModeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
    have hmw :
        atkinsonModeWeight (k - j)
          = atkinsonModeWeight k * atkinsonShiftedRelativeWeight k j := by
            simpa using (atkinsonModeWeight_mul_shiftedRelativeWeight k j).symm
    have hcoeff :
        atkinsonShiftedRelativeWeight k j * (1 / atkinsonShiftedRelativePhase k j)
          ≤ Real.sqrt 2 * (((k : ℝ) + 1) / j) := by
      have hweight := atkinsonShiftedRelativeWeight_le_sqrt_two k j hj_half
      have hphase := atkinsonShiftedRelativePhase_inv_upper k j hj hjk
      have hphase_pos : 0 < atkinsonShiftedRelativePhase k j :=
        atkinsonShiftedRelativePhase_pos k j hj hjk
      exact mul_le_mul hweight hphase
        (by simpa using one_div_nonneg.mpr (le_of_lt hphase_pos))
        (by positivity)
    calc
      atkinsonModeWeight (k - j) / atkinsonShiftedRelativePhase k j
          = atkinsonModeWeight k *
              (atkinsonShiftedRelativeWeight k j * (1 / atkinsonShiftedRelativePhase k j)) := by
                rw [hmw]
                ring
      _ ≤ atkinsonModeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
            exact mul_le_mul_of_nonneg_left hcoeff (atkinsonModeWeight_nonneg k)
  have hboundaryBound :
      ‖atkinsonResonantShiftedBoundaryTerm (k - j) j‖
        ≤ 2 * atkinsonModeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
    have hraw := atkinsonResonantShiftedBoundaryTerm_norm_le_clean (k - j) j hj
    have hboundaryScale' :
        atkinsonModeWeight (k - j) / atkinsonShiftedRelativePhase ((k - j) + j) j
          ≤ atkinsonModeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
      simpa [show (k - j) + j = k by omega] using hboundaryScale
    calc
      ‖atkinsonResonantShiftedBoundaryTerm (k - j) j‖
          ≤ 2 * (atkinsonModeWeight (k - j) / atkinsonShiftedRelativePhase ((k - j) + j) j) := by
              simpa [show (k - j) + j = k by omega] using hraw
      _ ≤ 2 * (atkinsonModeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j))) := by
            exact mul_le_mul_of_nonneg_left hboundaryScale' (by positivity : (0 : ℝ) ≤ 2)
      _ = 2 * atkinsonModeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
            ring
  have hmode_sqrt :
      atkinsonModeWeight k * ((k : ℝ) + 1) = Real.sqrt ((k : ℝ) + 1) := by
    simpa using atkinsonModeWeight_mul_succ_eq_sqrt k
  calc
    ‖(((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
        ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
          HardyCosSmooth.hardyCosExp (k - j) t)‖
        = ‖atkinsonResonantShiftedBoundaryTerm (k - j) j
              - atkinsonResonantShiftedCorrectionTerm (k - j) j‖ := by
                rw [hmain, hcell]
    _ ≤ ‖atkinsonResonantShiftedBoundaryTerm (k - j) j‖
          + ‖atkinsonResonantShiftedCorrectionTerm (k - j) j‖ := by
            exact norm_sub_le _ _
    _ ≤ 2 * atkinsonModeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j))
          + Cω * atkinsonModeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
            exact add_le_add hboundaryBound hIntBound
    _ = (2 + Cω) * atkinsonModeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
          ring
    _ = C * Real.sqrt ((k : ℝ) + 1) / j := by
          dsimp [C]
          calc
            (2 + Cω) * atkinsonModeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j))
                = (Real.sqrt 2 * (2 + Cω)) * (atkinsonModeWeight k * ((k : ℝ) + 1)) / j := by
                    field_simp [show (j : ℝ) ≠ 0 by positivity]
            _ = C * Real.sqrt ((k : ℝ) + 1) / j := by
                  rw [hmode_sqrt]

/-- The isolated first boundary term in the `Ico (j - 1) (m + 1)` correction
prefix has the same `sqrt / j` scale as the main range. -/
private lemma atkinsonBoundary_jMinusOne_le
    (j : ℕ) (hj : 1 ≤ j) (m : ℕ) :
    ‖atkinsonResonantShiftedBoundaryTerm (j - 1) j‖
      ≤ (2 / Real.log 2) * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
  have hjk : j ≤ (j - 1) + j := by omega
  have hphase_pos :
      0 < atkinsonShiftedRelativePhase ((j - 1) + j) j :=
    atkinsonShiftedRelativePhase_pos ((j - 1) + j) j hj hjk
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hj_pos : (0 : ℝ) < (j : ℝ) := by positivity
  have hbound := atkinsonResonantShiftedBoundaryTerm_norm_le (j - 1) j hj
  have hmw_mul := atkinsonModeWeight_mul_succ_eq_sqrt (j - 1)
  have hpred_cast : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hj
  rw [hpred_cast] at hmw_mul
  have hphase_eq :
      atkinsonShiftedRelativePhase ((j - 1) + j) j = Real.log 2 := by
    rw [atkinsonShiftedRelativePhase_eq_sub_logs]
    have hk_nat_nat : (j - 1 + j : ℕ) + 1 = 2 * j := by
      omega
    have hk_nat : (((j - 1 + j : ℕ) : ℝ) + 1) = 2 * (j : ℝ) := by
      exact_mod_cast hk_nat_nat
    have hk_sub_nat_nat : ((j - 1 + j - j : ℕ)) + 1 = j := by
      rw [Nat.add_sub_cancel_right, Nat.sub_add_cancel hj]
    have hk_sub_nat : ((((j - 1 + j - j : ℕ) : ℝ)) + 1) = (j : ℝ) := by
      exact_mod_cast hk_sub_nat_nat
    rw [hk_nat, hk_sub_nat]
    rw [← Real.log_div (by positivity : (2 : ℝ) * (j : ℝ) ≠ 0)
      (by positivity : (j : ℝ) ≠ 0)]
    congr 1
    field_simp
  have hsqrt_le :
      Real.sqrt (j : ℝ) ≤ Real.sqrt (((m + j : ℕ) : ℝ) + 1) :=
    by
      have hsqrt_arg_nat : j ≤ m + j + 1 := by
        omega
      exact Real.sqrt_le_sqrt (by exact_mod_cast hsqrt_arg_nat)
  have hmw_eq :
      atkinsonModeWeight (j - 1) = Real.sqrt (j : ℝ) / j := by
    apply (eq_div_iff (show (j : ℝ) ≠ 0 by positivity)).2
    simpa [mul_comm] using hmw_mul
  have hdiv :
      Real.sqrt (j : ℝ) / j ≤ Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j := by
    have hinv_nonneg : 0 ≤ (1 / (j : ℝ)) := by
      positivity
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_right hsqrt_le hinv_nonneg
  calc
    ‖atkinsonResonantShiftedBoundaryTerm (j - 1) j‖
      ≤ 2 * (atkinsonModeWeight (j - 1) /
            atkinsonShiftedRelativePhase ((j - 1) + j) j) := hbound
    _ = (2 / Real.log 2) * (Real.sqrt (j : ℝ) / j) := by
          rw [hphase_eq, hmw_eq]
          ring
    _ ≤ (2 / Real.log 2) * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
          exact mul_le_mul_of_nonneg_left hdiv (by positivity)

/-- For sufficiently large shifts, the isolated head cell already satisfies the
required no-log `sqrt / j` scale. This is the native single-cell input needed
to reduce the large-`j` public leaf to the genuine row tail. -/
private theorem atkinson_shiftedInversePhaseCell_head_no_log_eventually :
    ∃ C_head > 0, ∃ J_head : ℕ, ∀ j : ℕ, J_head ≤ j → 3 ≤ j → 1 ≤ j → ∀ m : ℕ, j - 1 ≤ m →
      ‖((((1 / atkinsonShiftedRelativePhase ((j - 1) + j) j : ℝ) : ℂ)) *
          atkinsonResonantShiftedPhaseWeightedCell (j - 1) j)‖
        ≤ C_head * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_head, hC_head, N0, hcell⟩ :=
    atkinson_weighted_shifted_completeBlock_complex_bound_eventually
  refine ⟨C_head, hC_head, max 3 N0, ?_⟩
  intro j hjJ hj3 hj1 m hnonempty
  have hN0 : N0 ≤ j := le_trans (Nat.le_max_right _ _) hjJ
  have hk_large : N0 ≤ 2 * j - 1 := by
    omega
  have hj_half : j ≤ ((2 * j - 1) + 1) / 2 := by
    omega
  have hraw := hcell (2 * j - 1) hk_large j hj1 hj_half
  have hmain :
      (((atkinsonModeWeight ((2 * j - 1) - j) : ℝ) : ℂ) *
        ∫ t in Ioc (hardyStart (2 * j - 1)) (hardyStart ((2 * j - 1) + 1)),
          HardyCosSmooth.hardyCosExp ((2 * j - 1) - j) t)
        =
      ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand ((2 * j - 1) - j) j u := by
    have hblock :=
      Aristotle.StationaryPhaseMainMode.hardyCosExp_completeBlock_eq_common_blockParamIntegral
        (2 * j - 1) j hj1 (by omega)
    calc
      (((atkinsonModeWeight ((2 * j - 1) - j) : ℝ) : ℂ) *
          ∫ t in Ioc (hardyStart (2 * j - 1)) (hardyStart ((2 * j - 1) + 1)),
            HardyCosSmooth.hardyCosExp ((2 * j - 1) - j) t)
          =
        (((atkinsonModeWeight ((2 * j - 1) - j) : ℝ) : ℂ) *
          ∫ u in Ioc (0 : ℝ) 1,
            HardyCosSmooth.hardyCosExp ((2 * j - 1) - j) (blockCoord (2 * j - 1) u) *
              blockJacobian (2 * j - 1) u) := by
              rw [hblock]
      _ =
        ∫ u in Ioc (0 : ℝ) 1,
          atkinsonComplexShiftedCompleteRowIntegrand ((2 * j - 1) - j) j u := by
            rw [← MeasureTheory.integral_const_mul]
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
            unfold atkinsonComplexShiftedCompleteRowIntegrand
            simp [show ((2 * j - 1) - j) + j = 2 * j - 1 by omega]
      _ =
        ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand ((2 * j - 1) - j) j u := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
          exact
            atkinsonComplexShiftedCompleteRowIntegrand_eq_resonantCarrier_singlePacket
              ((2 * j - 1) - j) j u
  have hcell_eq :
      ((((1 / atkinsonShiftedRelativePhase ((j - 1) + j) j : ℝ) : ℂ)) *
          atkinsonResonantShiftedPhaseWeightedCell (j - 1) j)
        =
      (((atkinsonModeWeight ((2 * j - 1) - j) : ℝ) : ℂ) *
        ∫ t in Ioc (hardyStart (2 * j - 1)) (hardyStart ((2 * j - 1) + 1)),
          HardyCosSmooth.hardyCosExp ((2 * j - 1) - j) t) := by
    calc
      ((((1 / atkinsonShiftedRelativePhase ((j - 1) + j) j : ℝ) : ℂ)) *
          atkinsonResonantShiftedPhaseWeightedCell (j - 1) j)
        =
      ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand (j - 1) j u := by
          simpa [Nat.add_assoc, add_left_comm, add_comm] using
            atkinson_inverse_phase_mul_phaseWeightedCell_eq_rowIntegral (j - 1) j hj1
      _ =
        ∫ u in Ioc (0 : ℝ) 1,
          atkinsonResonantShiftedRowSummand ((2 * j - 1) - j) j u := by
            have hidx : ((2 * j - 1) - j : ℕ) = j - 1 := by
              omega
            simpa [hidx]
      _ =
        (((atkinsonModeWeight ((2 * j - 1) - j) : ℝ) : ℂ) *
          ∫ t in Ioc (hardyStart (2 * j - 1)) (hardyStart ((2 * j - 1) + 1)),
            HardyCosSmooth.hardyCosExp ((2 * j - 1) - j) t) := by
            symm
            simpa [Nat.add_assoc, add_left_comm, add_comm] using hmain
  have hsqrt_mono :
      Real.sqrt ((((2 * j - 1 : ℕ) : ℝ) + 1)) / j
        ≤ Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j := by
    have hle : (((2 * j - 1 : ℕ) : ℝ) + 1) ≤ (((m + j : ℕ) : ℝ) + 1) := by
      exact_mod_cast (by omega : (2 * j - 1) + 1 ≤ m + j + 1)
    exact
      div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hle)
        (by positivity : (0 : ℝ) ≤ j)
  calc
    ‖((((1 / atkinsonShiftedRelativePhase ((j - 1) + j) j : ℝ) : ℂ)) *
        atkinsonResonantShiftedPhaseWeightedCell (j - 1) j)‖
      =
    ‖(((atkinsonModeWeight ((2 * j - 1) - j) : ℝ) : ℂ) *
        ∫ t in Ioc (hardyStart (2 * j - 1)) (hardyStart ((2 * j - 1) + 1)),
          HardyCosSmooth.hardyCosExp ((2 * j - 1) - j) t)‖ := by
          rw [hcell_eq]
    _ ≤ C_head * Real.sqrt ((((2 * j - 1 : ℕ) : ℝ) + 1)) / j := by
          exact hraw
    _ = C_head * (Real.sqrt ((((2 * j - 1 : ℕ) : ℝ) + 1)) / j) := by
          ring
    _ ≤ C_head * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
          exact mul_le_mul_of_nonneg_left hsqrt_mono (le_of_lt hC_head)

/-- Eventual large-`j` no-log reduction of the public inverse-phase-cell leaf
to the genuine row tail. Once the row-tail integral is controlled for large
shifts, the isolated head cell is already handled by the native single-cell
estimate above. -/
private theorem atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_rowIntegral
    (hrow :
      ∃ C_row > 0, ∃ J_row : ℕ, ∀ j : ℕ, J_row ≤ j → 3 ≤ j → 1 ≤ j → ∀ M : ℕ,
        ‖∫ u in Ioc (0 : ℝ) 1,
            ∑ n ∈ Finset.range M,
              (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0)‖
          ≤ C_row * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j)) :
    ∃ Cevent > 0, ∃ J0 : ℕ, ∀ j : ℕ, J0 ≤ j → 3 ≤ j → 1 ≤ j → ∀ m : ℕ,
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)‖
        ≤ Cevent * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_row, hC_row, J_row, hrow'⟩ := hrow
  obtain ⟨C_head, hC_head, J_head, hhead'⟩ :=
    atkinson_shiftedInversePhaseCell_head_no_log_eventually
  let J0 : ℕ := max J_row J_head
  obtain ⟨Cevent, hCevent, hbound⟩ :=
    atkinson_shiftedInversePhaseCellPrefix_no_log_j3_of_rowIntegral_and_head
      (J0 := J0)
      (hrow := ⟨C_row, hC_row, by
        intro j hJ0 hj3 hj1 M
        exact hrow' j (le_trans (Nat.le_max_left _ _) hJ0) hj3 hj1 M⟩)
      (hhead := ⟨C_head, hC_head, by
        intro j hJ0 hj3 hj1 m hnonempty
        exact hhead' j (le_trans (Nat.le_max_right _ _) hJ0) hj3 hj1 m hnonempty⟩)
  exact ⟨Cevent, hCevent, J0, hbound⟩

/-- Equivalent large-`j` reduction of the public inverse-phase-cell leaf in
the native Hardy-cosine complete-block coordinates.

This is the same large-`j` obligation as the row-tail theorem above, but stated
directly as a complex fixed-shift complete-block prefix bound. It isolates the
remaining analytic content without the extra row-integral wrapper. -/
private theorem atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_completeBlockPrefix
    (hblock :
      ∃ C_row > 0, ∃ J_row : ℕ, ∀ j : ℕ, J_row ≤ j → 3 ≤ j → 1 ≤ j → ∀ M : ℕ,
        ‖∑ n ∈ Finset.range M,
            (if j ≤ n then
              (((atkinsonModeWeight n : ℝ) : ℂ) *
                ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
                  HardyCosSmooth.hardyCosExp n t)
             else 0)‖
          ≤ C_row * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j)) :
    ∃ Cevent > 0, ∃ J0 : ℕ, ∀ j : ℕ, J0 ≤ j → 3 ≤ j → 1 ≤ j → ∀ m : ℕ,
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)‖
        ≤ Cevent * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_row, hC_row, J_row, hblock'⟩ := hblock
  refine
    atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_rowIntegral
      ⟨C_row, hC_row, J_row, ?_⟩
  intro j hJ_row hj3 hj1 M
  calc
    ‖∫ u in Ioc (0 : ℝ) 1,
        ∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0)‖
      =
    ‖∑ n ∈ Finset.range M,
        (if j ≤ n then
          (((atkinsonModeWeight n : ℝ) : ℂ) *
            ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
              HardyCosSmooth.hardyCosExp n t)
         else 0)‖ := by
          congr 1
          calc
            ∫ u in Ioc (0 : ℝ) 1,
                ∑ n ∈ Finset.range M,
                  (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0)
              =
            ∑ n ∈ Finset.range M,
              ∫ u in Ioc (0 : ℝ) 1,
                (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0) := by
                  rw [MeasureTheory.integral_finset_sum]
                  intro n hn
                  by_cases hjn : j ≤ n
                  · simpa [hjn] using
                      (atkinsonResonantShiftedRowSummand_continuous n j).integrableOn_Ioc
                  · simp [hjn]
            _ =
            ∑ n ∈ Finset.range M,
              (if j ≤ n then
                (((atkinsonModeWeight n : ℝ) : ℂ) *
                  ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
                    HardyCosSmooth.hardyCosExp n t)
               else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro n hn
                  by_cases hjn : j ≤ n
                  · simp [hjn]
                    simpa using
                      (atkinsonWeightedShiftedCompleteBlockComplex_eq_rowIntegral n j hj1).symm
                  · simp [hjn]
    _ ≤ C_row * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
          exact hblock' j hJ_row hj3 hj1 M

/-- Reduction of the large-`j` complete-block prefix theorem to an explicit
main-term prefix plus a summable `modeWeight / j` remainder.

This isolates the genuine next analytic content for the public inverse-phase
cell leaf: once the shifted complete-block sum is decomposed into a cancellative
main term at the target `sqrt / j` scale and a pointwise remainder of size
`modeWeight (n+j) / j`, the existing `sum_rpow_neg_half_le` bound already
closes the remainder prefix. -/
private theorem
    atkinson_weighted_shifted_completeBlock_prefix_bound_of_target_and_modeWeight_remainder
    (targetFn : ℕ → ℕ → ℂ)
    (htarget :
      ∃ C_target > 0, ∃ J_target : ℕ, ∀ j : ℕ, J_target ≤ j → 3 ≤ j → 1 ≤ j → ∀ M : ℕ,
        ‖∑ n ∈ Finset.range M, (if j ≤ n then targetFn n j else 0)‖
          ≤ C_target * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j))
    (herr :
      ∃ C_err > 0, ∃ J_err : ℕ, ∀ j : ℕ, J_err ≤ j → 3 ≤ j → 1 ≤ j → ∀ n : ℕ, j ≤ n →
        ‖((((atkinsonModeWeight n : ℝ) : ℂ) *
              ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
                HardyCosSmooth.hardyCosExp n t) - targetFn n j)‖
          ≤ C_err * (atkinsonModeWeight (n + j) / j)) :
    ∃ C_row > 0, ∃ J_row : ℕ, ∀ j : ℕ, J_row ≤ j → 3 ≤ j → 1 ≤ j → ∀ M : ℕ,
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then
            (((atkinsonModeWeight n : ℝ) : ℂ) *
              ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
                HardyCosSmooth.hardyCosExp n t)
           else 0)‖
        ≤ C_row * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_target, hC_target, J_target, htarget'⟩ := htarget
  obtain ⟨C_err, hC_err, J_err, herr'⟩ := herr
  let J_row : ℕ := max J_target J_err
  let blockFn : ℕ → ℕ → ℂ := fun n j =>
    (((atkinsonModeWeight n : ℝ) : ℂ) *
      ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
        HardyCosSmooth.hardyCosExp n t)
  refine ⟨C_target + 2 * C_err, by positivity, J_row, ?_⟩
  intro j hJrow hj3 hj1 M
  let target : ℝ := Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j
  have hmain :
      ‖∑ n ∈ Finset.range M, (if j ≤ n then targetFn n j else 0)‖
        ≤ C_target * target := by
    simpa [target] using
      htarget' j (le_trans (Nat.le_max_left _ _) hJrow) hj3 hj1 M
  have hweightSum :
      ∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonModeWeight (n + j) / j else 0)
        ≤ 2 * target := by
    have hsum_if :
        ∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonModeWeight (n + j) / j else 0)
          =
        ∑ n ∈ Finset.Ico j M, atkinsonModeWeight (n + j) / j := by
      rw [← Finset.sum_filter]
      congr 1
      ext x
      simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    calc
      ∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonModeWeight (n + j) / j else 0)
        =
      ∑ n ∈ Finset.Ico j M, atkinsonModeWeight (n + j) / j := hsum_if
      _ = ∑ n ∈ Finset.Ico j M, (1 / (j : ℝ)) * atkinsonModeWeight (n + j) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            field_simp [show (j : ℝ) ≠ 0 by positivity]
      _ = (1 / (j : ℝ)) * ∑ n ∈ Finset.Ico j M, atkinsonModeWeight (n + j) := by
            rw [Finset.mul_sum]
      _ = (1 / (j : ℝ)) * ∑ r ∈ Finset.Ico (j + j) (M + j), atkinsonModeWeight r := by
            congr 1
            simpa [Nat.add_assoc, add_left_comm, add_comm] using
              (Finset.sum_Ico_add (f := fun r => atkinsonModeWeight r) j M j)
      _ ≤ (1 / (j : ℝ)) * ∑ r ∈ Finset.range (M + j + 1), atkinsonModeWeight r := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by
                intro r hr
                exact Finset.mem_range.mpr <| by
                  exact lt_of_lt_of_le (Finset.mem_Ico.mp hr).2 (Nat.le_succ _))
              (by
                intro r hr hmem
                exact atkinsonModeWeight_nonneg r)
      _ = (1 / (j : ℝ)) * ∑ r ∈ Finset.range (M + j + 1), ((r + 1 : ℝ) ^ (-1 / 2 : ℝ)) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro r hr
            rw [atkinsonModeWeight]
            congr 1
            ring
      _ ≤ (1 / (j : ℝ)) * (2 * Real.sqrt ((M + j + 1 : ℕ) : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le (M + j + 1)
      _ = 2 * target := by
            unfold target
            norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
            ring
  have herrSum :
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then blockFn n j - targetFn n j else 0)‖
        ≤ (2 * C_err) * target := by
    calc
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then blockFn n j - targetFn n j else 0)‖
        ≤ ∑ n ∈ Finset.range M,
            ‖if j ≤ n then blockFn n j - targetFn n j else 0‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range M,
            (if j ≤ n then C_err * (atkinsonModeWeight (n + j) / j) else 0) := by
            refine Finset.sum_le_sum ?_
            intro n hn
            by_cases hjn : j ≤ n
            · simpa [blockFn, hjn] using
                herr' j (le_trans (Nat.le_max_right _ _) hJrow) hj3 hj1 n hjn
            · simp [hjn]
      _ = C_err * ∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonModeWeight (n + j) / j else 0) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro n hn
            by_cases hjn : j ≤ n <;> simp [hjn]
      _ ≤ C_err * (2 * target) := by
            exact mul_le_mul_of_nonneg_left hweightSum (le_of_lt hC_err)
      _ = (2 * C_err) * target := by ring
  have hsplit :
      ∑ n ∈ Finset.range M,
          (if j ≤ n then blockFn n j else 0)
        =
      (∑ n ∈ Finset.range M,
          (if j ≤ n then targetFn n j else 0))
        +
      ∑ n ∈ Finset.range M,
          (if j ≤ n then blockFn n j - targetFn n j else 0) := by
    calc
      ∑ n ∈ Finset.range M,
          (if j ≤ n then blockFn n j else 0)
        =
      ∑ n ∈ Finset.range M,
          ((if j ≤ n then targetFn n j else 0)
            + (if j ≤ n then blockFn n j - targetFn n j else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              by_cases hjn : j ≤ n <;> simp [hjn] <;> ring
      _ =
      (∑ n ∈ Finset.range M,
          (if j ≤ n then targetFn n j else 0))
        +
      ∑ n ∈ Finset.range M,
          (if j ≤ n then blockFn n j - targetFn n j else 0) := by
            rw [Finset.sum_add_distrib]
  calc
    ‖∑ n ∈ Finset.range M,
        (if j ≤ n then blockFn n j else 0)‖
      =
    ‖(∑ n ∈ Finset.range M,
          (if j ≤ n then targetFn n j else 0))
        +
      ∑ n ∈ Finset.range M,
          (if j ≤ n then blockFn n j - targetFn n j else 0)‖ := by
          rw [hsplit]
    _ ≤ ‖∑ n ∈ Finset.range M,
            (if j ≤ n then targetFn n j else 0)‖
          +
        ‖∑ n ∈ Finset.range M,
            (if j ≤ n then blockFn n j - targetFn n j else 0)‖ := by
            exact norm_add_le _ _
    _ ≤ C_target * target + (2 * C_err) * target := by
          exact add_le_add hmain herrSum
    _ = (C_target + 2 * C_err) * target := by
          ring

/-- Direct public-leaf reduction: it is enough to prove a cancellative shifted
complete-block main term at the target scale together with a pointwise
`modeWeight (n+j) / j` remainder. -/
private theorem
    atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_target_and_modeWeight_remainder
    (targetFn : ℕ → ℕ → ℂ)
    (htarget :
      ∃ C_target > 0, ∃ J_target : ℕ, ∀ j : ℕ, J_target ≤ j → 3 ≤ j → 1 ≤ j → ∀ M : ℕ,
        ‖∑ n ∈ Finset.range M, (if j ≤ n then targetFn n j else 0)‖
          ≤ C_target * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j))
    (herr :
      ∃ C_err > 0, ∃ J_err : ℕ, ∀ j : ℕ, J_err ≤ j → 3 ≤ j → 1 ≤ j → ∀ n : ℕ, j ≤ n →
        ‖((((atkinsonModeWeight n : ℝ) : ℂ) *
              ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
                HardyCosSmooth.hardyCosExp n t) - targetFn n j)‖
          ≤ C_err * (atkinsonModeWeight (n + j) / j)) :
    ∃ Cevent > 0, ∃ J0 : ℕ, ∀ j : ℕ, J0 ≤ j → 3 ≤ j → 1 ≤ j → ∀ m : ℕ,
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)‖
        ≤ Cevent * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
  exact
    atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_completeBlockPrefix
      (atkinson_weighted_shifted_completeBlock_prefix_bound_of_target_and_modeWeight_remainder
        targetFn htarget herr)

/-- Same reduction as
`atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_target_and_modeWeight_remainder`,
but stated in the natural complete-block coordinates `k = n + j`.

The shifted complete-block stationary-phase APIs are naturally indexed by the
block number `k`, while the public leaf is phrased in the mode index `n`. This
wrapper banks the exact reindexing once so the remaining large-`j` work can be
done directly on `k ∈ Ico (2 * j) (M + j)`. -/
private theorem
    atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_kTarget_and_modeWeight_remainder
    (targetK : ℕ → ℕ → ℂ)
    (htarget :
      ∃ C_target > 0, ∃ J_target : ℕ, ∀ j : ℕ, J_target ≤ j → 3 ≤ j → 1 ≤ j → ∀ M : ℕ,
        ‖∑ k ∈ Finset.Ico (2 * j) (M + j), targetK k j‖
          ≤ C_target * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j))
    (herr :
      ∃ C_err > 0, ∃ J_err : ℕ, ∀ j : ℕ, J_err ≤ j → 3 ≤ j → 1 ≤ j → ∀ k : ℕ, 2 * j ≤ k →
        ‖((((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
              ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                HardyCosSmooth.hardyCosExp (k - j) t) - targetK k j)‖
          ≤ C_err * (atkinsonModeWeight k / j)) :
    ∃ Cevent > 0, ∃ J0 : ℕ, ∀ j : ℕ, J0 ≤ j → 3 ≤ j → 1 ≤ j → ∀ m : ℕ,
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)‖
        ≤ Cevent * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
  refine
    atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_target_and_modeWeight_remainder
      (targetFn := fun n j => targetK (n + j) j) ?_ ?_
  · obtain ⟨C_target, hC_target, J_target, htarget'⟩ := htarget
    refine ⟨C_target, hC_target, J_target, ?_⟩
    intro j hJ_target hj3 hj1 M
    have hsum₁ :
        ∑ n ∈ Finset.range M, (if j ≤ n then targetK (n + j) j else 0)
          =
        ∑ n ∈ Finset.Ico j M, targetK (n + j) j := by
      rw [← Finset.sum_filter]
      have hset : (Finset.range M).filter (fun n => j ≤ n) = Finset.Ico j M := by
        ext x
        simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      rw [hset]
    have hsum₂ :
        ∑ n ∈ Finset.Ico j M, targetK (n + j) j
          =
        ∑ k ∈ Finset.Ico (2 * j) (M + j), targetK k j := by
      rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
      rw [show (M + j) - 2 * j = M - j by omega]
      refine Finset.sum_congr rfl ?_
      intro r hr
      simp [two_mul, Nat.add_assoc, add_left_comm, add_comm]
    have hsum := hsum₁.trans hsum₂
    have hmain :
        ‖∑ n ∈ Finset.range M, (if j ≤ n then targetK (n + j) j else 0)‖
          ≤ C_target * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
      calc
        ‖∑ n ∈ Finset.range M, (if j ≤ n then targetK (n + j) j else 0)‖
          = ‖∑ k ∈ Finset.Ico (2 * j) (M + j), targetK k j‖ := by
              rw [hsum]
        _ ≤ C_target * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) :=
            htarget' j hJ_target hj3 hj1 M
    simpa using hmain
  · obtain ⟨C_err, hC_err, J_err, herr'⟩ := herr
    refine ⟨C_err, hC_err, J_err, ?_⟩
    intro j hJ_err hj3 hj1 n hjn
    simpa [Nat.add_sub_cancel_right, Nat.add_assoc, add_left_comm, add_comm] using
      herr' j hJ_err hj3 hj1 (n + j) (by omega : 2 * j ≤ n + j)

/-- Concrete affine stationary-phase target for the large-`j` shifted
complete-block prefix.

This is the honest branch-free target suggested by the imported first-block
anchor asymptotic: an alternating `√(k+1)` main profile together with the
corresponding lower-order `modeWeight k` correction, both at scale `1 / j`. -/
private noncomputable def atkinsonCompleteBlockTargetK (k j : ℕ) : ℂ :=
  ((((1 / (j : ℝ) : ℝ) : ℂ) *
      (((-Complex.I) * Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
        Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope)) *
    ((((-1 : ℝ) ^ (k + 1) * Real.sqrt ((k : ℝ) + 1) : ℝ) : ℂ)))
  +
  ((((1 / (j : ℝ) : ℝ) : ℂ) *
      (((-Complex.I) * Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
        Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset)) *
    ((((-1 : ℝ) ^ (k + 1) * atkinsonModeWeight k : ℝ) : ℂ)))

/-- The concrete affine stationary-phase target already has the required
large-`j` prefix scale. So the remaining large-`j` public-leaf content is the
pointwise remainder against this explicit target, not another oscillatory
summation problem. -/
private theorem atkinsonCompleteBlockTargetK_prefix_bound :
    ∃ C_target > 0, ∃ J_target : ℕ, ∀ j : ℕ, J_target ≤ j → 3 ≤ j → 1 ≤ j → ∀ M : ℕ,
      ‖∑ k ∈ Finset.Ico (2 * j) (M + j), atkinsonCompleteBlockTargetK k j‖
        ≤ C_target * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  let A : ℂ := (-Complex.I) * Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor
  let altSqrt : ℕ → ℝ := fun k => (-1 : ℝ) ^ (k + 1) * Real.sqrt ((k : ℝ) + 1)
  let altWeight : ℕ → ℝ := fun k => (-1 : ℝ) ^ (k + 1) * atkinsonModeWeight k
  refine
    ⟨2 * (‖Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope‖
        + ‖Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset‖) + 1,
      by positivity, 1, ?_⟩
  intro j hJ_target hj3 hj1 M
  let Bsqrt : ℂ := (((1 / (j : ℝ) : ℝ) : ℂ)) *
    (A * Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope)
  let Bweight : ℂ := (((1 / (j : ℝ) : ℝ) : ℂ)) *
    (A * Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset)
  have hA_norm : ‖A‖ = 1 := by
    unfold A Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor
    rw [norm_mul, norm_neg, Complex.norm_I, Complex.norm_exp]
    simp
  have hBsqrt_norm :
      ‖Bsqrt‖ = ‖Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope‖ / j := by
    unfold Bsqrt
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hA_norm, one_mul]
    have hj_nonneg : 0 ≤ 1 / (j : ℝ) := by positivity
    rw [abs_of_nonneg hj_nonneg]
    ring
  have hBweight_norm :
      ‖Bweight‖ = ‖Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset‖ / j := by
    unfold Bweight
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hA_norm, one_mul]
    have hj_nonneg : 0 ≤ 1 / (j : ℝ) := by positivity
    rw [abs_of_nonneg hj_nonneg]
    ring
  by_cases hMj : M < j
  · have hIco_empty : Finset.Ico (2 * j) (M + j) = ∅ := by
      ext k
      simp [Finset.mem_Ico]
      omega
    rw [hIco_empty, Finset.sum_empty]
    have hnonneg :
        0 ≤
          (2 * (‖Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope‖
              + ‖Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset‖) + 1) *
            (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
      positivity
    simpa using hnonneg
  · have hlarge : 2 * j ≤ M + j := by omega
    have hsum :
        ∑ k ∈ Finset.Ico (2 * j) (M + j), atkinsonCompleteBlockTargetK k j
          =
        Bsqrt *
            (((∑ k ∈ Finset.Ico (2 * j) (M + j), altSqrt k : ℝ) : ℝ) : ℂ)
          +
        Bweight *
            (((∑ k ∈ Finset.Ico (2 * j) (M + j), altWeight k : ℝ) : ℝ) : ℂ) := by
      calc
        ∑ k ∈ Finset.Ico (2 * j) (M + j), atkinsonCompleteBlockTargetK k j
            =
          ∑ k ∈ Finset.Ico (2 * j) (M + j),
            (Bsqrt * (((altSqrt k : ℝ) : ℂ))
              + Bweight * (((altWeight k : ℝ) : ℂ))) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              simp [atkinsonCompleteBlockTargetK, Bsqrt, Bweight, A, altSqrt, altWeight]
        _ =
          (∑ k ∈ Finset.Ico (2 * j) (M + j), Bsqrt * (((altSqrt k : ℝ) : ℂ)))
            +
          ∑ k ∈ Finset.Ico (2 * j) (M + j), Bweight * (((altWeight k : ℝ) : ℂ)) := by
            rw [Finset.sum_add_distrib]
        _ =
          Bsqrt * ∑ k ∈ Finset.Ico (2 * j) (M + j), (((altSqrt k : ℝ) : ℂ))
            +
          Bweight * ∑ k ∈ Finset.Ico (2 * j) (M + j), (((altWeight k : ℝ) : ℂ)) := by
            rw [Finset.mul_sum, Finset.mul_sum]
        _ =
          Bsqrt * (((∑ k ∈ Finset.Ico (2 * j) (M + j), altSqrt k : ℝ) : ℝ) : ℂ)
            +
          Bweight * (((∑ k ∈ Finset.Ico (2 * j) (M + j), altWeight k : ℝ) : ℝ) : ℂ) := by
            simp
    have hico_abs :
        |∑ k ∈ Finset.Ico (2 * j) (M + j), altSqrt k|
          ≤ 2 * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
      have hsplit :
          ∑ k ∈ Finset.Ico (2 * j) (M + j), altSqrt k
            =
          ∑ k ∈ Finset.range (M + j), altSqrt k - ∑ k ∈ Finset.range (2 * j), altSqrt k := by
            rw [Finset.sum_Ico_eq_sub _ hlarge]
      have hupper_big :
          |∑ k ∈ Finset.range (M + j), altSqrt k|
            ≤ Real.sqrt (((M + j : ℕ) : ℝ)) := by
              simpa [altSqrt] using atkinson_alternating_shifted_sqrt_sum_bound_range (M + j)
      have hupper_small :
          |∑ k ∈ Finset.range (2 * j), altSqrt k|
            ≤ Real.sqrt (((2 * j : ℕ) : ℝ)) := by
              simpa [altSqrt] using atkinson_alternating_shifted_sqrt_sum_bound_range (2 * j)
      have hsqrt_big :
          Real.sqrt (((M + j : ℕ) : ℝ)) ≤ Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
            exact Real.sqrt_le_sqrt (by nlinarith : ((M + j : ℕ) : ℝ) ≤ (((M + j : ℕ) : ℝ) + 1))
      have hsqrt_small :
          Real.sqrt (((2 * j : ℕ) : ℝ)) ≤ Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
            apply Real.sqrt_le_sqrt
            exact_mod_cast (by omega : 2 * j ≤ M + j + 1)
      rw [hsplit]
      calc
        |∑ k ∈ Finset.range (M + j), altSqrt k - ∑ k ∈ Finset.range (2 * j), altSqrt k|
            ≤ |∑ k ∈ Finset.range (M + j), altSqrt k|
                + |∑ k ∈ Finset.range (2 * j), altSqrt k| := by
                  simpa [sub_eq_add_neg] using
                    (norm_add_le (∑ k ∈ Finset.range (M + j), altSqrt k)
                      (-(∑ k ∈ Finset.range (2 * j), altSqrt k)))
        _ ≤ Real.sqrt (((M + j : ℕ) : ℝ)) + Real.sqrt (((2 * j : ℕ) : ℝ)) := by
              nlinarith [hupper_big, hupper_small]
        _ ≤ 2 * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
              nlinarith [hsqrt_big, hsqrt_small]
    have hico_weight :
        |∑ k ∈ Finset.Ico (2 * j) (M + j), altWeight k|
          ≤ 2 * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
      calc
        |∑ k ∈ Finset.Ico (2 * j) (M + j), altWeight k|
            ≤ ∑ k ∈ Finset.Ico (2 * j) (M + j), |altWeight k| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k ∈ Finset.Ico (2 * j) (M + j), atkinsonModeWeight k := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              rw [show altWeight k = (-1 : ℝ) ^ (k + 1) * atkinsonModeWeight k by rfl]
              rw [abs_mul, abs_of_nonneg (atkinsonModeWeight_nonneg k)]
              simp
        _ ≤ ∑ k ∈ Finset.range (M + j + 1), atkinsonModeWeight k := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro k hk
                exact Finset.mem_range.mpr <| by
                  exact lt_of_lt_of_le (Finset.mem_Ico.mp hk).2 (Nat.le_succ _)
              · intro k hk hmem
                exact atkinsonModeWeight_nonneg k
        _ = ∑ k ∈ Finset.range (M + j + 1), ((k + 1 : ℝ) ^ (-1 / 2 : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              rw [atkinsonModeWeight]
              congr 1
              norm_num
        _ ≤ 2 * Real.sqrt ((M + j + 1 : ℕ) : ℝ) := by
              simpa [div_eq_mul_inv, show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by ring_nf] using
                Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le (M + j + 1)
        _ = 2 * Real.sqrt (((M + j : ℕ) : ℝ) + 1) := by
              congr 2
              norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
    calc
      ‖∑ k ∈ Finset.Ico (2 * j) (M + j), atkinsonCompleteBlockTargetK k j‖
          =
        ‖Bsqrt * (((∑ k ∈ Finset.Ico (2 * j) (M + j), altSqrt k : ℝ) : ℝ) : ℂ)
            +
          Bweight * (((∑ k ∈ Finset.Ico (2 * j) (M + j), altWeight k : ℝ) : ℝ) : ℂ)‖ := by
                rw [hsum]
      _ ≤ ‖Bsqrt * (((∑ k ∈ Finset.Ico (2 * j) (M + j), altSqrt k : ℝ) : ℝ) : ℂ)‖
            + ‖Bweight * (((∑ k ∈ Finset.Ico (2 * j) (M + j), altWeight k : ℝ) : ℝ) : ℂ)‖ := by
              exact norm_add_le _ _
      _ = (‖Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope‖ / j) *
              |∑ k ∈ Finset.Ico (2 * j) (M + j), altSqrt k|
            +
            (‖Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset‖ / j) *
              |∑ k ∈ Finset.Ico (2 * j) (M + j), altWeight k| := by
              rw [norm_mul, hBsqrt_norm, Complex.norm_real, Real.norm_eq_abs]
              rw [norm_mul, hBweight_norm, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (‖Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope‖ / j) *
              (2 * Real.sqrt (((M + j : ℕ) : ℝ) + 1))
            +
            (‖Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset‖ / j) *
              (2 * Real.sqrt (((M + j : ℕ) : ℝ) + 1)) := by
              gcongr
      _ = (2 * (‖Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope‖
              + ‖Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset‖)) *
            (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
              field_simp [show (j : ℝ) ≠ 0 by positivity]
      _ ≤ (2 * (‖Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope‖
              + ‖Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset‖) + 1) *
            (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
              have htarget_nonneg : 0 ≤ Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j := by
                positivity
              nlinarith

/-- Concrete large-`j` public-leaf reduction. Once the genuine shifted
complete-block integral is known to equal the explicit stationary-phase target
up to a pointwise `modeWeight / j` remainder, the inverse-phase cell prefix is
closed. -/
private theorem
    atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_completeBlockTargetK_remainder
    (herr :
      ∃ C_err > 0, ∃ J_err : ℕ, ∀ j : ℕ, J_err ≤ j → 3 ≤ j → 1 ≤ j → ∀ k : ℕ, 2 * j ≤ k →
        ‖((((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
              ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                HardyCosSmooth.hardyCosExp (k - j) t) - atkinsonCompleteBlockTargetK k j)‖
          ≤ C_err * (atkinsonModeWeight k / j)) :
    ∃ Cevent > 0, ∃ J0 : ℕ, ∀ j : ℕ, J0 ≤ j → 3 ≤ j → 1 ≤ j → ∀ m : ℕ,
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)‖
        ≤ Cevent * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
  exact
    atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_kTarget_and_modeWeight_remainder
      atkinsonCompleteBlockTargetK atkinsonCompleteBlockTargetK_prefix_bound herr

/-- Public-class bypass for the large-`j` no-log leaf. A complete-block-target
remainder bound gives the eventual estimate, and a separate finite patch for
shifts below the eventual cutoff packages the public provider without using the
large-shift core-prefix contraction route. -/
private theorem
    atkinson_shiftedInversePhaseCellPrefixBound_of_completeBlockTargetK_remainder_and_finite_patch
    (herr :
      ∃ C_err > 0, ∃ J_err : ℕ, ∀ j : ℕ, J_err ≤ j → 3 ≤ j → 1 ≤ j → ∀ k : ℕ, 2 * j ≤ k →
        ‖((((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
              ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                HardyCosSmooth.hardyCosExp (k - j) t) - atkinsonCompleteBlockTargetK k j)‖
          ≤ C_err * (atkinsonModeWeight k / j))
    (hpatch :
      ∀ J0 : ℕ, ∀ j : ℕ, 1 ≤ j → j < J0 →
        ∃ Cj > 0, ∀ m : ℕ,
          ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
              ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                atkinsonResonantShiftedPhaseWeightedCell n j)‖
            ≤ Cj * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j)) :
    AtkinsonShiftedInversePhaseCellPrefixBoundHyp := by
  obtain ⟨Cevent, hCevent, J0, hevent⟩ :=
    atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_completeBlockTargetK_remainder
      herr
  let J : ℕ := max 3 J0
  refine
    atkinson_shiftedInversePhaseCellPrefixBound_of_eventual_and_finite_patch
      (J0 := J) ?_ ?_
  · refine ⟨Cevent, hCevent, ?_⟩
    intro j hJ hj1 m
    exact hevent j (le_trans (Nat.le_max_right _ _) hJ)
      (le_trans (Nat.le_max_left _ _) hJ) hj1 m
  · intro j hj hjlt
    exact hpatch J j hj hjlt

/-- Equivalent concrete public-leaf reduction in the common block-parameter
coordinates `u ∈ Ioc 0 1` of the `k`-th Hardy block.

This is the same large-`j` remainder surface as
`atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_completeBlockTargetK_remainder`,
but expressed in the exact common interval used by the shifted complete-block
row integrands. -/
private theorem
    atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_commonBlockParamTargetK_remainder
    (herr :
      ∃ C_err > 0, ∃ J_err : ℕ, ∀ j : ℕ, J_err ≤ j → 3 ≤ j → 1 ≤ j → ∀ k : ℕ, 2 * j ≤ k →
        ‖((((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
              ∫ u in Ioc (0 : ℝ) 1,
                HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u) *
                  blockJacobian k u) - atkinsonCompleteBlockTargetK k j)‖
          ≤ C_err * (atkinsonModeWeight k / j)) :
    ∃ Cevent > 0, ∃ J0 : ℕ, ∀ j : ℕ, J0 ≤ j → 3 ≤ j → 1 ≤ j → ∀ m : ℕ,
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)‖
        ≤ Cevent * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_err, hC_err, J_err, herr'⟩ := herr
  refine
    atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_completeBlockTargetK_remainder
      ⟨C_err, hC_err, J_err, ?_⟩
  intro j hJ_err hj3 hj1 k hjk
  have hjk' : j ≤ k := by
    omega
  have hblock :
      ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
          HardyCosSmooth.hardyCosExp (k - j) t
        =
      ∫ u in Ioc (0 : ℝ) 1,
          HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u) *
            blockJacobian k u := by
    simpa using
      Aristotle.StationaryPhaseMainMode.hardyCosExp_completeBlock_eq_common_blockParamIntegral
        k j hj1 hjk'
  simpa [hblock] using herr' j hJ_err hj3 hj1 k hjk

/-- The shifted block-parameter remainder is the natural Hardy tail leaf behind
the complete-block-target pointwise remainder hypothesis. This isolates the
coordinate-change step before the public cell-prefix summation argument. -/
private theorem atkinson_completeBlockTargetK_remainder_of_shiftedBlockParamTargetK_remainder
    (herr :
      ∃ C_err > 0, ∃ J_err : ℕ, ∀ j : ℕ, J_err ≤ j → 3 ≤ j → 1 ≤ j → ∀ k : ℕ, 2 * j ≤ k →
        ‖((((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
              ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
                HardyCosSmooth.hardyCosExp (k - j) (blockCoord (k - j) p) *
                  blockJacobian (k - j) p) - atkinsonCompleteBlockTargetK k j)‖
          ≤ C_err * (atkinsonModeWeight k / j)) :
    ∃ C_err > 0, ∃ J_err : ℕ, ∀ j : ℕ, J_err ≤ j → 3 ≤ j → 1 ≤ j → ∀ k : ℕ, 2 * j ≤ k →
      ‖((((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
            ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
              HardyCosSmooth.hardyCosExp (k - j) t) - atkinsonCompleteBlockTargetK k j)‖
        ≤ C_err * (atkinsonModeWeight k / j) := by
  obtain ⟨C_err, hC_err, J_err, herr'⟩ := herr
  refine ⟨C_err, hC_err, J_err, ?_⟩
  intro j hJ_err hj3 hj1 k hjk
  have hblock :
      ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
          HardyCosSmooth.hardyCosExp (k - j) t
        =
      ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
          HardyCosSmooth.hardyCosExp (k - j) (blockCoord (k - j) p) *
            blockJacobian (k - j) p := by
    have hjk' : j ≤ k := by
      omega
    have hcast : ((k : ℝ) - ((k - j : ℕ) : ℝ)) = (j : ℝ) := by
      rw [Nat.cast_sub hjk']
      ring
    simpa [hcast, Nat.add_assoc, add_left_comm, add_comm] using
      Aristotle.StationaryPhaseMainMode.hardyCosExp_completeBlock_eq_shifted_blockParamIntegral
        (k - j) k (by omega)
  simpa [hblock] using herr' j hJ_err hj3 hj1 k hjk

/-- Native stationary-phase handoff for the shifted block remainder. The
imported stationary-phase API is phrased with `blockMode`; this wrapper unfolds
that notation to the Hardy exponential form consumed by the Atkinson reduction. -/
private theorem atkinson_shiftedBlockParamTargetK_remainder_of_blockMode_stationaryPhase
    (herr :
      ∃ C_err > 0, ∃ J_err : ℕ, ∀ j : ℕ, J_err ≤ j → 3 ≤ j → 1 ≤ j → ∀ k : ℕ, 2 * j ≤ k →
        ‖((((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
              ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
                Aristotle.StationaryPhaseMainMode.blockMode (k - j) p *
                  blockJacobian (k - j) p) - atkinsonCompleteBlockTargetK k j)‖
          ≤ C_err * (atkinsonModeWeight k / j)) :
    ∃ C_err > 0, ∃ J_err : ℕ, ∀ j : ℕ, J_err ≤ j → 3 ≤ j → 1 ≤ j → ∀ k : ℕ, 2 * j ≤ k →
      ‖((((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
            ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
              HardyCosSmooth.hardyCosExp (k - j) (blockCoord (k - j) p) *
                blockJacobian (k - j) p) - atkinsonCompleteBlockTargetK k j)‖
        ≤ C_err * (atkinsonModeWeight k / j) := by
  obtain ⟨C_err, hC_err, J_err, herr'⟩ := herr
  refine ⟨C_err, hC_err, J_err, ?_⟩
  intro j hJ_err hj3 hj1 k hjk
  simpa [Aristotle.StationaryPhaseMainMode.blockMode] using
    herr' j hJ_err hj3 hj1 k hjk

/-- Complete-block-target remainder reduced to the native `blockMode`
stationary-phase statement on the shifted interval `p ∈ Ioc j (j + 1)`. -/
private theorem atkinson_completeBlockTargetK_remainder_of_blockMode_stationaryPhase
    (herr :
      ∃ C_err > 0, ∃ J_err : ℕ, ∀ j : ℕ, J_err ≤ j → 3 ≤ j → 1 ≤ j → ∀ k : ℕ, 2 * j ≤ k →
        ‖((((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
              ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
                Aristotle.StationaryPhaseMainMode.blockMode (k - j) p *
                  blockJacobian (k - j) p) - atkinsonCompleteBlockTargetK k j)‖
          ≤ C_err * (atkinsonModeWeight k / j)) :
    ∃ C_err > 0, ∃ J_err : ℕ, ∀ j : ℕ, J_err ≤ j → 3 ≤ j → 1 ≤ j → ∀ k : ℕ, 2 * j ≤ k →
      ‖((((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
            ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
              HardyCosSmooth.hardyCosExp (k - j) t) - atkinsonCompleteBlockTargetK k j)‖
        ≤ C_err * (atkinsonModeWeight k / j) := by
  exact
    atkinson_completeBlockTargetK_remainder_of_shiftedBlockParamTargetK_remainder
      (atkinson_shiftedBlockParamTargetK_remainder_of_blockMode_stationaryPhase herr)

/-- Mode-indexed form of the native shifted-block stationary-phase remainder.
Stationary-phase estimates are naturally eventual in the Hardy mode `n`; this
wrapper removes the `k = n + j` arithmetic layer from the Atkinson target. -/
private theorem atkinson_blockMode_stationaryPhase_of_mode_eventual_shifted_interval_remainder
    (hmode :
      ∃ C_err > 0, ∃ N_err : ℕ, ∀ n : ℕ, N_err ≤ n → ∀ j : ℕ,
        3 ≤ j → 1 ≤ j → j ≤ n →
          ‖((((atkinsonModeWeight n : ℝ) : ℂ) *
                ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
                  Aristotle.StationaryPhaseMainMode.blockMode n p *
                    blockJacobian n p) - atkinsonCompleteBlockTargetK (n + j) j)‖
            ≤ C_err * (atkinsonModeWeight (n + j) / j)) :
    ∃ C_err > 0, ∃ J_err : ℕ, ∀ j : ℕ, J_err ≤ j → 3 ≤ j → 1 ≤ j → ∀ k : ℕ, 2 * j ≤ k →
      ‖((((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
            ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
              Aristotle.StationaryPhaseMainMode.blockMode (k - j) p *
                blockJacobian (k - j) p) - atkinsonCompleteBlockTargetK k j)‖
        ≤ C_err * (atkinsonModeWeight k / j) := by
  obtain ⟨C_err, hC_err, N_err, hmode'⟩ := hmode
  refine ⟨C_err, hC_err, N_err, ?_⟩
  intro j hJ hj3 hj1 k hjk
  have hkn : j ≤ k - j := by
    omega
  have hn_large : N_err ≤ k - j := le_trans hJ hkn
  have hkj : (k - j) + j = k := by
    omega
  simpa [hkj] using hmode' (k - j) hn_large j hj3 hj1 hkn

/-- The direct quadratic-anchor model for the shifted interval
`p ∈ Ioc j (j + 1)`: freeze `blockMode n p` at its stationary anchor and keep
the full shifted quadratic kernel integral. -/
private noncomputable def atkinsonShiftedQuadraticAnchorModel (n j : ℕ) : ℂ :=
  (((atkinsonModeWeight n : ℝ) : ℂ) *
    (((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
      Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor)) *
    ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
      Aristotle.StationaryPhaseMainMode.quadraticKernel p * blockJacobian n p)

/-- The same shifted quadratic model before replacing `blockMode n 0` by the
stationary anchor. -/
private noncomputable def atkinsonShiftedQuadraticBlockModeZeroModel (n j : ℕ) : ℂ :=
  (((atkinsonModeWeight n : ℝ) : ℂ) *
    Aristotle.StationaryPhaseMainMode.blockMode n 0 *
    ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
      Aristotle.StationaryPhaseMainMode.quadraticKernel p * blockJacobian n p)

/-- The native shifted-interval quadratic-anchor approximation follows from a
zero-model approximation plus the oscillatory bound for the shifted quadratic
kernel integral. The latter is the exact place where the missing `1 / j`
cancellation must enter. -/
private theorem atkinson_shifted_interval_quadratic_anchor_approx_of_zero_model_and_kernel_bound
    (hzeroModel :
      ∃ C_model > 0, ∃ N_model : ℕ, ∀ n : ℕ, N_model ≤ n → ∀ j : ℕ,
        3 ≤ j → 1 ≤ j → j ≤ n →
          ‖((((atkinsonModeWeight n : ℝ) : ℂ) *
                ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
                  Aristotle.StationaryPhaseMainMode.blockMode n p *
                    blockJacobian n p) - atkinsonShiftedQuadraticBlockModeZeroModel n j)‖
            ≤ C_model * (atkinsonModeWeight (n + j) / j))
    (hkernel :
      ∃ C_kernel > 0, ∀ n j : ℕ, 3 ≤ j → 1 ≤ j → j ≤ n →
        ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
            Aristotle.StationaryPhaseMainMode.quadraticKernel p * blockJacobian n p‖
          ≤ C_kernel * ((((n : ℝ) + 1) / atkinsonModeWeight n) *
              (atkinsonModeWeight (n + j) / j))) :
    ∃ C_quad > 0, ∃ N_quad : ℕ, ∀ n : ℕ, N_quad ≤ n → ∀ j : ℕ,
      3 ≤ j → 1 ≤ j → j ≤ n →
        ‖((((atkinsonModeWeight n : ℝ) : ℂ) *
              ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
                Aristotle.StationaryPhaseMainMode.blockMode n p *
                  blockJacobian n p) - atkinsonShiftedQuadraticAnchorModel n j)‖
          ≤ C_quad * (atkinsonModeWeight (n + j) / j) := by
  obtain ⟨C_model, hC_model, N_model, hzeroModel'⟩ := hzeroModel
  obtain ⟨C_kernel, hC_kernel, hkernel'⟩ := hkernel
  obtain ⟨C_zero, hC_zero, hzero⟩ :=
    Aristotle.StationaryPhaseMainMode.blockMode_zero_asymptotic
  refine ⟨C_model + C_zero * C_kernel, by positivity, N_model, ?_⟩
  intro n hn j hj3 hj1 hjn
  let actual : ℂ :=
    (((atkinsonModeWeight n : ℝ) : ℂ) *
      ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
        Aristotle.StationaryPhaseMainMode.blockMode n p * blockJacobian n p)
  let zeroModel : ℂ := atkinsonShiftedQuadraticBlockModeZeroModel n j
  let anchorModel : ℂ := atkinsonShiftedQuadraticAnchorModel n j
  let kernelInt : ℂ :=
    ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
      Aristotle.StationaryPhaseMainMode.quadraticKernel p * blockJacobian n p
  let anchor : ℂ :=
    ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
      Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor)
  let scale : ℝ := atkinsonModeWeight (n + j) / j
  have hactual_zero : ‖actual - zeroModel‖ ≤ C_model * scale := by
    simpa [actual, zeroModel, scale] using hzeroModel' n hn j hj3 hj1 hjn
  have hkernel_bound :
      ‖kernelInt‖
        ≤ C_kernel * ((((n : ℝ) + 1) / atkinsonModeWeight n) * scale) := by
    simpa [kernelInt, scale] using hkernel' n j hj3 hj1 hjn
  have hzero_bound :
      ‖Aristotle.StationaryPhaseMainMode.blockMode n 0 - anchor‖
        ≤ C_zero / ((n : ℝ) + 1) := by
    simpa [anchor] using hzero n
  have hweight_norm :
      ‖(((atkinsonModeWeight n : ℝ) : ℂ))‖ = atkinsonModeWeight n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (atkinsonModeWeight_nonneg n)]
  have hzero_anchor_eq :
      zeroModel - anchorModel =
        (((atkinsonModeWeight n : ℝ) : ℂ) *
          (Aristotle.StationaryPhaseMainMode.blockMode n 0 - anchor) *
          kernelInt) := by
    simp [zeroModel, anchorModel, atkinsonShiftedQuadraticBlockModeZeroModel,
      atkinsonShiftedQuadraticAnchorModel, kernelInt, anchor]
    ring
  have hzero_anchor : ‖zeroModel - anchorModel‖ ≤ (C_zero * C_kernel) * scale := by
    calc
      ‖zeroModel - anchorModel‖
          =
        ‖(((atkinsonModeWeight n : ℝ) : ℂ) *
            (Aristotle.StationaryPhaseMainMode.blockMode n 0 - anchor) *
            kernelInt)‖ := by
            rw [hzero_anchor_eq]
      _ =
        atkinsonModeWeight n *
          ‖Aristotle.StationaryPhaseMainMode.blockMode n 0 - anchor‖ *
          ‖kernelInt‖ := by
            rw [norm_mul, norm_mul, hweight_norm]
      _ ≤ atkinsonModeWeight n * (C_zero / ((n : ℝ) + 1)) *
          (C_kernel * ((((n : ℝ) + 1) / atkinsonModeWeight n) * scale)) := by
            gcongr
            exact mul_nonneg (atkinsonModeWeight_nonneg n)
              (div_nonneg hC_zero.le (by positivity))
            exact atkinsonModeWeight_nonneg n
      _ = (C_zero * C_kernel) * scale := by
            have hn_pos : 0 < ((n : ℝ) + 1) := by positivity
            have hw_pos : 0 < atkinsonModeWeight n := atkinsonModeWeight_pos n
            field_simp [hn_pos.ne', hw_pos.ne']
  have hsplit : actual - anchorModel = (actual - zeroModel) + (zeroModel - anchorModel) := by
    ring
  calc
    ‖((((atkinsonModeWeight n : ℝ) : ℂ) *
          ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
            Aristotle.StationaryPhaseMainMode.blockMode n p *
              blockJacobian n p) - atkinsonShiftedQuadraticAnchorModel n j)‖
        = ‖actual - anchorModel‖ := by
            simp [actual, anchorModel]
    _ = ‖(actual - zeroModel) + (zeroModel - anchorModel)‖ := by
          rw [hsplit]
    _ ≤ ‖actual - zeroModel‖ + ‖zeroModel - anchorModel‖ := norm_add_le _ _
    _ ≤ C_model * scale + (C_zero * C_kernel) * scale :=
          add_le_add hactual_zero hzero_anchor
    _ = (C_model + C_zero * C_kernel) * scale := by
          ring

/-- The shifted quadratic-kernel integral bound follows from the two natural
oscillatory pieces: `∫ exp(i2πp²)` has size `O(1 / j)`, while the
`4πp`-weighted piece is uniformly bounded by the exact derivative boundary
term. The remaining comparison is the elementary Atkinson weight scale. -/
private theorem atkinson_shifted_quadratic_kernel_integral_bound_of_mass_moment_scale
    (hmass :
      ∃ C_mass > 0, ∀ j : ℕ, 1 ≤ j →
        ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
            Aristotle.StationaryPhaseMainMode.quadraticKernel p‖ ≤ C_mass / j)
    (hmoment :
      ∃ C_moment > 0, ∀ j : ℕ, 1 ≤ j →
        ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
            (((4 * Real.pi * p : ℝ) : ℂ) *
              Aristotle.StationaryPhaseMainMode.quadraticKernel p)‖ ≤ C_moment)
    (hscale :
      ∃ C_scale > 0, ∀ n j : ℕ, 3 ≤ j → 1 ≤ j → j ≤ n →
        (((n : ℝ) + 1) / j + 1)
          ≤ C_scale * ((((n : ℝ) + 1) / atkinsonModeWeight n) *
              (atkinsonModeWeight (n + j) / j))) :
    ∃ C_kernel > 0, ∀ n j : ℕ, 3 ≤ j → 1 ≤ j → j ≤ n →
      ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
          Aristotle.StationaryPhaseMainMode.quadraticKernel p * blockJacobian n p‖
        ≤ C_kernel * ((((n : ℝ) + 1) / atkinsonModeWeight n) *
            (atkinsonModeWeight (n + j) / j)) := by
  obtain ⟨C_mass, hC_mass, hmass'⟩ := hmass
  obtain ⟨C_moment, hC_moment, hmoment'⟩ := hmoment
  obtain ⟨C_scale, hC_scale, hscale'⟩ := hscale
  refine ⟨(4 * Real.pi * C_mass + C_moment) * C_scale, by positivity, ?_⟩
  intro n j hj3 hj1 hjn
  let mass : ℂ :=
    ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
      Aristotle.StationaryPhaseMainMode.quadraticKernel p
  let moment : ℂ :=
    ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
      (((4 * Real.pi * p : ℝ) : ℂ) *
        Aristotle.StationaryPhaseMainMode.quadraticKernel p)
  let scale : ℝ :=
    (((n : ℝ) + 1) / atkinsonModeWeight n) * (atkinsonModeWeight (n + j) / j)
  have hcont_kernel :
      Continuous Aristotle.StationaryPhaseMainMode.quadraticKernel := by
    unfold Aristotle.StationaryPhaseMainMode.quadraticKernel
    continuity
  have hIntMass :
      IntegrableOn Aristotle.StationaryPhaseMainMode.quadraticKernel
        (Ioc (j : ℝ) ((j : ℝ) + 1)) := by
    exact hcont_kernel.integrableOn_Ioc
  have hIntMoment :
      IntegrableOn
        (fun p : ℝ =>
          (((4 * Real.pi * p : ℝ) : ℂ) *
            Aristotle.StationaryPhaseMainMode.quadraticKernel p))
        (Ioc (j : ℝ) ((j : ℝ) + 1)) := by
    have hcont :
        Continuous
          (fun p : ℝ =>
            (((4 * Real.pi * p : ℝ) : ℂ) *
              Aristotle.StationaryPhaseMainMode.quadraticKernel p)) := by
      exact (Complex.continuous_ofReal.comp
        (((continuous_const.mul continuous_const).mul continuous_id))).mul hcont_kernel
    exact hcont.integrableOn_Ioc
  have hrepr :
      (∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
          Aristotle.StationaryPhaseMainMode.quadraticKernel p * blockJacobian n p)
        =
      ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * mass) + moment) := by
    calc
      ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
          Aristotle.StationaryPhaseMainMode.quadraticKernel p * blockJacobian n p
          =
        ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
          ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) *
              Aristotle.StationaryPhaseMainMode.quadraticKernel p)
            +
            (((4 * Real.pi * p : ℝ) : ℂ) *
              Aristotle.StationaryPhaseMainMode.quadraticKernel p)) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with p hp
            rw [Aristotle.StationaryPhaseMainMode.blockJacobian_eq_affine]
            push_cast
            ring
      _ =
        ((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * mass) + moment) := by
          rw [MeasureTheory.integral_add (hIntMass.const_mul _) hIntMoment,
            MeasureTheory.integral_const_mul]
  have hmass_bound : ‖mass‖ ≤ C_mass / j := by
    simpa [mass] using hmass' j hj1
  have hmoment_bound : ‖moment‖ ≤ C_moment := by
    simpa [moment] using hmoment' j hj1
  let x : ℝ := ((n : ℝ) + 1) / j
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hraw :
      ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
          Aristotle.StationaryPhaseMainMode.quadraticKernel p * blockJacobian n p‖
        ≤ (4 * Real.pi * C_mass + C_moment) * (x + 1) := by
    have hcoef_nonneg : 0 ≤ 4 * Real.pi * ((n : ℝ) + 1) := by
      positivity
    have hA_nonneg : 0 ≤ 4 * Real.pi * C_mass := by
      positivity
    have hB_nonneg : 0 ≤ C_moment := le_of_lt hC_moment
    calc
      ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
          Aristotle.StationaryPhaseMainMode.quadraticKernel p * blockJacobian n p‖
          =
        ‖((((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * mass) + moment)‖ := by
          rw [hrepr]
      _ ≤ ‖(((4 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) * mass)‖ + ‖moment‖ :=
          norm_add_le _ _
      _ =
        (4 * Real.pi * ((n : ℝ) + 1)) * ‖mass‖ + ‖moment‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef_nonneg]
      _ ≤ (4 * Real.pi * ((n : ℝ) + 1)) * (C_mass / j) + C_moment := by
          gcongr
      _ = (4 * Real.pi * C_mass) * x + C_moment := by
          dsimp [x]
          ring
      _ ≤ (4 * Real.pi * C_mass + C_moment) * (x + 1) := by
          nlinarith [mul_nonneg hA_nonneg hx_nonneg, mul_nonneg hB_nonneg hx_nonneg]
  have hscale_bound : x + 1 ≤ C_scale * scale := by
    simpa [x, scale] using hscale' n j hj3 hj1 hjn
  calc
    ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
        Aristotle.StationaryPhaseMainMode.quadraticKernel p * blockJacobian n p‖
        ≤ (4 * Real.pi * C_mass + C_moment) * (x + 1) := hraw
    _ ≤ (4 * Real.pi * C_mass + C_moment) * (C_scale * scale) := by
          gcongr
    _ = ((4 * Real.pi * C_mass + C_moment) * C_scale) * scale := by
          ring

/-- Elementary Atkinson weight-scale comparison for the shifted quadratic
kernel bound. The only input is that, on `j ≤ n`, the weights
`atkinsonModeWeight n` and `atkinsonModeWeight (n + j)` differ by at most a
fixed factor. -/
private theorem atkinson_shifted_quadratic_kernel_weight_scale :
    ∃ C_scale > 0, ∀ n j : ℕ, 3 ≤ j → 1 ≤ j → j ≤ n →
      (((n : ℝ) + 1) / j + 1)
        ≤ C_scale * ((((n : ℝ) + 1) / atkinsonModeWeight n) *
            (atkinsonModeWeight (n + j) / j)) := by
  refine ⟨4, by norm_num, ?_⟩
  intro n j hj3 hj1 hjn
  let A : ℝ := (n : ℝ) + 1
  let w0 : ℝ := atkinsonModeWeight n
  let w1 : ℝ := atkinsonModeWeight (n + j)
  let base : ℝ := (A / w0) * (w1 / j)
  have hj_pos : (0 : ℝ) < j := by positivity
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hw0_pos : 0 < w0 := by
    dsimp [w0]
    exact atkinsonModeWeight_pos n
  have hw1_pos : 0 < w1 := by
    dsimp [w1]
    exact atkinsonModeWeight_pos (n + j)
  have hrel_le_sqrt_two :
      atkinsonShiftedRelativeWeight (n + j) j ≤ Real.sqrt 2 := by
    exact atkinsonShiftedRelativeWeight_le_sqrt_two (n + j) j (by omega)
  have hsqrt_two_le_two : Real.sqrt 2 ≤ (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hrel_le_two :
      atkinsonShiftedRelativeWeight (n + j) j ≤ (2 : ℝ) :=
    le_trans hrel_le_sqrt_two hsqrt_two_le_two
  have hrel_eq :
      atkinsonShiftedRelativeWeight (n + j) j = w0 / w1 := by
    dsimp [w0, w1]
    unfold atkinsonShiftedRelativeWeight
    have hsub : n + j - j = n := by omega
    rw [hsub]
  have hw0_le_two_w1 : w0 ≤ 2 * w1 := by
    have hdiv : w0 / w1 ≤ (2 : ℝ) := by
      simpa [hrel_eq] using hrel_le_two
    exact (div_le_iff₀ hw1_pos).1 hdiv
  have hw0_half_le_w1 : w0 / 2 ≤ w1 := by
    nlinarith
  have hone_le_A_div_j : (1 : ℝ) ≤ A / j := by
    have hj_le_A : (j : ℝ) ≤ A := by
      dsimp [A]
      exact_mod_cast (by omega : j ≤ n + 1)
    exact (le_div_iff₀ hj_pos).2 (by simpa using hj_le_A)
  have hlhs_le : A / j + 1 ≤ 2 * (A / j) := by
    nlinarith
  have hbase_lower : A / (2 * (j : ℝ)) ≤ base := by
    calc
      A / (2 * (j : ℝ)) = (A / w0) * ((w0 / 2) / j) := by
        field_simp [hw0_pos.ne', hj_pos.ne']
      _ ≤ (A / w0) * (w1 / j) := by
        have hleft_nonneg : 0 ≤ A / w0 := div_nonneg hA_pos.le hw0_pos.le
        have hright : (w0 / 2) / j ≤ w1 / j :=
          div_le_div_of_nonneg_right hw0_half_le_w1 hj_pos.le
        exact mul_le_mul_of_nonneg_left hright hleft_nonneg
  calc
    ((n : ℝ) + 1) / j + 1
        = A / j + 1 := by
          simp [A]
    _ ≤ 2 * (A / j) := hlhs_le
    _ = 4 * (A / (2 * (j : ℝ))) := by
          ring
    _ ≤ 4 * base := by
          exact mul_le_mul_of_nonneg_left hbase_lower (by norm_num : (0 : ℝ) ≤ 4)
    _ = 4 * ((((n : ℝ) + 1) / atkinsonModeWeight n) *
          (atkinsonModeWeight (n + j) / j)) := by
          simp [A, w0, w1, base]

/-- Derivative of the shifted quadratic kernel phase `2πp²`. -/
private lemma atkinson_quadraticKernel_phase_hasDerivAt (p : ℝ) :
    HasDerivAt (fun x : ℝ => 2 * Real.pi * x ^ 2) (4 * Real.pi * p) p := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * p) p := by
    simpa [pow_two] using ((hasDerivAt_id p).pow 2)
  have hmul : HasDerivAt (fun x : ℝ => 2 * Real.pi * x ^ 2)
      ((2 * Real.pi) * (2 * p)) p := by
    simpa [pow_two, mul_assoc] using (HasDerivAt.const_mul (2 * Real.pi) hpow)
  convert hmul using 1 <;> ring

/-- The exact derivative identity behind the shifted weighted quadratic
moment: `quadraticKernel' p = i * (4πp) * quadraticKernel p`. -/
private lemma atkinson_quadraticKernel_hasDerivAt (p : ℝ) :
    HasDerivAt Aristotle.StationaryPhaseMainMode.quadraticKernel
      (Complex.I * (((4 * Real.pi * p : ℝ) : ℂ)) *
        Aristotle.StationaryPhaseMainMode.quadraticKernel p) p := by
  have hphaseC :
      HasDerivAt (fun x : ℝ => ((2 * Real.pi * x ^ 2 : ℝ) : ℂ))
        (((4 * Real.pi * p : ℝ) : ℂ)) p := by
    exact HasDerivAt.ofReal_comp (atkinson_quadraticKernel_phase_hasDerivAt p)
  have harg :
      HasDerivAt
        (fun x : ℝ => Complex.I * (((2 * Real.pi * x ^ 2 : ℝ) : ℂ)))
        (Complex.I * (((4 * Real.pi * p : ℝ) : ℂ))) p := by
    simpa [mul_assoc] using hphaseC.const_mul Complex.I
  change
    HasDerivAt
      (fun x : ℝ => Complex.exp (Complex.I * (((2 * Real.pi * x ^ 2 : ℝ) : ℂ))))
      (Complex.I * (((4 * Real.pi * p : ℝ) : ℂ)) *
        Aristotle.StationaryPhaseMainMode.quadraticKernel p) p
  simpa [Aristotle.StationaryPhaseMainMode.quadraticKernel, mul_assoc, mul_left_comm, mul_comm]
    using harg.cexp

/-- Exact FTC boundary identity for the `4πp`-weighted shifted quadratic
moment. This closes the uniform weighted moment atom; the only remaining
oscillatory input for the shifted quadratic kernel is the unweighted mass
`O(1 / j)` estimate. -/
private theorem atkinson_shifted_quadratic_weighted_moment_boundary_identity :
    ∀ j : ℕ, 1 ≤ j →
      (∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
          (((4 * Real.pi * p : ℝ) : ℂ) *
            Aristotle.StationaryPhaseMainMode.quadraticKernel p))
        =
      (-Complex.I) *
        (Aristotle.StationaryPhaseMainMode.quadraticKernel ((j : ℝ) + 1) -
          Aristotle.StationaryPhaseMainMode.quadraticKernel (j : ℝ)) := by
  intro j _hj
  let a : ℝ := j
  let b : ℝ := (j : ℝ) + 1
  let q : ℝ → ℂ := Aristotle.StationaryPhaseMainMode.quadraticKernel
  let g : ℝ → ℂ := fun p => (((4 * Real.pi * p : ℝ) : ℂ) * q p)
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt q (Complex.I * g x) x := by
    intro x _hx
    dsimp [q, g]
    simpa [mul_assoc] using atkinson_quadraticKernel_hasDerivAt x
  have hcont_q : Continuous q := by
    dsimp [q]
    unfold Aristotle.StationaryPhaseMainMode.quadraticKernel
    continuity
  have hcont_g : Continuous g := by
    dsimp [g]
    exact (Complex.continuous_ofReal.comp
      (((continuous_const.mul continuous_const).mul continuous_id))).mul hcont_q
  have hint : IntervalIntegrable (fun p : ℝ => Complex.I * g p) volume a b := by
    simpa using (((continuous_const : Continuous fun _ : ℝ => Complex.I).mul hcont_g).intervalIntegrable a b)
  have hFTC : ∫ p in a..b, Complex.I * g p = q b - q a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hundo (z : ℂ) : z = (-Complex.I) * (Complex.I * z) := by
    have hI : (-Complex.I) * Complex.I = 1 := by norm_num
    calc
      z = 1 * z := by simp
      _ = ((-Complex.I) * Complex.I) * z := by rw [hI]
      _ = (-Complex.I) * (Complex.I * z) := by ring
  calc
    ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
        (((4 * Real.pi * p : ℝ) : ℂ) *
          Aristotle.StationaryPhaseMainMode.quadraticKernel p)
        = ∫ p in a..b, g p := by
            change ∫ p in Ioc a b, g p = ∫ p in a..b, g p
            rw [← intervalIntegral.integral_of_le hab]
    _ = (-Complex.I) * (∫ p in a..b, Complex.I * g p) := by
          rw [intervalIntegral.integral_const_mul]
          exact hundo (∫ p in a..b, g p)
    _ = (-Complex.I) * (q b - q a) := by
          rw [hFTC]
    _ =
      (-Complex.I) *
        (Aristotle.StationaryPhaseMainMode.quadraticKernel ((j : ℝ) + 1) -
          Aristotle.StationaryPhaseMainMode.quadraticKernel (j : ℝ)) := by
          rfl

/-- The weighted shifted quadratic moment is uniformly bounded once the exact
FTC boundary identity for the quadratic kernel is available. This isolates the
remaining analytic step to proving that
`d/dp quadraticKernel p = i * (4πp) * quadraticKernel p` on each shifted
cell and converting the interval integral to the `Ioc` form. -/
private theorem atkinson_shifted_quadratic_weighted_moment_bound_of_boundary_identity
    (hboundary :
      ∀ j : ℕ, 1 ≤ j →
        (∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
            (((4 * Real.pi * p : ℝ) : ℂ) *
              Aristotle.StationaryPhaseMainMode.quadraticKernel p))
          =
        (-Complex.I) *
          (Aristotle.StationaryPhaseMainMode.quadraticKernel ((j : ℝ) + 1) -
            Aristotle.StationaryPhaseMainMode.quadraticKernel (j : ℝ))) :
    ∃ C_moment > 0, ∀ j : ℕ, 1 ≤ j →
      ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
          (((4 * Real.pi * p : ℝ) : ℂ) *
            Aristotle.StationaryPhaseMainMode.quadraticKernel p)‖ ≤ C_moment := by
  refine ⟨2, by norm_num, ?_⟩
  intro j hj
  have hnorm_kernel (x : ℝ) :
      ‖Aristotle.StationaryPhaseMainMode.quadraticKernel x‖ = 1 := by
    unfold Aristotle.StationaryPhaseMainMode.quadraticKernel
    exact Complex.norm_exp_I_mul_ofReal (2 * Real.pi * x ^ 2)
  calc
    ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
        (((4 * Real.pi * p : ℝ) : ℂ) *
          Aristotle.StationaryPhaseMainMode.quadraticKernel p)‖
        =
      ‖(-Complex.I) *
        (Aristotle.StationaryPhaseMainMode.quadraticKernel ((j : ℝ) + 1) -
          Aristotle.StationaryPhaseMainMode.quadraticKernel (j : ℝ))‖ := by
          rw [hboundary j hj]
    _ =
      ‖Aristotle.StationaryPhaseMainMode.quadraticKernel ((j : ℝ) + 1) -
        Aristotle.StationaryPhaseMainMode.quadraticKernel (j : ℝ)‖ := by
          rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    _ ≤
      ‖Aristotle.StationaryPhaseMainMode.quadraticKernel ((j : ℝ) + 1)‖ +
        ‖Aristotle.StationaryPhaseMainMode.quadraticKernel (j : ℝ)‖ :=
          norm_sub_le _ _
    _ = 2 := by
          rw [hnorm_kernel, hnorm_kernel]
          norm_num

/-- The weighted shifted quadratic moment is uniformly bounded by the exact
quadratic-kernel boundary identity. -/
private theorem atkinson_shifted_quadratic_weighted_moment_bound :
    ∃ C_moment > 0, ∀ j : ℕ, 1 ≤ j →
      ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
          (((4 * Real.pi * p : ℝ) : ℂ) *
            Aristotle.StationaryPhaseMainMode.quadraticKernel p)‖ ≤ C_moment := by
  exact
    atkinson_shifted_quadratic_weighted_moment_bound_of_boundary_identity
      atkinson_shifted_quadratic_weighted_moment_boundary_identity

/-- Kernel bound with the elementary weight scale discharged; the remaining
inputs are exactly the two shifted Fresnel estimates. -/
private theorem atkinson_shifted_quadratic_kernel_integral_bound_of_mass_moment
    (hmass :
      ∃ C_mass > 0, ∀ j : ℕ, 1 ≤ j →
        ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
            Aristotle.StationaryPhaseMainMode.quadraticKernel p‖ ≤ C_mass / j)
    (hmoment :
      ∃ C_moment > 0, ∀ j : ℕ, 1 ≤ j →
        ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
            (((4 * Real.pi * p : ℝ) : ℂ) *
              Aristotle.StationaryPhaseMainMode.quadraticKernel p)‖ ≤ C_moment) :
    ∃ C_kernel > 0, ∀ n j : ℕ, 3 ≤ j → 1 ≤ j → j ≤ n →
      ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
          Aristotle.StationaryPhaseMainMode.quadraticKernel p * blockJacobian n p‖
        ≤ C_kernel * ((((n : ℝ) + 1) / atkinsonModeWeight n) *
            (atkinsonModeWeight (n + j) / j)) := by
  exact
    atkinson_shifted_quadratic_kernel_integral_bound_of_mass_moment_scale
      hmass hmoment atkinson_shifted_quadratic_kernel_weight_scale

/-- Kernel bound after replacing the weighted moment atom by its exact
quadratic-kernel boundary identity. The only remaining independent Fresnel
input is the shifted mass `O(1 / j)` estimate. -/
private theorem atkinson_shifted_quadratic_kernel_integral_bound_of_mass_boundary
    (hmass :
      ∃ C_mass > 0, ∀ j : ℕ, 1 ≤ j →
        ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
            Aristotle.StationaryPhaseMainMode.quadraticKernel p‖ ≤ C_mass / j)
    (hboundary :
      ∀ j : ℕ, 1 ≤ j →
        (∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
            (((4 * Real.pi * p : ℝ) : ℂ) *
              Aristotle.StationaryPhaseMainMode.quadraticKernel p))
          =
        (-Complex.I) *
          (Aristotle.StationaryPhaseMainMode.quadraticKernel ((j : ℝ) + 1) -
            Aristotle.StationaryPhaseMainMode.quadraticKernel (j : ℝ))) :
    ∃ C_kernel > 0, ∀ n j : ℕ, 3 ≤ j → 1 ≤ j → j ≤ n →
      ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
          Aristotle.StationaryPhaseMainMode.quadraticKernel p * blockJacobian n p‖
        ≤ C_kernel * ((((n : ℝ) + 1) / atkinsonModeWeight n) *
            (atkinsonModeWeight (n + j) / j)) := by
  exact
    atkinson_shifted_quadratic_kernel_integral_bound_of_mass_moment hmass
      (atkinson_shifted_quadratic_weighted_moment_bound_of_boundary_identity hboundary)

/-- Kernel bound with the weighted moment discharged by FTC. The shifted mass
`O(1 / j)` estimate is now the only remaining Fresnel atom for this kernel
leaf. -/
private theorem atkinson_shifted_quadratic_kernel_integral_bound_of_mass
    (hmass :
      ∃ C_mass > 0, ∀ j : ℕ, 1 ≤ j →
        ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
            Aristotle.StationaryPhaseMainMode.quadraticKernel p‖ ≤ C_mass / j) :
    ∃ C_kernel > 0, ∀ n j : ℕ, 3 ≤ j → 1 ≤ j → j ≤ n →
      ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
          Aristotle.StationaryPhaseMainMode.quadraticKernel p * blockJacobian n p‖
        ≤ C_kernel * ((((n : ℝ) + 1) / atkinsonModeWeight n) *
            (atkinsonModeWeight (n + j) / j)) := by
  exact
    atkinson_shifted_quadratic_kernel_integral_bound_of_mass_boundary hmass
      atkinson_shifted_quadratic_weighted_moment_boundary_identity

/-- The angular velocity of `quadraticKernel` is the linear function `4πp`. -/
private lemma atkinson_quadraticKernel_omega_hasDerivAt (p : ℝ) :
    HasDerivAt (fun x : ℝ => 4 * Real.pi * x) (4 * Real.pi) p := by
  simpa using (hasDerivAt_id p).const_mul (4 * Real.pi)

private lemma atkinson_quadraticKernel_omega_differentiable :
    Differentiable ℝ (fun x : ℝ => 4 * Real.pi * x) := by
  intro p
  exact (atkinson_quadraticKernel_omega_hasDerivAt p).differentiableAt

private lemma atkinson_quadraticKernel_omega_deriv (p : ℝ) :
    deriv (fun x : ℝ => 4 * Real.pi * x) p = 4 * Real.pi := by
  exact (atkinson_quadraticKernel_omega_hasDerivAt p).deriv

private lemma atkinson_quadraticKernel_omega_deriv_continuous :
    Continuous (deriv (fun x : ℝ => 4 * Real.pi * x)) := by
  have hderiv :
      deriv (fun x : ℝ => 4 * Real.pi * x) = fun _ : ℝ => 4 * Real.pi := by
    funext p
    exact atkinson_quadraticKernel_omega_deriv p
  rw [hderiv]
  continuity

/-- Shifted quadratic Fresnel mass bound on each cell. This is the complex VdC
first-derivative test applied to `quadraticKernel`, whose angular velocity
`4πp` is bounded below by `4πj` on `p ∈ [j, j + 1]`. -/
private theorem atkinson_shifted_quadratic_mass_bound :
    ∃ C_mass > 0, ∀ j : ℕ, 1 ≤ j →
      ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
          Aristotle.StationaryPhaseMainMode.quadraticKernel p‖ ≤ C_mass / j := by
  refine ⟨3, by norm_num, ?_⟩
  intro j hj
  let a : ℝ := j
  let b : ℝ := (j : ℝ) + 1
  let q : ℝ → ℂ := Aristotle.StationaryPhaseMainMode.quadraticKernel
  let omega : ℝ → ℝ := fun p => 4 * Real.pi * p
  let m : ℝ := 4 * Real.pi * (j : ℝ)
  have hj_nat_pos : 0 < j := lt_of_lt_of_le (by norm_num) hj
  have hj_pos : (0 : ℝ) < j := by exact_mod_cast hj_nat_pos
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have hm_pos : 0 < m := by
    dsimp [m]
    positivity
  have hbound_interval : ‖∫ p in a..b, q p‖ ≤ 3 / m := by
    refine
      Aristotle.ComplexVdC.complex_vdc_angular q omega a b m hab hm_pos ?_ ?_ ?_ ?_ ?_ ?_
    · intro p hp
      dsimp [q, omega]
      simpa [mul_assoc] using atkinson_quadraticKernel_hasDerivAt p
    · intro p hp
      have hnorm : ‖q p‖ = 1 := by
        dsimp [q]
        unfold Aristotle.StationaryPhaseMainMode.quadraticKernel
        exact Complex.norm_exp_I_mul_ofReal (2 * Real.pi * p ^ 2)
      rw [hnorm]
    · dsimp [omega]
      exact atkinson_quadraticKernel_omega_differentiable
    · dsimp [omega]
      exact atkinson_quadraticKernel_omega_deriv_continuous
    · intro p hp
      have hp_ge : (j : ℝ) ≤ p := by
        have hp' : p ∈ Icc a b := hp
        simpa [a] using hp'.1
      dsimp [omega, m]
      nlinarith [Real.pi_pos, hp_ge]
    · intro p hp
      dsimp [omega]
      rw [atkinson_quadraticKernel_omega_deriv]
      positivity
  calc
    ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
        Aristotle.StationaryPhaseMainMode.quadraticKernel p‖
        = ‖∫ p in a..b, q p‖ := by
            congr 1
            change
              ∫ p in Ioc a b, q p = ∫ p in a..b, q p
            rw [← intervalIntegral.integral_of_le hab]
    _ ≤ 3 / m := hbound_interval
    _ ≤ 3 / j := by
          have hden_le : (j : ℝ) ≤ m := by
            dsimp [m]
            nlinarith [Real.pi_gt_three, hj_pos]
          exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) hj_pos hden_le

/-- Shifted quadratic-kernel integral bound with both Fresnel atoms discharged:
the weighted moment by FTC and the mass by complex VdC. -/
private theorem atkinson_shifted_quadratic_kernel_integral_bound :
    ∃ C_kernel > 0, ∀ n j : ℕ, 3 ≤ j → 1 ≤ j → j ≤ n →
      ‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
          Aristotle.StationaryPhaseMainMode.quadraticKernel p * blockJacobian n p‖
        ≤ C_kernel * ((((n : ℝ) + 1) / atkinsonModeWeight n) *
            (atkinsonModeWeight (n + j) / j)) := by
  exact
    atkinson_shifted_quadratic_kernel_integral_bound_of_mass
      atkinson_shifted_quadratic_mass_bound

/-- Native shifted-interval quadratic-anchor approximation with the shifted
quadratic-kernel bound discharged. The only remaining input is the local
zero-model approximation for `blockMode n p` on `p ∈ Ioc j (j + 1)`. -/
private theorem atkinson_shifted_interval_quadratic_anchor_approx_of_zero_model
    (hzeroModel :
      ∃ C_model > 0, ∃ N_model : ℕ, ∀ n : ℕ, N_model ≤ n → ∀ j : ℕ,
        3 ≤ j → 1 ≤ j → j ≤ n →
          ‖((((atkinsonModeWeight n : ℝ) : ℂ) *
                ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
                  Aristotle.StationaryPhaseMainMode.blockMode n p *
                    blockJacobian n p) - atkinsonShiftedQuadraticBlockModeZeroModel n j)‖
            ≤ C_model * (atkinsonModeWeight (n + j) / j)) :
    ∃ C_quad > 0, ∃ N_quad : ℕ, ∀ n : ℕ, N_quad ≤ n → ∀ j : ℕ,
      3 ≤ j → 1 ≤ j → j ≤ n →
        ‖((((atkinsonModeWeight n : ℝ) : ℂ) *
              ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
                Aristotle.StationaryPhaseMainMode.blockMode n p *
                  blockJacobian n p) - atkinsonShiftedQuadraticAnchorModel n j)‖
          ≤ C_quad * (atkinsonModeWeight (n + j) / j) := by
  exact
    atkinson_shifted_interval_quadratic_anchor_approx_of_zero_model_and_kernel_bound
      hzeroModel atkinson_shifted_quadratic_kernel_integral_bound

/-- The mode-eventual shifted-interval `blockMode` remainder follows once the
native integral is close to the quadratic-anchor model and that model matches
the explicit Atkinson complete-block target. -/
private theorem atkinson_mode_eventual_shifted_interval_remainder_of_quadratic_anchor_model
    (hquad :
      ∃ C_quad > 0, ∃ N_quad : ℕ, ∀ n : ℕ, N_quad ≤ n → ∀ j : ℕ,
        3 ≤ j → 1 ≤ j → j ≤ n →
          ‖((((atkinsonModeWeight n : ℝ) : ℂ) *
                ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
                  Aristotle.StationaryPhaseMainMode.blockMode n p *
                    blockJacobian n p) - atkinsonShiftedQuadraticAnchorModel n j)‖
            ≤ C_quad * (atkinsonModeWeight (n + j) / j))
    (htarget :
      ∃ C_target > 0, ∃ N_target : ℕ, ∀ n : ℕ, N_target ≤ n → ∀ j : ℕ,
        3 ≤ j → 1 ≤ j → j ≤ n →
          ‖(atkinsonShiftedQuadraticAnchorModel n j - atkinsonCompleteBlockTargetK (n + j) j)‖
            ≤ C_target * (atkinsonModeWeight (n + j) / j)) :
    ∃ C_err > 0, ∃ N_err : ℕ, ∀ n : ℕ, N_err ≤ n → ∀ j : ℕ,
      3 ≤ j → 1 ≤ j → j ≤ n →
        ‖((((atkinsonModeWeight n : ℝ) : ℂ) *
              ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
                Aristotle.StationaryPhaseMainMode.blockMode n p *
                  blockJacobian n p) - atkinsonCompleteBlockTargetK (n + j) j)‖
          ≤ (C_err * (atkinsonModeWeight (n + j) / j)) := by
  obtain ⟨C_quad, hC_quad, N_quad, hquad'⟩ := hquad
  obtain ⟨C_target, hC_target, N_target, htarget'⟩ := htarget
  refine ⟨C_quad + C_target, add_pos hC_quad hC_target, max N_quad N_target, ?_⟩
  intro n hn j hj3 hj1 hjn
  have hn_quad : N_quad ≤ n := le_trans (Nat.le_max_left N_quad N_target) hn
  have hn_target : N_target ≤ n := le_trans (Nat.le_max_right N_quad N_target) hn
  let actual : ℂ :=
    (((atkinsonModeWeight n : ℝ) : ℂ) *
      ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
        Aristotle.StationaryPhaseMainMode.blockMode n p * blockJacobian n p)
  let model : ℂ := atkinsonShiftedQuadraticAnchorModel n j
  let target : ℂ := atkinsonCompleteBlockTargetK (n + j) j
  let scale : ℝ := atkinsonModeWeight (n + j) / j
  have hquad_bound : ‖actual - model‖ ≤ C_quad * scale := by
    simpa [actual, model, scale] using hquad' n hn_quad j hj3 hj1 hjn
  have htarget_bound : ‖model - target‖ ≤ C_target * scale := by
    simpa [model, target, scale] using htarget' n hn_target j hj3 hj1 hjn
  have hsplit : actual - target = (actual - model) + (model - target) := by
    ring
  calc
    ‖((((atkinsonModeWeight n : ℝ) : ℂ) *
          ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
            Aristotle.StationaryPhaseMainMode.blockMode n p *
              blockJacobian n p) - atkinsonCompleteBlockTargetK (n + j) j)‖
        = ‖actual - target‖ := by
            simp [actual, target]
    _ = ‖(actual - model) + (model - target)‖ := by
          rw [hsplit]
    _ ≤ ‖actual - model‖ + ‖model - target‖ := norm_add_le _ _
    _ ≤ C_quad * scale + C_target * scale := add_le_add hquad_bound htarget_bound
    _ = (C_quad + C_target) * scale := by
          ring

/-- Mode-eventual shifted-interval remainder with the shifted quadratic kernel
fully discharged. The surviving proof obligations are the zero-model
approximation and the explicit target-matching estimate. -/
private theorem atkinson_mode_eventual_shifted_interval_remainder_of_zero_model_and_target
    (hzeroModel :
      ∃ C_model > 0, ∃ N_model : ℕ, ∀ n : ℕ, N_model ≤ n → ∀ j : ℕ,
        3 ≤ j → 1 ≤ j → j ≤ n →
          ‖((((atkinsonModeWeight n : ℝ) : ℂ) *
                ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
                  Aristotle.StationaryPhaseMainMode.blockMode n p *
                    blockJacobian n p) - atkinsonShiftedQuadraticBlockModeZeroModel n j)‖
            ≤ C_model * (atkinsonModeWeight (n + j) / j))
    (htarget :
      ∃ C_target > 0, ∃ N_target : ℕ, ∀ n : ℕ, N_target ≤ n → ∀ j : ℕ,
        3 ≤ j → 1 ≤ j → j ≤ n →
          ‖(atkinsonShiftedQuadraticAnchorModel n j - atkinsonCompleteBlockTargetK (n + j) j)‖
            ≤ C_target * (atkinsonModeWeight (n + j) / j)) :
    ∃ C_err > 0, ∃ N_err : ℕ, ∀ n : ℕ, N_err ≤ n → ∀ j : ℕ,
      3 ≤ j → 1 ≤ j → j ≤ n →
        ‖((((atkinsonModeWeight n : ℝ) : ℂ) *
              ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
                Aristotle.StationaryPhaseMainMode.blockMode n p *
                  blockJacobian n p) - atkinsonCompleteBlockTargetK (n + j) j)‖
          ≤ (C_err * (atkinsonModeWeight (n + j) / j)) := by
  exact
    atkinson_mode_eventual_shifted_interval_remainder_of_quadratic_anchor_model
      (atkinson_shifted_interval_quadratic_anchor_approx_of_zero_model hzeroModel)
      htarget

/-- Complete-block-target stationary-phase handoff after discharging the
shifted quadratic-kernel estimates. This is the narrowed interface directly
below the public Atkinson leaf. -/
private theorem atkinson_blockMode_stationaryPhase_of_zero_model_and_target
    (hzeroModel :
      ∃ C_model > 0, ∃ N_model : ℕ, ∀ n : ℕ, N_model ≤ n → ∀ j : ℕ,
        3 ≤ j → 1 ≤ j → j ≤ n →
          ‖((((atkinsonModeWeight n : ℝ) : ℂ) *
                ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
                  Aristotle.StationaryPhaseMainMode.blockMode n p *
                    blockJacobian n p) - atkinsonShiftedQuadraticBlockModeZeroModel n j)‖
            ≤ C_model * (atkinsonModeWeight (n + j) / j))
    (htarget :
      ∃ C_target > 0, ∃ N_target : ℕ, ∀ n : ℕ, N_target ≤ n → ∀ j : ℕ,
        3 ≤ j → 1 ≤ j → j ≤ n →
          ‖(atkinsonShiftedQuadraticAnchorModel n j - atkinsonCompleteBlockTargetK (n + j) j)‖
            ≤ C_target * (atkinsonModeWeight (n + j) / j)) :
    ∃ C_err > 0, ∃ J_err : ℕ, ∀ j : ℕ, J_err ≤ j → 3 ≤ j → 1 ≤ j → ∀ k : ℕ, 2 * j ≤ k →
      ‖((((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
            ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
              Aristotle.StationaryPhaseMainMode.blockMode (k - j) p *
                blockJacobian (k - j) p) - atkinsonCompleteBlockTargetK k j)‖
        ≤ C_err * (atkinsonModeWeight k / j) := by
  exact
    atkinson_blockMode_stationaryPhase_of_mode_eventual_shifted_interval_remainder
      (atkinson_mode_eventual_shifted_interval_remainder_of_zero_model_and_target
        hzeroModel htarget)

/-- Equivalent concrete public-leaf reduction in the shifted block-parameter
coordinates of the mode `k - j`.

This is the same large-`j` remainder surface as
`atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_completeBlockTargetK_remainder`,
but expressed over `p ∈ Ioc j (j + 1)`. That is the natural coordinate system
for the imported Hardy stationary-phase tail theorems, so this wrapper exposes
the exact next analytic leaf without changing the public consequence. -/
private theorem
    atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_shiftedBlockParamTargetK_remainder
    (herr :
      ∃ C_err > 0, ∃ J_err : ℕ, ∀ j : ℕ, J_err ≤ j → 3 ≤ j → 1 ≤ j → ∀ k : ℕ, 2 * j ≤ k →
        ‖((((atkinsonModeWeight (k - j) : ℝ) : ℂ) *
              ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),
                HardyCosSmooth.hardyCosExp (k - j) (blockCoord (k - j) p) *
                  blockJacobian (k - j) p) - atkinsonCompleteBlockTargetK k j)‖
          ≤ C_err * (atkinsonModeWeight k / j)) :
    ∃ Cevent > 0, ∃ J0 : ℕ, ∀ j : ℕ, J0 ≤ j → 3 ≤ j → 1 ≤ j → ∀ m : ℕ,
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)‖
        ≤ Cevent * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
  exact
    atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_completeBlockTargetK_remainder
      (atkinson_completeBlockTargetK_remainder_of_shiftedBlockParamTargetK_remainder herr)

/-- On the genuine near-band `n ≥ j - 1`, the phase-weighted fixed-shift block
prefix is already `O(√(m+j))`. The phase factor converts the cellwise
`√(n+j)/j` loss into a summable `1 / √(n+j)` profile. -/
private theorem atkinsonResonantShiftedPhaseWeightedFixedShiftPrefix_bound_eventually :
    ∃ C > 0, ∃ J0 : ℕ, ∀ j : ℕ, J0 ≤ j →
      ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1), atkinsonResonantShiftedPhaseWeightedCell n j‖
          ≤ C * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
  obtain ⟨C0, hC0, N0, hcell⟩ := atkinson_weighted_shifted_completeBlock_complex_bound_eventually
  let J0 : ℕ := max 1 N0
  let C : ℝ := 4 * C0
  refine ⟨C, by
    dsimp [C]
    positivity, J0, ?_⟩
  intro j hj m
  calc
    ‖∑ n ∈ Finset.Ico (j - 1) (m + 1), atkinsonResonantShiftedPhaseWeightedCell n j‖
        ≤ ∑ n ∈ Finset.Ico (j - 1) (m + 1), ‖atkinsonResonantShiftedPhaseWeightedCell n j‖ :=
          norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ico (j - 1) (m + 1), 2 * C0 * atkinsonModeWeight (n + j) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hn_lo : j - 1 ≤ n := (Finset.mem_Ico.mp hn).1
          have hj_one : 1 ≤ j := by
            have hJ0 : 1 ≤ J0 := by
              dsimp [J0]
              exact Nat.le_max_left _ _
            exact le_trans hJ0 hj
          have hk_large : N0 ≤ n + j := by
            have hN0_le_J0 : N0 ≤ J0 := by
              dsimp [J0]
              exact Nat.le_max_right _ _
            omega
          have hhalf : j ≤ (n + j + 1) / 2 := by
            omega
          have hphase_nonneg : 0 ≤ atkinsonShiftedRelativePhase (n + j) j := by
            exact (atkinsonShiftedRelativePhase_pos (n + j) j hj_one (by omega)).le
          have hphase_upper :
              atkinsonShiftedRelativePhase (n + j) j ≤ (j : ℝ) / ((n : ℝ) + 1) := by
            simpa [Nat.add_sub_cancel_right, Nat.cast_add, add_assoc, add_left_comm, add_comm] using
              atkinsonShiftedRelativePhase_upper (n + j) j hj_one (by omega)
          have hweighted :
              ‖(((atkinsonModeWeight n : ℝ) : ℂ) *
                  ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
                    HardyCosSmooth.hardyCosExp n t)‖
                ≤ C0 * Real.sqrt ((((n + j : ℕ) : ℝ) + 1)) / j := by
            simpa using hcell (n + j) hk_large j hj_one hhalf
          have hrow_eq :
              (((atkinsonModeWeight n : ℝ) : ℂ) *
                  ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
                    HardyCosSmooth.hardyCosExp n t)
                =
              ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u := by
            have hblock :=
              Aristotle.StationaryPhaseMainMode.hardyCosExp_completeBlock_eq_common_blockParamIntegral
                (n + j) j hj_one (by omega)
            have hblock' :
                ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
                  HardyCosSmooth.hardyCosExp n t
                  =
                ∫ u in Ioc (0 : ℝ) 1,
                  HardyCosSmooth.hardyCosExp n (blockCoord (n + j) u) *
                    blockJacobian (n + j) u := by
              simpa using hblock
            calc
              (((atkinsonModeWeight n : ℝ) : ℂ) *
                  ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
                    HardyCosSmooth.hardyCosExp n t)
                  =
                (((atkinsonModeWeight n : ℝ) : ℂ) *
                  ∫ u in Ioc (0 : ℝ) 1,
                    HardyCosSmooth.hardyCosExp n (blockCoord (n + j) u) *
                      blockJacobian (n + j) u) := by
                    rw [hblock']
              _ =
                ∫ u in Ioc (0 : ℝ) 1, atkinsonComplexShiftedCompleteRowIntegrand n j u := by
                  rw [← MeasureTheory.integral_const_mul]
                  refine MeasureTheory.integral_congr_ae ?_
                  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
                  unfold atkinsonComplexShiftedCompleteRowIntegrand
                  simp [show n + j = n + j by rfl]
              _ =
                ∫ u in Ioc (0 : ℝ) 1, atkinsonResonantShiftedRowSummand n j u := by
                  refine MeasureTheory.integral_congr_ae ?_
                  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
                  exact atkinsonComplexShiftedCompleteRowIntegrand_eq_resonantCarrier_singlePacket n j u
          have hsqrt :
              atkinsonModeWeight (n + j) * ((((n + j : ℕ) : ℝ) + 1))
                = Real.sqrt ((((n + j : ℕ) : ℝ) + 1)) := by
            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
              atkinsonModeWeight_mul_succ_eq_sqrt (n + j)
          have hmode_eq :
              atkinsonModeWeight (n + j)
                = Real.sqrt ((((n + j : ℕ) : ℝ) + 1)) / ((((n + j : ℕ) : ℝ) + 1)) := by
            have hden_ne : ((((n + j : ℕ) : ℝ) + 1)) ≠ 0 := by positivity
            exact (eq_div_iff hden_ne).2 <| by
              simpa [mul_comm] using hsqrt
          have hratio :
              Real.sqrt ((((n + j : ℕ) : ℝ) + 1)) / ((n : ℝ) + 1)
                ≤ 2 * atkinsonModeWeight (n + j) := by
            have hden :
                (1 : ℝ) / ((n : ℝ) + 1) ≤ 2 / ((((n + j : ℕ) : ℝ) + 1)) := by
              have hnum : (n + j + 1 : ℕ) ≤ 2 * (n + 1) := by
                omega
              have hnumR : ((((n + j : ℕ) : ℝ) + 1) : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
                exact_mod_cast hnum
              field_simp [show (n : ℝ) + 1 ≠ 0 by positivity,
                show ((((n + j : ℕ) : ℝ) + 1)) ≠ 0 by positivity]
              nlinarith
            have hsqrt_nonneg : 0 ≤ Real.sqrt ((((n + j : ℕ) : ℝ) + 1)) := by
              positivity
            calc
              Real.sqrt ((((n + j : ℕ) : ℝ) + 1)) / ((n : ℝ) + 1)
                  = Real.sqrt ((((n + j : ℕ) : ℝ) + 1)) * ((1 : ℝ) / ((n : ℝ) + 1)) := by
                    ring
              _ ≤ Real.sqrt ((((n + j : ℕ) : ℝ) + 1)) *
                    (2 / ((((n + j : ℕ) : ℝ) + 1))) := by
                    exact mul_le_mul_of_nonneg_left hden hsqrt_nonneg
              _ = 2 * atkinsonModeWeight (n + j) := by
                    rw [hmode_eq]
                    ring
          calc
            ‖atkinsonResonantShiftedPhaseWeightedCell n j‖
                = atkinsonShiftedRelativePhase (n + j) j *
                    ‖(((atkinsonModeWeight n : ℝ) : ℂ) *
                        ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
                          HardyCosSmooth.hardyCosExp n t)‖ := by
                      unfold atkinsonResonantShiftedPhaseWeightedCell
                      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hphase_nonneg]
                      rw [← hrow_eq]
            _ ≤ atkinsonShiftedRelativePhase (n + j) j *
                  (C0 * Real.sqrt ((((n + j : ℕ) : ℝ) + 1)) / j) := by
                    exact mul_le_mul_of_nonneg_left hweighted hphase_nonneg
            _ ≤ ((j : ℝ) / ((n : ℝ) + 1)) *
                  (C0 * Real.sqrt ((((n + j : ℕ) : ℝ) + 1)) / j) := by
                    have hfac_nonneg :
                        0 ≤ C0 * Real.sqrt ((((n + j : ℕ) : ℝ) + 1)) / j := by
                      positivity
                    exact mul_le_mul_of_nonneg_right hphase_upper hfac_nonneg
            _ = C0 * (Real.sqrt ((((n + j : ℕ) : ℝ) + 1)) / ((n : ℝ) + 1)) := by
                  field_simp [show (j : ℝ) ≠ 0 by positivity]
            _ ≤ C0 * (2 * atkinsonModeWeight (n + j)) := by
                  exact mul_le_mul_of_nonneg_left hratio (le_of_lt hC0)
            _ = 2 * C0 * atkinsonModeWeight (n + j) := by ring
    _ = 2 * C0 * ∑ n ∈ Finset.Ico (j - 1) (m + 1), atkinsonModeWeight (n + j) := by
          rw [Finset.mul_sum]
    _ = 2 * C0 * ∑ r ∈ Finset.Ico (j - 1 + j) (m + 1 + j), atkinsonModeWeight r := by
          congr 1
          simpa [add_assoc, add_left_comm, add_comm] using
            (Finset.sum_Ico_add (f := fun r => atkinsonModeWeight r) (j - 1) (m + 1) j)
    _ ≤ 2 * C0 * ∑ r ∈ Finset.range (m + j + 1), atkinsonModeWeight r := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (by
              intro r hr
              exact Finset.mem_range.mpr <| by
                simpa [Nat.add_assoc, add_left_comm, add_comm] using (Finset.mem_Ico.mp hr).2)
            (by
              intro r hr hmem
              exact le_of_lt (atkinsonModeWeight_pos r))
    _ ≤ 2 * C0 * (2 * Real.sqrt ((m + j + 1 : ℕ) : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc
            ∑ r ∈ Finset.range (m + j + 1), atkinsonModeWeight r
                = ∑ r ∈ Finset.range (m + j + 1), ((r + 1 : ℝ) ^ (-1 / 2 : ℝ)) := by
                    refine Finset.sum_congr rfl ?_
                    intro r hr
                    rw [atkinsonModeWeight]
                    congr 1
                    norm_num
            _ ≤ 2 * Real.sqrt ((m + j + 1 : ℕ) : ℝ) :=
                  Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le (m + j + 1)
    _ = C * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
          calc
            2 * C0 * (2 * Real.sqrt ((m + j + 1 : ℕ) : ℝ))
                = C0 * Real.sqrt ((m + j + 1 : ℕ) : ℝ) * 4 := by ring
            _ = C0 * Real.sqrt ((((m + j : ℕ) : ℝ) + 1)) * 4 := by
                  congr 2
                  norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
            _ = C * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
                  dsimp [C]
                  ring

/-- The genuine near-band phase-weighted correction prefix is already
`O(√(m+j))`. This is the direct current analogue of the old correction-prefix
bound, but for the weighted correction packet that the present file exposes
canonically. -/
private theorem atkinsonResonantShiftedPhaseWeightedCorrectionFixedShiftPrefix_bound_eventually :
    ∃ C > 0, ∃ J0 : ℕ, ∀ j : ℕ, J0 ≤ j →
      ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonResonantShiftedCorrectionTerm n j)‖
          ≤ C * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
  obtain ⟨Cφ, hCφ, Jφ, hphase⟩ :=
    atkinsonResonantShiftedPhaseWeightedFixedShiftPrefix_bound_eventually
  let J0 : ℕ := max 2 Jφ
  let C : ℝ := Cφ + 16
  refine ⟨C, by
    dsimp [C]
    positivity, J0, ?_⟩
  intro j hj m
  by_cases hnonempty : j - 1 ≤ m
  · have hj_two : 2 ≤ j := le_trans (by exact Nat.le_max_left _ _) hj
    have hj_one : 1 ≤ j := by omega
    have hj_phase : Jφ ≤ j := le_trans (by exact Nat.le_max_right _ _) hj
    have hEq :=
      atkinsonResonantShiftedPhaseWeightedCorrectionFixedShiftPrefix_eq_boundaryDiff_minus_cellPrefix
        m j hj_two hnonempty
    have hcoreEq :=
      atkinsonShiftedSingleBoundaryCoreFixedShiftPrefix_eq_boundaryDiff m j hj_two hnonempty
    have hcoreBound :
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            (atkinsonShiftedSingleBoundaryCore n (j + 1) -
              atkinsonShiftedSingleBoundaryCore n j)‖
          ≤ 16 * Real.sqrt (((m + j : ℕ) : ℝ) + 1) :=
      atkinsonShiftedSingleBoundaryCoreFixedShiftPrefix_bound m j hj_one
    have hphaseBound :
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1), atkinsonResonantShiftedPhaseWeightedCell n j‖
          ≤ Cφ * Real.sqrt (((m + j : ℕ) : ℝ) + 1) :=
      hphase j hj_phase m
    calc
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedCorrectionTerm n j)‖
          =
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            (atkinsonShiftedSingleBoundaryCore n (j + 1) -
              atkinsonShiftedSingleBoundaryCore n j)
          - ∑ n ∈ Finset.Ico (j - 1) (m + 1), atkinsonResonantShiftedPhaseWeightedCell n j‖ := by
            rw [hEq, hcoreEq]
      _ ≤ ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
              (atkinsonShiftedSingleBoundaryCore n (j + 1) -
                atkinsonShiftedSingleBoundaryCore n j)‖
            + ‖∑ n ∈ Finset.Ico (j - 1) (m + 1), atkinsonResonantShiftedPhaseWeightedCell n j‖ := by
              exact norm_sub_le _ _
      _ ≤ 16 * Real.sqrt (((m + j : ℕ) : ℝ) + 1)
            + Cφ * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
              exact add_le_add hcoreBound hphaseBound
      _ ≤ (Cφ + 16) * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
              have hsqrt_nonneg : 0 ≤ Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by positivity
              nlinarith
      _ = C * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
              rfl
  · have hEmpty : Finset.Ico (j - 1) (m + 1) = ∅ := by
      apply Finset.Ico_eq_empty_of_le
      omega
    rw [hEmpty, Finset.sum_empty]
    have hnonneg : 0 ≤ C * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
      positivity
    simpa using hnonneg

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private lemma atkinsonBoundary_jMinusOne_le_clean
    (j : ℕ) (hj : 1 ≤ j) (m : ℕ) :
    ‖atkinsonResonantShiftedBoundaryTerm (j - 1) j‖
      ≤ (2 / Real.log 2) * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
  have hjk : j ≤ (j - 1) + j := by omega
  have hphase_pos :
      0 < atkinsonShiftedRelativePhase ((j - 1) + j) j :=
    atkinsonShiftedRelativePhase_pos ((j - 1) + j) j hj hjk
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hj_pos : (0 : ℝ) < (j : ℝ) := by positivity
  have hbound := atkinsonResonantShiftedBoundaryTerm_norm_le_clean (j - 1) j hj
  have hmw_mul := atkinsonModeWeight_mul_succ_eq_sqrt (j - 1)
  have hpred_cast : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hj
  rw [hpred_cast] at hmw_mul
  have hphase_eq :
      atkinsonShiftedRelativePhase ((j - 1) + j) j = Real.log 2 := by
    rw [atkinsonShiftedRelativePhase_eq_sub_logs]
    have hk_nat_nat : (j - 1 + j : ℕ) + 1 = 2 * j := by
      omega
    have hk_nat : (((j - 1 + j : ℕ) : ℝ) + 1) = 2 * (j : ℝ) := by
      exact_mod_cast hk_nat_nat
    have hk_sub_nat_nat : ((j - 1 + j - j : ℕ)) + 1 = j := by
      rw [Nat.add_sub_cancel_right, Nat.sub_add_cancel hj]
    have hk_sub_nat : ((((j - 1 + j - j : ℕ) : ℝ)) + 1) = (j : ℝ) := by
      exact_mod_cast hk_sub_nat_nat
    rw [hk_nat, hk_sub_nat]
    rw [← Real.log_div (by positivity : (2 : ℝ) * (j : ℝ) ≠ 0)
      (by positivity : (j : ℝ) ≠ 0)]
    congr 1
    field_simp
  have hsqrt_le :
      Real.sqrt (j : ℝ) ≤ Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
    have hsqrt_arg_nat : j ≤ m + j + 1 := by
      omega
    exact Real.sqrt_le_sqrt (by exact_mod_cast hsqrt_arg_nat)
  have hmw_eq :
      atkinsonModeWeight (j - 1) = Real.sqrt (j : ℝ) / j := by
    apply (eq_div_iff (show (j : ℝ) ≠ 0 by positivity)).2
    simpa [mul_comm] using hmw_mul
  have hdiv :
      Real.sqrt (j : ℝ) / j ≤ Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j := by
    have hinv_nonneg : 0 ≤ (1 / (j : ℝ)) := by
      positivity
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_right hsqrt_le hinv_nonneg
  calc
    ‖atkinsonResonantShiftedBoundaryTerm (j - 1) j‖
      ≤ 2 * (atkinsonModeWeight (j - 1) /
            atkinsonShiftedRelativePhase ((j - 1) + j) j) := hbound
    _ = (2 / Real.log 2) * (Real.sqrt (j : ℝ) / j) := by
          rw [hphase_eq, hmw_eq]
          ring
    _ ≤ (2 / Real.log 2) * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
          exact mul_le_mul_of_nonneg_left hdiv (by positivity)

private theorem atkinson_shift1_boundaryPrefix_bound_atomic :
    ∃ C_bdry > 0, ∀ K : ℕ,
      ‖∑ k ∈ Finset.range (K + 1),
          atkinsonResonantShiftedBoundaryTerm (k + 1) 1‖
        ≤ C_bdry * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
  obtain ⟨C_up, hC_up, hupper⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_upper_boundary_sum_bound_atomic
  obtain ⟨C_low, hC_low, hlower⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_lower_boundary_sum_bound_atomic
  refine ⟨C_up + C_low, by positivity, ?_⟩
  intro K
  let su : ℂ :=
    ∑ k ∈ Finset.range (K + 1),
      atkinsonWeightedResonantBlockMode (k + 2) 1 *
        atkinsonShiftedSinglePrimitive (k + 2) 1 1
  let sl : ℂ :=
    ∑ k ∈ Finset.range (K + 1),
      atkinsonWeightedResonantBlockMode (k + 2) 0 *
        atkinsonShiftedSinglePrimitive (k + 2) 1 0
  have hconv_up :
      su =
      ∑ n ∈ Finset.range (K + 2),
        (if 1 ≤ n then
          atkinsonWeightedResonantBlockMode (n + 1) 1 *
            atkinsonShiftedSinglePrimitive (n + 1) 1 1
        else 0) := by
    calc
      su =
        ∑ n ∈ Finset.Ico 1 (K + 2),
          atkinsonWeightedResonantBlockMode (n + 1) 1 *
            atkinsonShiftedSinglePrimitive (n + 1) 1 1 := by
            simpa [su, Nat.add_assoc, add_left_comm, add_comm] using
              (Finset.sum_Ico_eq_sum_range
                (f := fun n =>
                  atkinsonWeightedResonantBlockMode (n + 1) 1 *
                    atkinsonShiftedSinglePrimitive (n + 1) 1 1)
                (m := 1) (n := K + 2)).symm
      _ =
        ∑ n ∈ Finset.range (K + 2),
          (if 1 ≤ n then
            atkinsonWeightedResonantBlockMode (n + 1) 1 *
              atkinsonShiftedSinglePrimitive (n + 1) 1 1
          else 0) := by
            rw [← Finset.sum_filter]
            congr 1
            ext x
            constructor <;> intro hx <;>
              simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx ⊢ <;> omega
  have hsu :
      ‖su‖ ≤ C_up * Real.log 2 * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
    rw [hconv_up]
    have hraw := hupper 1 (by norm_num) (K + 2)
    simp only [Nat.cast_one, show (1 : ℝ) + 1 = 2 from by norm_num,
      show ((K + 2 + 1 : ℕ) : ℝ) = ((K + 3 : ℕ) : ℝ) from by push_cast; ring,
      div_one] at hraw
    simpa [Nat.add_assoc, add_left_comm, add_comm] using hraw
  have hsl :
      ‖sl‖ ≤ C_low * Real.log 2 * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
    have hconv_low :
        sl =
        ∑ n ∈ Finset.range (K + 2),
          (if 1 ≤ n then
            atkinsonWeightedResonantBlockMode (n + 1) 0 *
              atkinsonShiftedSinglePrimitive (n + 1) 1 0
          else 0) := by
      calc
        sl =
          ∑ n ∈ Finset.Ico 1 (K + 2),
            atkinsonWeightedResonantBlockMode (n + 1) 0 *
              atkinsonShiftedSinglePrimitive (n + 1) 1 0 := by
              simpa [sl, Nat.add_assoc, add_left_comm, add_comm] using
                (Finset.sum_Ico_eq_sum_range
                  (f := fun n =>
                    atkinsonWeightedResonantBlockMode (n + 1) 0 *
                      atkinsonShiftedSinglePrimitive (n + 1) 1 0)
                  (m := 1) (n := K + 2)).symm
        _ =
          ∑ n ∈ Finset.range (K + 2),
            (if 1 ≤ n then
              atkinsonWeightedResonantBlockMode (n + 1) 0 *
                atkinsonShiftedSinglePrimitive (n + 1) 1 0
            else 0) := by
              rw [← Finset.sum_filter]
              congr 1
              ext x
              constructor <;> intro hx <;>
                simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx ⊢ <;> omega
    rw [hconv_low]
    have hraw := hlower 1 (by norm_num) (K + 2)
    simp only [Nat.cast_one, show (1 : ℝ) + 1 = 2 from by norm_num,
      show ((K + 2 + 1 : ℕ) : ℝ) = ((K + 3 : ℕ) : ℝ) from by push_cast; ring,
      div_one] at hraw
    simpa [Nat.add_assoc, add_left_comm, add_comm] using hraw
  have hsplit :
      ∑ k ∈ Finset.range (K + 1), atkinsonResonantShiftedBoundaryTerm (k + 1) 1
        = su - sl := by
    calc
      ∑ k ∈ Finset.range (K + 1), atkinsonResonantShiftedBoundaryTerm (k + 1) 1
          =
        ∑ k ∈ Finset.range (K + 1),
          (atkinsonWeightedResonantBlockMode (k + 2) 1 *
              atkinsonShiftedSinglePrimitive (k + 2) 1 1
            - atkinsonWeightedResonantBlockMode (k + 2) 0 *
              atkinsonShiftedSinglePrimitive (k + 2) 1 0) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp [atkinsonResonantShiftedBoundaryTerm, Nat.add_assoc, add_left_comm, add_comm]
      _ = su - sl := by
            simp [su, sl, Finset.sum_sub_distrib]
  calc
    ‖∑ k ∈ Finset.range (K + 1), atkinsonResonantShiftedBoundaryTerm (k + 1) 1‖
      = ‖su - sl‖ := by
          rw [hsplit]
    _ ≤ ‖su‖ + ‖sl‖ := by
          exact norm_sub_le _ _
    _ ≤ C_up * Real.log 2 * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1)
        + C_low * Real.log 2 * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
          exact add_le_add hsu hsl
    _ = (C_up + C_low) * Real.log 2 * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
          ring
    _ ≤ (C_up + C_low) * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
          have hlog2 : Real.log 2 ≤ 1 := by
            have h2le : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
            exact (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).mpr h2le
          have hsqrt := Real.sqrt_nonneg (((K + 3 : ℕ) : ℝ) + 1)
          have hCpos : 0 < C_up + C_low := by linarith
          nlinarith [mul_nonneg (mul_nonneg (le_of_lt hCpos) hsqrt) (sub_nonneg.mpr hlog2)]

private theorem atkinson_j2_kernelWeighted_boundaryGap_bound :
    ∃ C_gap > 0, ∀ M : ℕ,
      ‖∑ n ∈ Finset.range (M + 1),
          ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm n 1)‖
        ≤ C_gap * (Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (2 : ℝ)) := by
  obtain ⟨C_bdry, hC_bdry, hbdry⟩ :=
    atkinson_shift1_boundaryPrefix_bound_atomic
  refine ⟨4 * C_bdry + 4 / Real.log 2, by positivity, ?_⟩
  intro M
  let gapFn : ℕ → ℂ := fun n =>
    ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
      atkinsonResonantShiftedBoundaryTerm n 1)
  let baseFn : ℕ → ℂ := fun k => atkinsonResonantShiftedBoundaryTerm (k + 1) 1
  let b : ℕ → ℝ := fun k => atkinsonLowerBoundaryShiftKernel (k + 1) 2 1
  let target : ℝ := Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (2 : ℝ)
  have hsplit :
      ∑ n ∈ Finset.range (M + 1), gapFn n
        =
      gapFn 0 + ∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k) := by
    calc
      ∑ n ∈ Finset.range (M + 1), gapFn n
          =
        (∑ n ∈ Finset.range 1, gapFn n) + ∑ n ∈ Finset.Ico 1 (M + 1), gapFn n := by
            simpa using
              (Finset.sum_range_add_sum_Ico gapFn (show 1 ≤ M + 1 by omega)).symm
      _ = gapFn 0 + ∑ n ∈ Finset.Ico 1 (M + 1), gapFn n := by
            simp [gapFn]
      _ = gapFn 0 + ∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k) := by
            congr 1
            rw [Finset.sum_Ico_eq_sum_range]
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp [gapFn, baseFn, b, add_comm, add_left_comm]
  have hhead_kernel : atkinsonLowerBoundaryShiftKernel 0 2 1 ≤ 1 := by
    have hstep := atkinsonLowerBoundaryShiftKernel_step_mul 0 1 1 (by norm_num) le_rfl
    have hself : atkinsonLowerBoundaryShiftKernel 0 1 1 = 1 := by
      simpa using atkinsonLowerBoundaryShiftKernel_self 0 1 (by norm_num)
    calc
      atkinsonLowerBoundaryShiftKernel 0 2 1
          = (1 / atkinsonUpperBoundaryStepCoeff 0 1) * 1 := by
              simpa [hself] using hstep
      _ ≤ 1 * 1 := by
            gcongr
            simpa using
              (one_div_le_one_div_of_le
                (by positivity : (0 : ℝ) < 1)
                (atkinsonUpperBoundaryStepCoeff_one_le 0 1 (by norm_num)))
      _ = 1 := by ring
  have hhead_term :
      ‖gapFn 0‖ ≤ (4 / Real.log 2) * target := by
    have hraw :
        ‖atkinsonResonantShiftedBoundaryTerm 0 1‖
          ≤ (2 / Real.log 2) * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ)) := by
      simpa using atkinsonBoundary_jMinusOne_le 1 (by norm_num) M
    have hsqrt_le :
        Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ) ≤ 2 * target := by
      have hle :
          (((M + 1 : ℕ) : ℝ) + 1) ≤ (((M + 2 : ℕ) : ℝ) + 1) := by
        exact_mod_cast (by omega : (M + 1) + 1 ≤ (M + 2) + 1)
      calc
        Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ)
            ≤ Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (1 : ℝ) := by
                exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hle)
                  (by positivity : (0 : ℝ) ≤ (1 : ℝ))
        _ = 2 * target := by
              unfold target
              ring
    calc
      ‖gapFn 0‖
          =
        atkinsonLowerBoundaryShiftKernel 0 2 1 * ‖atkinsonResonantShiftedBoundaryTerm 0 1‖ := by
            simp [gapFn, Real.norm_eq_abs, abs_of_nonneg
              (atkinsonLowerBoundaryShiftKernel_nonneg 0 2 1 (by norm_num) (by norm_num))]
      _ ≤ 1 * ‖atkinsonResonantShiftedBoundaryTerm 0 1‖ := by
            gcongr
      _ ≤ 1 * ((2 / Real.log 2) * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) := by
            gcongr
      _ ≤ 1 * ((2 / Real.log 2) * (2 * target)) := by
            gcongr
      _ = (4 / Real.log 2) * target := by ring
  have htail_term :
      ‖∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k)‖ ≤ 4 * C_bdry * target := by
    by_cases hM0 : M = 0
    · have hzero : ∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k) = 0 := by
        simp [hM0]
      have hnonneg : 0 ≤ 4 * C_bdry * target := by positivity
      simpa [hzero] using hnonneg
    · obtain ⟨n0, hn0 : M = n0 + 1⟩ := Nat.exists_eq_succ_of_ne_zero hM0
      let C0 : ℝ := 2 * C_bdry * target
      let aRe : ℕ → ℝ := fun k => (baseFn k).re
      let aIm : ℕ → ℝ := fun k => (baseFn k).im
      have hpartial_bound (K : ℕ) (hK : K ≤ n0) :
          ‖∑ k ∈ Finset.range (K + 1), baseFn k‖ ≤ C0 := by
        have hraw :
            ‖∑ k ∈ Finset.range (K + 1), baseFn k‖
              ≤ C_bdry * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
            simpa [baseFn, Nat.add_assoc, add_left_comm, add_comm] using hbdry K
        have htarget_K :
            Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) ≤ 2 * target := by
          have hle_nat : (K + 3) + 1 ≤ (M + 2) + 1 := by
            rw [hn0]
            omega
          have hle :
              ((((K + 3 : ℕ) : ℝ) + 1)) ≤ ((((M + 2 : ℕ) : ℝ) + 1)) := by
            exact_mod_cast hle_nat
          calc
            Real.sqrt (((K + 3 : ℕ) : ℝ) + 1)
                ≤ Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) := by
                    exact Real.sqrt_le_sqrt hle
            _ = 2 * target := by
                  unfold target
                  ring
        calc
          ‖∑ k ∈ Finset.range (K + 1), baseFn k‖
              ≤ C_bdry * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := hraw
          _ ≤ C_bdry * (2 * target) := by
                exact mul_le_mul_of_nonneg_left htarget_K (le_of_lt hC_bdry)
          _ = C0 := by
                unfold C0
                ring
      have hpartial_re : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aRe m| ≤ C0 := by
        intro k hk
        have hbound := hpartial_bound k hk
        calc
          |∑ m ∈ Finset.range (k + 1), aRe m|
              = |(∑ m ∈ Finset.range (k + 1), baseFn m).re| := by
                  simp [aRe]
          _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_re_le_norm _
          _ ≤ C0 := hbound
      have hpartial_im : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aIm m| ≤ C0 := by
        intro k hk
        have hbound := hpartial_bound k hk
        calc
          |∑ m ∈ Finset.range (k + 1), aIm m|
              = |(∑ m ∈ Finset.range (k + 1), baseFn m).im| := by
                  simp [aIm]
          _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_im_le_norm _
          _ ≤ C0 := hbound
      have hb_nonneg : ∀ k ≤ n0, 0 ≤ b k := by
        intro k hk
        simpa [b, add_comm, add_left_comm] using
          atkinsonLowerBoundaryShiftKernel_nonneg (k + 1) 2 1 (by norm_num) (by norm_num)
      have hb_anti : ∀ k < n0, b (k + 1) ≤ b k := by
        intro k hk
        simpa [b, add_comm, add_left_comm] using
          (atkinsonLowerBoundaryShiftKernel_antitone 2 1 (by norm_num) (by norm_num)
            (by omega : k + 1 ≤ k + 2))
      have hb_head : b 0 ≤ 1 := by
        have hstep := atkinsonLowerBoundaryShiftKernel_step_mul 1 1 1 (by norm_num) le_rfl
        have hself : atkinsonLowerBoundaryShiftKernel 1 1 1 = 1 := by
          simpa using atkinsonLowerBoundaryShiftKernel_self 1 1 (by norm_num)
        calc
          b 0 = (1 / atkinsonUpperBoundaryStepCoeff 1 1) * 1 := by
                  simp [b, hstep, hself]
          _ ≤ 1 * 1 := by
                gcongr
                simpa using
                  (one_div_le_one_div_of_le
                    (by positivity : (0 : ℝ) < 1)
                    (atkinsonUpperBoundaryStepCoeff_one_le 1 1 (by norm_num)))
          _ = 1 := by ring
      have hsum_re :
          (∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re
            =
          ∑ k ∈ Finset.range (n0 + 1), aRe k * b k := by
        simp [aRe, b, baseFn, mul_comm]
      have hsum_im :
          (∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im
            =
          ∑ k ∈ Finset.range (n0 + 1), aIm k * b k := by
        simp [aIm, b, baseFn, mul_comm]
      have hre :
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re| ≤ C0 := by
        have habel :=
          AbelSummation.abel_summation_bound aRe b n0 C0 hpartial_re hb_nonneg hb_anti
        calc
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
              = |∑ k ∈ Finset.range (n0 + 1), aRe k * b k| := by
                  rw [hsum_re]
          _ ≤ C0 * b 0 := habel
          _ ≤ C0 * 1 := by
                gcongr
          _ = C0 := by ring
      have him :
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| ≤ C0 := by
        have habel :=
          AbelSummation.abel_summation_bound aIm b n0 C0 hpartial_im hb_nonneg hb_anti
        calc
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im|
              = |∑ k ∈ Finset.range (n0 + 1), aIm k * b k| := by
                  rw [hsum_im]
          _ ≤ C0 * b 0 := habel
          _ ≤ C0 * 1 := by
                gcongr
          _ = C0 := by ring
      have hnorm :
          ‖∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k)‖ ≤ 2 * C0 := by
        calc
          ‖∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k)‖
              = ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖ := by
                  rw [hn0]
          _ ≤
            |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
              +
            |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| := by
                exact Complex.norm_le_abs_re_add_abs_im _
          _ ≤ C0 + C0 := add_le_add hre him
          _ = 2 * C0 := by ring
      calc
        ‖∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k)‖
            ≤ 2 * C0 := hnorm
        _ = 4 * C_bdry * target := by
              unfold C0
              ring
  calc
    ‖∑ n ∈ Finset.range (M + 1),
        ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
          atkinsonResonantShiftedBoundaryTerm n 1)‖
      = ‖gapFn 0 + ∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k)‖ := by
          rw [show
            (∑ n ∈ Finset.range (M + 1),
              ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
                atkinsonResonantShiftedBoundaryTerm n 1))
              = ∑ n ∈ Finset.range (M + 1), gapFn n by rfl]
          rw [hsplit]
    _ ≤ ‖gapFn 0‖ + ‖∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k)‖ := by
          exact norm_add_le _ _
    _ ≤ (4 / Real.log 2) * target + 4 * C_bdry * target := by
          exact add_le_add hhead_term htail_term
    _ = (4 * C_bdry + 4 / Real.log 2) * target := by
          ring

private theorem atkinson_j2_kernelWeighted_j1_headCore_bound_of_j1
    (hj1 :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) :
    ∃ C_head > 0, ∀ M : ℕ,
      ‖∑ n ∈ Finset.range (M + 1),
          ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1))‖
        ≤ C_head * (Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (2 : ℝ)) := by
  obtain ⟨C1, hC1, hj1_bound⟩ := hj1
  refine ⟨4 * C1, by positivity, ?_⟩
  intro M
  let baseFn : ℕ → ℂ := fun n =>
    ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
      atkinsonShiftedSingleBoundaryCore n 1)
  let b : ℕ → ℝ := fun n => atkinsonLowerBoundaryShiftKernel n 2 1
  let target : ℝ := Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (2 : ℝ)
  let C0 : ℝ := 2 * C1 * target
  let aRe : ℕ → ℝ := fun k => (baseFn k).re
  let aIm : ℕ → ℝ := fun k => (baseFn k).im
  have hpartial_bound (K : ℕ) (hK : K ≤ M) :
      ‖∑ n ∈ Finset.range (K + 1), baseFn n‖ ≤ C0 := by
    have hraw := hj1_bound K
    have htarget_K :
        Real.sqrt (((K + 1 : ℕ) : ℝ) + 1) / (1 : ℝ) ≤ 2 * target := by
      have hle :
          ((((K + 1 : ℕ) : ℝ) + 1)) ≤ ((((M + 2 : ℕ) : ℝ) + 1)) := by
        exact_mod_cast (by omega : (K + 1) + 1 ≤ (M + 2) + 1)
      calc
        Real.sqrt (((K + 1 : ℕ) : ℝ) + 1) / (1 : ℝ)
            ≤ Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (1 : ℝ) := by
                exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hle)
                  (by positivity : (0 : ℝ) ≤ (1 : ℝ))
        _ = 2 * target := by
              unfold target
              ring
    calc
      ‖∑ n ∈ Finset.range (K + 1), baseFn n‖
          ≤ C1 * (Real.sqrt (((K + 1 : ℕ) : ℝ) + 1) / (1 : ℝ)) := hraw
      _ ≤ C1 * (2 * target) := by
            exact mul_le_mul_of_nonneg_left htarget_K (le_of_lt hC1)
      _ = C0 := by
            unfold C0
            ring
  have hpartial_re : ∀ k ≤ M, |∑ m ∈ Finset.range (k + 1), aRe m| ≤ C0 := by
    intro k hk
    have hbound := hpartial_bound k hk
    calc
      |∑ m ∈ Finset.range (k + 1), aRe m|
          = |(∑ m ∈ Finset.range (k + 1), baseFn m).re| := by
              simp [aRe]
      _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_re_le_norm _
      _ ≤ C0 := hbound
  have hpartial_im : ∀ k ≤ M, |∑ m ∈ Finset.range (k + 1), aIm m| ≤ C0 := by
    intro k hk
    have hbound := hpartial_bound k hk
    calc
      |∑ m ∈ Finset.range (k + 1), aIm m|
          = |(∑ m ∈ Finset.range (k + 1), baseFn m).im| := by
              simp [aIm]
      _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_im_le_norm _
      _ ≤ C0 := hbound
  have hb_nonneg : ∀ k ≤ M, 0 ≤ b k := by
    intro k hk
    simpa [b] using
      atkinsonLowerBoundaryShiftKernel_nonneg k 2 1 (by norm_num) (by norm_num)
  have hb_anti : ∀ k < M, b (k + 1) ≤ b k := by
    intro k hk
    simpa [b] using
      (atkinsonLowerBoundaryShiftKernel_antitone 2 1 (by norm_num) (by norm_num)
        (by omega : k ≤ k + 1))
  have hb_head : b 0 ≤ 1 := by
    have hstep := atkinsonLowerBoundaryShiftKernel_step_mul 0 1 1 (by norm_num) le_rfl
    have hself : atkinsonLowerBoundaryShiftKernel 0 1 1 = 1 := by
      simpa using atkinsonLowerBoundaryShiftKernel_self 0 1 (by norm_num)
    calc
      b 0 = (1 / atkinsonUpperBoundaryStepCoeff 0 1) * 1 := by
              simp [b, hstep, hself]
      _ ≤ 1 * 1 := by
            gcongr
            simpa using
              (one_div_le_one_div_of_le
                (by positivity : (0 : ℝ) < 1)
                (atkinsonUpperBoundaryStepCoeff_one_le 0 1 (by norm_num)))
      _ = 1 := by ring
  have hsum_re :
      (∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re
        =
      ∑ k ∈ Finset.range (M + 1), aRe k * b k := by
        simp [aRe, b, baseFn, mul_comm]
  have hsum_im :
      (∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im
        =
      ∑ k ∈ Finset.range (M + 1), aIm k * b k := by
        simp [aIm, b, baseFn, mul_comm]
  have hre :
      |(∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re| ≤ C0 := by
    have habel :=
      AbelSummation.abel_summation_bound aRe b M C0 hpartial_re hb_nonneg hb_anti
    calc
      |(∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
          = |∑ k ∈ Finset.range (M + 1), aRe k * b k| := by
              rw [hsum_re]
      _ ≤ C0 * b 0 := habel
      _ ≤ C0 * 1 := by
            gcongr
      _ = C0 := by ring
  have him :
      |(∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| ≤ C0 := by
    have habel :=
      AbelSummation.abel_summation_bound aIm b M C0 hpartial_im hb_nonneg hb_anti
    calc
      |(∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im|
          = |∑ k ∈ Finset.range (M + 1), aIm k * b k| := by
              rw [hsum_im]
      _ ≤ C0 * b 0 := habel
      _ ≤ C0 * 1 := by
            gcongr
      _ = C0 := by ring
  have hnorm :
      ‖∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖ ≤ 2 * C0 := by
    calc
      ‖∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖
          ≤
        |(∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
          +
        |(∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| := by
            exact Complex.norm_le_abs_re_add_abs_im _
      _ ≤ C0 + C0 := add_le_add hre him
      _ = 2 * C0 := by ring
  calc
    ‖∑ n ∈ Finset.range (M + 1),
        ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n 1))‖
      = ‖∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖ := by
          simp [b, baseFn]
    _ ≤ 2 * C0 := hnorm
    _ = (4 * C1) * target := by
          unfold C0
          ring

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private theorem atkinson_j2_kernelWeighted_j1_headCore_bound_of_j1_clean
    (hj1 :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) :
    ∃ C_head > 0, ∀ M : ℕ,
      ‖∑ n ∈ Finset.range (M + 1),
          ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1))‖
        ≤ C_head * (Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (2 : ℝ)) := by
  obtain ⟨C1, hC1, hj1_bound⟩ := hj1
  refine ⟨4 * C1, by positivity, ?_⟩
  intro M
  let baseFn : ℕ → ℂ := fun n =>
    ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
      atkinsonShiftedSingleBoundaryCore n 1)
  let b : ℕ → ℝ := fun n => atkinsonLowerBoundaryShiftKernel n 2 1
  let target : ℝ := Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (2 : ℝ)
  let C0 : ℝ := 2 * C1 * target
  let aRe : ℕ → ℝ := fun k => (baseFn k).re
  let aIm : ℕ → ℝ := fun k => (baseFn k).im
  have hpartial_bound (K : ℕ) (hK : K ≤ M) :
      ‖∑ n ∈ Finset.range (K + 1), baseFn n‖ ≤ C0 := by
    have hraw := hj1_bound K
    have htarget_K :
        Real.sqrt (((K + 1 : ℕ) : ℝ) + 1) / (1 : ℝ) ≤ 2 * target := by
      have hle :
          ((((K + 1 : ℕ) : ℝ) + 1)) ≤ ((((M + 2 : ℕ) : ℝ) + 1)) := by
        exact_mod_cast (by omega : (K + 1) + 1 ≤ (M + 2) + 1)
      calc
        Real.sqrt (((K + 1 : ℕ) : ℝ) + 1) / (1 : ℝ)
            ≤ Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (1 : ℝ) := by
                exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hle)
                  (by positivity : (0 : ℝ) ≤ (1 : ℝ))
        _ = 2 * target := by
              unfold target
              ring
    calc
      ‖∑ n ∈ Finset.range (K + 1), baseFn n‖
          ≤ C1 * (Real.sqrt (((K + 1 : ℕ) : ℝ) + 1) / (1 : ℝ)) := hraw
      _ ≤ C1 * (2 * target) := by
            exact mul_le_mul_of_nonneg_left htarget_K (le_of_lt hC1)
      _ = C0 := by
            unfold C0
            ring
  have hpartial_re : ∀ k ≤ M, |∑ m ∈ Finset.range (k + 1), aRe m| ≤ C0 := by
    intro k hk
    have hbound := hpartial_bound k hk
    calc
      |∑ m ∈ Finset.range (k + 1), aRe m|
          = |(∑ m ∈ Finset.range (k + 1), baseFn m).re| := by
              simp [aRe]
      _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_re_le_norm _
      _ ≤ C0 := hbound
  have hpartial_im : ∀ k ≤ M, |∑ m ∈ Finset.range (k + 1), aIm m| ≤ C0 := by
    intro k hk
    have hbound := hpartial_bound k hk
    calc
      |∑ m ∈ Finset.range (k + 1), aIm m|
          = |(∑ m ∈ Finset.range (k + 1), baseFn m).im| := by
              simp [aIm]
      _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_im_le_norm _
      _ ≤ C0 := hbound
  have hb_nonneg : ∀ k ≤ M, 0 ≤ b k := by
    intro k hk
    simpa [b] using
      atkinsonLowerBoundaryShiftKernel_nonneg k 2 1 (by norm_num) (by norm_num)
  have hb_anti : ∀ k < M, b (k + 1) ≤ b k := by
    intro k hk
    simpa [b] using
      (atkinsonLowerBoundaryShiftKernel_antitone 2 1 (by norm_num) (by norm_num)
        (by omega : k ≤ k + 1))
  have hb_head : b 0 ≤ 1 := by
    have hstep := atkinsonLowerBoundaryShiftKernel_step_mul 0 1 1 (by norm_num) le_rfl
    have hself : atkinsonLowerBoundaryShiftKernel 0 1 1 = 1 := by
      simpa using atkinsonLowerBoundaryShiftKernel_self 0 1 (by norm_num)
    calc
      b 0 = (1 / atkinsonUpperBoundaryStepCoeff 0 1) * 1 := by
              simp [b, hstep, hself]
      _ ≤ 1 * 1 := by
            gcongr
            simpa using
              (one_div_le_one_div_of_le
                (by positivity : (0 : ℝ) < 1)
                (atkinsonUpperBoundaryStepCoeff_one_le 0 1 (by norm_num)))
      _ = 1 := by ring
  have hsum_re :
      (∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re
        =
      ∑ k ∈ Finset.range (M + 1), aRe k * b k := by
        simp [aRe, b, baseFn, mul_comm]
  have hsum_im :
      (∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im
        =
      ∑ k ∈ Finset.range (M + 1), aIm k * b k := by
        simp [aIm, b, baseFn, mul_comm]
  have hre :
      |(∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re| ≤ C0 := by
    have habel :=
      AbelSummation.abel_summation_bound aRe b M C0 hpartial_re hb_nonneg hb_anti
    calc
      |(∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
          = |∑ k ∈ Finset.range (M + 1), aRe k * b k| := by
              rw [hsum_re]
      _ ≤ C0 * b 0 := habel
      _ ≤ C0 * 1 := by
            gcongr
      _ = C0 := by ring
  have him :
      |(∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| ≤ C0 := by
    have habel :=
      AbelSummation.abel_summation_bound aIm b M C0 hpartial_im hb_nonneg hb_anti
    calc
      |(∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im|
          = |∑ k ∈ Finset.range (M + 1), aIm k * b k| := by
              rw [hsum_im]
      _ ≤ C0 * b 0 := habel
      _ ≤ C0 * 1 := by
            gcongr
      _ = C0 := by ring
  have hnorm :
      ‖∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖ ≤ 2 * C0 := by
    calc
      ‖∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖
          ≤
        |(∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
          +
        |(∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| := by
            exact Complex.norm_le_abs_re_add_abs_im _
      _ ≤ C0 + C0 := add_le_add hre him
      _ = 2 * C0 := by ring
  calc
    ‖∑ n ∈ Finset.range (M + 1),
        ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n 1))‖
      = ‖∑ k ∈ Finset.range (M + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖ := by
          simp [b, baseFn]
    _ ≤ 2 * C0 := hnorm
    _ = (4 * C1) * target := by
          unfold C0
          ring

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
theorem atkinson_inversePhaseCorePrefix_bound_j1 :
    ∃ C1 > 0, ∀ M : ℕ,
      ‖∑ n ∈ Finset.range (M + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n 1)‖
        ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ)) := by
  obtain ⟨Cquad, hCquad, N0, hquad⟩ :=
    Aristotle.StationaryPhaseMainMode.blockMode_quadratic_model_eventually
  obtain ⟨Cstart, hCstart, hstart⟩ :=
    Aristotle.StationaryPhaseMainMode.blockMode_zero_asymptotic
  let Cmode : ℝ := Cquad + Cstart
  let Chead : ℝ := 2 * (N0 : ℝ) * Real.sqrt ((N0 : ℝ) + 1)
  let Cmain : ℝ := 1 + Real.sqrt (N0 : ℝ)
  let Cerr : ℝ := 2 * (2 * Cmode + 1)
  refine ⟨Chead + Cmain + Cerr, by positivity, ?_⟩
  intro M
  let coeff : ℕ → ℝ := fun n =>
    atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + 1) 1
  let actual : ℕ → ℂ := fun n =>
    ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
      atkinsonShiftedSingleBoundaryCore n 1)
  let anchor : ℕ → ℂ := fun n =>
    ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
      Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor)
  let mainTerm : ℕ → ℂ := fun n =>
    (-Complex.I) * ((((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ)) * anchor n)
  let errFn : ℕ → ℂ := fun n => actual n - mainTerm n
  let target : ℝ := Real.sqrt (((M + 1 : ℕ) : ℝ) + 1)
  have htarget_ge_one : 1 ≤ target := by
    have hle : (1 : ℝ) ≤ (((M + 1 : ℕ) : ℝ) + 1) := by
      have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
      nlinarith
    simpa [target] using (Real.sqrt_le_sqrt hle)
  have htarget_ge_sqrtM : Real.sqrt (M + 1) ≤ target := by
    have hle : ((M + 1 : ℕ) : ℝ) ≤ (((M + 1 : ℕ) : ℝ) + 1) := by
      nlinarith
    simpa [target] using (Real.sqrt_le_sqrt hle)
  have hweight_formula (n : ℕ) :
      atkinsonModeWeight n = Real.sqrt ((n : ℝ) + 1) / ((n : ℝ) + 1) := by
    apply (eq_div_iff (show ((n : ℝ) + 1) ≠ 0 by positivity)).2
    simpa [mul_comm] using atkinsonModeWeight_mul_succ_eq_sqrt n
  have hcoeff_gap_nonneg (n : ℕ) :
      0 ≤ coeff n - Real.sqrt ((n : ℝ) + 1) := by
    have hphi_upper :
        atkinsonShiftedRelativePhase (n + 1) 1 ≤ 1 / ((n : ℝ) + 1) := by
      simpa [Nat.add_assoc, add_left_comm, add_comm] using
        atkinsonShiftedRelativePhase_one_upper n
    have hphi_pos : 0 < atkinsonShiftedRelativePhase (n + 1) 1 :=
      atkinsonShiftedRelativePhase_pos (n + 1) 1 (by norm_num) (by omega)
    have hinv_lower :
        (n : ℝ) + 1 ≤ 1 / atkinsonShiftedRelativePhase (n + 1) 1 := by
      have hrecip :
          1 / (1 / ((n : ℝ) + 1)) ≤ 1 / atkinsonShiftedRelativePhase (n + 1) 1 := by
        exact one_div_le_one_div_of_le hphi_pos hphi_upper
      simpa [one_div_div] using hrecip
    have hgap :
        0 ≤ 1 / atkinsonShiftedRelativePhase (n + 1) 1 - ((n : ℝ) + 1) := by
      linarith
    have hgap_eq :
        coeff n - Real.sqrt ((n : ℝ) + 1)
          =
        atkinsonModeWeight n *
          (1 / atkinsonShiftedRelativePhase (n + 1) 1 - ((n : ℝ) + 1)) := by
      unfold coeff
      rw [div_eq_mul_inv, ← atkinsonModeWeight_mul_succ_eq_sqrt n]
      ring
    rw [hgap_eq]
    exact mul_nonneg (atkinsonModeWeight_nonneg n) hgap
  have hcoeff_gap_le_weight (n : ℕ) :
      coeff n - Real.sqrt ((n : ℝ) + 1) ≤ atkinsonModeWeight n := by
    have hphi_lower :
        1 / ((n : ℝ) + 2) ≤ atkinsonShiftedRelativePhase (n + 1) 1 := by
      have hraw :
          (1 : ℝ) / ((((n + 1 : ℕ) : ℝ) + 1)) ≤ atkinsonShiftedRelativePhase (n + 1) 1 := by
        simpa using atkinsonShiftedRelativePhase_lower (n + 1) 1 (by norm_num) (by omega)
      have hdenom : (n : ℝ) + 2 = (((n + 1 : ℕ) : ℝ) + 1) := by
        exact_mod_cast (by omega : n + 2 = (n + 1) + 1)
      simpa [hdenom] using hraw
    have hphi_inv :
        1 / atkinsonShiftedRelativePhase (n + 1) 1 ≤ (n : ℝ) + 2 := by
      have hpos : 0 < (1 / (((n : ℝ) + 2 : ℝ))) := by positivity
      have htmp :
          1 / atkinsonShiftedRelativePhase (n + 1) 1 ≤
            1 / (1 / (((n : ℝ) + 2 : ℝ))) := by
        exact one_div_le_one_div_of_le hpos hphi_lower
      have hconv : 1 / (1 / (((n : ℝ) + 2 : ℝ))) = (n : ℝ) + 2 := by
        field_simp [show ((n : ℝ) + 2 : ℝ) ≠ 0 by positivity]
      simpa [hconv] using htmp
    have hgap :
        1 / atkinsonShiftedRelativePhase (n + 1) 1 - ((n : ℝ) + 1) ≤ 1 := by
      nlinarith [hphi_inv]
    have hgap_eq :
        coeff n - Real.sqrt ((n : ℝ) + 1)
          =
        atkinsonModeWeight n *
          (1 / atkinsonShiftedRelativePhase (n + 1) 1 - ((n : ℝ) + 1)) := by
      unfold coeff
      rw [div_eq_mul_inv, ← atkinsonModeWeight_mul_succ_eq_sqrt n]
      ring
    rw [hgap_eq]
    have hmw_nonneg : 0 ≤ atkinsonModeWeight n := atkinsonModeWeight_nonneg n
    have hmul :
        atkinsonModeWeight n *
            (1 / atkinsonShiftedRelativePhase (n + 1) 1 - ((n : ℝ) + 1))
          ≤ atkinsonModeWeight n * 1 := by
      exact mul_le_mul_of_nonneg_left hgap hmw_nonneg
    linarith
  have hcoeff_gap_abs (n : ℕ) :
      |coeff n - Real.sqrt ((n : ℝ) + 1)| ≤ atkinsonModeWeight n := by
    rw [abs_of_nonneg (hcoeff_gap_nonneg n)]
    exact hcoeff_gap_le_weight n
  have hweight_le_sqrt (n : ℕ) :
      atkinsonModeWeight n ≤ Real.sqrt ((n : ℝ) + 1) := by
    have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := by
      have hle : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
        nlinarith
      simpa using (Real.sqrt_le_sqrt hle)
    exact le_trans (atkinsonModeWeight_le_one n) hsqrt_ge_one
  have hcoeff_le_two_sqrt (n : ℕ) :
      coeff n ≤ 2 * Real.sqrt ((n : ℝ) + 1) := by
    have hsplit :
        coeff n
          =
        Real.sqrt ((n : ℝ) + 1) + (coeff n - Real.sqrt ((n : ℝ) + 1)) := by
      ring
    rw [hsplit]
    nlinarith [hcoeff_gap_le_weight n, hweight_le_sqrt n]
  have hactual_eq (n : ℕ) :
      actual n
        =
      (-Complex.I) *
        ((((coeff n : ℝ) : ℂ)) * Aristotle.StationaryPhaseMainMode.blockMode n 1) := by
    unfold actual coeff
    rw [atkinsonShiftedSingleBoundaryCore_eq_weightedModeStart n 1 (by norm_num)]
    simp [Aristotle.StationaryPhaseMainMode.blockMode, blockCoord_one]
    ring
  have hanchor_norm (n : ℕ) : ‖anchor n‖ = 1 := by
    unfold anchor Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    simp
  have hmain_as_const (n : ℕ) :
      mainTerm n
        =
      ((-Complex.I) * Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
        ((((-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ)) := by
    simp [mainTerm, anchor, Complex.ofReal_mul, mul_assoc, mul_left_comm, mul_comm]
  have hhead_prefix_bound (L : ℕ) (hL : L ≤ N0) :
      ‖∑ n ∈ Finset.range L, actual n‖ ≤ Chead := by
    calc
      ‖∑ n ∈ Finset.range L, actual n‖
        ≤ ∑ n ∈ Finset.range L, ‖actual n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range L, 2 * Real.sqrt ((N0 : ℝ) + 1) := by
            refine Finset.sum_le_sum ?_
            intro n hn
            have hnL : n < L := Finset.mem_range.mp hn
            have hn0 : ((n : ℝ) + 1) ≤ ((N0 : ℝ) + 1) := by
              exact_mod_cast (by omega : n + 1 ≤ N0 + 1)
            calc
              ‖actual n‖
                = atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + 1) 1 := by
                    rw [show actual n =
                      atkinsonWeightedResonantBlockMode (n + 1) 0 *
                        atkinsonShiftedSinglePrimitive (n + 1) 1 0 by
                          simpa [actual] using
                            (atkinson_inverse_phase_core_eq_lowerBoundaryTerm n 1 (by norm_num))]
                    simpa using atkinsonLowerBoundaryTerm_norm n 1 (by norm_num)
              _ = coeff n := by
                    rfl
              _ ≤ 2 * Real.sqrt ((n : ℝ) + 1) := hcoeff_le_two_sqrt n
              _ ≤ 2 * Real.sqrt ((N0 : ℝ) + 1) := by
                    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hn0) (by positivity)
      _ = (L : ℝ) * (2 * Real.sqrt ((N0 : ℝ) + 1)) := by
            simp
      _ ≤ Chead := by
            unfold Chead
            have hL' : (L : ℝ) ≤ N0 := by
              exact_mod_cast hL
            have hsqrt_nonneg : 0 ≤ Real.sqrt ((N0 : ℝ) + 1) := by
              positivity
            nlinarith
  have hmode_bound (n : ℕ) (hn : N0 ≤ n) :
      ‖Aristotle.StationaryPhaseMainMode.blockMode n 1 - anchor n‖
        ≤ Cmode / ((n : ℝ) + 1) := by
    have hquad1_raw := hquad n hn (1 : ℝ) (by simp)
    have hquad1 :
        ‖Aristotle.StationaryPhaseMainMode.blockMode n 1
            - Aristotle.StationaryPhaseMainMode.blockMode n 0‖
          ≤ Cquad / ((n : ℝ) + 1) := by
      have hexp :
          Complex.exp (Complex.I * (((2 * Real.pi : ℝ) : ℂ))) = 1 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using Complex.exp_two_pi_mul_I
      have hquad1_raw' :
          ‖Aristotle.StationaryPhaseMainMode.blockMode n 1
              - Aristotle.StationaryPhaseMainMode.blockMode n 0 *
                  Complex.exp (Complex.I * (((2 * Real.pi : ℝ) : ℂ)))‖
            ≤ Cquad / ((n : ℝ) + 1) := by
        simpa [pow_two] using hquad1_raw
      rw [hexp] at hquad1_raw'
      simpa [Aristotle.StationaryPhaseMainMode.blockMode_zero, mul_comm, mul_left_comm,
        mul_assoc] using hquad1_raw'
    have hstart' :
        ‖Aristotle.StationaryPhaseMainMode.blockMode n 0 - anchor n‖
          ≤ Cstart / ((n : ℝ) + 1) := by
      simpa [anchor] using hstart n
    have hsplit :
        Aristotle.StationaryPhaseMainMode.blockMode n 1 - anchor n
          =
        (Aristotle.StationaryPhaseMainMode.blockMode n 1
            - Aristotle.StationaryPhaseMainMode.blockMode n 0)
          +
        (Aristotle.StationaryPhaseMainMode.blockMode n 0 - anchor n) := by
      ring
    calc
      ‖Aristotle.StationaryPhaseMainMode.blockMode n 1 - anchor n‖
        = ‖(Aristotle.StationaryPhaseMainMode.blockMode n 1
              - Aristotle.StationaryPhaseMainMode.blockMode n 0)
            +
            (Aristotle.StationaryPhaseMainMode.blockMode n 0 - anchor n)‖ := by
              rw [hsplit]
      _ ≤ ‖Aristotle.StationaryPhaseMainMode.blockMode n 1
              - Aristotle.StationaryPhaseMainMode.blockMode n 0‖
            +
            ‖Aristotle.StationaryPhaseMainMode.blockMode n 0 - anchor n‖ := by
              exact norm_add_le _ _
      _ ≤ Cquad / ((n : ℝ) + 1) + Cstart / ((n : ℝ) + 1) := by
            exact add_le_add hquad1 hstart'
      _ = Cmode / ((n : ℝ) + 1) := by
            unfold Cmode
            ring
  have herr_point (n : ℕ) (hn : N0 ≤ n) :
      ‖errFn n‖ ≤ (2 * Cmode + 1) * atkinsonModeWeight n := by
    have hcoeff_nonneg : 0 ≤ coeff n := by
      unfold coeff
      exact div_nonneg (atkinsonModeWeight_nonneg n)
        (le_of_lt (atkinsonShiftedRelativePhase_pos (n + 1) 1 (by norm_num) (by omega)))
    have hsplit :
        errFn n
          =
        (-Complex.I) *
            ((((coeff n : ℝ) : ℂ)) *
              (Aristotle.StationaryPhaseMainMode.blockMode n 1 - anchor n))
          +
        (-Complex.I) *
            ((((coeff n - Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ)) * anchor n) := by
      rw [show errFn n = actual n - mainTerm n by rfl]
      rw [hactual_eq]
      simp [mainTerm, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
      ring
    have hfirst :
        ‖(-Complex.I) *
            ((((coeff n : ℝ) : ℂ)) *
              (Aristotle.StationaryPhaseMainMode.blockMode n 1 - anchor n))‖
          ≤ 2 * Cmode * atkinsonModeWeight n := by
      have hmode := hmode_bound n hn
      calc
        ‖(-Complex.I) *
            ((((coeff n : ℝ) : ℂ)) *
              (Aristotle.StationaryPhaseMainMode.blockMode n 1 - anchor n))‖
          =
        coeff n *
          ‖Aristotle.StationaryPhaseMainMode.blockMode n 1 - anchor n‖ := by
            rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hcoeff_nonneg]
            ring
        _ ≤ coeff n * (Cmode / ((n : ℝ) + 1)) := by
              gcongr
        _ ≤ (2 * Real.sqrt ((n : ℝ) + 1)) * (Cmode / ((n : ℝ) + 1)) := by
              gcongr
              exact hcoeff_le_two_sqrt n
        _ = 2 * Cmode * atkinsonModeWeight n := by
              rw [hweight_formula n]
              field_simp [show ((n : ℝ) + 1) ≠ 0 by positivity]
    have hsecond :
        ‖(-Complex.I) *
            ((((coeff n - Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ)) * anchor n)‖
          ≤ atkinsonModeWeight n := by
      calc
        ‖(-Complex.I) *
            ((((coeff n - Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ)) * anchor n)‖
          =
        |coeff n - Real.sqrt ((n : ℝ) + 1)| * ‖anchor n‖ := by
            rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
            ring
        _ = |coeff n - Real.sqrt ((n : ℝ) + 1)| := by
              rw [hanchor_norm]
              ring
        _ ≤ atkinsonModeWeight n := hcoeff_gap_abs n
    calc
      ‖errFn n‖
        = ‖(-Complex.I) *
              ((((coeff n : ℝ) : ℂ)) *
                (Aristotle.StationaryPhaseMainMode.blockMode n 1 - anchor n))
            +
            (-Complex.I) *
              ((((coeff n - Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ)) * anchor n)‖ := by
              rw [hsplit]
      _ ≤ ‖(-Complex.I) *
              ((((coeff n : ℝ) : ℂ)) *
                (Aristotle.StationaryPhaseMainMode.blockMode n 1 - anchor n))‖
            +
            ‖(-Complex.I) *
              ((((coeff n - Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ)) * anchor n)‖ := by
              exact norm_add_le _ _
      _ ≤ 2 * Cmode * atkinsonModeWeight n + atkinsonModeWeight n := by
            exact add_le_add hfirst hsecond
      _ = (2 * Cmode + 1) * atkinsonModeWeight n := by
            ring
  by_cases hsmall : M + 1 ≤ N0
  · calc
      ‖∑ n ∈ Finset.range (M + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n 1)‖
        = ‖∑ n ∈ Finset.range (M + 1), actual n‖ := by
            rfl
      _ ≤ Chead := hhead_prefix_bound (M + 1) hsmall
      _ ≤ (Chead + Cmain + Cerr) * target := by
            have hrest_nonneg : 0 ≤ Cmain + Cerr := by
              unfold Cmain Cerr
              positivity
            have htarget_nonneg : 0 ≤ target := by positivity
            unfold target
            have hChead_nonneg : 0 ≤ Chead := by
              unfold Chead
              positivity
            nlinarith [htarget_ge_one, hrest_nonneg, hChead_nonneg]
      _ = (Chead + Cmain + Cerr) * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ)) := by
            ring
  · have hN0 : N0 ≤ M + 1 := by omega
    have hsplit_total :
        ∑ n ∈ Finset.range (M + 1), actual n
          =
        (∑ n ∈ Finset.range N0, actual n)
          +
        ∑ n ∈ Finset.Ico N0 (M + 1), actual n := by
      rw [← Finset.sum_range_add_sum_Ico actual hN0]
    have hmain_tail_bound :
        ‖∑ n ∈ Finset.Ico N0 (M + 1), mainTerm n‖ ≤ Cmain * target := by
      let A : ℂ := (-Complex.I) * Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor
      let alt : ℕ → ℝ := fun n => (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1)
      have hA_norm : ‖A‖ = 1 := by
        unfold A Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor
        rw [norm_mul, norm_neg, Complex.norm_I, Complex.norm_exp]
        simp
      have hsum :
          ∑ n ∈ Finset.Ico N0 (M + 1), mainTerm n
            =
          A * (((∑ n ∈ Finset.Ico N0 (M + 1), alt n : ℝ) : ℝ) : ℂ) := by
        calc
          ∑ n ∈ Finset.Ico N0 (M + 1), mainTerm n
              = ∑ n ∈ Finset.Ico N0 (M + 1), A * (((alt n : ℝ) : ℂ)) := by
                  refine Finset.sum_congr rfl ?_
                  intro n hn
                  simp [A, alt, hmain_as_const]
          _ = A * ∑ n ∈ Finset.Ico N0 (M + 1), (((alt n : ℝ) : ℂ)) := by
                  rw [Finset.mul_sum]
          _ = A * (((∑ n ∈ Finset.Ico N0 (M + 1), alt n : ℝ) : ℝ) : ℂ) := by
                  simp
      have hreal_tail :
          |∑ n ∈ Finset.Ico N0 (M + 1), alt n| ≤ Real.sqrt (M + 1) + Real.sqrt (N0 : ℝ) := by
        have hIco :
            ∑ n ∈ Finset.Ico N0 (M + 1), alt n
              =
            ∑ n ∈ Finset.range (M + 1), alt n - ∑ n ∈ Finset.range N0, alt n := by
          rw [Finset.sum_Ico_eq_sub _ hN0]
        rw [hIco]
        calc
          |∑ n ∈ Finset.range (M + 1), alt n - ∑ n ∈ Finset.range N0, alt n|
            ≤ |∑ n ∈ Finset.range (M + 1), alt n|
                + |∑ n ∈ Finset.range N0, alt n| := by
                  simpa [Real.norm_eq_abs, sub_eq_add_neg] using
                    (norm_add_le (∑ n ∈ Finset.range (M + 1), alt n)
                      (-(∑ n ∈ Finset.range N0, alt n)))
          _ ≤ Real.sqrt (M + 1) + Real.sqrt (N0 : ℝ) := by
                exact add_le_add
                  (by simpa [alt] using atkinson_alternating_shifted_sqrt_sum_bound_range (M + 1))
                  (by simpa [alt] using atkinson_alternating_shifted_sqrt_sum_bound_range N0)
      have hreal_tail_target :
          Real.sqrt (M + 1) + Real.sqrt (N0 : ℝ) ≤ Cmain * target := by
        have hsqrtN0_target : Real.sqrt (N0 : ℝ) ≤ Real.sqrt (N0 : ℝ) * target := by
          have hnonneg : 0 ≤ Real.sqrt (N0 : ℝ) := by positivity
          nlinarith [htarget_ge_one, hnonneg]
        calc
          Real.sqrt (M + 1) + Real.sqrt (N0 : ℝ)
            ≤ target + Real.sqrt (N0 : ℝ) * target := by
                nlinarith [htarget_ge_sqrtM, hsqrtN0_target]
          _ = Cmain * target := by
                unfold Cmain
                ring
      calc
        ‖∑ n ∈ Finset.Ico N0 (M + 1), mainTerm n‖
          = ‖A * (((∑ n ∈ Finset.Ico N0 (M + 1), alt n : ℝ) : ℝ) : ℂ)‖ := by
              rw [hsum]
        _ = |∑ n ∈ Finset.Ico N0 (M + 1), alt n| := by
              rw [norm_mul, hA_norm, one_mul]
              simpa using (Complex.norm_real (∑ n ∈ Finset.Ico N0 (M + 1), alt n))
        _ ≤ Cmain * target := le_trans hreal_tail hreal_tail_target
    have htail_err_weight :
        ∑ n ∈ Finset.Ico N0 (M + 1), atkinsonModeWeight n ≤ 2 * target := by
      have hIco :
          ∑ n ∈ Finset.Ico N0 (M + 1), atkinsonModeWeight n
            =
          ∑ n ∈ Finset.range (M + 1), atkinsonModeWeight n
            - ∑ n ∈ Finset.range N0, atkinsonModeWeight n := by
        rw [Finset.sum_Ico_eq_sub _ hN0]
      calc
        ∑ n ∈ Finset.Ico N0 (M + 1), atkinsonModeWeight n
          =
        ∑ n ∈ Finset.range (M + 1), atkinsonModeWeight n
          - ∑ n ∈ Finset.range N0, atkinsonModeWeight n := hIco
        _ ≤ ∑ n ∈ Finset.range (M + 1), atkinsonModeWeight n := by
              have hnonneg : 0 ≤ ∑ n ∈ Finset.range N0, atkinsonModeWeight n := by
                exact Finset.sum_nonneg (by intro n hn; exact atkinsonModeWeight_nonneg n)
              linarith
        _ = ∑ n ∈ Finset.range (M + 1), ((n + 1 : ℝ) ^ (-1 / 2 : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              rw [atkinsonModeWeight]
              norm_num
        _ ≤ 2 * Real.sqrt (M + 1) := by
              simpa [div_eq_mul_inv, show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by ring_nf] using
                Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le (M + 1)
        _ ≤ 2 * target := by
              exact mul_le_mul_of_nonneg_left htarget_ge_sqrtM (by positivity)
    have htail_err_bound :
        ‖∑ n ∈ Finset.Ico N0 (M + 1), errFn n‖ ≤ Cerr * target := by
      calc
        ‖∑ n ∈ Finset.Ico N0 (M + 1), errFn n‖
          ≤ ∑ n ∈ Finset.Ico N0 (M + 1), ‖errFn n‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.Ico N0 (M + 1), ((2 * Cmode + 1) * atkinsonModeWeight n) := by
              refine Finset.sum_le_sum ?_
              intro n hn
              exact herr_point n (Finset.mem_Ico.mp hn).1
        _ = (2 * Cmode + 1) * ∑ n ∈ Finset.Ico N0 (M + 1), atkinsonModeWeight n := by
              rw [Finset.mul_sum]
        _ ≤ (2 * Cmode + 1) * (2 * target) := by
              gcongr
        _ = Cerr * target := by
              unfold Cerr
              ring
    have htail_split :
        ∑ n ∈ Finset.Ico N0 (M + 1), actual n
          =
        (∑ n ∈ Finset.Ico N0 (M + 1), mainTerm n)
          +
        ∑ n ∈ Finset.Ico N0 (M + 1), errFn n := by
      calc
        ∑ n ∈ Finset.Ico N0 (M + 1), actual n
          =
        ∑ n ∈ Finset.Ico N0 (M + 1), (mainTerm n + errFn n) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              unfold errFn
              ring
        _ =
        (∑ n ∈ Finset.Ico N0 (M + 1), mainTerm n)
          +
        ∑ n ∈ Finset.Ico N0 (M + 1), errFn n := by
              rw [Finset.sum_add_distrib]
    calc
      ‖∑ n ∈ Finset.range (M + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n 1)‖
        = ‖∑ n ∈ Finset.range (M + 1), actual n‖ := by
            simp [actual]
      _ = ‖(∑ n ∈ Finset.range N0, actual n)
              + ∑ n ∈ Finset.Ico N0 (M + 1), actual n‖ := by
              rw [hsplit_total]
      _ ≤ ‖∑ n ∈ Finset.range N0, actual n‖
            + ‖∑ n ∈ Finset.Ico N0 (M + 1), actual n‖ := by
              exact norm_add_le _ _
      _ ≤ Chead + ‖∑ n ∈ Finset.Ico N0 (M + 1), actual n‖ := by
              gcongr
              exact hhead_prefix_bound N0 le_rfl
      _ = Chead + ‖(∑ n ∈ Finset.Ico N0 (M + 1), mainTerm n)
              + ∑ n ∈ Finset.Ico N0 (M + 1), errFn n‖ := by
              rw [htail_split]
      _ ≤ Chead + (‖∑ n ∈ Finset.Ico N0 (M + 1), mainTerm n‖
            + ‖∑ n ∈ Finset.Ico N0 (M + 1), errFn n‖) := by
              gcongr
              exact norm_add_le _ _
      _ ≤ Chead + (Cmain * target + Cerr * target) := by
              gcongr
      _ ≤ Chead * target + (Cmain * target + Cerr * target) := by
              have hChead_nonneg : 0 ≤ Chead := by
                unfold Chead
                positivity
              nlinarith [htarget_ge_one, hChead_nonneg]
      _ = (Chead + Cmain + Cerr) * target := by
              ring
      _ = (Chead + Cmain + Cerr) * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ)) := by
              ring

-- Head Core Bound for j ≥ 3: kernel-weighted j=1 prefix sum bounded by
-- C · log(j+1) · √(N+j+1) / j via Abel summation with antitone kernel weights.
omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
theorem atkinson_general_kernelWeighted_j1_headCore_bound_of_j1
    (hj1 :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) :
    ∃ C_head > 0, ∀ j : ℕ, 3 ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase (k + j + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) 1))‖
        ≤ C_head * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C1, hC1, hj1_bound⟩ := hj1
  refine ⟨8 * C1, by positivity, ?_⟩
  intro j hj N
  -- The base oscillatory function (j=1 summand shifted by j)
  let baseFn : ℕ → ℂ := fun k =>
    ((((1 / atkinsonShiftedRelativePhase (k + j + 1) 1 : ℝ) : ℂ)) *
      atkinsonShiftedSingleBoundaryCore (k + j) 1)
  -- The kernel weights
  let b : ℕ → ℝ := fun k => atkinsonLowerBoundaryShiftKernel (k + j) j 1
  -- Handle N = 0 case
  by_cases hN : N = 0
  · simp [hN]
    have hlog_nn : 0 ≤ Real.log (↑j + 1) :=
      Real.log_nonneg (by exact_mod_cast show (1 : ℕ) ≤ j + 1 by omega)
    have hC1_nn : 0 ≤ 8 * C1 := by linarith
    positivity
  · obtain ⟨n0, hn0⟩ := Nat.exists_eq_succ_of_ne_zero hN
    subst hn0
    let target : ℝ := Real.sqrt (((n0 + 1 + j : ℕ) : ℝ) + 1) / j
    -- Uniform bound on partial sums of baseFn
    -- baseFn(k) = j=1 base at index (k+j), so
    -- ∑_{k<K+1} baseFn(k) = prefix(K+j+1) - prefix(j)
    let C0 : ℝ := 2 * C1 * Real.sqrt (((n0 + 1 + j : ℕ) : ℝ) + 1)
    -- The j=1 prefix function
    let prefixFn : ℕ → ℂ := fun M =>
      ∑ n ∈ Finset.range M, baseFn n
    -- For k ≤ n0, bound ‖∑_{m<k+1} baseFn(m)‖
    have hpartial_norm (K : ℕ) (hK : K ≤ n0) :
        ‖∑ m ∈ Finset.range (K + 1), baseFn m‖ ≤ C0 := by
      -- baseFn(m) = j=1 base at index (m+j)
      -- ∑_{m<K+1} baseFn(m) = ∑_{n∈Ico j (K+j+1)} (j=1 base at n)
      --   = prefix_{j=1}(K+j+1) - prefix_{j=1}(j)
      let f : ℕ → ℂ := fun n =>
        ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n 1)
      have hbaseFn_eq : ∀ m : ℕ, baseFn m = f (m + j) := by
        intro m; simp [baseFn, f, Nat.add_assoc, add_comm, add_left_comm]
      have hsum_shift :
          ∑ m ∈ Finset.range (K + 1), baseFn m =
            ∑ m ∈ Finset.range (K + 1), f (m + j) :=
        Finset.sum_congr rfl (fun m _ => hbaseFn_eq m)
      -- prefix(K+j+1) = ∑_{n<K+j+1} f(n)
      have hprefK : ∑ n ∈ Finset.range (K + j + 1), f n =
          ∑ n ∈ Finset.range j, f n +
          ∑ m ∈ Finset.range (K + 1), f (m + j) := by
        rw [show K + j + 1 = j + (K + 1) from by omega]
        rw [Finset.sum_range_add f j (K + 1)]
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        congr 1
        omega
      have hshift_eq :
          ∑ m ∈ Finset.range (K + 1), f (m + j) =
            ∑ n ∈ Finset.range (K + j + 1), f n -
            ∑ n ∈ Finset.range j, f n := by
        rw [hprefK]; ring
      rw [hsum_shift, hshift_eq]
      calc
        ‖∑ n ∈ Finset.range (K + j + 1), f n -
            ∑ n ∈ Finset.range j, f n‖
          ≤ ‖∑ n ∈ Finset.range (K + j + 1), f n‖ +
              ‖∑ n ∈ Finset.range j, f n‖ := norm_sub_le _ _
        _ ≤ C1 * Real.sqrt (((n0 + 1 + j : ℕ) : ℝ) + 1) +
              C1 * Real.sqrt (((n0 + 1 + j : ℕ) : ℝ) + 1) := by
            apply add_le_add
            · have h1 := hj1_bound (K + j)
              rw [show K + j + 1 = (K + j) + 1 from by omega] at h1
              calc ‖∑ n ∈ Finset.range (K + j + 1), f n‖
                  ≤ C1 * (Real.sqrt (↑((K + j) + 1) + 1) / 1) := h1
                _ = C1 * Real.sqrt (↑((K + j) + 1) + 1) := by rw [div_one]
                _ ≤ C1 * Real.sqrt (((n0 + 1 + j : ℕ) : ℝ) + 1) := by
                    apply mul_le_mul_of_nonneg_left _ (le_of_lt hC1)
                    apply Real.sqrt_le_sqrt
                    have : K ≤ n0 := hK
                    exact_mod_cast show ((K + j) + 1 + 1 : ℕ) ≤ (n0 + 1 + j) + 1 by omega
            · have h2 := hj1_bound (j - 1)
              have hj_sub : (j - 1) + 1 = j := by omega
              rw [hj_sub] at h2
              calc ‖∑ n ∈ Finset.range j, f n‖
                  ≤ C1 * (Real.sqrt (↑j + 1) / 1) := h2
                _ = C1 * Real.sqrt (↑j + 1) := by rw [div_one]
                _ ≤ C1 * Real.sqrt (((n0 + 1 + j : ℕ) : ℝ) + 1) := by
                    apply mul_le_mul_of_nonneg_left _ (le_of_lt hC1)
                    apply Real.sqrt_le_sqrt
                    exact_mod_cast show (j + 1 : ℕ) ≤ (n0 + 1 + j) + 1 by omega
        _ = C0 := by unfold C0; ring
    let aRe : ℕ → ℝ := fun k => (baseFn k).re
    let aIm : ℕ → ℝ := fun k => (baseFn k).im
    have hpartial_re : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aRe m| ≤ C0 := by
      intro k hk
      calc |∑ m ∈ Finset.range (k + 1), aRe m|
          = |(∑ m ∈ Finset.range (k + 1), baseFn m).re| := by simp [aRe]
        _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_re_le_norm _
        _ ≤ C0 := hpartial_norm k hk
    have hpartial_im : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aIm m| ≤ C0 := by
      intro k hk
      calc |∑ m ∈ Finset.range (k + 1), aIm m|
          = |(∑ m ∈ Finset.range (k + 1), baseFn m).im| := by simp [aIm]
        _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_im_le_norm _
        _ ≤ C0 := hpartial_norm k hk
    have hb_nonneg : ∀ k ≤ n0, 0 ≤ b k := by
      intro k _
      simpa [b] using
        atkinsonLowerBoundaryShiftKernel_nonneg (k + j) j 1 (by norm_num) (by omega)
    have hb_anti : ∀ k < n0, b (k + 1) ≤ b k := by
      intro k _
      simpa [b, show k + 1 + j = (k + j) + 1 from by omega] using
        (atkinsonLowerBoundaryShiftKernel_antitone j 1 (by norm_num) (by omega)
          (by omega : k + j ≤ k + 1 + j))
    have hb_head : b 0 ≤ 2 / (j : ℝ) := by
      simpa [b] using
        atkinsonLowerBoundaryShiftKernel_le_two_mul_div j j 1 (by norm_num) (by omega) le_rfl
    have hsum_re :
        (∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re =
          ∑ k ∈ Finset.range (n0 + 1), aRe k * b k := by
      simp [aRe, b, baseFn, mul_comm]
    have hsum_im :
        (∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im =
          ∑ k ∈ Finset.range (n0 + 1), aIm k * b k := by
      simp [aIm, b, baseFn, mul_comm]
    have hre :
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re| ≤ C0 * (2 / j) := by
      calc
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
            = |∑ k ∈ Finset.range (n0 + 1), aRe k * b k| := by rw [hsum_re]
        _ ≤ C0 * b 0 :=
              AbelSummation.abel_summation_bound aRe b n0 C0 hpartial_re hb_nonneg hb_anti
        _ ≤ C0 * (2 / j) := by gcongr
    have him :
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| ≤ C0 * (2 / j) := by
      calc
        |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im|
            = |∑ k ∈ Finset.range (n0 + 1), aIm k * b k| := by rw [hsum_im]
        _ ≤ C0 * b 0 :=
              AbelSummation.abel_summation_bound aIm b n0 C0 hpartial_im hb_nonneg hb_anti
        _ ≤ C0 * (2 / j) := by gcongr
    have hnorm :
        ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖ ≤
          2 * (C0 * (2 / j)) := by
      calc
        ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖
            ≤ |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re| +
                |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| :=
              Complex.norm_le_abs_re_add_abs_im _
        _ ≤ C0 * (2 / j) + C0 * (2 / j) := add_le_add hre him
        _ = 2 * (C0 * (2 / j)) := by ring
    have hlog_ge_one : 1 ≤ Real.log (↑j + 1) := by
      have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
        calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
          _ ≤ Real.log 4 := by
              exact Real.log_le_log (Real.exp_pos 1)
                (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num)))
      calc Real.log (↑j + 1) ≥ Real.log 4 := by
              apply Real.log_le_log (by positivity : (0 : ℝ) < 4)
              exact_mod_cast show (4 : ℕ) ≤ j + 1 by omega
        _ ≥ 1 := hlog4
    calc
      ‖∑ k ∈ Finset.range (n0 + 1),
          ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase (k + j + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) 1))‖
        = ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖ := by
            simp [b, baseFn]
      _ ≤ 2 * (C0 * (2 / j)) := hnorm
      _ = (8 * C1) * (Real.sqrt (((n0 + 1 + j : ℕ) : ℝ) + 1) / j) := by
            unfold C0; field_simp; ring
      _ ≤ (8 * C1) * Real.log (↑j + 1) *
            (Real.sqrt (((n0 + 1 + j : ℕ) : ℝ) + 1) / j) := by
            have htarget_pos : 0 < Real.sqrt (((n0 + 1 + j : ℕ) : ℝ) + 1) / j := by
              positivity
            have h8C1_pos : 0 < 8 * C1 := by positivity
            calc 8 * C1 * (Real.sqrt (((n0 + 1 + j : ℕ) : ℝ) + 1) / ↑j)
                = 8 * C1 * 1 * (Real.sqrt (((n0 + 1 + j : ℕ) : ℝ) + 1) / ↑j) := by ring
              _ ≤ 8 * C1 * Real.log (↑j + 1) * (Real.sqrt (((n0 + 1 + j : ℕ) : ℝ) + 1) / ↑j) := by
                    gcongr

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private theorem atkinson_largeShiftBoundaryAbelRemainder_eq_prefix_sub_headCore
    (N j : ℕ) (hj : 1 ≤ j) :
    let headCore : ℕ → ℂ := fun k =>
      ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
        ((((1 / atkinsonShiftedRelativePhase (k + j + 1) 1 : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + j) 1))
    let headTail : ℕ → ℂ := fun k =>
      ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
        ∑ s ∈ Finset.range (j - 1),
          atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1))
    let incTail : ℕ → ℕ → ℂ := fun k r =>
      (((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 2)
            - atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
          ∑ s ∈ Finset.Ico (r + 1) (j - 1),
            atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1)))
    (∑ k ∈ Finset.range N, headTail k)
      +
    ∑ r ∈ Finset.range (j - 1),
      ∑ k ∈ Finset.range N, incTail k r
      =
    (∑ k ∈ Finset.range N,
        ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + j) j))
      -
    ∑ k ∈ Finset.range N, headCore k := by
  intro headCore headTail incTail
  have hdecomp :=
    atkinsonShiftedInversePhaseCorePrefix_eq_shiftBoundaryAbelDecomposition N j hj
  exact eq_sub_iff_add_eq.mpr <| by
    simpa [headCore, headTail, incTail, add_assoc, add_left_comm, add_comm] using hdecomp.symm

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private theorem atkinson_largeShiftBoundaryAbelRemainder_eq_weightedBoundarySum
    (N j : ℕ) :
    let headTail : ℕ → ℂ := fun k =>
      ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
        ∑ s ∈ Finset.range (j - 1),
          atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1))
    let incTail : ℕ → ℕ → ℂ := fun k r =>
      (((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 2)
            - atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
          ∑ s ∈ Finset.Ico (r + 1) (j - 1),
            atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1)))
    (∑ k ∈ Finset.range N, headTail k)
      +
    ∑ r ∈ Finset.range (j - 1),
      ∑ k ∈ Finset.range N, incTail k r
      =
    ∑ k ∈ Finset.range N,
      ∑ r ∈ Finset.range (j - 1),
        ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
          atkinsonResonantShiftedBoundaryTerm (k + j) (r + 1)) := by
  intro headTail incTail
  simpa [headTail, incTail] using
    (atkinsonShiftBoundary_remainder_abel_reorder N j).symm

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private theorem atkinson_largeShiftWeightedBoundarySum_eq_prefix_sub_headCore
    (N j : ℕ) (hj : 1 ≤ j) :
    (∑ k ∈ Finset.range N,
        ∑ r ∈ Finset.range (j - 1),
          ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm (k + j) (r + 1)))
      =
    (∑ k ∈ Finset.range N,
        ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + j) j))
      -
    ∑ k ∈ Finset.range N,
      ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
        ((((1 / atkinsonShiftedRelativePhase (k + j + 1) 1 : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + j) 1)) := by
  let headCore : ℕ → ℂ := fun k =>
    ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
      ((((1 / atkinsonShiftedRelativePhase (k + j + 1) 1 : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore (k + j) 1))
  let headTail : ℕ → ℂ := fun k =>
    ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
      ∑ s ∈ Finset.range (j - 1),
        atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1))
  let incTail : ℕ → ℕ → ℂ := fun k r =>
    (((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 2)
          - atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
        ∑ s ∈ Finset.Ico (r + 1) (j - 1),
          atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1)))
  calc
    (∑ k ∈ Finset.range N,
        ∑ r ∈ Finset.range (j - 1),
          ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm (k + j) (r + 1)))
      =
    (∑ k ∈ Finset.range N, headTail k)
      +
    ∑ r ∈ Finset.range (j - 1),
      ∑ k ∈ Finset.range N, incTail k r := by
        symm
        simpa [headTail, incTail] using
          atkinson_largeShiftBoundaryAbelRemainder_eq_weightedBoundarySum N j
    _ =
      (∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) j))
        -
      ∑ k ∈ Finset.range N, headCore k := by
          simpa [headCore, headTail, incTail] using
            atkinson_largeShiftBoundaryAbelRemainder_eq_prefix_sub_headCore N j hj

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private theorem atkinson_inversePhaseCorePrefix_bound_large_j :
    ∃ C > 0, ∀ j : ℕ, 3 ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) j)‖
        ≤ C * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
  sorry

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private theorem atkinson_largeShiftWeightedBoundarySum_bound :
    ∃ C_rem > 0, ∀ j : ℕ, 3 ≤ j → ∀ N : ℕ,
      ‖∑ k ∈ Finset.range N,
          ∑ r ∈ Finset.range (j - 1),
            ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
              atkinsonResonantShiftedBoundaryTerm (k + j) (r + 1))‖
        ≤ C_rem * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_prefix, hC_prefix, hprefix⟩ := atkinson_inversePhaseCorePrefix_bound_large_j
  obtain ⟨C1, hC1, hj1⟩ := atkinson_inversePhaseCorePrefix_bound_j1
  obtain ⟨C_head, hC_head, hhead⟩ :=
    atkinson_general_kernelWeighted_j1_headCore_bound_of_j1 ⟨C1, hC1, hj1⟩
  refine ⟨C_prefix + C_head, by linarith, ?_⟩
  intro j hj N
  have hdecomp :=
    atkinson_largeShiftWeightedBoundarySum_eq_prefix_sub_headCore N j (by omega : 1 ≤ j)
  have hpre :
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) j)‖
        ≤ C_prefix * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) :=
    hprefix j hj N
  have hhd :
      ‖∑ k ∈ Finset.range N,
          ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
            ((((1 / atkinsonShiftedRelativePhase (k + j + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore (k + j) 1))‖
        ≤ C_head * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) :=
    hhead j hj N
  have htri := norm_sub_le
    (∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) j))
    (∑ k ∈ Finset.range N,
        ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
          ((((1 / atkinsonShiftedRelativePhase (k + j + 1) 1 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) 1)))
  rw [← hdecomp] at htri
  linarith [add_le_add hpre hhd]

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] in
private theorem atkinson_largeShiftBoundaryAbelRemainder_bound_of_largeShiftPrefix
    [AtkinsonLargeShiftPrefixBoundHyp] :
    ∃ C_rem > 0, ∀ j : ℕ, 3 ≤ j → ∀ N : ℕ,
      let headTail : ℕ → ℂ := fun k =>
        ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
          ∑ s ∈ Finset.range (j - 1),
            atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1))
      let incTail : ℕ → ℕ → ℂ := fun k r =>
        (((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 2)
              - atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
            ∑ s ∈ Finset.Ico (r + 1) (j - 1),
              atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1)))
      ‖(∑ k ∈ Finset.range N, headTail k)
          +
        ∑ r ∈ Finset.range (j - 1),
          ∑ k ∈ Finset.range N, incTail k r‖
        ≤ C_rem * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C1, hC1, hj1⟩ := atkinson_inversePhaseCorePrefix_bound_j1
  obtain ⟨C_head, hC_head, hhead⟩ :=
    atkinson_general_kernelWeighted_j1_headCore_bound_of_j1 ⟨C1, hC1, hj1⟩
  obtain ⟨C_large, hC_large, hlarge⟩ := AtkinsonLargeShiftPrefixBoundHyp.bound
  refine ⟨C_head + C_large, by positivity, ?_⟩
  intro j hj N
  set target : ℝ := Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)
  set headCore : ℕ → ℂ := fun k =>
    ((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ) *
      ((((1 / atkinsonShiftedRelativePhase (k + j + 1) 1 : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore (k + j) 1)
  set headTail : ℕ → ℂ := fun k =>
    ((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ) *
      (∑ s ∈ Finset.range (j - 1),
        atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1))
  set incTail : ℕ → ℕ → ℂ := fun k r =>
    ((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 2)
        - atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ) *
      (∑ s ∈ Finset.Ico (r + 1) (j - 1),
        atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1))
  have hrem_eq :
      (∑ k ∈ Finset.range N, headTail k)
        +
      ∑ r ∈ Finset.range (j - 1),
        ∑ k ∈ Finset.range N, incTail k r
        =
      (∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) j))
        -
      ∑ k ∈ Finset.range N, headCore k := by
    simpa [headCore, headTail, incTail] using
      atkinson_largeShiftBoundaryAbelRemainder_eq_prefix_sub_headCore N j (by omega)
  have hhead' :
      ‖∑ k ∈ Finset.range N, headCore k‖
        ≤ C_head * target := by
    simpa [headCore, target, mul_assoc] using hhead j hj N
  have hlarge' :
      ‖∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) j)‖
        ≤ C_large * target := by
    simpa [target, mul_assoc] using hlarge j hj N
  have hbound :
      ‖(∑ k ∈ Finset.range N, headTail k)
            +
          ∑ r ∈ Finset.range (j - 1),
            ∑ k ∈ Finset.range N, incTail k r‖
        ≤ (C_head + C_large) * target := by
    calc
      ‖(∑ k ∈ Finset.range N, headTail k)
            +
          ∑ r ∈ Finset.range (j - 1),
            ∑ k ∈ Finset.range N, incTail k r‖
        = ‖(∑ k ∈ Finset.range N,
              ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
                atkinsonShiftedSingleBoundaryCore (k + j) j))
            - ∑ k ∈ Finset.range N, headCore k‖ := by
              rw [hrem_eq]
      _ ≤ ‖∑ k ∈ Finset.range N,
              ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
                atkinsonShiftedSingleBoundaryCore (k + j) j)‖
            +
          ‖∑ k ∈ Finset.range N, headCore k‖ := by
              exact norm_sub_le _ _
      _ ≤ C_large * target + C_head * target := by
              exact add_le_add hlarge' hhead'
      _ = (C_head + C_large) * target := by ring
  simpa [target, headTail, incTail, mul_assoc] using hbound

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonLargeShiftPrefixBoundHyp] in
private theorem atkinson_largeShiftBoundaryAbelRemainder_bound_of_contracting_nextShift
    [AtkinsonSmallShiftPrefixBoundHyp]
    (γ : ℝ) (hγ_lt_one : γ < 1)
    (hbdryRow :
      ∃ C_bdry > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
        ‖∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)‖
          ≤ C_bdry * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j))
    (htail :
      ∀ C_prev : ℝ, 0 < C_prev →
      ∀ j : ℕ, 2 ≤ j →
        (∀ N : ℕ,
          ‖∑ k ∈ Finset.range N,
              ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
                atkinsonShiftedSingleBoundaryCore (k + j) j)‖
            ≤ C_prev * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)) →
        ∀ N : ℕ,
          ‖∑ k ∈ Finset.range N,
              ((((1 / atkinsonUpperBoundaryStepCoeff (k + (j + 1)) j : ℝ) : ℂ)) *
                ((((1 / atkinsonShiftedRelativePhase
                    (k + ((j + 1) + j)) j : ℝ) : ℂ)) *
                  atkinsonShiftedSingleBoundaryCore (k + (j + 1)) j))‖
            ≤ γ * C_prev *
                (Real.sqrt (((N + (j + 1) : ℕ) : ℝ) + 1) / (j + 1))) :
    ∃ C_rem > 0, ∀ j : ℕ, 3 ≤ j → ∀ N : ℕ,
      let headTail : ℕ → ℂ := fun k =>
        ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
          ∑ s ∈ Finset.range (j - 1),
            atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1))
      let incTail : ℕ → ℕ → ℂ := fun k r =>
        (((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 2)
              - atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
            ∑ s ∈ Finset.Ico (r + 1) (j - 1),
              atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1)))
      ‖(∑ k ∈ Finset.range N, headTail k)
          +
        ∑ r ∈ Finset.range (j - 1),
          ∑ k ∈ Finset.range N, incTail k r‖
        ≤ C_rem * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
  letI : AtkinsonLargeShiftPrefixBoundHyp :=
    atkinson_largeShiftPrefixBound_atomic_of_nextShift γ hγ_lt_one hbdryRow htail
  exact atkinson_largeShiftBoundaryAbelRemainder_bound_of_largeShiftPrefix

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private theorem atkinson_largeShiftBoundaryAbelRemainder_bound :
    ∃ C_rem > 0, ∀ j : ℕ, 3 ≤ j → ∀ N : ℕ,
      let headTail : ℕ → ℂ := fun k =>
        ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
          ∑ s ∈ Finset.range (j - 1),
            atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1))
      let incTail : ℕ → ℕ → ℂ := fun k r =>
        (((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 2)
              - atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
            ∑ s ∈ Finset.Ico (r + 1) (j - 1),
              atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1)))
      ‖(∑ k ∈ Finset.range N, headTail k)
          +
        ∑ r ∈ Finset.range (j - 1),
          ∑ k ∈ Finset.range N, incTail k r‖
        ≤ C_rem * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_rem, hC_rem, hweighted⟩ := atkinson_largeShiftWeightedBoundarySum_bound
  refine ⟨C_rem, hC_rem, ?_⟩
  intro j hj N
  let headTail : ℕ → ℂ := fun k =>
    ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
      ∑ s ∈ Finset.range (j - 1),
        atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1))
  let incTail : ℕ → ℕ → ℂ := fun k r =>
    (((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 2)
          - atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
        ∑ s ∈ Finset.Ico (r + 1) (j - 1),
          atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1)))
  calc
    ‖(∑ k ∈ Finset.range N, headTail k)
          +
        ∑ r ∈ Finset.range (j - 1),
          ∑ k ∈ Finset.range N, incTail k r‖
      =
    ‖∑ k ∈ Finset.range N,
        ∑ r ∈ Finset.range (j - 1),
          ((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm (k + j) (r + 1))‖ := by
          rw [atkinson_largeShiftBoundaryAbelRemainder_eq_weightedBoundarySum N j]
    _ ≤ C_rem * Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) :=
      hweighted j hj N

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
theorem atkinson_largeShiftPrefixBound_of_direct_abel :
    AtkinsonLargeShiftPrefixBoundHyp := by
  obtain ⟨C1, hC1, hj1⟩ := atkinson_inversePhaseCorePrefix_bound_j1
  obtain ⟨C_head, hC_head, hhead⟩ :=
    atkinson_general_kernelWeighted_j1_headCore_bound_of_j1 ⟨C1, hC1, hj1⟩
  obtain ⟨C_rem, hC_rem, hrem⟩ := atkinson_largeShiftBoundaryAbelRemainder_bound
  refine ⟨C_head + C_rem, by positivity, ?_⟩
  intro j hj N
  let target : ℝ := Real.log (↑j + 1) * (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j)
  let headCore : ℕ → ℂ := fun k =>
    ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
      ((((1 / atkinsonShiftedRelativePhase (k + j + 1) 1 : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore (k + j) 1))
  let headTail : ℕ → ℂ := fun k =>
    ((((atkinsonLowerBoundaryShiftKernel (k + j) j 1 : ℝ) : ℂ)) *
      ∑ s ∈ Finset.range (j - 1),
        atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1))
  let incTail : ℕ → ℕ → ℂ := fun k r =>
    (((((atkinsonLowerBoundaryShiftKernel (k + j) j (r + 2)
          - atkinsonLowerBoundaryShiftKernel (k + j) j (r + 1) : ℝ) : ℂ)) *
        ∑ s ∈ Finset.Ico (r + 1) (j - 1),
          atkinsonResonantShiftedBoundaryTerm (k + j) (s + 1)))
  have hdecomp :
      ∑ k ∈ Finset.range N,
          ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + j) j)
        =
      (∑ k ∈ Finset.range N, headCore k)
        +
      (∑ k ∈ Finset.range N, headTail k)
        +
      ∑ r ∈ Finset.range (j - 1),
          ∑ k ∈ Finset.range N, incTail k r := by
    simpa [headCore, headTail, incTail] using
      atkinsonShiftedInversePhaseCorePrefix_eq_shiftBoundaryAbelDecomposition N j (by omega)
  have hhead' :
      ‖∑ k ∈ Finset.range N, headCore k‖
        ≤ C_head * target := by
    simpa [headCore, target, mul_assoc] using hhead j hj N
  have hrem' :
      ‖(∑ k ∈ Finset.range N, headTail k)
          +
        ∑ r ∈ Finset.range (j - 1),
          ∑ k ∈ Finset.range N, incTail k r‖
        ≤ C_rem * target := by
    simpa [headTail, incTail, target, mul_assoc] using hrem j hj N
  calc
    ‖∑ k ∈ Finset.range N,
        ((((1 / atkinsonShiftedRelativePhase (k + (j + j)) j : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + j) j)‖
      =
    ‖(∑ k ∈ Finset.range N, headCore k)
        +
      ((∑ k ∈ Finset.range N, headTail k)
        +
      ∑ r ∈ Finset.range (j - 1),
        ∑ k ∈ Finset.range N, incTail k r)‖ := by
          rw [hdecomp]
          ring_nf
    _ ≤ ‖∑ k ∈ Finset.range N, headCore k‖
          +
        ‖(∑ k ∈ Finset.range N, headTail k)
            +
          ∑ r ∈ Finset.range (j - 1),
            ∑ k ∈ Finset.range N, incTail k r‖ := by
            exact norm_add_le _ _
    _ ≤ C_head * target + C_rem * target := by
            exact add_le_add hhead' hrem'
    _ = (C_head + C_rem) * target := by
            ring
    _ = (C_head + C_rem) * Real.log (↑j + 1) *
          (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) := by
            rw [show (C_head + C_rem) * target
                = (C_head + C_rem) * Real.log (↑j + 1) *
                    (Real.sqrt (((N + j : ℕ) : ℝ) + 1) / j) by
                  simp [target, mul_assoc]]

private theorem atkinson_shift1_lowerBoundaryPrefix_bound_atomic_of_j1
    (hj1 :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) :
    ∃ C_low > 0, ∀ K : ℕ,
      ‖∑ k ∈ Finset.range (K + 1),
          atkinsonWeightedResonantBlockMode (k + 2) 0 *
            atkinsonShiftedSinglePrimitive (k + 2) 1 0‖
        ≤ C_low * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
  have hj1' :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)) := by
    simpa using hj1
  obtain ⟨C_low, hC_low, hshift⟩ :=
    atkinson_shiftedInversePhaseCorePrefix_bound_shifted_of_native_fixedShift 1 (by norm_num) hj1'
  refine ⟨C_low, hC_low, ?_⟩
  intro K
  have hpointwise :
      ∑ k ∈ Finset.range (K + 1),
          atkinsonWeightedResonantBlockMode (k + 2) 0 *
            atkinsonShiftedSinglePrimitive (k + 2) 1 0
        =
      ∑ k ∈ Finset.range (K + 1),
          ((((1 / atkinsonShiftedRelativePhase (k + (1 + 1)) 1 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + 1) 1) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    simpa [Nat.add_assoc, add_left_comm, add_comm] using
      (atkinson_inverse_phase_core_eq_lowerBoundaryTerm (k + 1) 1 (by norm_num)).symm
  have hsqrt :
      Real.sqrt (((K + 2 : ℕ) : ℝ) + 1) / (1 : ℝ) ≤ Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
    calc
      Real.sqrt (((K + 2 : ℕ) : ℝ) + 1) / (1 : ℝ)
          = Real.sqrt (((K + 2 : ℕ) : ℝ) + 1) := by ring
      _ ≤ Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
            exact Real.sqrt_le_sqrt (by
              exact_mod_cast (by omega : (K + 2) + 1 ≤ (K + 3) + 1))
  calc
    ‖∑ k ∈ Finset.range (K + 1),
        atkinsonWeightedResonantBlockMode (k + 2) 0 *
          atkinsonShiftedSinglePrimitive (k + 2) 1 0‖
      =
    ‖∑ k ∈ Finset.range (K + 1),
        ((((1 / atkinsonShiftedRelativePhase (k + (1 + 1)) 1 : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + 1) 1)‖ := by
          rw [hpointwise]
    _ ≤ C_low * (Real.sqrt ((((K + 1) + 1 : ℕ) : ℝ) + 1) / (1 : ℝ)) := by
          simpa [Nat.add_assoc, add_left_comm, add_comm] using hshift (K + 1)
    _ = C_low * (Real.sqrt (((K + 2 : ℕ) : ℝ) + 1) / (1 : ℝ)) := by
          ring_nf
    _ ≤ C_low * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
          exact mul_le_mul_of_nonneg_left hsqrt (le_of_lt hC_low)

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private theorem atkinson_shift1_lowerBoundaryPrefix_bound_atomic_of_j1_clean
    (hj1 :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) :
    ∃ C_low > 0, ∀ K : ℕ,
      ‖∑ k ∈ Finset.range (K + 1),
          atkinsonWeightedResonantBlockMode (k + 2) 0 *
            atkinsonShiftedSinglePrimitive (k + 2) 1 0‖
        ≤ C_low * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
  have hj1' :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / ((1 : ℕ) : ℝ)) := by
    simpa using hj1
  obtain ⟨C_low, hC_low, hshift⟩ :=
    atkinson_shiftedInversePhaseCorePrefix_bound_shifted_of_native_fixedShift 1 (by norm_num) hj1'
  refine ⟨C_low, hC_low, ?_⟩
  intro K
  have hpointwise :
      ∑ k ∈ Finset.range (K + 1),
          atkinsonWeightedResonantBlockMode (k + 2) 0 *
            atkinsonShiftedSinglePrimitive (k + 2) 1 0
        =
      ∑ k ∈ Finset.range (K + 1),
          ((((1 / atkinsonShiftedRelativePhase (k + (1 + 1)) 1 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore (k + 1) 1) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    simpa [Nat.add_assoc, add_left_comm, add_comm] using
      (atkinson_inverse_phase_core_eq_lowerBoundaryTerm (k + 1) 1 (by norm_num)).symm
  have hsqrt :
      Real.sqrt (((K + 2 : ℕ) : ℝ) + 1) / (1 : ℝ) ≤ Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
    calc
      Real.sqrt (((K + 2 : ℕ) : ℝ) + 1) / (1 : ℝ)
          = Real.sqrt (((K + 2 : ℕ) : ℝ) + 1) := by ring
      _ ≤ Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
            exact Real.sqrt_le_sqrt (by
              exact_mod_cast (by omega : (K + 2) + 1 ≤ (K + 3) + 1))
  calc
    ‖∑ k ∈ Finset.range (K + 1),
        atkinsonWeightedResonantBlockMode (k + 2) 0 *
          atkinsonShiftedSinglePrimitive (k + 2) 1 0‖
      =
    ‖∑ k ∈ Finset.range (K + 1),
        ((((1 / atkinsonShiftedRelativePhase (k + (1 + 1)) 1 : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore (k + 1) 1)‖ := by
          rw [hpointwise]
    _ ≤ C_low * (Real.sqrt ((((K + 1) + 1 : ℕ) : ℝ) + 1) / (1 : ℝ)) := by
          simpa [Nat.add_assoc, add_left_comm, add_comm] using hshift (K + 1)
    _ = C_low * (Real.sqrt (((K + 2 : ℕ) : ℝ) + 1) / (1 : ℝ)) := by
          ring_nf
    _ ≤ C_low * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
          exact mul_le_mul_of_nonneg_left hsqrt (le_of_lt hC_low)

private lemma atkinson_shift1_upperBoundaryTerm_eq_blockMode_two
    (n : ℕ) :
    atkinsonWeightedResonantBlockMode (n + 1) 1 *
      atkinsonShiftedSinglePrimitive (n + 1) 1 1
      =
    (-Complex.I) *
      ((((atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
        Aristotle.StationaryPhaseMainMode.blockMode n 2) := by
  have hpacket :
      atkinsonWeightedResonantBlockMode (n + 1) 1 *
        atkinsonShiftedSinglePacket (n + 1) 1 1
        =
      (((atkinsonModeWeight n : ℝ) : ℂ) *
        Aristotle.StationaryPhaseMainMode.blockMode n 2) := by
    calc
      atkinsonWeightedResonantBlockMode (n + 1) 1 *
          atkinsonShiftedSinglePacket (n + 1) 1 1
          =
        (((atkinsonModeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (blockCoord (n + 1) 1)) := by
            simpa [show n + 1 - 1 = n by omega, atkinsonWeightedResonantBlockMode,
              Aristotle.StationaryPhaseMainMode.blockMode]
              using
                (atkinsonWeighted_hardyCosExp_eq_resonant_times_shiftedPacket (n + 1) 1 1).symm
      _ =
        (((atkinsonModeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (blockCoord n 2)) := by
            congr 2
            calc
              blockCoord (n + 1) 1 = hardyStart (n + 2) := by
                simpa using blockCoord_one (n + 1)
              _ = blockCoord n (((n + 1 : ℝ) - n) + 1) := by
                simpa using
                  Aristotle.StationaryPhaseMainMode.hardyStart_succ_eq_blockCoord_shift n (n + 1)
              _ = blockCoord n 2 := by
                congr 1
                ring
      _ =
        (((atkinsonModeWeight n : ℝ) : ℂ) *
          Aristotle.StationaryPhaseMainMode.blockMode n 2) := by
            rw [Aristotle.StationaryPhaseMainMode.blockMode]
  have hphase_pos : 0 < atkinsonShiftedRelativePhase (n + 1) 1 := by
    exact atkinsonShiftedRelativePhase_pos (n + 1) 1 (by norm_num) (by omega)
  have hphase_ne : (((atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt hphase_pos
  have hprimitive :
      atkinsonShiftedSinglePrimitive (n + 1) 1 1
        =
      ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
        ((-Complex.I) * atkinsonShiftedSinglePacket (n + 1) 1 1)) := by
    calc
      atkinsonShiftedSinglePrimitive (n + 1) 1 1
          = (1 : ℂ) * atkinsonShiftedSinglePrimitive (n + 1) 1 1 := by simp
      _ =
        (((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
            (((atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ))) *
          atkinsonShiftedSinglePrimitive (n + 1) 1 1) := by
            have hcancel :
                ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
                  (((atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ))) = 1 := by
              exact_mod_cast
                (one_div_mul_cancel
                  (show atkinsonShiftedRelativePhase (n + 1) 1 ≠ 0 by
                    linarith [hphase_pos]))
            rw [hcancel]
      _ =
        ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
          ((((atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
            atkinsonShiftedSinglePrimitive (n + 1) 1 1)) := by
            ring
      _ =
        ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
          ((-Complex.I) * atkinsonShiftedSinglePacket (n + 1) 1 1)) := by
            rw [atkinsonShiftedRelativePhase_mul_shiftedSinglePrimitive (n + 1) 1 1
              (by norm_num) (by omega)]
  calc
    atkinsonWeightedResonantBlockMode (n + 1) 1 *
        atkinsonShiftedSinglePrimitive (n + 1) 1 1
        =
      atkinsonWeightedResonantBlockMode (n + 1) 1 *
        ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
          ((-Complex.I) * atkinsonShiftedSinglePacket (n + 1) 1 1)) := by
            rw [hprimitive]
    _ =
      (-Complex.I) *
        ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
          (atkinsonWeightedResonantBlockMode (n + 1) 1 *
            atkinsonShiftedSinglePacket (n + 1) 1 1)) := by
            simp [mul_assoc, mul_left_comm, mul_comm]
    _ =
      (-Complex.I) *
        ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
          ((((atkinsonModeWeight n : ℝ) : ℂ) *
            Aristotle.StationaryPhaseMainMode.blockMode n 2))) := by
            rw [hpacket]
    _ =
      (-Complex.I) *
        ((((atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
          Aristotle.StationaryPhaseMainMode.blockMode n 2) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private lemma atkinson_shift1_upperBoundaryTerm_eq_blockMode_two_clean
    (n : ℕ) :
    atkinsonWeightedResonantBlockMode (n + 1) 1 *
      atkinsonShiftedSinglePrimitive (n + 1) 1 1
      =
    (-Complex.I) *
      ((((atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
        Aristotle.StationaryPhaseMainMode.blockMode n 2) := by
  have hpacket :
      atkinsonWeightedResonantBlockMode (n + 1) 1 *
        atkinsonShiftedSinglePacket (n + 1) 1 1
        =
      (((atkinsonModeWeight n : ℝ) : ℂ) *
        Aristotle.StationaryPhaseMainMode.blockMode n 2) := by
    calc
      atkinsonWeightedResonantBlockMode (n + 1) 1 *
          atkinsonShiftedSinglePacket (n + 1) 1 1
          =
        (((atkinsonModeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (blockCoord (n + 1) 1)) := by
            simpa [show n + 1 - 1 = n by omega, atkinsonWeightedResonantBlockMode,
              Aristotle.StationaryPhaseMainMode.blockMode]
              using
                (atkinsonWeighted_hardyCosExp_eq_resonant_times_shiftedPacket (n + 1) 1 1).symm
      _ =
        (((atkinsonModeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (blockCoord n 2)) := by
            congr 2
            calc
              blockCoord (n + 1) 1 = hardyStart (n + 2) := by
                simpa using blockCoord_one (n + 1)
              _ = blockCoord n (((n + 1 : ℝ) - n) + 1) := by
                simpa using
                  Aristotle.StationaryPhaseMainMode.hardyStart_succ_eq_blockCoord_shift n (n + 1)
              _ = blockCoord n 2 := by
                congr 1
                ring
      _ =
        (((atkinsonModeWeight n : ℝ) : ℂ) *
          Aristotle.StationaryPhaseMainMode.blockMode n 2) := by
            rw [Aristotle.StationaryPhaseMainMode.blockMode]
  have hphase_pos : 0 < atkinsonShiftedRelativePhase (n + 1) 1 := by
    exact atkinsonShiftedRelativePhase_pos (n + 1) 1 (by norm_num) (by omega)
  have hprimitive :
      atkinsonShiftedSinglePrimitive (n + 1) 1 1
        =
      ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
        ((-Complex.I) * atkinsonShiftedSinglePacket (n + 1) 1 1)) := by
    calc
      atkinsonShiftedSinglePrimitive (n + 1) 1 1
          = (1 : ℂ) * atkinsonShiftedSinglePrimitive (n + 1) 1 1 := by simp
      _ =
        (((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
            (((atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ))) *
          atkinsonShiftedSinglePrimitive (n + 1) 1 1) := by
            have hcancel :
                ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
                  (((atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ))) = 1 := by
              exact_mod_cast
                (one_div_mul_cancel
                  (show atkinsonShiftedRelativePhase (n + 1) 1 ≠ 0 by
                    linarith [hphase_pos]))
            rw [hcancel]
      _ =
        ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
          ((((atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
            atkinsonShiftedSinglePrimitive (n + 1) 1 1)) := by
            ring
      _ =
        ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
          ((-Complex.I) * atkinsonShiftedSinglePacket (n + 1) 1 1)) := by
            rw [atkinsonShiftedRelativePhase_mul_shiftedSinglePrimitive (n + 1) 1 1
              (by norm_num) (by omega)]
  calc
    atkinsonWeightedResonantBlockMode (n + 1) 1 *
        atkinsonShiftedSinglePrimitive (n + 1) 1 1
        =
      atkinsonWeightedResonantBlockMode (n + 1) 1 *
        ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
          ((-Complex.I) * atkinsonShiftedSinglePacket (n + 1) 1 1)) := by
            rw [hprimitive]
    _ =
      (-Complex.I) *
        ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
          (atkinsonWeightedResonantBlockMode (n + 1) 1 *
            atkinsonShiftedSinglePacket (n + 1) 1 1)) := by
            simp [mul_assoc, mul_left_comm, mul_comm]
    _ =
      (-Complex.I) *
        ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
          ((((atkinsonModeWeight n : ℝ) : ℂ) *
            Aristotle.StationaryPhaseMainMode.blockMode n 2))) := by
            rw [hpacket]
    _ =
      (-Complex.I) *
        ((((atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
          Aristotle.StationaryPhaseMainMode.blockMode n 2) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

private lemma atkinson_shift1_lowerBoundaryTerm_eq_blockMode_one
    (n : ℕ) :
    atkinsonWeightedResonantBlockMode (n + 1) 0 *
      atkinsonShiftedSinglePrimitive (n + 1) 1 0
      =
    (-Complex.I) *
      ((((atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
        Aristotle.StationaryPhaseMainMode.blockMode n 1) := by
  calc
    atkinsonWeightedResonantBlockMode (n + 1) 0 *
        atkinsonShiftedSinglePrimitive (n + 1) 1 0
        =
      ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n 1) := by
            simpa [Nat.add_assoc, add_left_comm, add_comm] using
              (atkinson_inverse_phase_core_eq_lowerBoundaryTerm n 1 (by norm_num)).symm
    _ =
      (-Complex.I) *
        ((((atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
          Aristotle.StationaryPhaseMainMode.blockMode n 1) := by
            rw [atkinsonShiftedSingleBoundaryCore_eq_weightedModeStart n 1 (by norm_num)]
            simp [Aristotle.StationaryPhaseMainMode.blockMode, blockCoord_one, div_eq_mul_inv,
              mul_assoc, mul_left_comm, mul_comm]

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private lemma atkinson_shift1_lowerBoundaryTerm_eq_blockMode_one_clean
    (n : ℕ) :
    atkinsonWeightedResonantBlockMode (n + 1) 0 *
      atkinsonShiftedSinglePrimitive (n + 1) 1 0
      =
    (-Complex.I) *
      ((((atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
        Aristotle.StationaryPhaseMainMode.blockMode n 1) := by
  calc
    atkinsonWeightedResonantBlockMode (n + 1) 0 *
        atkinsonShiftedSinglePrimitive (n + 1) 1 0
        =
      ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n 1) := by
            simpa [Nat.add_assoc, add_left_comm, add_comm] using
              (atkinson_inverse_phase_core_eq_lowerBoundaryTerm n 1 (by norm_num)).symm
    _ =
      (-Complex.I) *
        ((((atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
          Aristotle.StationaryPhaseMainMode.blockMode n 1) := by
            rw [atkinsonShiftedSingleBoundaryCore_eq_weightedModeStart n 1 (by norm_num)]
            simp [Aristotle.StationaryPhaseMainMode.blockMode, blockCoord_one, div_eq_mul_inv,
              mul_assoc, mul_left_comm, mul_comm]

private lemma atkinson_shift1_upperMinusLowerBoundaryTerm_eq_blockMode_two_minus_one
    (n : ℕ) :
    atkinsonWeightedResonantBlockMode (n + 1) 1 *
        atkinsonShiftedSinglePrimitive (n + 1) 1 1
      -
      atkinsonWeightedResonantBlockMode (n + 1) 0 *
        atkinsonShiftedSinglePrimitive (n + 1) 1 0
      =
    (-Complex.I) *
      ((((atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
        (Aristotle.StationaryPhaseMainMode.blockMode n 2 -
          Aristotle.StationaryPhaseMainMode.blockMode n 1)) := by
  rw [atkinson_shift1_upperBoundaryTerm_eq_blockMode_two, atkinson_shift1_lowerBoundaryTerm_eq_blockMode_one]
  ring

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private lemma atkinson_shift1_upperMinusLowerBoundaryTerm_eq_blockMode_two_minus_one_clean
    (n : ℕ) :
    atkinsonWeightedResonantBlockMode (n + 1) 1 *
        atkinsonShiftedSinglePrimitive (n + 1) 1 1
      -
      atkinsonWeightedResonantBlockMode (n + 1) 0 *
        atkinsonShiftedSinglePrimitive (n + 1) 1 0
      =
    (-Complex.I) *
      ((((atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
        (Aristotle.StationaryPhaseMainMode.blockMode n 2 -
          Aristotle.StationaryPhaseMainMode.blockMode n 1)) := by
  rw [atkinson_shift1_upperBoundaryTerm_eq_blockMode_two_clean,
    atkinson_shift1_lowerBoundaryTerm_eq_blockMode_one_clean]
  ring

private theorem atkinson_shift1_upperBoundaryPrefix_bound_atomic_native
    (hmode21 :
      ∃ C21 > 0, ∃ N21 : ℕ, ∀ n : ℕ, N21 ≤ n →
        ‖Aristotle.StationaryPhaseMainMode.blockMode n 2 -
            Aristotle.StationaryPhaseMainMode.blockMode n 1‖
          ≤ C21 / ((n : ℝ) + 1)) :
    ∃ C_up > 0, ∀ K : ℕ,
      ‖∑ k ∈ Finset.range (K + 1),
          atkinsonWeightedResonantBlockMode (k + 2) 1 *
            atkinsonShiftedSinglePrimitive (k + 2) 1 1‖
        ≤ C_up * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
  obtain ⟨C_low, hC_low, hlower⟩ :=
    atkinson_shift1_lowerBoundaryPrefix_bound_atomic_of_j1 atkinson_inversePhaseCorePrefix_bound_j1
  obtain ⟨C21, hC21, N21, h21⟩ := hmode21
  let upperTerm : ℕ → ℂ := fun k =>
    atkinsonWeightedResonantBlockMode (k + 2) 1 *
      atkinsonShiftedSinglePrimitive (k + 2) 1 1
  let lowerTerm : ℕ → ℂ := fun k =>
    atkinsonWeightedResonantBlockMode (k + 2) 0 *
      atkinsonShiftedSinglePrimitive (k + 2) 1 0
  let diffTerm : ℕ → ℂ := fun k => upperTerm k - lowerTerm k
  let target : ℕ → ℝ := fun K => Real.sqrt (((K + 3 : ℕ) : ℝ) + 1)
  let Dhead : ℝ := 2 * (N21 : ℝ) * ((N21 : ℝ) + 2)
  let Dtail : ℝ := 4 * C21
  have htarget_ge_one (K : ℕ) : 1 ≤ target K := by
    have hK_nonneg : 0 ≤ (K : ℝ) := by positivity
    have hle : (1 : ℝ) ≤ (((K + 3 : ℕ) : ℝ) + 1) := by
      nlinarith
    simpa [target] using Real.sqrt_le_sqrt hle
  have htarget_mono (K : ℕ) : Real.sqrt (((K + 1 : ℕ) : ℝ) + 1) ≤ target K := by
    have hle : (((K + 1 : ℕ) : ℝ) + 1) ≤ (((K + 3 : ℕ) : ℝ) + 1) := by
      exact_mod_cast (by omega : (K + 1) + 1 ≤ (K + 3) + 1)
    simpa [target] using Real.sqrt_le_sqrt hle
  have hcoeff_nonneg (n : ℕ) :
      0 ≤ atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + 1) 1 := by
    exact div_nonneg (atkinsonModeWeight_nonneg n)
      (le_of_lt (atkinsonShiftedRelativePhase_pos (n + 1) 1 (by norm_num) (by omega)))
  have hhead_coeff_bound (k : ℕ) (hk : k < N21) :
      atkinsonModeWeight (k + 1) / atkinsonShiftedRelativePhase (k + 2) 1 ≤ (N21 : ℝ) + 2 := by
    have hphase_lower :
        1 / ((((k + 2 : ℕ) : ℝ) + 1)) ≤ atkinsonShiftedRelativePhase (k + 2) 1 := by
      simpa using atkinsonShiftedRelativePhase_lower (k + 2) 1 (by norm_num) (by omega)
    have hphase_inv :
        1 / atkinsonShiftedRelativePhase (k + 2) 1 ≤ (((k + 2 : ℕ) : ℝ) + 1) := by
      have hpos : 0 < 1 / ((((k + 2 : ℕ) : ℝ) + 1)) := by positivity
      have htmp :
          1 / atkinsonShiftedRelativePhase (k + 2) 1
            ≤ 1 / (1 / ((((k + 2 : ℕ) : ℝ) + 1))) := by
        exact one_div_le_one_div_of_le hpos hphase_lower
      have hconv : 1 / (1 / ((((k + 2 : ℕ) : ℝ) + 1))) = (((k + 2 : ℕ) : ℝ) + 1) := by
        field_simp [show ((((k + 2 : ℕ) : ℝ) + 1) : ℝ) ≠ 0 by positivity]
      simpa [hconv] using htmp
    have hphase_nonneg : 0 ≤ atkinsonShiftedRelativePhase (k + 2) 1 := by
      exact le_of_lt (atkinsonShiftedRelativePhase_pos (k + 2) 1 (by norm_num) (by omega))
    have hweight_bound :
        atkinsonModeWeight (k + 1) / atkinsonShiftedRelativePhase (k + 2) 1
          ≤ 1 / atkinsonShiftedRelativePhase (k + 2) 1 := by
      exact div_le_div_of_nonneg_right (atkinsonModeWeight_le_one (k + 1)) hphase_nonneg
    have hhead_nat :
        (((k + 2 : ℕ) : ℝ) + 1) ≤ (N21 : ℝ) + 2 := by
      exact_mod_cast (by omega : k + 3 ≤ N21 + 2)
    exact le_trans hweight_bound (le_trans hphase_inv hhead_nat)
  have hhead_bound (L : ℕ) (hL : L ≤ N21) :
      ‖∑ k ∈ Finset.range L, diffTerm k‖ ≤ Dhead := by
    calc
      ‖∑ k ∈ Finset.range L, diffTerm k‖
        ≤ ∑ k ∈ Finset.range L, ‖diffTerm k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range L, (2 * ((N21 : ℝ) + 2)) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            have hkL : k < L := Finset.mem_range.mp hk
            have hkN : k < N21 := lt_of_lt_of_le hkL hL
            calc
              ‖diffTerm k‖
                ≤ ‖upperTerm k‖ + ‖lowerTerm k‖ := by
                    unfold diffTerm upperTerm lowerTerm
                    exact norm_sub_le _ _
              _ =
                atkinsonModeWeight (k + 1) / atkinsonShiftedRelativePhase (k + 2) 1
                  +
                atkinsonModeWeight (k + 1) / atkinsonShiftedRelativePhase (k + 2) 1 := by
                    unfold upperTerm lowerTerm
                    rw [atkinsonUpperBoundaryTerm_norm (k + 1) 1 (by norm_num),
                      atkinsonLowerBoundaryTerm_norm (k + 1) 1 (by norm_num)]
              _ ≤ (N21 : ℝ) + 2 + ((N21 : ℝ) + 2) := by
                    nlinarith [hhead_coeff_bound k hkN]
              _ = 2 * ((N21 : ℝ) + 2) := by ring
      _ = (L : ℝ) * (2 * ((N21 : ℝ) + 2)) := by simp
      _ ≤ (N21 : ℝ) * (2 * ((N21 : ℝ) + 2)) := by
            have hcast : (L : ℝ) ≤ (N21 : ℝ) := by exact_mod_cast hL
            nlinarith
      _ = Dhead := by
            unfold Dhead
            ring
  have hshifted_weight_sum (L : ℕ) :
      ∑ k ∈ Finset.range L, atkinsonModeWeight (k + 1)
        ≤ 2 * Real.sqrt (((L : ℕ) : ℝ) + 1) := by
    calc
      ∑ k ∈ Finset.range L, atkinsonModeWeight (k + 1)
        ≤ atkinsonModeWeight 0 + ∑ k ∈ Finset.range L, atkinsonModeWeight (k + 1) := by
            have hnonneg0 : 0 ≤ atkinsonModeWeight 0 := atkinsonModeWeight_nonneg 0
            have hsum_nonneg :
                0 ≤ ∑ k ∈ Finset.range L, atkinsonModeWeight (k + 1) := by
              exact Finset.sum_nonneg (by intro k hk; exact atkinsonModeWeight_nonneg (k + 1))
            nlinarith
      _ = ∑ n ∈ Finset.range (L + 1), atkinsonModeWeight n := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (Finset.sum_range_succ' (fun n => atkinsonModeWeight n) L).symm
      _ ≤ 2 * Real.sqrt (L + 1) := by
            calc
              ∑ n ∈ Finset.range (L + 1), atkinsonModeWeight n
                  =
                ∑ n ∈ Finset.range (L + 1), ((n + 1 : ℝ) ^ (-1 / 2 : ℝ)) := by
                      refine Finset.sum_congr rfl ?_
                      intro n hn
                      rw [atkinsonModeWeight]
                      congr
                      norm_num
              _ ≤ 2 * Real.sqrt (L + 1) := by
                  simpa [div_eq_mul_inv, show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by ring_nf] using
                    Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le (L + 1)
  have htail_point (K k : ℕ) (hk : k ∈ Finset.Ico N21 (K + 1)) :
      ‖diffTerm k‖ ≤ 2 * C21 * atkinsonModeWeight (k + 1) := by
    have hkN : N21 ≤ k := (Finset.mem_Ico.mp hk).1
    have hmode : ‖Aristotle.StationaryPhaseMainMode.blockMode (k + 1) 2 -
        Aristotle.StationaryPhaseMainMode.blockMode (k + 1) 1‖
          ≤ C21 / (((k + 1 : ℕ) : ℝ) + 1) := by
      exact h21 (k + 1) (by omega)
    have hphase_pos : 0 < atkinsonShiftedRelativePhase (k + 2) 1 := by
      exact atkinsonShiftedRelativePhase_pos (k + 2) 1 (by norm_num) (by omega)
    have hphase_lower :
        1 / ((((k + 2 : ℕ) : ℝ) + 1)) ≤ atkinsonShiftedRelativePhase (k + 2) 1 := by
      simpa using atkinsonShiftedRelativePhase_lower (k + 2) 1 (by norm_num) (by omega)
    have hphase_inv :
        1 / atkinsonShiftedRelativePhase (k + 2) 1 ≤ (((k + 2 : ℕ) : ℝ) + 1) := by
      have hpos : 0 < 1 / ((((k + 2 : ℕ) : ℝ) + 1)) := by positivity
      have htmp :
          1 / atkinsonShiftedRelativePhase (k + 2) 1
            ≤ 1 / (1 / ((((k + 2 : ℕ) : ℝ) + 1))) := by
        exact one_div_le_one_div_of_le hpos hphase_lower
      have hconv : 1 / (1 / ((((k + 2 : ℕ) : ℝ) + 1))) = (((k + 2 : ℕ) : ℝ) + 1) := by
        field_simp [show ((((k + 2 : ℕ) : ℝ) + 1) : ℝ) ≠ 0 by positivity]
      simpa [hconv] using htmp
    have hcoeff_nonneg' : 0 ≤ atkinsonModeWeight (k + 1) / atkinsonShiftedRelativePhase (k + 2) 1 := by
      exact hcoeff_nonneg (k + 1)
    calc
      ‖diffTerm k‖
        =
      (atkinsonModeWeight (k + 1) / atkinsonShiftedRelativePhase (k + 2) 1) *
        ‖Aristotle.StationaryPhaseMainMode.blockMode (k + 1) 2 -
            Aristotle.StationaryPhaseMainMode.blockMode (k + 1) 1‖ := by
            unfold diffTerm
            rw [atkinson_shift1_upperMinusLowerBoundaryTerm_eq_blockMode_two_minus_one]
            rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hcoeff_nonneg']
            ring
      _ ≤ (atkinsonModeWeight (k + 1) / atkinsonShiftedRelativePhase (k + 2) 1) *
            (C21 / (((k + 1 : ℕ) : ℝ) + 1)) := by
              gcongr
      _ ≤ (atkinsonModeWeight (k + 1) * ((((k + 2 : ℕ) : ℝ) + 1))) *
            (C21 / (((k + 1 : ℕ) : ℝ) + 1)) := by
              have hcoeff_le :
                  atkinsonModeWeight (k + 1) / atkinsonShiftedRelativePhase (k + 2) 1
                    ≤ atkinsonModeWeight (k + 1) * ((((k + 2 : ℕ) : ℝ) + 1)) := by
                calc
                  atkinsonModeWeight (k + 1) / atkinsonShiftedRelativePhase (k + 2) 1
                      =
                    atkinsonModeWeight (k + 1) *
                      (1 / atkinsonShiftedRelativePhase (k + 2) 1) := by
                        ring
                  _ ≤ atkinsonModeWeight (k + 1) * ((((k + 2 : ℕ) : ℝ) + 1)) := by
                        exact mul_le_mul_of_nonneg_left hphase_inv
                          (atkinsonModeWeight_nonneg (k + 1))
              have htail_nonneg : 0 ≤ C21 / (((k + 1 : ℕ) : ℝ) + 1) := by positivity
              exact mul_le_mul_of_nonneg_right hcoeff_le htail_nonneg
      _ ≤ atkinsonModeWeight (k + 1) * (2 * C21) := by
            have hfrac :
                ((((k + 2 : ℕ) : ℝ) + 1) * (C21 / (((k + 1 : ℕ) : ℝ) + 1))) ≤ 2 * C21 := by
              have hkden : 0 < (((k + 1 : ℕ) : ℝ) + 1) := by positivity
              have hratio :
                  ((((k + 2 : ℕ) : ℝ) + 1) / (((k + 1 : ℕ) : ℝ) + 1)) ≤ 2 := by
                have hnum :
                    (((k + 2 : ℕ) : ℝ) + 1) ≤ 2 * ((((k + 1 : ℕ) : ℝ) + 1)) := by
                  exact_mod_cast (by omega : k + 3 ≤ 2 * (k + 2))
                calc
                  ((((k + 2 : ℕ) : ℝ) + 1) / (((k + 1 : ℕ) : ℝ) + 1))
                      = ((((k + 2 : ℕ) : ℝ) + 1)) * (1 / (((k + 1 : ℕ) : ℝ) + 1)) := by
                          ring
                  _ ≤ (2 * ((((k + 1 : ℕ) : ℝ) + 1))) * (1 / (((k + 1 : ℕ) : ℝ) + 1)) := by
                        gcongr
                  _ = 2 := by
                        field_simp [show (((k + 1 : ℕ) : ℝ) + 1) ≠ 0 by positivity]
              calc
                ((((k + 2 : ℕ) : ℝ) + 1) * (C21 / (((k + 1 : ℕ) : ℝ) + 1)))
                    = C21 * ((((k + 2 : ℕ) : ℝ) + 1) / (((k + 1 : ℕ) : ℝ) + 1)) := by
                        ring
                _ ≤ C21 * 2 := by
                      gcongr
                _ = 2 * C21 := by ring
            have hweight_nonneg : 0 ≤ atkinsonModeWeight (k + 1) := atkinsonModeWeight_nonneg (k + 1)
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_left hfrac hweight_nonneg
      _ = 2 * C21 * atkinsonModeWeight (k + 1) := by ring
  refine ⟨C_low + Dhead + Dtail, by positivity, ?_⟩
  intro K
  have hsplit :
      ∑ k ∈ Finset.range (K + 1), upperTerm k
        =
      (∑ k ∈ Finset.range (K + 1), lowerTerm k)
        + ∑ k ∈ Finset.range (K + 1), diffTerm k := by
    calc
      ∑ k ∈ Finset.range (K + 1), upperTerm k
          = ∑ k ∈ Finset.range (K + 1), (lowerTerm k + diffTerm k) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                unfold diffTerm
                ring
      _ = (∑ k ∈ Finset.range (K + 1), lowerTerm k)
            + ∑ k ∈ Finset.range (K + 1), diffTerm k := by
                rw [Finset.sum_add_distrib]
  have hdiff_bound :
      ‖∑ k ∈ Finset.range (K + 1), diffTerm k‖ ≤ (Dhead + Dtail) * target K := by
    by_cases hsmall : K + 1 ≤ N21
    · calc
        ‖∑ k ∈ Finset.range (K + 1), diffTerm k‖
          ≤ Dhead := hhead_bound (K + 1) hsmall
        _ ≤ (Dhead + Dtail) * target K := by
              have htarget_nonneg : 0 ≤ target K := by positivity
              have hbase_nonneg : 0 ≤ Dhead + Dtail := by
                unfold Dhead Dtail
                positivity
              nlinarith [htarget_ge_one K]
    · have hN21K : N21 ≤ K + 1 := le_of_not_ge hsmall
      have hhead :
          ‖∑ k ∈ Finset.range N21, diffTerm k‖ ≤ Dhead := hhead_bound N21 le_rfl
      have hweight_tail :
          ∑ k ∈ Finset.Ico N21 (K + 1), atkinsonModeWeight (k + 1)
            ≤ 2 * Real.sqrt ((K + 1) + 1) := by
        have hsplitW :
            (∑ k ∈ Finset.range (K + 1), atkinsonModeWeight (k + 1))
              =
            (∑ k ∈ Finset.range N21, atkinsonModeWeight (k + 1))
              + ∑ k ∈ Finset.Ico N21 (K + 1), atkinsonModeWeight (k + 1) := by
                simpa using (Finset.sum_range_add_sum_Ico (fun k => atkinsonModeWeight (k + 1)) hN21K).symm
        have hhead_nonneg :
            0 ≤ ∑ k ∈ Finset.range N21, atkinsonModeWeight (k + 1) := by
          exact Finset.sum_nonneg (by intro k hk; exact atkinsonModeWeight_nonneg (k + 1))
        calc
          ∑ k ∈ Finset.Ico N21 (K + 1), atkinsonModeWeight (k + 1)
            ≤ (∑ k ∈ Finset.range N21, atkinsonModeWeight (k + 1))
                + ∑ k ∈ Finset.Ico N21 (K + 1), atkinsonModeWeight (k + 1) := by
                  linarith
          _ = ∑ k ∈ Finset.range (K + 1), atkinsonModeWeight (k + 1) := by
                rw [← hsplitW]
          _ ≤ 2 * Real.sqrt ((K + 1) + 1) := by
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
                  hshifted_weight_sum (K + 1)
      have htail :
          ‖∑ k ∈ Finset.Ico N21 (K + 1), diffTerm k‖ ≤ Dtail * target K := by
        calc
          ‖∑ k ∈ Finset.Ico N21 (K + 1), diffTerm k‖
            ≤ ∑ k ∈ Finset.Ico N21 (K + 1), ‖diffTerm k‖ := norm_sum_le _ _
          _ ≤ ∑ k ∈ Finset.Ico N21 (K + 1), (2 * C21 * atkinsonModeWeight (k + 1)) := by
                refine Finset.sum_le_sum ?_
                intro k hk
                exact htail_point K k hk
          _ = (2 * C21) * ∑ k ∈ Finset.Ico N21 (K + 1), atkinsonModeWeight (k + 1) := by
                rw [← Finset.mul_sum]
          _ ≤ (2 * C21) * (2 * Real.sqrt ((K + 1) + 1)) := by
                gcongr
          _ = Dtail * Real.sqrt ((K + 1) + 1) := by
                unfold Dtail
                ring
          _ ≤ Dtail * target K := by
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
                  (mul_le_mul_of_nonneg_left (htarget_mono K) (by
                    unfold Dtail
                    positivity))
      have hsplitD :
          ∑ k ∈ Finset.range (K + 1), diffTerm k
            =
          (∑ k ∈ Finset.range N21, diffTerm k)
            + ∑ k ∈ Finset.Ico N21 (K + 1), diffTerm k := by
              simpa using (Finset.sum_range_add_sum_Ico diffTerm hN21K).symm
      calc
        ‖∑ k ∈ Finset.range (K + 1), diffTerm k‖
          = ‖(∑ k ∈ Finset.range N21, diffTerm k)
                + ∑ k ∈ Finset.Ico N21 (K + 1), diffTerm k‖ := by
                  rw [hsplitD]
        _ ≤ ‖∑ k ∈ Finset.range N21, diffTerm k‖
              + ‖∑ k ∈ Finset.Ico N21 (K + 1), diffTerm k‖ := norm_add_le _ _
        _ ≤ Dhead + Dtail * target K := by
              nlinarith [hhead, htail]
        _ ≤ (Dhead + Dtail) * target K := by
              have hDhead_nonneg : 0 ≤ Dhead := by
                unfold Dhead
                positivity
              have hDtail_nonneg : 0 ≤ Dtail := by
                unfold Dtail
                positivity
              have hDhead_le : Dhead ≤ Dhead * target K := by
                simpa using mul_le_mul_of_nonneg_left (htarget_ge_one K) hDhead_nonneg
              nlinarith
  calc
    ‖∑ k ∈ Finset.range (K + 1),
        atkinsonWeightedResonantBlockMode (k + 2) 1 *
          atkinsonShiftedSinglePrimitive (k + 2) 1 1‖
      = ‖∑ k ∈ Finset.range (K + 1), upperTerm k‖ := by
          rfl
    _ = ‖(∑ k ∈ Finset.range (K + 1), lowerTerm k)
            + ∑ k ∈ Finset.range (K + 1), diffTerm k‖ := by
          rw [hsplit]
    _ ≤ ‖∑ k ∈ Finset.range (K + 1), lowerTerm k‖
          + ‖∑ k ∈ Finset.range (K + 1), diffTerm k‖ := norm_add_le _ _
    _ ≤ C_low * target K + (Dhead + Dtail) * target K := by
          have hlow_raw := hlower K
          nlinarith [hlow_raw]
    _ = (C_low + Dhead + Dtail) * target K := by ring

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private theorem atkinson_shift1_upperBoundaryPrefix_bound_atomic_native_clean
    (hmode21 :
      ∃ C21 > 0, ∃ N21 : ℕ, ∀ n : ℕ, N21 ≤ n →
        ‖Aristotle.StationaryPhaseMainMode.blockMode n 2 -
            Aristotle.StationaryPhaseMainMode.blockMode n 1‖
          ≤ C21 / ((n : ℝ) + 1)) :
    ∃ C_up > 0, ∀ K : ℕ,
      ‖∑ k ∈ Finset.range (K + 1),
          atkinsonWeightedResonantBlockMode (k + 2) 1 *
            atkinsonShiftedSinglePrimitive (k + 2) 1 1‖
        ≤ C_up * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
  obtain ⟨C_low, hC_low, hlower⟩ :=
    atkinson_shift1_lowerBoundaryPrefix_bound_atomic_of_j1_clean atkinson_inversePhaseCorePrefix_bound_j1
  obtain ⟨C21, hC21, N21, h21⟩ := hmode21
  let upperTerm : ℕ → ℂ := fun k =>
    atkinsonWeightedResonantBlockMode (k + 2) 1 *
      atkinsonShiftedSinglePrimitive (k + 2) 1 1
  let lowerTerm : ℕ → ℂ := fun k =>
    atkinsonWeightedResonantBlockMode (k + 2) 0 *
      atkinsonShiftedSinglePrimitive (k + 2) 1 0
  let diffTerm : ℕ → ℂ := fun k => upperTerm k - lowerTerm k
  let target : ℕ → ℝ := fun K => Real.sqrt (((K + 3 : ℕ) : ℝ) + 1)
  let Dhead : ℝ := 2 * (N21 : ℝ) * ((N21 : ℝ) + 2)
  let Dtail : ℝ := 4 * C21
  have htarget_ge_one (K : ℕ) : 1 ≤ target K := by
    have hK_nonneg : 0 ≤ (K : ℝ) := by positivity
    have hle : (1 : ℝ) ≤ (((K + 3 : ℕ) : ℝ) + 1) := by
      nlinarith
    simpa [target] using Real.sqrt_le_sqrt hle
  have htarget_mono (K : ℕ) : Real.sqrt (((K + 1 : ℕ) : ℝ) + 1) ≤ target K := by
    have hle : (((K + 1 : ℕ) : ℝ) + 1) ≤ (((K + 3 : ℕ) : ℝ) + 1) := by
      exact_mod_cast (by omega : (K + 1) + 1 ≤ (K + 3) + 1)
    simpa [target] using Real.sqrt_le_sqrt hle
  have hcoeff_nonneg (n : ℕ) :
      0 ≤ atkinsonModeWeight n / atkinsonShiftedRelativePhase (n + 1) 1 := by
    exact div_nonneg (atkinsonModeWeight_nonneg n)
      (le_of_lt (atkinsonShiftedRelativePhase_pos (n + 1) 1 (by norm_num) (by omega)))
  have hhead_coeff_bound (k : ℕ) (hk : k < N21) :
      atkinsonModeWeight (k + 1) / atkinsonShiftedRelativePhase (k + 2) 1 ≤ (N21 : ℝ) + 2 := by
    have hphase_lower :
        1 / ((((k + 2 : ℕ) : ℝ) + 1)) ≤ atkinsonShiftedRelativePhase (k + 2) 1 := by
      simpa using atkinsonShiftedRelativePhase_lower (k + 2) 1 (by norm_num) (by omega)
    have hphase_inv :
        1 / atkinsonShiftedRelativePhase (k + 2) 1 ≤ (((k + 2 : ℕ) : ℝ) + 1) := by
      have hpos : 0 < 1 / ((((k + 2 : ℕ) : ℝ) + 1)) := by positivity
      have htmp :
          1 / atkinsonShiftedRelativePhase (k + 2) 1
            ≤ 1 / (1 / ((((k + 2 : ℕ) : ℝ) + 1))) := by
        exact one_div_le_one_div_of_le hpos hphase_lower
      have hconv : 1 / (1 / ((((k + 2 : ℕ) : ℝ) + 1))) = (((k + 2 : ℕ) : ℝ) + 1) := by
        field_simp [show ((((k + 2 : ℕ) : ℝ) + 1) : ℝ) ≠ 0 by positivity]
      simpa [hconv] using htmp
    have hphase_nonneg : 0 ≤ atkinsonShiftedRelativePhase (k + 2) 1 := by
      exact le_of_lt (atkinsonShiftedRelativePhase_pos (k + 2) 1 (by norm_num) (by omega))
    have hweight_bound :
        atkinsonModeWeight (k + 1) / atkinsonShiftedRelativePhase (k + 2) 1
          ≤ 1 / atkinsonShiftedRelativePhase (k + 2) 1 := by
      exact div_le_div_of_nonneg_right (atkinsonModeWeight_le_one (k + 1)) hphase_nonneg
    have hhead_nat :
        (((k + 2 : ℕ) : ℝ) + 1) ≤ (N21 : ℝ) + 2 := by
      exact_mod_cast (by omega : k + 3 ≤ N21 + 2)
    exact le_trans hweight_bound (le_trans hphase_inv hhead_nat)
  have hhead_bound (L : ℕ) (hL : L ≤ N21) :
      ‖∑ k ∈ Finset.range L, diffTerm k‖ ≤ Dhead := by
    calc
      ‖∑ k ∈ Finset.range L, diffTerm k‖
        ≤ ∑ k ∈ Finset.range L, ‖diffTerm k‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range L, (2 * ((N21 : ℝ) + 2)) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            have hkL : k < L := Finset.mem_range.mp hk
            have hkN : k < N21 := lt_of_lt_of_le hkL hL
            calc
              ‖diffTerm k‖
                ≤ ‖upperTerm k‖ + ‖lowerTerm k‖ := by
                    unfold diffTerm upperTerm lowerTerm
                    exact norm_sub_le _ _
              _ =
                atkinsonModeWeight (k + 1) / atkinsonShiftedRelativePhase (k + 2) 1
                  +
                atkinsonModeWeight (k + 1) / atkinsonShiftedRelativePhase (k + 2) 1 := by
                    unfold upperTerm lowerTerm
                    rw [atkinsonUpperBoundaryTerm_norm_clean (k + 1) 1 (by norm_num),
                      atkinsonLowerBoundaryTerm_norm (k + 1) 1 (by norm_num)]
              _ ≤ (N21 : ℝ) + 2 + ((N21 : ℝ) + 2) := by
                    nlinarith [hhead_coeff_bound k hkN]
              _ = 2 * ((N21 : ℝ) + 2) := by ring
      _ = (L : ℝ) * (2 * ((N21 : ℝ) + 2)) := by simp
      _ ≤ (N21 : ℝ) * (2 * ((N21 : ℝ) + 2)) := by
            have hcast : (L : ℝ) ≤ (N21 : ℝ) := by exact_mod_cast hL
            nlinarith
      _ = Dhead := by
            unfold Dhead
            ring
  have hshifted_weight_sum (L : ℕ) :
      ∑ k ∈ Finset.range L, atkinsonModeWeight (k + 1)
        ≤ 2 * Real.sqrt (((L : ℕ) : ℝ) + 1) := by
    calc
      ∑ k ∈ Finset.range L, atkinsonModeWeight (k + 1)
        ≤ atkinsonModeWeight 0 + ∑ k ∈ Finset.range L, atkinsonModeWeight (k + 1) := by
            have hnonneg0 : 0 ≤ atkinsonModeWeight 0 := atkinsonModeWeight_nonneg 0
            have hsum_nonneg :
                0 ≤ ∑ k ∈ Finset.range L, atkinsonModeWeight (k + 1) := by
              exact Finset.sum_nonneg (by intro k hk; exact atkinsonModeWeight_nonneg (k + 1))
            nlinarith
      _ = ∑ n ∈ Finset.range (L + 1), atkinsonModeWeight n := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (Finset.sum_range_succ' (fun n => atkinsonModeWeight n) L).symm
      _ ≤ 2 * Real.sqrt (L + 1) := by
            calc
              ∑ n ∈ Finset.range (L + 1), atkinsonModeWeight n
                  =
                ∑ n ∈ Finset.range (L + 1), ((n + 1 : ℝ) ^ (-1 / 2 : ℝ)) := by
                      refine Finset.sum_congr rfl ?_
                      intro n hn
                      rw [atkinsonModeWeight]
                      congr
                      norm_num
              _ ≤ 2 * Real.sqrt (L + 1) := by
                  simpa [div_eq_mul_inv, show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by ring_nf] using
                    Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le (L + 1)
  have htail_point (K k : ℕ) (hk : k ∈ Finset.Ico N21 (K + 1)) :
      ‖diffTerm k‖ ≤ 2 * C21 * atkinsonModeWeight (k + 1) := by
    have hkN : N21 ≤ k := (Finset.mem_Ico.mp hk).1
    have hmode : ‖Aristotle.StationaryPhaseMainMode.blockMode (k + 1) 2 -
        Aristotle.StationaryPhaseMainMode.blockMode (k + 1) 1‖
          ≤ C21 / (((k + 1 : ℕ) : ℝ) + 1) := by
      exact h21 (k + 1) (by omega)
    have hphase_pos : 0 < atkinsonShiftedRelativePhase (k + 2) 1 := by
      exact atkinsonShiftedRelativePhase_pos (k + 2) 1 (by norm_num) (by omega)
    have hphase_lower :
        1 / ((((k + 2 : ℕ) : ℝ) + 1)) ≤ atkinsonShiftedRelativePhase (k + 2) 1 := by
      simpa using atkinsonShiftedRelativePhase_lower (k + 2) 1 (by norm_num) (by omega)
    have hphase_inv :
        1 / atkinsonShiftedRelativePhase (k + 2) 1 ≤ (((k + 2 : ℕ) : ℝ) + 1) := by
      have hpos : 0 < 1 / ((((k + 2 : ℕ) : ℝ) + 1)) := by positivity
      have htmp :
          1 / atkinsonShiftedRelativePhase (k + 2) 1
            ≤ 1 / (1 / ((((k + 2 : ℕ) : ℝ) + 1))) := by
        exact one_div_le_one_div_of_le hpos hphase_lower
      have hconv : 1 / (1 / ((((k + 2 : ℕ) : ℝ) + 1))) = (((k + 2 : ℕ) : ℝ) + 1) := by
        field_simp [show ((((k + 2 : ℕ) : ℝ) + 1) : ℝ) ≠ 0 by positivity]
      simpa [hconv] using htmp
    have hcoeff_nonneg' : 0 ≤ atkinsonModeWeight (k + 1) / atkinsonShiftedRelativePhase (k + 2) 1 := by
      exact hcoeff_nonneg (k + 1)
    calc
      ‖diffTerm k‖
        =
      (atkinsonModeWeight (k + 1) / atkinsonShiftedRelativePhase (k + 2) 1) *
        ‖Aristotle.StationaryPhaseMainMode.blockMode (k + 1) 2 -
            Aristotle.StationaryPhaseMainMode.blockMode (k + 1) 1‖ := by
            unfold diffTerm
            rw [atkinson_shift1_upperMinusLowerBoundaryTerm_eq_blockMode_two_minus_one_clean]
            rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hcoeff_nonneg']
            ring
      _ ≤ (atkinsonModeWeight (k + 1) / atkinsonShiftedRelativePhase (k + 2) 1) *
            (C21 / (((k + 1 : ℕ) : ℝ) + 1)) := by
              gcongr
      _ ≤ (atkinsonModeWeight (k + 1) * ((((k + 2 : ℕ) : ℝ) + 1))) *
            (C21 / (((k + 1 : ℕ) : ℝ) + 1)) := by
              have hcoeff_le :
                  atkinsonModeWeight (k + 1) / atkinsonShiftedRelativePhase (k + 2) 1
                    ≤ atkinsonModeWeight (k + 1) * ((((k + 2 : ℕ) : ℝ) + 1)) := by
                calc
                  atkinsonModeWeight (k + 1) / atkinsonShiftedRelativePhase (k + 2) 1
                      =
                    atkinsonModeWeight (k + 1) *
                      (1 / atkinsonShiftedRelativePhase (k + 2) 1) := by
                        ring
                  _ ≤ atkinsonModeWeight (k + 1) * ((((k + 2 : ℕ) : ℝ) + 1)) := by
                        exact mul_le_mul_of_nonneg_left hphase_inv
                          (atkinsonModeWeight_nonneg (k + 1))
              have htail_nonneg : 0 ≤ C21 / (((k + 1 : ℕ) : ℝ) + 1) := by positivity
              exact mul_le_mul_of_nonneg_right hcoeff_le htail_nonneg
      _ ≤ atkinsonModeWeight (k + 1) * (2 * C21) := by
            have hfrac :
                ((((k + 2 : ℕ) : ℝ) + 1) * (C21 / (((k + 1 : ℕ) : ℝ) + 1))) ≤ 2 * C21 := by
              have hkden : 0 < (((k + 1 : ℕ) : ℝ) + 1) := by positivity
              have hratio :
                  ((((k + 2 : ℕ) : ℝ) + 1) / (((k + 1 : ℕ) : ℝ) + 1)) ≤ 2 := by
                have hnum :
                    (((k + 2 : ℕ) : ℝ) + 1) ≤ 2 * ((((k + 1 : ℕ) : ℝ) + 1)) := by
                  exact_mod_cast (by omega : k + 3 ≤ 2 * (k + 2))
                calc
                  ((((k + 2 : ℕ) : ℝ) + 1) / (((k + 1 : ℕ) : ℝ) + 1))
                      = ((((k + 2 : ℕ) : ℝ) + 1)) * (1 / (((k + 1 : ℕ) : ℝ) + 1)) := by
                          ring
                  _ ≤ (2 * ((((k + 1 : ℕ) : ℝ) + 1))) * (1 / (((k + 1 : ℕ) : ℝ) + 1)) := by
                        gcongr
                  _ = 2 := by
                        field_simp [show (((k + 1 : ℕ) : ℝ) + 1) ≠ 0 by positivity]
              calc
                ((((k + 2 : ℕ) : ℝ) + 1) * (C21 / (((k + 1 : ℕ) : ℝ) + 1)))
                    = C21 * ((((k + 2 : ℕ) : ℝ) + 1) / (((k + 1 : ℕ) : ℝ) + 1)) := by
                        ring
                _ ≤ C21 * 2 := by
                      gcongr
                _ = 2 * C21 := by ring
            have hweight_nonneg : 0 ≤ atkinsonModeWeight (k + 1) := atkinsonModeWeight_nonneg (k + 1)
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_left hfrac hweight_nonneg
      _ = 2 * C21 * atkinsonModeWeight (k + 1) := by ring
  refine ⟨C_low + Dhead + Dtail, by positivity, ?_⟩
  intro K
  have hdiff_bound :
      ‖∑ k ∈ Finset.range (K + 1), diffTerm k‖ ≤ (Dhead + Dtail) * target K := by
    by_cases hsmall : K + 1 ≤ N21
    · calc
        ‖∑ k ∈ Finset.range (K + 1), diffTerm k‖
          ≤ Dhead := hhead_bound (K + 1) hsmall
        _ ≤ (Dhead + Dtail) * target K := by
              have htarget_nonneg : 0 ≤ target K := by positivity
              have hbase_nonneg : 0 ≤ Dhead + Dtail := by
                unfold Dhead Dtail
                positivity
              nlinarith [htarget_ge_one K]
    · have hN21K : N21 ≤ K + 1 := le_of_not_ge hsmall
      have hhead :
          ‖∑ k ∈ Finset.range N21, diffTerm k‖ ≤ Dhead := hhead_bound N21 le_rfl
      have hweight_tail :
          ∑ k ∈ Finset.Ico N21 (K + 1), atkinsonModeWeight (k + 1)
            ≤ 2 * Real.sqrt ((K + 1) + 1) := by
        have hsplitW :
            (∑ k ∈ Finset.range (K + 1), atkinsonModeWeight (k + 1))
              =
            (∑ k ∈ Finset.range N21, atkinsonModeWeight (k + 1))
              + ∑ k ∈ Finset.Ico N21 (K + 1), atkinsonModeWeight (k + 1) := by
                simpa using (Finset.sum_range_add_sum_Ico (fun k => atkinsonModeWeight (k + 1)) hN21K).symm
        have hhead_nonneg :
            0 ≤ ∑ k ∈ Finset.range N21, atkinsonModeWeight (k + 1) := by
          exact Finset.sum_nonneg (by intro k hk; exact atkinsonModeWeight_nonneg (k + 1))
        calc
          ∑ k ∈ Finset.Ico N21 (K + 1), atkinsonModeWeight (k + 1)
            ≤ (∑ k ∈ Finset.range N21, atkinsonModeWeight (k + 1))
                + ∑ k ∈ Finset.Ico N21 (K + 1), atkinsonModeWeight (k + 1) := by
                  linarith
          _ = ∑ k ∈ Finset.range (K + 1), atkinsonModeWeight (k + 1) := by
                rw [← hsplitW]
          _ ≤ 2 * Real.sqrt ((K + 1) + 1) := by
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
                  hshifted_weight_sum (K + 1)
      have htail :
          ‖∑ k ∈ Finset.Ico N21 (K + 1), diffTerm k‖ ≤ Dtail * target K := by
        calc
          ‖∑ k ∈ Finset.Ico N21 (K + 1), diffTerm k‖
            ≤ ∑ k ∈ Finset.Ico N21 (K + 1), ‖diffTerm k‖ := norm_sum_le _ _
          _ ≤ ∑ k ∈ Finset.Ico N21 (K + 1), (2 * C21 * atkinsonModeWeight (k + 1)) := by
                refine Finset.sum_le_sum ?_
                intro k hk
                exact htail_point K k hk
          _ = (2 * C21) * ∑ k ∈ Finset.Ico N21 (K + 1), atkinsonModeWeight (k + 1) := by
                rw [← Finset.mul_sum]
          _ ≤ (2 * C21) * (2 * Real.sqrt ((K + 1) + 1)) := by
                gcongr
          _ = Dtail * Real.sqrt ((K + 1) + 1) := by
                unfold Dtail
                ring
          _ ≤ Dtail * target K := by
                simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
                  (mul_le_mul_of_nonneg_left (htarget_mono K) (by
                    unfold Dtail
                    positivity))
      have hsplitD :
          ∑ k ∈ Finset.range (K + 1), diffTerm k
            =
          (∑ k ∈ Finset.range N21, diffTerm k)
            + ∑ k ∈ Finset.Ico N21 (K + 1), diffTerm k := by
              simpa using (Finset.sum_range_add_sum_Ico diffTerm hN21K).symm
      calc
        ‖∑ k ∈ Finset.range (K + 1), diffTerm k‖
          = ‖(∑ k ∈ Finset.range N21, diffTerm k)
                + ∑ k ∈ Finset.Ico N21 (K + 1), diffTerm k‖ := by
                  rw [hsplitD]
        _ ≤ ‖∑ k ∈ Finset.range N21, diffTerm k‖
              + ‖∑ k ∈ Finset.Ico N21 (K + 1), diffTerm k‖ := norm_add_le _ _
        _ ≤ Dhead + Dtail * target K := by
              nlinarith [hhead, htail]
        _ ≤ (Dhead + Dtail) * target K := by
              have hDhead_nonneg : 0 ≤ Dhead := by
                unfold Dhead
                positivity
              have hDtail_nonneg : 0 ≤ Dtail := by
                unfold Dtail
                positivity
              have hDhead_le : Dhead ≤ Dhead * target K := by
                simpa using mul_le_mul_of_nonneg_left (htarget_ge_one K) hDhead_nonneg
              nlinarith
  calc
    ‖∑ k ∈ Finset.range (K + 1),
        atkinsonWeightedResonantBlockMode (k + 2) 1 *
          atkinsonShiftedSinglePrimitive (k + 2) 1 1‖
      = ‖∑ k ∈ Finset.range (K + 1), upperTerm k‖ := by
          rfl
    _ = ‖(∑ k ∈ Finset.range (K + 1), lowerTerm k)
            + ∑ k ∈ Finset.range (K + 1), diffTerm k‖ := by
          have hsplit :
              ∑ k ∈ Finset.range (K + 1), upperTerm k
                =
              (∑ k ∈ Finset.range (K + 1), lowerTerm k)
                + ∑ k ∈ Finset.range (K + 1), diffTerm k := by
                  calc
                    ∑ k ∈ Finset.range (K + 1), upperTerm k
                        = ∑ k ∈ Finset.range (K + 1), (lowerTerm k + diffTerm k) := by
                              refine Finset.sum_congr rfl ?_
                              intro k hk
                              unfold diffTerm
                              ring
                    _ = (∑ k ∈ Finset.range (K + 1), lowerTerm k)
                          + ∑ k ∈ Finset.range (K + 1), diffTerm k := by
                              rw [Finset.sum_add_distrib]
          rw [hsplit]
    _ ≤ ‖∑ k ∈ Finset.range (K + 1), lowerTerm k‖
          + ‖∑ k ∈ Finset.range (K + 1), diffTerm k‖ := norm_add_le _ _
    _ ≤ C_low * target K + (Dhead + Dtail) * target K := by
          have hlow_raw := hlower K
          nlinarith [hlow_raw]
    _ = (C_low + Dhead + Dtail) * target K := by ring

private theorem
    atkinson_shift1_upperBoundaryPrefix_bound_atomic_of_blockOmega_linear_model_upto_two_eventually
    (hOmega2 :
      ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
        ∀ p ∈ Icc (0 : ℝ) 2,
          |Aristotle.StationaryPhaseMainMode.blockOmega n p - 4 * Real.pi * p|
            ≤ C / ((n : ℝ) + 1)) :
    ∃ C_up > 0, ∀ K : ℕ,
      ‖∑ k ∈ Finset.range (K + 1),
          atkinsonWeightedResonantBlockMode (k + 2) 1 *
            atkinsonShiftedSinglePrimitive (k + 2) 1 1‖
        ≤ C_up * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
  exact
    atkinson_shift1_upperBoundaryPrefix_bound_atomic_native
      (Aristotle.StationaryPhaseMainMode.blockMode_two_minus_one_asymptotic_of_blockOmega_linear_model_upto_two_eventually
        hOmega2)

private theorem
    atkinson_shift1_boundaryPrefix_bound_atomic_local_of_blockOmega_linear_model_upto_two_eventually_and_j1
    (hOmega2 :
      ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
        ∀ p ∈ Icc (0 : ℝ) 2,
          |Aristotle.StationaryPhaseMainMode.blockOmega n p - 4 * Real.pi * p|
            ≤ C / ((n : ℝ) + 1))
    (hj1 :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) :
    ∃ C_bdry > 0, ∀ K : ℕ,
      ‖∑ k ∈ Finset.range (K + 1),
          atkinsonResonantShiftedBoundaryTerm (k + 1) 1‖
        ≤ C_bdry * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
  obtain ⟨C_up, hC_up, hupper⟩ :=
    atkinson_shift1_upperBoundaryPrefix_bound_atomic_of_blockOmega_linear_model_upto_two_eventually
      hOmega2
  obtain ⟨C_low, hC_low, hlower⟩ :=
    atkinson_shift1_lowerBoundaryPrefix_bound_atomic_of_j1 hj1
  refine ⟨C_up + C_low, by positivity, ?_⟩
  intro K
  let su : ℂ :=
    ∑ k ∈ Finset.range (K + 1),
      atkinsonWeightedResonantBlockMode (k + 2) 1 *
        atkinsonShiftedSinglePrimitive (k + 2) 1 1
  let sl : ℂ :=
    ∑ k ∈ Finset.range (K + 1),
      atkinsonWeightedResonantBlockMode (k + 2) 0 *
        atkinsonShiftedSinglePrimitive (k + 2) 1 0
  have hsplit :
      ∑ k ∈ Finset.range (K + 1), atkinsonResonantShiftedBoundaryTerm (k + 1) 1
        = su - sl := by
    calc
      ∑ k ∈ Finset.range (K + 1), atkinsonResonantShiftedBoundaryTerm (k + 1) 1
          =
        ∑ k ∈ Finset.range (K + 1),
          (atkinsonWeightedResonantBlockMode (k + 2) 1 *
              atkinsonShiftedSinglePrimitive (k + 2) 1 1
            - atkinsonWeightedResonantBlockMode (k + 2) 0 *
              atkinsonShiftedSinglePrimitive (k + 2) 1 0) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp [atkinsonResonantShiftedBoundaryTerm, Nat.add_assoc, add_left_comm, add_comm]
      _ = su - sl := by
            simp [su, sl, Finset.sum_sub_distrib]
  calc
    ‖∑ k ∈ Finset.range (K + 1), atkinsonResonantShiftedBoundaryTerm (k + 1) 1‖
      = ‖su - sl‖ := by
          rw [hsplit]
    _ ≤ ‖su‖ + ‖sl‖ := by
          exact norm_sub_le _ _
    _ ≤ C_up * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1)
          + C_low * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
            exact add_le_add (hupper K) (hlower K)
    _ = (C_up + C_low) * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
          ring

private theorem atkinson_shift1_boundaryPrefix_bound_atomic_local_of_upper_and_j1
    (hupper :
      ∃ C_up > 0, ∀ K : ℕ,
        ‖∑ k ∈ Finset.range (K + 1),
            atkinsonWeightedResonantBlockMode (k + 2) 1 *
              atkinsonShiftedSinglePrimitive (k + 2) 1 1‖
          ≤ C_up * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1))
    (hj1 :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) :
    ∃ C_bdry > 0, ∀ K : ℕ,
      ‖∑ k ∈ Finset.range (K + 1),
          atkinsonResonantShiftedBoundaryTerm (k + 1) 1‖
        ≤ C_bdry * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
  obtain ⟨C_up, hC_up, hupper⟩ := hupper
  obtain ⟨C_low, hC_low, hlower⟩ :=
    atkinson_shift1_lowerBoundaryPrefix_bound_atomic_of_j1 hj1
  refine ⟨C_up + C_low, by positivity, ?_⟩
  intro K
  let su : ℂ :=
    ∑ k ∈ Finset.range (K + 1),
      atkinsonWeightedResonantBlockMode (k + 2) 1 *
        atkinsonShiftedSinglePrimitive (k + 2) 1 1
  let sl : ℂ :=
    ∑ k ∈ Finset.range (K + 1),
      atkinsonWeightedResonantBlockMode (k + 2) 0 *
        atkinsonShiftedSinglePrimitive (k + 2) 1 0
  have hsplit :
      ∑ k ∈ Finset.range (K + 1), atkinsonResonantShiftedBoundaryTerm (k + 1) 1
        = su - sl := by
    calc
      ∑ k ∈ Finset.range (K + 1), atkinsonResonantShiftedBoundaryTerm (k + 1) 1
          =
        ∑ k ∈ Finset.range (K + 1),
          (atkinsonWeightedResonantBlockMode (k + 2) 1 *
              atkinsonShiftedSinglePrimitive (k + 2) 1 1
            - atkinsonWeightedResonantBlockMode (k + 2) 0 *
              atkinsonShiftedSinglePrimitive (k + 2) 1 0) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp [atkinsonResonantShiftedBoundaryTerm, Nat.add_assoc, add_left_comm, add_comm]
      _ = su - sl := by
            simp [su, sl, Finset.sum_sub_distrib]
  calc
    ‖∑ k ∈ Finset.range (K + 1), atkinsonResonantShiftedBoundaryTerm (k + 1) 1‖
      = ‖su - sl‖ := by
          rw [hsplit]
    _ ≤ ‖su‖ + ‖sl‖ := by
          exact norm_sub_le _ _
    _ ≤ C_up * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1)
          + C_low * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
            exact add_le_add (hupper K) (hlower K)
    _ = (C_up + C_low) * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
          ring

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private theorem atkinson_shift1_boundaryPrefix_bound_atomic_local_of_upper_and_j1_clean
    (hupper :
      ∃ C_up > 0, ∀ K : ℕ,
        ‖∑ k ∈ Finset.range (K + 1),
            atkinsonWeightedResonantBlockMode (k + 2) 1 *
              atkinsonShiftedSinglePrimitive (k + 2) 1 1‖
          ≤ C_up * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1))
    (hj1 :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) :
    ∃ C_bdry > 0, ∀ K : ℕ,
      ‖∑ k ∈ Finset.range (K + 1),
          atkinsonResonantShiftedBoundaryTerm (k + 1) 1‖
        ≤ C_bdry * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
  obtain ⟨C_up, hC_up, hupper⟩ := hupper
  obtain ⟨C_low, hC_low, hlower⟩ :=
    atkinson_shift1_lowerBoundaryPrefix_bound_atomic_of_j1_clean hj1
  refine ⟨C_up + C_low, by positivity, ?_⟩
  intro K
  let su : ℂ :=
    ∑ k ∈ Finset.range (K + 1),
      atkinsonWeightedResonantBlockMode (k + 2) 1 *
        atkinsonShiftedSinglePrimitive (k + 2) 1 1
  let sl : ℂ :=
    ∑ k ∈ Finset.range (K + 1),
      atkinsonWeightedResonantBlockMode (k + 2) 0 *
        atkinsonShiftedSinglePrimitive (k + 2) 1 0
  have hsplit :
      ∑ k ∈ Finset.range (K + 1), atkinsonResonantShiftedBoundaryTerm (k + 1) 1
        = su - sl := by
    calc
      ∑ k ∈ Finset.range (K + 1), atkinsonResonantShiftedBoundaryTerm (k + 1) 1
          =
        ∑ k ∈ Finset.range (K + 1),
          (atkinsonWeightedResonantBlockMode (k + 2) 1 *
              atkinsonShiftedSinglePrimitive (k + 2) 1 1
            - atkinsonWeightedResonantBlockMode (k + 2) 0 *
              atkinsonShiftedSinglePrimitive (k + 2) 1 0) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp [atkinsonResonantShiftedBoundaryTerm, Nat.add_assoc, add_left_comm, add_comm]
      _ = su - sl := by
            simp [su, sl, Finset.sum_sub_distrib]
  calc
    ‖∑ k ∈ Finset.range (K + 1), atkinsonResonantShiftedBoundaryTerm (k + 1) 1‖
      = ‖su - sl‖ := by
          rw [hsplit]
    _ ≤ ‖su‖ + ‖sl‖ := by
          exact norm_sub_le _ _
    _ ≤ C_up * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1)
          + C_low * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
            exact add_le_add (hupper K) (hlower K)
    _ = (C_up + C_low) * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
          ring

private theorem atkinson_j2_kernelWeighted_boundaryGap_bound_local_of_upper_and_j1
    (hupper :
      ∃ C_up > 0, ∀ K : ℕ,
        ‖∑ k ∈ Finset.range (K + 1),
            atkinsonWeightedResonantBlockMode (k + 2) 1 *
              atkinsonShiftedSinglePrimitive (k + 2) 1 1‖
          ≤ C_up * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1))
    (hj1 :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) :
    ∃ C_gap > 0, ∀ M : ℕ,
      ‖∑ n ∈ Finset.range (M + 1),
          ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm n 1)‖
        ≤ C_gap * (Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (2 : ℝ)) := by
  obtain ⟨C_bdry, hC_bdry, hbdry⟩ :=
    atkinson_shift1_boundaryPrefix_bound_atomic_local_of_upper_and_j1 hupper hj1
  refine ⟨4 * C_bdry + 4 / Real.log 2, by positivity, ?_⟩
  intro M
  let gapFn : ℕ → ℂ := fun n =>
    ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
      atkinsonResonantShiftedBoundaryTerm n 1)
  let baseFn : ℕ → ℂ := fun k => atkinsonResonantShiftedBoundaryTerm (k + 1) 1
  let b : ℕ → ℝ := fun k => atkinsonLowerBoundaryShiftKernel (k + 1) 2 1
  let target : ℝ := Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (2 : ℝ)
  have hsplit :
      ∑ n ∈ Finset.range (M + 1), gapFn n
        =
      gapFn 0 + ∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k) := by
    calc
      ∑ n ∈ Finset.range (M + 1), gapFn n
          =
        (∑ n ∈ Finset.range 1, gapFn n) + ∑ n ∈ Finset.Ico 1 (M + 1), gapFn n := by
            simpa using
              (Finset.sum_range_add_sum_Ico gapFn (show 1 ≤ M + 1 by omega)).symm
      _ = gapFn 0 + ∑ n ∈ Finset.Ico 1 (M + 1), gapFn n := by
            simp [gapFn]
      _ = gapFn 0 + ∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k) := by
            congr 1
            rw [Finset.sum_Ico_eq_sum_range]
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp [gapFn, baseFn, b, add_comm, add_left_comm]
  have hhead_kernel : atkinsonLowerBoundaryShiftKernel 0 2 1 ≤ 1 := by
    have hstep := atkinsonLowerBoundaryShiftKernel_step_mul 0 1 1 (by norm_num) le_rfl
    have hself : atkinsonLowerBoundaryShiftKernel 0 1 1 = 1 := by
      simpa using atkinsonLowerBoundaryShiftKernel_self 0 1 (by norm_num)
    calc
      atkinsonLowerBoundaryShiftKernel 0 2 1
          = (1 / atkinsonUpperBoundaryStepCoeff 0 1) * 1 := by
              simpa [hself] using hstep
      _ ≤ 1 * 1 := by
            gcongr
            simpa using
              (one_div_le_one_div_of_le
                (by positivity : (0 : ℝ) < 1)
                (atkinsonUpperBoundaryStepCoeff_one_le 0 1 (by norm_num)))
      _ = 1 := by ring
  have hhead_term :
      ‖gapFn 0‖ ≤ (4 / Real.log 2) * target := by
    have hraw :
        ‖atkinsonResonantShiftedBoundaryTerm 0 1‖
          ≤ (2 / Real.log 2) * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ)) := by
      simpa using atkinsonBoundary_jMinusOne_le 1 (by norm_num) M
    have hsqrt_le :
        Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ) ≤ 2 * target := by
      have hle :
          (((M + 1 : ℕ) : ℝ) + 1) ≤ (((M + 2 : ℕ) : ℝ) + 1) := by
        exact_mod_cast (by omega : (M + 1) + 1 ≤ (M + 2) + 1)
      calc
        Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ)
            ≤ Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (1 : ℝ) := by
                exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hle)
                  (by positivity : (0 : ℝ) ≤ (1 : ℝ))
        _ = 2 * target := by
              unfold target
              ring
    calc
      ‖gapFn 0‖
          =
        atkinsonLowerBoundaryShiftKernel 0 2 1 * ‖atkinsonResonantShiftedBoundaryTerm 0 1‖ := by
            simp [gapFn, Real.norm_eq_abs, abs_of_nonneg
              (atkinsonLowerBoundaryShiftKernel_nonneg 0 2 1 (by norm_num) (by norm_num))]
      _ ≤ 1 * ‖atkinsonResonantShiftedBoundaryTerm 0 1‖ := by
            gcongr
      _ ≤ 1 * ((2 / Real.log 2) * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) := by
            gcongr
      _ ≤ 1 * ((2 / Real.log 2) * (2 * target)) := by
            gcongr
      _ = (4 / Real.log 2) * target := by ring
  have htail_term :
      ‖∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k)‖ ≤ 4 * C_bdry * target := by
    by_cases hM0 : M = 0
    · have hzero : ∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k) = 0 := by
        simp [hM0]
      have hnonneg : 0 ≤ 4 * C_bdry * target := by positivity
      simpa [hzero] using hnonneg
    · obtain ⟨n0, hn0 : M = n0 + 1⟩ := Nat.exists_eq_succ_of_ne_zero hM0
      let C0 : ℝ := 2 * C_bdry * target
      let aRe : ℕ → ℝ := fun k => (baseFn k).re
      let aIm : ℕ → ℝ := fun k => (baseFn k).im
      have hpartial_bound (K : ℕ) (hK : K ≤ n0) :
          ‖∑ k ∈ Finset.range (K + 1), baseFn k‖ ≤ C0 := by
        have hraw :
            ‖∑ k ∈ Finset.range (K + 1), baseFn k‖
              ≤ C_bdry * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
            simpa [baseFn, Nat.add_assoc, add_left_comm, add_comm] using hbdry K
        have htarget_K :
            Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) ≤ 2 * target := by
          have hle_nat : (K + 3) + 1 ≤ (M + 2) + 1 := by
            rw [hn0]
            omega
          have hle :
              ((((K + 3 : ℕ) : ℝ) + 1)) ≤ ((((M + 2 : ℕ) : ℝ) + 1)) := by
            exact_mod_cast hle_nat
          calc
            Real.sqrt (((K + 3 : ℕ) : ℝ) + 1)
                ≤ Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) := by
                    exact Real.sqrt_le_sqrt hle
            _ = 2 * target := by
                  unfold target
                  ring
        calc
          ‖∑ k ∈ Finset.range (K + 1), baseFn k‖
              ≤ C_bdry * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := hraw
          _ ≤ C_bdry * (2 * target) := by
                exact mul_le_mul_of_nonneg_left htarget_K (le_of_lt hC_bdry)
          _ = C0 := by
                unfold C0
                ring
      have hpartial_re : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aRe m| ≤ C0 := by
        intro k hk
        have hbound := hpartial_bound k hk
        calc
          |∑ m ∈ Finset.range (k + 1), aRe m|
              = |(∑ m ∈ Finset.range (k + 1), baseFn m).re| := by
                  simp [aRe]
          _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_re_le_norm _
          _ ≤ C0 := hbound
      have hpartial_im : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aIm m| ≤ C0 := by
        intro k hk
        have hbound := hpartial_bound k hk
        calc
          |∑ m ∈ Finset.range (k + 1), aIm m|
              = |(∑ m ∈ Finset.range (k + 1), baseFn m).im| := by
                  simp [aIm]
          _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_im_le_norm _
          _ ≤ C0 := hbound
      have hb_nonneg : ∀ k ≤ n0, 0 ≤ b k := by
        intro k hk
        simpa [b, add_comm, add_left_comm] using
          atkinsonLowerBoundaryShiftKernel_nonneg (k + 1) 2 1 (by norm_num) (by norm_num)
      have hb_anti : ∀ k < n0, b (k + 1) ≤ b k := by
        intro k hk
        simpa [b, add_comm, add_left_comm] using
          (atkinsonLowerBoundaryShiftKernel_antitone 2 1 (by norm_num) (by norm_num)
            (by omega : k + 1 ≤ k + 2))
      have hb_head : b 0 ≤ 1 := by
        have hstep := atkinsonLowerBoundaryShiftKernel_step_mul 1 1 1 (by norm_num) le_rfl
        have hself : atkinsonLowerBoundaryShiftKernel 1 1 1 = 1 := by
          simpa using atkinsonLowerBoundaryShiftKernel_self 1 1 (by norm_num)
        calc
          b 0 = (1 / atkinsonUpperBoundaryStepCoeff 1 1) * 1 := by
                  simp [b, hstep, hself]
          _ ≤ 1 * 1 := by
                gcongr
                simpa using
                  (one_div_le_one_div_of_le
                    (by positivity : (0 : ℝ) < 1)
                    (atkinsonUpperBoundaryStepCoeff_one_le 1 1 (by norm_num)))
          _ = 1 := by ring
      have hsum_re :
          (∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re
            =
          ∑ k ∈ Finset.range (n0 + 1), aRe k * b k := by
        simp [aRe, b, baseFn, mul_comm]
      have hsum_im :
          (∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im
            =
          ∑ k ∈ Finset.range (n0 + 1), aIm k * b k := by
        simp [aIm, b, baseFn, mul_comm]
      have hre :
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re| ≤ C0 := by
        have habel :=
          AbelSummation.abel_summation_bound aRe b n0 C0 hpartial_re hb_nonneg hb_anti
        calc
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
              = |∑ k ∈ Finset.range (n0 + 1), aRe k * b k| := by
                  rw [hsum_re]
          _ ≤ C0 * b 0 := habel
          _ ≤ C0 * 1 := by
                gcongr
          _ = C0 := by ring
      have him :
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| ≤ C0 := by
        have habel :=
          AbelSummation.abel_summation_bound aIm b n0 C0 hpartial_im hb_nonneg hb_anti
        calc
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im|
              = |∑ k ∈ Finset.range (n0 + 1), aIm k * b k| := by
                  rw [hsum_im]
          _ ≤ C0 * b 0 := habel
          _ ≤ C0 * 1 := by
                gcongr
          _ = C0 := by ring
      have hnorm :
          ‖∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k)‖ ≤ 2 * C0 := by
        calc
          ‖∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k)‖
              = ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖ := by
                  rw [hn0]
          _ ≤
            |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
              +
            |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| := by
                exact Complex.norm_le_abs_re_add_abs_im _
          _ ≤ C0 + C0 := add_le_add hre him
          _ = 2 * C0 := by ring
      calc
        ‖∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k)‖
            ≤ 2 * C0 := hnorm
        _ = 4 * C_bdry * target := by
              unfold C0
              ring
  calc
    ‖∑ n ∈ Finset.range (M + 1),
        ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
          atkinsonResonantShiftedBoundaryTerm n 1)‖
      = ‖gapFn 0 + ∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k)‖ := by
          rw [show
            (∑ n ∈ Finset.range (M + 1),
              ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
                atkinsonResonantShiftedBoundaryTerm n 1))
              = ∑ n ∈ Finset.range (M + 1), gapFn n by rfl]
          rw [hsplit]
    _ ≤ ‖gapFn 0‖ + ‖∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k)‖ := by
          exact norm_add_le _ _
    _ ≤ (4 / Real.log 2) * target + 4 * C_bdry * target := by
          exact add_le_add hhead_term htail_term
    _ = (4 * C_bdry + 4 / Real.log 2) * target := by
          ring

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private theorem atkinson_j2_kernelWeighted_boundaryGap_bound_local_of_upper_and_j1_clean
    (hupper :
      ∃ C_up > 0, ∀ K : ℕ,
        ‖∑ k ∈ Finset.range (K + 1),
            atkinsonWeightedResonantBlockMode (k + 2) 1 *
              atkinsonShiftedSinglePrimitive (k + 2) 1 1‖
          ≤ C_up * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1))
    (hj1 :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) :
    ∃ C_gap > 0, ∀ M : ℕ,
      ‖∑ n ∈ Finset.range (M + 1),
          ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm n 1)‖
        ≤ C_gap * (Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (2 : ℝ)) := by
  obtain ⟨C_bdry, hC_bdry, hbdry⟩ :=
    atkinson_shift1_boundaryPrefix_bound_atomic_local_of_upper_and_j1_clean hupper hj1
  refine ⟨4 * C_bdry + 4 / Real.log 2, by positivity, ?_⟩
  intro M
  let gapFn : ℕ → ℂ := fun n =>
    ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
      atkinsonResonantShiftedBoundaryTerm n 1)
  let baseFn : ℕ → ℂ := fun k => atkinsonResonantShiftedBoundaryTerm (k + 1) 1
  let b : ℕ → ℝ := fun k => atkinsonLowerBoundaryShiftKernel (k + 1) 2 1
  let target : ℝ := Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (2 : ℝ)
  have hsplit :
      ∑ n ∈ Finset.range (M + 1), gapFn n
        =
      gapFn 0 + ∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k) := by
    calc
      ∑ n ∈ Finset.range (M + 1), gapFn n
          =
        (∑ n ∈ Finset.range 1, gapFn n) + ∑ n ∈ Finset.Ico 1 (M + 1), gapFn n := by
            simpa using
              (Finset.sum_range_add_sum_Ico gapFn (show 1 ≤ M + 1 by omega)).symm
      _ = gapFn 0 + ∑ n ∈ Finset.Ico 1 (M + 1), gapFn n := by
            simp [gapFn]
      _ = gapFn 0 + ∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k) := by
            congr 1
            rw [Finset.sum_Ico_eq_sum_range]
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp [gapFn, baseFn, b, add_comm, add_left_comm]
  have hhead_kernel : atkinsonLowerBoundaryShiftKernel 0 2 1 ≤ 1 := by
    have hstep := atkinsonLowerBoundaryShiftKernel_step_mul 0 1 1 (by norm_num) le_rfl
    have hself : atkinsonLowerBoundaryShiftKernel 0 1 1 = 1 := by
      simpa using atkinsonLowerBoundaryShiftKernel_self 0 1 (by norm_num)
    calc
      atkinsonLowerBoundaryShiftKernel 0 2 1
          = (1 / atkinsonUpperBoundaryStepCoeff 0 1) * 1 := by
              simpa [hself] using hstep
      _ ≤ 1 * 1 := by
            gcongr
            simpa using
              (one_div_le_one_div_of_le
                (by positivity : (0 : ℝ) < 1)
                (atkinsonUpperBoundaryStepCoeff_one_le 0 1 (by norm_num)))
      _ = 1 := by ring
  have hhead_term :
      ‖gapFn 0‖ ≤ (4 / Real.log 2) * target := by
    have hraw :
        ‖atkinsonResonantShiftedBoundaryTerm 0 1‖
          ≤ (2 / Real.log 2) * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ)) := by
      simpa using atkinsonBoundary_jMinusOne_le_clean 1 (by norm_num) M
    have hsqrt_le :
        Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ) ≤ 2 * target := by
      have hle :
          (((M + 1 : ℕ) : ℝ) + 1) ≤ (((M + 2 : ℕ) : ℝ) + 1) := by
        exact_mod_cast (by omega : (M + 1) + 1 ≤ (M + 2) + 1)
      calc
        Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ)
            ≤ Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (1 : ℝ) := by
                exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hle)
                  (by positivity : (0 : ℝ) ≤ (1 : ℝ))
        _ = 2 * target := by
              unfold target
              ring
    calc
      ‖gapFn 0‖
          =
        atkinsonLowerBoundaryShiftKernel 0 2 1 * ‖atkinsonResonantShiftedBoundaryTerm 0 1‖ := by
            simp [gapFn, Real.norm_eq_abs, abs_of_nonneg
              (atkinsonLowerBoundaryShiftKernel_nonneg 0 2 1 (by norm_num) (by norm_num))]
      _ ≤ 1 * ‖atkinsonResonantShiftedBoundaryTerm 0 1‖ := by
            gcongr
      _ ≤ 1 * ((2 / Real.log 2) * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) := by
            gcongr
      _ ≤ 1 * ((2 / Real.log 2) * (2 * target)) := by
            gcongr
      _ = (4 / Real.log 2) * target := by ring
  have htail_term :
      ‖∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k)‖ ≤ 4 * C_bdry * target := by
    by_cases hM0 : M = 0
    · have hzero : ∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k) = 0 := by
        simp [hM0]
      have hnonneg : 0 ≤ 4 * C_bdry * target := by positivity
      simpa [hzero] using hnonneg
    · obtain ⟨n0, hn0 : M = n0 + 1⟩ := Nat.exists_eq_succ_of_ne_zero hM0
      let C0 : ℝ := 2 * C_bdry * target
      let aRe : ℕ → ℝ := fun k => (baseFn k).re
      let aIm : ℕ → ℝ := fun k => (baseFn k).im
      have hpartial_bound (K : ℕ) (hK : K ≤ n0) :
          ‖∑ k ∈ Finset.range (K + 1), baseFn k‖ ≤ C0 := by
        have hraw :
            ‖∑ k ∈ Finset.range (K + 1), baseFn k‖
              ≤ C_bdry * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := by
            simpa [baseFn, Nat.add_assoc, add_left_comm, add_comm] using hbdry K
        have htarget_K :
            Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) ≤ 2 * target := by
          have hle_nat : (K + 3) + 1 ≤ (M + 2) + 1 := by
            rw [hn0]
            omega
          have hle :
              ((((K + 3 : ℕ) : ℝ) + 1)) ≤ ((((M + 2 : ℕ) : ℝ) + 1)) := by
            exact_mod_cast hle_nat
          calc
            Real.sqrt (((K + 3 : ℕ) : ℝ) + 1)
                ≤ Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) := by
                    exact Real.sqrt_le_sqrt hle
            _ = 2 * target := by
                  unfold target
                  ring
        calc
          ‖∑ k ∈ Finset.range (K + 1), baseFn k‖
              ≤ C_bdry * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1) := hraw
          _ ≤ C_bdry * (2 * target) := by
                exact mul_le_mul_of_nonneg_left htarget_K (le_of_lt hC_bdry)
          _ = C0 := by
                unfold C0
                ring
      have hpartial_re : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aRe m| ≤ C0 := by
        intro k hk
        have hbound := hpartial_bound k hk
        calc
          |∑ m ∈ Finset.range (k + 1), aRe m|
              = |(∑ m ∈ Finset.range (k + 1), baseFn m).re| := by
                  simp [aRe]
          _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_re_le_norm _
          _ ≤ C0 := hbound
      have hpartial_im : ∀ k ≤ n0, |∑ m ∈ Finset.range (k + 1), aIm m| ≤ C0 := by
        intro k hk
        have hbound := hpartial_bound k hk
        calc
          |∑ m ∈ Finset.range (k + 1), aIm m|
              = |(∑ m ∈ Finset.range (k + 1), baseFn m).im| := by
                  simp [aIm]
          _ ≤ ‖∑ m ∈ Finset.range (k + 1), baseFn m‖ := Complex.abs_im_le_norm _
          _ ≤ C0 := hbound
      have hb_nonneg : ∀ k ≤ n0, 0 ≤ b k := by
        intro k hk
        simpa [b, add_comm, add_left_comm] using
          atkinsonLowerBoundaryShiftKernel_nonneg (k + 1) 2 1 (by norm_num) (by norm_num)
      have hb_anti : ∀ k < n0, b (k + 1) ≤ b k := by
        intro k hk
        simpa [b, add_comm, add_left_comm] using
          (atkinsonLowerBoundaryShiftKernel_antitone 2 1 (by norm_num) (by norm_num)
            (by omega : k + 1 ≤ k + 2))
      have hb_head : b 0 ≤ 1 := by
        have hstep := atkinsonLowerBoundaryShiftKernel_step_mul 1 1 1 (by norm_num) le_rfl
        have hself : atkinsonLowerBoundaryShiftKernel 1 1 1 = 1 := by
          simpa using atkinsonLowerBoundaryShiftKernel_self 1 1 (by norm_num)
        calc
          b 0 = (1 / atkinsonUpperBoundaryStepCoeff 1 1) * 1 := by
                  simp [b, hstep, hself]
          _ ≤ 1 * 1 := by
                gcongr
                simpa using
                  (one_div_le_one_div_of_le
                    (by positivity : (0 : ℝ) < 1)
                    (atkinsonUpperBoundaryStepCoeff_one_le 1 1 (by norm_num)))
          _ = 1 := by ring
      have hsum_re :
          (∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re
            =
          ∑ k ∈ Finset.range (n0 + 1), aRe k * b k := by
        simp [aRe, b, baseFn, mul_comm]
      have hsum_im :
          (∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im
            =
          ∑ k ∈ Finset.range (n0 + 1), aIm k * b k := by
        simp [aIm, b, baseFn, mul_comm]
      have hre :
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re| ≤ C0 := by
        have habel :=
          AbelSummation.abel_summation_bound aRe b n0 C0 hpartial_re hb_nonneg hb_anti
        calc
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
              = |∑ k ∈ Finset.range (n0 + 1), aRe k * b k| := by
                  rw [hsum_re]
          _ ≤ C0 * b 0 := habel
          _ ≤ C0 * 1 := by
                gcongr
          _ = C0 := by ring
      have him :
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| ≤ C0 := by
        have habel :=
          AbelSummation.abel_summation_bound aIm b n0 C0 hpartial_im hb_nonneg hb_anti
        calc
          |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im|
              = |∑ k ∈ Finset.range (n0 + 1), aIm k * b k| := by
                  rw [hsum_im]
          _ ≤ C0 * b 0 := habel
          _ ≤ C0 * 1 := by
                gcongr
          _ = C0 := by ring
      have hnorm :
          ‖∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k)‖ ≤ 2 * C0 := by
        calc
          ‖∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k)‖
              = ‖∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)‖ := by
                  rw [hn0]
          _ ≤
            |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).re|
              +
            |(∑ k ∈ Finset.range (n0 + 1), ((((b k : ℝ) : ℂ)) * baseFn k)).im| := by
                exact Complex.norm_le_abs_re_add_abs_im _
          _ ≤ C0 + C0 := add_le_add hre him
          _ = 2 * C0 := by ring
      calc
        ‖∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k)‖
            ≤ 2 * C0 := hnorm
        _ = 4 * C_bdry * target := by
              unfold C0
              ring
  calc
    ‖∑ n ∈ Finset.range (M + 1),
        ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
          atkinsonResonantShiftedBoundaryTerm n 1)‖
      = ‖gapFn 0 + ∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k)‖ := by
          rw [show
            (∑ n ∈ Finset.range (M + 1),
              ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
                atkinsonResonantShiftedBoundaryTerm n 1))
              = ∑ n ∈ Finset.range (M + 1), gapFn n by rfl]
          rw [hsplit]
    _ ≤ ‖gapFn 0‖ + ‖∑ k ∈ Finset.range M, ((((b k : ℝ) : ℂ)) * baseFn k)‖ := by
          exact norm_add_le _ _
    _ ≤ (4 / Real.log 2) * target + 4 * C_bdry * target := by
          exact add_le_add hhead_term htail_term
    _ = (4 * C_bdry + 4 / Real.log 2) * target := by
          ring

private theorem
    atkinson_j2_kernelWeighted_boundaryGap_bound_local_of_blockOmega_linear_model_upto_two_eventually_and_j1
    (hOmega2 :
      ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
        ∀ p ∈ Icc (0 : ℝ) 2,
          |Aristotle.StationaryPhaseMainMode.blockOmega n p - 4 * Real.pi * p|
            ≤ C / ((n : ℝ) + 1))
    (hj1 :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) :
    ∃ C_gap > 0, ∀ M : ℕ,
      ‖∑ n ∈ Finset.range (M + 1),
          ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
            atkinsonResonantShiftedBoundaryTerm n 1)‖
        ≤ C_gap * (Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (2 : ℝ)) := by
  exact
    atkinson_j2_kernelWeighted_boundaryGap_bound_local_of_upper_and_j1
      (atkinson_shift1_upperBoundaryPrefix_bound_atomic_of_blockOmega_linear_model_upto_two_eventually
        hOmega2)
      hj1

private theorem atkinson_inversePhaseCorePrefix_bound_j2_of_upper_and_j1
    (hupper :
      ∃ C_up > 0, ∀ K : ℕ,
        ‖∑ k ∈ Finset.range (K + 1),
            atkinsonWeightedResonantBlockMode (k + 2) 1 *
              atkinsonShiftedSinglePrimitive (k + 2) 1 1‖
          ≤ C_up * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1))
    (hj1 :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) :
    ∃ C2 > 0, ∀ M : ℕ,
      ‖∑ n ∈ Finset.range (M + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + 2) 2 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n 2)‖
        ≤ C2 * (Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (2 : ℝ)) := by
  obtain ⟨C_head, hC_head, hhead⟩ :=
    atkinson_j2_kernelWeighted_j1_headCore_bound_of_j1 hj1
  obtain ⟨C_gap, hC_gap, hgap⟩ :=
    atkinson_j2_kernelWeighted_boundaryGap_bound_local_of_upper_and_j1 hupper hj1
  refine ⟨C_head + C_gap, by positivity, ?_⟩
  intro M
  let headFn : ℕ → ℂ := fun n =>
    ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
      ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n 1))
  let gapFn : ℕ → ℂ := fun n =>
    ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
      atkinsonResonantShiftedBoundaryTerm n 1)
  let target : ℝ := Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (2 : ℝ)
  have hdecomp :
      ∑ n ∈ Finset.range (M + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + 2) 2 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n 2)
        =
      (∑ n ∈ Finset.range (M + 1), headFn n)
        +
      ∑ n ∈ Finset.range (M + 1), gapFn n := by
    calc
      ∑ n ∈ Finset.range (M + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + 2) 2 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n 2)
          =
        ∑ n ∈ Finset.range (M + 1), (headFn n + gapFn n) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simpa [headFn, gapFn] using
              (atkinsonLowerBoundary_shiftBoundary_decomposition n 2 (by norm_num))
      _ =
        (∑ n ∈ Finset.range (M + 1), headFn n)
          +
        ∑ n ∈ Finset.range (M + 1), gapFn n := by
            rw [Finset.sum_add_distrib]
  calc
    ‖∑ n ∈ Finset.range (M + 1),
        ((((1 / atkinsonShiftedRelativePhase (n + 2) 2 : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n 2)‖
      = ‖(∑ n ∈ Finset.range (M + 1), headFn n)
            + ∑ n ∈ Finset.range (M + 1), gapFn n‖ := by
          rw [hdecomp]
    _ ≤ ‖∑ n ∈ Finset.range (M + 1), headFn n‖
          + ‖∑ n ∈ Finset.range (M + 1), gapFn n‖ := by
            exact norm_add_le _ _
    _ ≤ C_head * target + C_gap * target := by
          exact add_le_add (hhead M) (hgap M)
    _ = (C_head + C_gap) * target := by
          ring

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private theorem atkinson_inversePhaseCorePrefix_bound_j2_of_upper_and_j1_clean
    (hupper :
      ∃ C_up > 0, ∀ K : ℕ,
        ‖∑ k ∈ Finset.range (K + 1),
            atkinsonWeightedResonantBlockMode (k + 2) 1 *
              atkinsonShiftedSinglePrimitive (k + 2) 1 1‖
          ≤ C_up * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1))
    (hj1 :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) :
    ∃ C2 > 0, ∀ M : ℕ,
      ‖∑ n ∈ Finset.range (M + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + 2) 2 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n 2)‖
        ≤ C2 * (Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (2 : ℝ)) := by
  obtain ⟨C_head, hC_head, hhead⟩ :=
    atkinson_j2_kernelWeighted_j1_headCore_bound_of_j1_clean hj1
  obtain ⟨C_gap, hC_gap, hgap⟩ :=
    atkinson_j2_kernelWeighted_boundaryGap_bound_local_of_upper_and_j1_clean hupper hj1
  refine ⟨C_head + C_gap, by positivity, ?_⟩
  intro M
  let headFn : ℕ → ℂ := fun n =>
    ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
      ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
        atkinsonShiftedSingleBoundaryCore n 1))
  let gapFn : ℕ → ℂ := fun n =>
    ((((atkinsonLowerBoundaryShiftKernel n 2 1 : ℝ) : ℂ)) *
      atkinsonResonantShiftedBoundaryTerm n 1)
  let target : ℝ := Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (2 : ℝ)
  have hdecomp :
      ∑ n ∈ Finset.range (M + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + 2) 2 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n 2)
        =
      (∑ n ∈ Finset.range (M + 1), headFn n)
        +
      ∑ n ∈ Finset.range (M + 1), gapFn n := by
    calc
      ∑ n ∈ Finset.range (M + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + 2) 2 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n 2)
          =
        ∑ n ∈ Finset.range (M + 1), (headFn n + gapFn n) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simpa [headFn, gapFn] using
              (atkinsonLowerBoundary_shiftBoundary_decomposition n 2 (by norm_num))
      _ =
        (∑ n ∈ Finset.range (M + 1), headFn n)
          +
        ∑ n ∈ Finset.range (M + 1), gapFn n := by
            rw [Finset.sum_add_distrib]
  calc
    ‖∑ n ∈ Finset.range (M + 1),
        ((((1 / atkinsonShiftedRelativePhase (n + 2) 2 : ℝ) : ℂ)) *
          atkinsonShiftedSingleBoundaryCore n 2)‖
      = ‖(∑ n ∈ Finset.range (M + 1), headFn n)
            + ∑ n ∈ Finset.range (M + 1), gapFn n‖ := by
          rw [hdecomp]
    _ ≤ ‖∑ n ∈ Finset.range (M + 1), headFn n‖
          + ‖∑ n ∈ Finset.range (M + 1), gapFn n‖ := by
            exact norm_add_le _ _
    _ ≤ C_head * target + C_gap * target := by
          exact add_le_add (hhead M) (hgap M)
    _ = (C_head + C_gap) * target := by
          ring

private theorem
    atkinson_inversePhaseCorePrefix_bound_j2_of_blockOmega_linear_model_upto_two_eventually_and_j1
    (hOmega2 :
      ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
        ∀ p ∈ Icc (0 : ℝ) 2,
          |Aristotle.StationaryPhaseMainMode.blockOmega n p - 4 * Real.pi * p|
            ≤ C / ((n : ℝ) + 1))
    (hj1 :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) :
    ∃ C2 > 0, ∀ M : ℕ,
      ‖∑ n ∈ Finset.range (M + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + 2) 2 : ℝ) : ℂ)) *
            atkinsonShiftedSingleBoundaryCore n 2)‖
        ≤ C2 * (Real.sqrt (((M + 2 : ℕ) : ℝ) + 1) / (2 : ℝ)) := by
  exact
    atkinson_inversePhaseCorePrefix_bound_j2_of_upper_and_j1
      (atkinson_shift1_upperBoundaryPrefix_bound_atomic_of_blockOmega_linear_model_upto_two_eventually
        hOmega2)
      hj1

private theorem atkinson_smallShiftPrefixBound_of_native_j1_and_upper
    (hupper :
      ∃ C_up > 0, ∀ K : ℕ,
        ‖∑ k ∈ Finset.range (K + 1),
            atkinsonWeightedResonantBlockMode (k + 2) 1 *
              atkinsonShiftedSinglePrimitive (k + 2) 1 1‖
          ≤ C_up * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1))
    (hj1 :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) :
    AtkinsonSmallShiftPrefixBoundHyp := by
  exact atkinson_smallShiftPrefixBound_of_native_j1_j2 hj1
    (atkinson_inversePhaseCorePrefix_bound_j2_of_upper_and_j1 hupper hj1)

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private theorem atkinson_smallShiftPrefixBound_of_native_j1_and_upper_clean
    (hupper :
      ∃ C_up > 0, ∀ K : ℕ,
        ‖∑ k ∈ Finset.range (K + 1),
            atkinsonWeightedResonantBlockMode (k + 2) 1 *
              atkinsonShiftedSinglePrimitive (k + 2) 1 1‖
          ≤ C_up * Real.sqrt (((K + 3 : ℕ) : ℝ) + 1))
    (hj1 :
      ∃ C1 > 0, ∀ M : ℕ,
        ‖∑ n ∈ Finset.range (M + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + 1) 1 : ℝ) : ℂ)) *
              atkinsonShiftedSingleBoundaryCore n 1)‖
          ≤ C1 * (Real.sqrt (((M + 1 : ℕ) : ℝ) + 1) / (1 : ℝ))) :
    AtkinsonSmallShiftPrefixBoundHyp := by
  exact atkinson_smallShiftPrefixBound_of_native_j1_j2_clean hj1
    (atkinson_inversePhaseCorePrefix_bound_j2_of_upper_and_j1_clean hupper hj1)

private theorem
    atkinson_smallShiftPrefixBound_of_native_j1_and_blockOmega_linear_model_upto_two_eventually
    (hOmega2 :
      ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
        ∀ p ∈ Icc (0 : ℝ) 2,
          |Aristotle.StationaryPhaseMainMode.blockOmega n p - 4 * Real.pi * p|
            ≤ C / ((n : ℝ) + 1)) :
    AtkinsonSmallShiftPrefixBoundHyp := by
  exact
    atkinson_smallShiftPrefixBound_of_native_j1_and_upper
      (atkinson_shift1_upperBoundaryPrefix_bound_atomic_of_blockOmega_linear_model_upto_two_eventually
        hOmega2)
      atkinson_inversePhaseCorePrefix_bound_j1

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
private theorem
    atkinson_smallShiftPrefixBound_of_native_j1_and_blockOmega_linear_model_upto_two_eventually_clean :
    AtkinsonSmallShiftPrefixBoundHyp := by
  exact
    atkinson_smallShiftPrefixBound_of_native_j1_and_upper_clean
      (atkinson_shift1_upperBoundaryPrefix_bound_atomic_native_clean
        (Aristotle.StationaryPhaseMainMode.blockMode_two_minus_one_asymptotic_of_blockOmega_linear_model_upto_two_eventually
          Aristotle.StationaryPhaseMainMode.blockOmega_linear_model_upto_two_eventually))
      atkinson_inversePhaseCorePrefix_bound_j1

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
  [AtkinsonSmallShiftPrefixBoundHyp] [AtkinsonLargeShiftPrefixBoundHyp] in
instance : AtkinsonSmallShiftPrefixBoundHyp :=
  atkinson_smallShiftPrefixBound_of_native_j1_and_blockOmega_linear_model_upto_two_eventually_clean

/-- Smaller second-leaf package: the bare shifted correction prefix itself.
This sits strictly below `AtkinsonShiftedInversePhaseCellPrefixBoundHyp` and
is enough to recover it once the already-proved boundary prefix is added back
through the IBP identity. -/
class AtkinsonShiftedCorrectionPrefixBoundHyp : Prop where
  bound :
    ∃ C > 0, ∀ j : ℕ, 1 ≤ j → ∀ m : ℕ,
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
          atkinsonResonantShiftedCorrectionTerm n j‖
        ≤ C * Real.log (↑j + 1) * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j)

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
private theorem
    atkinson_large_modes_complete_resonant_packet_row_correction_sum_bound_atomic_of_shifted_correction_prefix
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0)‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_corr, hC_corr, hcorr⟩ := AtkinsonShiftedCorrectionPrefixBoundHyp.bound
  refine ⟨2 * C_corr, by positivity, ?_⟩
  intro j hj M
  by_cases hMj : M ≤ j
  · have hzero :
        ∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnlt : n < j := lt_of_lt_of_le (Finset.mem_range.mp hn) hMj
      simp [hnlt.not_ge]
    have hnonneg :
        0 ≤ (2 * C_corr) * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
      apply mul_nonneg
      · apply mul_nonneg; positivity
        exact Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)
      · positivity
    simpa [hzero] using hnonneg
  · have hJltM : j < M := lt_of_not_ge hMj
    have hMpos : 0 < M := by omega
    have hsum_if :
        ∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0)
          =
        ∑ n ∈ Finset.Ico j M, atkinsonResonantShiftedCorrectionTerm n j := by
      calc
        ∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0)
            =
          ∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0) := rfl
        _ =
          (∑ n ∈ Finset.range j,
              (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0))
            +
          ∑ n ∈ Finset.Ico j M,
            (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0) := by
              simpa using
                (Finset.sum_range_add_sum_Ico
                  (fun n => if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0)
                  (le_of_lt hJltM)).symm
        _ =
          ∑ n ∈ Finset.Ico j M,
            (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0) := by
              have hprefix_zero :
                  ∑ n ∈ Finset.range j,
                      (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0) = 0 := by
                apply Finset.sum_eq_zero
                intro n hn
                simp [(Finset.mem_range.mp hn).not_ge]
              rw [hprefix_zero, zero_add]
        _ =
          ∑ n ∈ Finset.Ico j M, atkinsonResonantShiftedCorrectionTerm n j := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simp [(Finset.mem_Ico.mp hn).1]
    have hsplit :
        ∑ n ∈ Finset.Ico j M, atkinsonResonantShiftedCorrectionTerm n j
          =
        (∑ n ∈ Finset.Ico (j - 1) M, atkinsonResonantShiftedCorrectionTerm n j)
          - ∑ n ∈ Finset.Ico (j - 1) j, atkinsonResonantShiftedCorrectionTerm n j := by
      calc
        ∑ n ∈ Finset.Ico j M, atkinsonResonantShiftedCorrectionTerm n j
            =
          (∑ n ∈ Finset.range M, atkinsonResonantShiftedCorrectionTerm n j)
            - ∑ n ∈ Finset.range j, atkinsonResonantShiftedCorrectionTerm n j := by
              rw [Finset.sum_Ico_eq_sub _ (le_of_lt hJltM)]
        _ =
          ((∑ n ∈ Finset.range M, atkinsonResonantShiftedCorrectionTerm n j)
              - ∑ n ∈ Finset.range (j - 1), atkinsonResonantShiftedCorrectionTerm n j)
            -
          ((∑ n ∈ Finset.range j, atkinsonResonantShiftedCorrectionTerm n j)
              - ∑ n ∈ Finset.range (j - 1), atkinsonResonantShiftedCorrectionTerm n j) := by
                ring
        _ =
          (∑ n ∈ Finset.Ico (j - 1) M, atkinsonResonantShiftedCorrectionTerm n j)
            - ∑ n ∈ Finset.Ico (j - 1) j, atkinsonResonantShiftedCorrectionTerm n j := by
              rw [← Finset.sum_Ico_eq_sub _ (by omega : j - 1 ≤ M)]
              rw [← Finset.sum_Ico_eq_sub _ (by omega : j - 1 ≤ j)]
    have hprefix_raw :
        ‖∑ n ∈ Finset.Ico (j - 1) M, atkinsonResonantShiftedCorrectionTerm n j‖
          ≤ C_corr * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
      have hraw :
          ‖∑ n ∈ Finset.Ico (j - 1) M, atkinsonResonantShiftedCorrectionTerm n j‖
            ≤ C_corr * Real.log (↑j + 1) * (Real.sqrt ((((M - 1 + j : ℕ) : ℝ) + 1)) / j) := by
        have hMend : (1 + (M - 1) : ℕ) = M := by omega
        simpa [hMend, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (hcorr j hj (M - 1))
      calc
        ‖∑ n ∈ Finset.Ico (j - 1) M, atkinsonResonantShiftedCorrectionTerm n j‖
            ≤ C_corr * Real.log (↑j + 1) * (Real.sqrt ((((M - 1 + j : ℕ) : ℝ) + 1)) / j) := hraw
        _ ≤ C_corr * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
              refine mul_le_mul_of_nonneg_left ?_
                (mul_nonneg (le_of_lt hC_corr)
                  (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)))
              exact div_le_div_of_nonneg_right
                (Real.sqrt_le_sqrt (by
                  exact_mod_cast (by omega : (M - 1 + j : ℕ) + 1 ≤ M + j + 1)))
                (by positivity : (0 : ℝ) ≤ j)
    have hhead_raw :
        ‖∑ n ∈ Finset.Ico (j - 1) j, atkinsonResonantShiftedCorrectionTerm n j‖
          ≤ C_corr * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
      have hraw := hcorr j hj (j - 1)
      have hle : (((j - 1 + j : ℕ) : ℝ) + 1) ≤ (((M + j : ℕ) : ℝ) + 1) := by
        exact_mod_cast (by omega : (j - 1 + j) + 1 ≤ M + j + 1)
      calc
        ‖∑ n ∈ Finset.Ico (j - 1) j, atkinsonResonantShiftedCorrectionTerm n j‖
            ≤ C_corr * Real.log (↑j + 1) * (Real.sqrt (((j - 1 + j : ℕ) : ℝ) + 1) / j) := by
              simpa [show j - 1 + 1 = j by omega, Nat.add_assoc, add_left_comm, add_comm] using hraw
        _ ≤ C_corr * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
              refine mul_le_mul_of_nonneg_left
                (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hle)
                  (by positivity : (0 : ℝ) ≤ j))
                (mul_nonneg (le_of_lt hC_corr)
                  (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)))
    calc
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0)‖
          =
        ‖∑ n ∈ Finset.Ico j M, atkinsonResonantShiftedCorrectionTerm n j‖ := by
            rw [hsum_if]
      _ =
        ‖(∑ n ∈ Finset.Ico (j - 1) M, atkinsonResonantShiftedCorrectionTerm n j)
            - ∑ n ∈ Finset.Ico (j - 1) j, atkinsonResonantShiftedCorrectionTerm n j‖ := by
            rw [hsplit]
      _ ≤ ‖∑ n ∈ Finset.Ico (j - 1) M, atkinsonResonantShiftedCorrectionTerm n j‖
            + ‖∑ n ∈ Finset.Ico (j - 1) j, atkinsonResonantShiftedCorrectionTerm n j‖ := by
            exact norm_sub_le _ _
      _ ≤ C_corr * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j)
            + C_corr * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
            exact add_le_add hprefix_raw hhead_raw
      _ = (2 * C_corr) * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
            ring

private theorem
    atkinson_large_modes_complete_resonant_packet_row_bound_atomic_of_shifted_correction_prefix
    [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      ‖∫ u in Ioc (0 : ℝ) 1,
          ∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0)‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_corr, hC_corr, hcorr⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_correction_sum_bound_atomic_of_shifted_correction_prefix
  obtain ⟨C_bdry, hC_bdry, hbdry⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_boundary_sum_bound_atomic
  refine ⟨C_bdry + C_corr, by positivity, ?_⟩
  intro j hj M
  have hrow :
      ∫ u in Ioc (0 : ℝ) 1,
          ∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0)
        =
      ∑ n ∈ Finset.range M,
        (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j
          - atkinsonResonantShiftedCorrectionTerm n j else 0) := by
    simpa using
      atkinsonResonantShiftedRowIntegral_eq_boundary_correction_sum j M hj
  have hsplit :
      ∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j
            - atkinsonResonantShiftedCorrectionTerm n j else 0)
        =
      (∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0))
        -
      ∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0) := by
    calc
      ∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j
            - atkinsonResonantShiftedCorrectionTerm n j else 0)
          =
      ∑ n ∈ Finset.range M,
          ((if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else (0 : ℂ))
            - (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else (0 : ℂ))) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              by_cases hjn : j ≤ n <;> simp [hjn]
      _ = (∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0))
          -
          ∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0) := by
              rw [Finset.sum_sub_distrib]
  calc
    ‖∫ u in Ioc (0 : ℝ) 1,
        ∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0)‖
        =
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j
            - atkinsonResonantShiftedCorrectionTerm n j else 0)‖ := by
            rw [hrow]
    _ =
      ‖(∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0))
          -
        ∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0)‖ := by
            rw [hsplit]
    _ ≤
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)‖
        +
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0)‖ := by
            exact norm_sub_le _ _
    _ ≤ C_bdry * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j)
        + C_corr * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
            gcongr
            · exact hbdry j hj M
            · exact hcorr j hj M
      _ = (C_bdry + C_corr) * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
            ring

private theorem
    atkinson_large_modes_complete_shifted_row_bound_atomic_of_shifted_correction_prefix
    [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      |atkinsonShiftedCompleteRow M j|
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_complete, hC_complete, hrow⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_bound_atomic_of_shifted_correction_prefix
  refine ⟨C_complete, hC_complete, ?_⟩
  intro j hj M
  rw [atkinsonShiftedCompleteRow_eq_rowIntegral M j hj]
  have hpointwise_re :
      ∀ u : ℝ,
        (∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonComplexShiftedCompleteRowIntegrand n j u else 0)).re
          =
        ∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonShiftedCompleteRowIntegrand n j u else 0) := by
    intro u
    induction M with
    | zero =>
        simp
    | succ M ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        rw [Complex.add_re, ih]
        by_cases hjM : j ≤ M
        · simp [hjM, atkinsonComplexShiftedCompleteRowIntegrand_re]
        · simp [hjM]
  let f : ℝ → ℂ := fun u =>
    ∑ n ∈ Finset.range M, (if j ≤ n then atkinsonComplexShiftedCompleteRowIntegrand n j u else 0)
  have hInt : IntegrableOn f (Ioc (0 : ℝ) 1) := by
    have hcont : Continuous f := by
      unfold f
      exact continuous_finset_sum _ fun n _ =>
        by
          by_cases hjn : j ≤ n
          · simpa [hjn, atkinsonComplexShiftedCompleteRowIntegrand] using
              (continuous_const.mul
                (((HardyCosSmooth.continuous_hardyCosExp_complex n).comp
                  (blockCoord_continuous (n + j))).mul
                  (Complex.continuous_ofReal.comp (blockJacobian_continuous (n + j)))))
          · simpa [hjn] using (continuous_zero : Continuous fun _ : ℝ => (0 : ℂ))
    exact hcont.integrableOn_Ioc
  have hreal_eq :
      ∫ u in Ioc (0 : ℝ) 1,
          ∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonShiftedCompleteRowIntegrand n j u else 0)
        =
      (∫ u in Ioc (0 : ℝ) 1, f u).re := by
    calc
      ∫ u in Ioc (0 : ℝ) 1,
          ∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonShiftedCompleteRowIntegrand n j u else 0)
          =
        ∫ u in Ioc (0 : ℝ) 1, (f u).re := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
            exact (hpointwise_re u).symm
      _ = (∫ u in Ioc (0 : ℝ) 1, f u).re := by
            simpa using integral_re hInt
  have hcomplex_eq :
      (∫ u in Ioc (0 : ℝ) 1, f u)
        =
      ∫ u in Ioc (0 : ℝ) 1,
        ∑ n ∈ Finset.range M,
          if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0 := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    unfold f
    refine Finset.sum_congr rfl ?_
    intro n hn
    by_cases hjn : j ≤ n
    · simp [hjn, atkinsonComplexShiftedCompleteRowIntegrand_eq_resonantCarrier_singlePacket]
    · simp [hjn]
  calc
    |∫ u in Ioc (0 : ℝ) 1,
        ∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonShiftedCompleteRowIntegrand n j u else 0)|
        = |(∫ u in Ioc (0 : ℝ) 1, f u).re| := by
            rw [hreal_eq]
    _ ≤ ‖∫ u in Ioc (0 : ℝ) 1, f u‖ := Complex.abs_re_le_norm _
    _ ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
          rw [hcomplex_eq]
          exact hrow j hj M

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
/-- The correction-prefix package implies the inverse-phase cell-prefix package.

This stays theorem-only so the public provider graph does not silently route
`AtkinsonShiftedInversePhaseCellPrefixBoundHyp` through
`AtkinsonShiftedCorrectionPrefixBoundHyp` during strict synthesis. -/
theorem atkinson_shiftedInversePhaseCellPrefixBound_of_shiftedCorrectionPrefix
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    AtkinsonShiftedInversePhaseCellPrefixBoundHyp := by
  constructor
  ·
    obtain ⟨C_corr, hC_corr, hcorr⟩ := AtkinsonShiftedCorrectionPrefixBoundHyp.bound
    obtain ⟨C_bdry, hC_bdry, hbdry⟩ :=
      atkinson_large_modes_complete_resonant_packet_row_boundary_sum_bound_atomic
    refine ⟨2 * C_bdry + C_corr + (2 / (Real.log 2) ^ 2), by positivity, ?_⟩
    intro j hj m
    set target : ℝ := Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j
    have hpointwise :
        ∀ n : ℕ, j ≤ n + j → j ≤ n + j →
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)
            =
          atkinsonResonantShiftedBoundaryTerm n j
            - atkinsonResonantShiftedCorrectionTerm n j := by
      intro n _ _
      rw [atkinson_inverse_phase_mul_phaseWeightedCell_eq_rowIntegral n j hj]
      exact atkinsonResonantShiftedCell_eq_boundary_minus_correction n j hj
    have hIco_eq :
        ∑ n ∈ Finset.Ico (j - 1) (m + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonResonantShiftedPhaseWeightedCell n j)
          =
        ∑ n ∈ Finset.Ico (j - 1) (m + 1),
            (atkinsonResonantShiftedBoundaryTerm n j
              - atkinsonResonantShiftedCorrectionTerm n j) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      exact hpointwise n (by omega) (by omega)
    have hlog_j_nonneg : 0 ≤ Real.log (↑j + 1) :=
      Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)
    have hlog2_le : Real.log 2 ≤ Real.log (↑j + 1) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast show 2 ≤ j + 1 by omega)
    have hboundaryPrefix :
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            atkinsonResonantShiftedBoundaryTerm n j‖
          ≤ (2 * C_bdry * Real.log (↑j + 1) + 2 / Real.log 2) * target := by
      by_cases hsmall : m + 1 ≤ j
      · by_cases hnonempty : j - 1 < m + 1
        · have hIco_single : Finset.Ico (j - 1) (m + 1) = {j - 1} := by
            ext x
            constructor <;> intro hx
            · rcases Finset.mem_Ico.mp hx with ⟨hx1, hx2⟩
              have hxj : x = j - 1 := by omega
              simp [hxj]
            · simp at hx
              subst hx
              exact Finset.mem_Ico.mpr (by omega)
          rw [hIco_single, Finset.sum_singleton]
          have hfirst := atkinsonBoundary_jMinusOne_le j hj m
          have htarget_nonneg : 0 ≤ target := by
            positivity
          nlinarith [hfirst, hC_bdry, hlog_j_nonneg, htarget_nonneg,
            mul_nonneg (mul_nonneg (le_of_lt hC_bdry) hlog_j_nonneg) htarget_nonneg]
        · have hIco_empty : Finset.Ico (j - 1) (m + 1) = ∅ := by
            ext x
            constructor <;> intro hx
            · rcases Finset.mem_Ico.mp hx with ⟨hx1, hx2⟩
              omega
            · simp at hx
          rw [hIco_empty, Finset.sum_empty, norm_zero]
          positivity
      · have hjm : j < m + 1 := by
          omega
        have hsplit :
            ∑ n ∈ Finset.Ico (j - 1) (m + 1),
                atkinsonResonantShiftedBoundaryTerm n j
              =
            atkinsonResonantShiftedBoundaryTerm (j - 1) j
              + ∑ n ∈ Finset.Ico j (m + 1),
                  atkinsonResonantShiftedBoundaryTerm n j := by
          have hset :
              Finset.Ico (j - 1) (m + 1) =
                ({j - 1} : Finset ℕ) ∪ Finset.Ico j (m + 1) := by
            ext x
            constructor <;> intro hx
            · rcases Finset.mem_Ico.mp hx with ⟨hx1, hx2⟩
              by_cases hxj : x = j - 1
              · exact Finset.mem_union.mpr <| Or.inl (by simpa [hxj])
              · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_Ico.mpr (by omega)
            · rcases Finset.mem_union.mp hx with hx | hx
              · simp at hx
                subst hx
                exact Finset.mem_Ico.mpr (by omega)
              · rcases Finset.mem_Ico.mp hx with ⟨hx1, hx2⟩
                exact Finset.mem_Ico.mpr (by omega)
          have hdisj :
              Disjoint ({j - 1} : Finset ℕ) (Finset.Ico j (m + 1)) := by
            refine Finset.disjoint_left.mpr ?_
            intro x hx1 hx2
            simp at hx1
            subst hx1
            rcases Finset.mem_Ico.mp hx2 with ⟨hx2l, hx2r⟩
            omega
          rw [hset, Finset.sum_union hdisj, Finset.sum_singleton]
        have hconv :
            ∑ n ∈ Finset.Ico j (m + 1), atkinsonResonantShiftedBoundaryTerm n j
              =
            ∑ n ∈ Finset.range (m + 1),
              (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0) := by
          rw [← Finset.sum_filter]
          congr 1
          ext x
          constructor <;> intro hx <;>
            simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx ⊢ <;> omega
        have htail1 :
            ‖∑ n ∈ Finset.Ico j (m + 1), atkinsonResonantShiftedBoundaryTerm n j‖
              ≤ C_bdry * Real.log (↑j + 1) * (Real.sqrt (((m + 1 + j : ℕ) : ℝ) + 1) / j) := by
          rw [hconv]
          exact hbdry j hj (m + 1)
        have htail :
            ‖∑ n ∈ Finset.Ico j (m + 1), atkinsonResonantShiftedBoundaryTerm n j‖
              ≤ 2 * C_bdry * Real.log (↑j + 1) * target := by
          let A : ℝ := (((m + j : ℕ) : ℝ) + 1)
          have hsqrt4 :
              Real.sqrt (4 * A) = 2 * Real.sqrt A := by
            have hA_nonneg : 0 ≤ A := by
              dsimp [A]
              positivity
            have hsq : 4 * A = (2 * Real.sqrt A)^2 := by
              calc
                4 * A = 4 * (Real.sqrt A)^2 := by rw [Real.sq_sqrt hA_nonneg]
                _ = (2 * Real.sqrt A)^2 := by ring
            rw [hsq, Real.sqrt_sq_eq_abs]
            rw [abs_of_nonneg]
            positivity
          have hsqrt_mono :
              Real.sqrt (((m + 1 + j : ℕ) : ℝ) + 1) / j ≤ Real.sqrt (4 * A) / j := by
            have hsqrt_raw :
                Real.sqrt (((m + 1 + j : ℕ) : ℝ) + 1) ≤ Real.sqrt (4 * A) := by
              have hraw_nat : m + 1 + j + 1 ≤ 4 * (m + j + 1) := by
                omega
              apply Real.sqrt_le_sqrt
              dsimp [A]
              exact_mod_cast hraw_nat
            have hinv_nonneg : 0 ≤ (1 / (j : ℝ)) := by
              positivity
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
              mul_le_mul_of_nonneg_right hsqrt_raw hinv_nonneg
          have hlog_j_nonneg : 0 ≤ Real.log (↑j + 1) :=
            Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)
          calc
            ‖∑ n ∈ Finset.Ico j (m + 1), atkinsonResonantShiftedBoundaryTerm n j‖
              ≤ C_bdry * Real.log (↑j + 1) * (Real.sqrt (((m + 1 + j : ℕ) : ℝ) + 1) / j) := htail1
            _ ≤ C_bdry * Real.log (↑j + 1) * (Real.sqrt (4 * A) / j) := by
              exact mul_le_mul_of_nonneg_left hsqrt_mono
                (mul_nonneg (le_of_lt hC_bdry) hlog_j_nonneg)
            _ = C_bdry * Real.log (↑j + 1) * (2 * Real.sqrt A / j) := by
              rw [hsqrt4]
            _ = 2 * C_bdry * Real.log (↑j + 1) * target := by
              simp [target, A]
              ring
        rw [hsplit]
        have hfirst := atkinsonBoundary_jMinusOne_le j hj m
        have htri :
            ‖atkinsonResonantShiftedBoundaryTerm (j - 1) j
                + ∑ n ∈ Finset.Ico j (m + 1),
                    atkinsonResonantShiftedBoundaryTerm n j‖
              ≤ ‖atkinsonResonantShiftedBoundaryTerm (j - 1) j‖
                  + ‖∑ n ∈ Finset.Ico j (m + 1),
                      atkinsonResonantShiftedBoundaryTerm n j‖ := by
          exact norm_add_le _ _
        nlinarith [htri, hfirst, htail]
    have hcorr' :
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1), atkinsonResonantShiftedCorrectionTerm n j‖
          ≤ C_corr * Real.log (↑j + 1) * target := by
      simpa [target] using hcorr j hj m
    rw [hIco_eq, Finset.sum_sub_distrib]
    have htri :
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
              atkinsonResonantShiftedBoundaryTerm n j
            - ∑ n ∈ Finset.Ico (j - 1) (m + 1),
              atkinsonResonantShiftedCorrectionTerm n j‖
          ≤ ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
                atkinsonResonantShiftedBoundaryTerm n j‖
              + ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
                atkinsonResonantShiftedCorrectionTerm n j‖ := norm_sub_le _ _
    have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have htarget_nonneg : 0 ≤ target := by positivity
    -- hboundaryPrefix: ≤ (2*C_bdry*log(j+1) + 2/log(2)) * target
    -- hcorr': ≤ C_corr * log(j+1) * target
    -- Goal: ≤ (2*C_bdry + C_corr + 2/log(2)^2) * log(j+1) * target
    -- Key: 2/log(2) ≤ (2/log(2)^2) * log(j+1) since log(j+1) ≥ log(2)
    have habs : 2 / Real.log 2 ≤ 2 / (Real.log 2) ^ 2 * Real.log (↑j + 1) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hlog2_pos (by positivity : (0 : ℝ) < (Real.log 2) ^ 2)]
      nlinarith [hlog2_le, sq_nonneg (Real.log 2)]
    nlinarith [htri, hboundaryPrefix, hcorr']

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
theorem atkinson_shiftedCorrectionPrefixBound_of_inversePhaseCellPrefix
    [AtkinsonShiftedInversePhaseCellPrefixBoundHyp] :
    AtkinsonShiftedCorrectionPrefixBoundHyp := by
  constructor
  obtain ⟨C_cell, hC_cell, hcell⟩ := AtkinsonShiftedInversePhaseCellPrefixBoundHyp.bound
  obtain ⟨C_bdry, hC_bdry, hbdry⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_boundary_sum_bound_atomic
  refine ⟨2 * C_bdry + C_cell + (2 / (Real.log 2) ^ 2), by positivity, ?_⟩
  intro j hj m
  set target : ℝ := Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j
  have hpointwise :
      ∀ n : ℕ, j ≤ n + j → j ≤ n + j →
        atkinsonResonantShiftedCorrectionTerm n j
          =
        atkinsonResonantShiftedBoundaryTerm n j
          - ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j) := by
    intro n _ _
    rw [atkinson_inverse_phase_mul_phaseWeightedCell_eq_rowIntegral n j hj]
    rw [atkinsonResonantShiftedCell_eq_boundary_minus_correction n j hj]
    ring
  have hIco_eq :
      ∑ n ∈ Finset.Ico (j - 1) (m + 1), atkinsonResonantShiftedCorrectionTerm n j
        =
      ∑ n ∈ Finset.Ico (j - 1) (m + 1), atkinsonResonantShiftedBoundaryTerm n j
        -
      ∑ n ∈ Finset.Ico (j - 1) (m + 1),
        ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonResonantShiftedPhaseWeightedCell n j) := by
    calc
      ∑ n ∈ Finset.Ico (j - 1) (m + 1), atkinsonResonantShiftedCorrectionTerm n j
          =
        ∑ n ∈ Finset.Ico (j - 1) (m + 1),
          (atkinsonResonantShiftedBoundaryTerm n j
            - ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonResonantShiftedPhaseWeightedCell n j)) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              exact hpointwise n (by omega) (by omega)
      _ =
        ∑ n ∈ Finset.Ico (j - 1) (m + 1), atkinsonResonantShiftedBoundaryTerm n j
          -
        ∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j) := by
              rw [Finset.sum_sub_distrib]
  have hlog_j_nonneg : 0 ≤ Real.log (↑j + 1) :=
    Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)
  have hlog2_le : Real.log 2 ≤ Real.log (↑j + 1) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast show 2 ≤ j + 1 by omega)
  have hboundaryPrefix :
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
          atkinsonResonantShiftedBoundaryTerm n j‖
        ≤ (2 * C_bdry * Real.log (↑j + 1) + 2 / Real.log 2) * target := by
    by_cases hsmall : m + 1 ≤ j
    · by_cases hnonempty : j - 1 < m + 1
      · have hIco_single : Finset.Ico (j - 1) (m + 1) = {j - 1} := by
          ext x
          constructor <;> intro hx
          · rcases Finset.mem_Ico.mp hx with ⟨hx1, hx2⟩
            have hxj : x = j - 1 := by omega
            simp [hxj]
          · simp at hx
            subst hx
            exact Finset.mem_Ico.mpr (by omega)
        rw [hIco_single, Finset.sum_singleton]
        have hfirst := atkinsonBoundary_jMinusOne_le j hj m
        have htarget_nonneg : 0 ≤ target := by positivity
        nlinarith [hfirst, hC_bdry, hlog_j_nonneg, htarget_nonneg,
          mul_nonneg (mul_nonneg (le_of_lt hC_bdry) hlog_j_nonneg) htarget_nonneg]
      · have hIco_empty : Finset.Ico (j - 1) (m + 1) = ∅ := by
          ext x
          constructor <;> intro hx
          · rcases Finset.mem_Ico.mp hx with ⟨hx1, hx2⟩
            omega
          · simp at hx
        rw [hIco_empty, Finset.sum_empty, norm_zero]
        positivity
    · have hjm : j < m + 1 := by
        omega
      have hsplit :
          ∑ n ∈ Finset.Ico (j - 1) (m + 1),
              atkinsonResonantShiftedBoundaryTerm n j
            =
          atkinsonResonantShiftedBoundaryTerm (j - 1) j
            + ∑ n ∈ Finset.Ico j (m + 1),
                atkinsonResonantShiftedBoundaryTerm n j := by
        have hset :
            Finset.Ico (j - 1) (m + 1) =
              ({j - 1} : Finset ℕ) ∪ Finset.Ico j (m + 1) := by
          ext x
          constructor <;> intro hx
          · rcases Finset.mem_Ico.mp hx with ⟨hx1, hx2⟩
            by_cases hxj : x = j - 1
            · exact Finset.mem_union.mpr <| Or.inl (by simpa [hxj])
            · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_Ico.mpr (by omega)
          · rcases Finset.mem_union.mp hx with hx | hx
            · simp at hx
              subst hx
              exact Finset.mem_Ico.mpr (by omega)
            · rcases Finset.mem_Ico.mp hx with ⟨hx1, hx2⟩
              exact Finset.mem_Ico.mpr (by omega)
        have hdisj :
            Disjoint ({j - 1} : Finset ℕ) (Finset.Ico j (m + 1)) := by
          refine Finset.disjoint_left.mpr ?_
          intro x hx1 hx2
          simp at hx1
          subst hx1
          rcases Finset.mem_Ico.mp hx2 with ⟨hx2l, hx2r⟩
          omega
        rw [hset, Finset.sum_union hdisj, Finset.sum_singleton]
      have hconv :
          ∑ n ∈ Finset.Ico j (m + 1), atkinsonResonantShiftedBoundaryTerm n j
            =
          ∑ n ∈ Finset.range (m + 1),
            (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0) := by
        rw [← Finset.sum_filter]
        congr 1
        ext x
        constructor <;> intro hx <;>
          simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx ⊢ <;> omega
      have htail1 :
          ‖∑ n ∈ Finset.Ico j (m + 1), atkinsonResonantShiftedBoundaryTerm n j‖
            ≤ C_bdry * Real.log (↑j + 1) * (Real.sqrt (((m + 1 + j : ℕ) : ℝ) + 1) / j) := by
        rw [hconv]
        exact hbdry j hj (m + 1)
      have htail :
          ‖∑ n ∈ Finset.Ico j (m + 1), atkinsonResonantShiftedBoundaryTerm n j‖
            ≤ 2 * C_bdry * Real.log (↑j + 1) * target := by
        let A : ℝ := (((m + j : ℕ) : ℝ) + 1)
        have hsqrt4 :
            Real.sqrt (4 * A) = 2 * Real.sqrt A := by
          have hA_nonneg : 0 ≤ A := by
            dsimp [A]
            positivity
          have hsq : 4 * A = (2 * Real.sqrt A)^2 := by
            calc
              4 * A = 4 * (Real.sqrt A)^2 := by rw [Real.sq_sqrt hA_nonneg]
              _ = (2 * Real.sqrt A)^2 := by ring
          rw [hsq, Real.sqrt_sq_eq_abs]
          rw [abs_of_nonneg]
          positivity
        have hsqrt_mono :
            Real.sqrt (((m + 1 + j : ℕ) : ℝ) + 1) / j ≤ Real.sqrt (4 * A) / j := by
          have hsqrt_raw :
              Real.sqrt (((m + 1 + j : ℕ) : ℝ) + 1) ≤ Real.sqrt (4 * A) := by
            have hraw_nat : m + 1 + j + 1 ≤ 4 * (m + j + 1) := by
              omega
            apply Real.sqrt_le_sqrt
            dsimp [A]
            exact_mod_cast hraw_nat
          have hinv_nonneg : 0 ≤ (1 / (j : ℝ)) := by
            positivity
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            mul_le_mul_of_nonneg_right hsqrt_raw hinv_nonneg
        calc
          ‖∑ n ∈ Finset.Ico j (m + 1), atkinsonResonantShiftedBoundaryTerm n j‖
            ≤ C_bdry * Real.log (↑j + 1) * (Real.sqrt (((m + 1 + j : ℕ) : ℝ) + 1) / j) := htail1
          _ ≤ C_bdry * Real.log (↑j + 1) * (Real.sqrt (4 * A) / j) := by
            exact mul_le_mul_of_nonneg_left hsqrt_mono
              (mul_nonneg (le_of_lt hC_bdry) hlog_j_nonneg)
          _ = C_bdry * Real.log (↑j + 1) * (2 * Real.sqrt A / j) := by
            rw [hsqrt4]
          _ = 2 * C_bdry * Real.log (↑j + 1) * target := by
            simp [target, A]
            ring
      rw [hsplit]
      have hfirst := atkinsonBoundary_jMinusOne_le j hj m
      have htri :
          ‖atkinsonResonantShiftedBoundaryTerm (j - 1) j
              + ∑ n ∈ Finset.Ico j (m + 1),
                  atkinsonResonantShiftedBoundaryTerm n j‖
            ≤ ‖atkinsonResonantShiftedBoundaryTerm (j - 1) j‖
                + ‖∑ n ∈ Finset.Ico j (m + 1),
                    atkinsonResonantShiftedBoundaryTerm n j‖ := by
        exact norm_add_le _ _
      nlinarith [htri, hfirst, htail]
  have hcellPrefix :
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)‖
        ≤ C_cell * Real.log (↑j + 1) * target := by
    simpa [target] using hcell j hj m
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have htarget_nonneg : 0 ≤ target := by positivity
  have habs : 2 / Real.log 2 ≤ 2 / (Real.log 2) ^ 2 * Real.log (↑j + 1) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hlog2_pos (by positivity : (0 : ℝ) < (Real.log 2) ^ 2)]
    nlinarith [hlog2_le, sq_nonneg (Real.log 2)]
  calc
    ‖∑ n ∈ Finset.Ico (j - 1) (m + 1), atkinsonResonantShiftedCorrectionTerm n j‖
        =
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1), atkinsonResonantShiftedBoundaryTerm n j
          -
        ∑ n ∈ Finset.Ico (j - 1) (m + 1),
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)‖ := by
            rw [hIco_eq]
    _ ≤ ‖∑ n ∈ Finset.Ico (j - 1) (m + 1), atkinsonResonantShiftedBoundaryTerm n j‖
          +
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonResonantShiftedPhaseWeightedCell n j)‖ := by
            exact norm_sub_le _ _
    _ ≤ (2 * C_bdry * Real.log (↑j + 1) + 2 / Real.log 2) * target
          + C_cell * Real.log (↑j + 1) * target := by
            exact add_le_add hboundaryPrefix hcellPrefix
    _ ≤ (2 * C_bdry + C_cell + (2 / (Real.log 2) ^ 2)) * Real.log (↑j + 1) * target := by
            nlinarith

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
private theorem
    atkinson_large_modes_complete_resonant_packet_row_correction_sum_bound_atomic_of_fixedShift_nontrivial
    {C_complete : ℝ}
    (hC_complete : 0 < C_complete)
    (hcorr' :
      ∀ j : ℕ, 1 ≤ j → ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            atkinsonResonantShiftedCorrectionTerm n j‖
          ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j))
    (j M : ℕ) (hj : 1 ≤ j) (hJM : j ≤ M) :
    ‖∑ n ∈ Finset.range M,
        (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0)‖
      ≤ (2 * C_complete) * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  let target : ℝ := Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j
  let corrFn : ℕ → ℂ := fun n => atkinsonResonantShiftedCorrectionTerm n j
  have hsum :
      ∑ n ∈ Finset.range M,
          (if j ≤ n then corrFn n else 0)
        =
      ∑ n ∈ Finset.Ico j M, corrFn n := by
    calc
      ∑ n ∈ Finset.range M,
          (if j ≤ n then corrFn n else 0)
        =
      (∑ n ∈ Finset.range j,
          (if j ≤ n then corrFn n else 0))
        +
      ∑ n ∈ Finset.Ico j M,
          (if j ≤ n then corrFn n else 0) := by
            simpa using
              (Finset.sum_range_add_sum_Ico (fun n => if j ≤ n then corrFn n else 0) hJM).symm
      _ =
      ∑ n ∈ Finset.Ico j M,
          (if j ≤ n then corrFn n else 0) := by
            have hprefix_zero :
                ∑ n ∈ Finset.range j,
                    (if j ≤ n then corrFn n else 0) = 0 := by
                  apply Finset.sum_eq_zero
                  intro n hn
                  simp [(Finset.mem_range.mp hn).not_ge]
            rw [hprefix_zero, zero_add]
      _ =
      ∑ n ∈ Finset.Ico j M, corrFn n := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simp [(Finset.mem_Ico.mp hn).1]
  have hsplit :
      ∑ n ∈ Finset.Ico j M, corrFn n
        =
      (∑ n ∈ Finset.Ico (j - 1) M, corrFn n)
        - ∑ n ∈ Finset.Ico (j - 1) j, corrFn n := by
          calc
            ∑ n ∈ Finset.Ico j M, corrFn n
                =
            (∑ n ∈ Finset.range M, corrFn n)
              - ∑ n ∈ Finset.range j, corrFn n := by
                  rw [Finset.sum_Ico_eq_sub _ hJM]
            _ =
            ((∑ n ∈ Finset.range M, corrFn n)
                - ∑ n ∈ Finset.range (j - 1), corrFn n)
              -
            ((∑ n ∈ Finset.range j, corrFn n)
                - ∑ n ∈ Finset.range (j - 1), corrFn n) := by
                  ring
            _ =
            (∑ n ∈ Finset.Ico (j - 1) M, corrFn n)
              - ∑ n ∈ Finset.Ico (j - 1) j, corrFn n := by
                  rw [← Finset.sum_Ico_eq_sub _ (by omega : j - 1 ≤ M)]
                  rw [← Finset.sum_Ico_eq_sub _ (by omega : j - 1 ≤ j)]
  have hmain :
      ‖∑ n ∈ Finset.Ico (j - 1) M, corrFn n‖
        ≤ C_complete * Real.log (↑j + 1) * target := by
    have hraw := hcorr' j hj (M - 1)
    calc
      ‖∑ n ∈ Finset.Ico (j - 1) M, corrFn n‖
          ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M - 1 + j : ℕ) : ℝ) + 1) / j) := by
            simpa [corrFn, show M - 1 + 1 = M by omega, Nat.add_assoc, add_left_comm, add_comm]
              using hraw
      _ = C_complete * Real.log (↑j + 1) * (Real.sqrt ((M + j : ℕ) : ℝ) / j) := by
            have hM : (M - 1 + j : ℕ) + 1 = M + j := by omega
            have hM' : (((M - 1 + j : ℕ) : ℝ) + 1) = ((M + j : ℕ) : ℝ) := by
              exact_mod_cast hM
            rw [hM']
      _ ≤ C_complete * Real.log (↑j + 1) * target := by
            apply mul_le_mul_of_nonneg_left _
              (mul_nonneg (le_of_lt hC_complete)
                (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)))
            exact div_le_div_of_nonneg_right
              (Real.sqrt_le_sqrt (by linarith))
              (by positivity : (0 : ℝ) ≤ j)
  have hhead :
      ‖∑ n ∈ Finset.Ico (j - 1) j, corrFn n‖
        ≤ C_complete * Real.log (↑j + 1) * target := by
    have hraw := hcorr' j hj (j - 1)
    have hj_le : ((j - 1 + j : ℕ) : ℝ) + 1 ≤ (((M + j : ℕ) : ℝ) + 1) := by
      exact_mod_cast (by omega : (j - 1 + j) + 1 ≤ M + j + 1)
    calc
      ‖∑ n ∈ Finset.Ico (j - 1) j, corrFn n‖
          ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((j - 1 + j : ℕ) : ℝ) + 1) / j) := by
            simpa [corrFn, show j - 1 + 1 = j by omega, Nat.add_assoc, add_left_comm, add_comm]
              using hraw
      _ ≤ C_complete * Real.log (↑j + 1) * target := by
            apply mul_le_mul_of_nonneg_left _
              (mul_nonneg (le_of_lt hC_complete)
                (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)))
            exact div_le_div_of_nonneg_right
              (Real.sqrt_le_sqrt hj_le)
              (by positivity : (0 : ℝ) ≤ j)
  calc
    ‖∑ n ∈ Finset.range M,
        (if j ≤ n then corrFn n else 0)‖
        =
    ‖∑ n ∈ Finset.Ico j M, corrFn n‖ := by
          rw [hsum]
    _ =
      ‖(∑ n ∈ Finset.Ico (j - 1) M, corrFn n)
          - (∑ n ∈ Finset.Ico (j - 1) j, corrFn n)‖ := by
            rw [hsplit]
    _ ≤ ‖∑ n ∈ Finset.Ico (j - 1) M, corrFn n‖
          + ‖∑ n ∈ Finset.Ico (j - 1) j, corrFn n‖ := by
            exact norm_sub_le _ _
    _ ≤ C_complete * Real.log (↑j + 1) * target + C_complete * Real.log (↑j + 1) * target := by
          exact add_le_add hmain hhead
    _ = (2 * C_complete) * Real.log (↑j + 1) * target := by ring

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
private theorem atkinson_large_modes_complete_resonant_packet_row_correction_sum_bound_atomic
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      ‖∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0)‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_complete, hC_complete, hcorr'⟩ := AtkinsonShiftedCorrectionPrefixBoundHyp.bound
  refine ⟨2 * C_complete, by positivity, ?_⟩
  intro j hj M
  by_cases hMj : M ≤ j
  · have hzero :
        ∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnlt : n < j := lt_of_lt_of_le (Finset.mem_range.mp hn) hMj
      simp [hnlt.not_ge]
    have hnonneg :
        0 ≤ (2 * C_complete) * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
      apply mul_nonneg
      · exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega))
      · positivity
    rw [hzero, norm_zero]
    exact hnonneg
  · exact
      atkinson_large_modes_complete_resonant_packet_row_correction_sum_bound_atomic_of_fixedShift_nontrivial
        hC_complete hcorr' j M hj (le_of_lt (lt_of_not_ge hMj))

private theorem atkinson_large_modes_complete_resonant_packet_row_bound_atomic_of_shiftedCorrectionPrefix
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      ‖∫ u in Ioc (0 : ℝ) 1,
          ∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0)‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_bdry, hC_bdry, hbdry⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_boundary_sum_bound_atomic
  obtain ⟨C_corr, hC_corr, hcorr⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_correction_sum_bound_atomic
  refine ⟨C_bdry + C_corr, by positivity, ?_⟩
  intro j hj M
  rw [atkinsonResonantShiftedRowIntegral_eq_boundary_correction_sum j M hj]
  have hsplit :
      ∑ n ∈ Finset.range M,
          (if j ≤ n then
            atkinsonResonantShiftedBoundaryTerm n j - atkinsonResonantShiftedCorrectionTerm n j
          else 0)
        =
      (∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0))
        -
      ∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0) := by
    calc
      ∑ n ∈ Finset.range M,
          (if j ≤ n then
            atkinsonResonantShiftedBoundaryTerm n j - atkinsonResonantShiftedCorrectionTerm n j
          else 0)
          =
      ∑ n ∈ Finset.range M,
          ((if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)
            - (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              by_cases hjn : j ≤ n <;> simp [hjn]
      _ = (∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0))
          -
          ∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0) := by
              rw [Finset.sum_sub_distrib]
  calc
    ‖∑ n ∈ Finset.range M,
        (if j ≤ n then
          atkinsonResonantShiftedBoundaryTerm n j - atkinsonResonantShiftedCorrectionTerm n j
        else 0)‖
      =
    ‖(∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0))
        -
      ∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0)‖ := by
          rw [hsplit]
    _ ≤ ‖∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedBoundaryTerm n j else 0)‖
          +
        ‖∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedCorrectionTerm n j else 0)‖ := by
            exact norm_sub_le _ _
    _ ≤ C_bdry * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j)
          + C_corr * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
            gcongr
            · exact hbdry j hj M
            · exact hcorr j hj M
    _ = (C_bdry + C_corr) * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
          ring

omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
private theorem atkinsonResonantShiftedRowIntegral_eq_inversePhaseCellSum
    (j M : ℕ) (hj : 1 ≤ j) :
    ∫ u in Ioc (0 : ℝ) 1,
      ∑ n ∈ Finset.range M,
        (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0)
      =
    ∑ n ∈ Finset.range M,
      (if j ≤ n then
        ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          atkinsonResonantShiftedPhaseWeightedCell n j)
      else 0) := by
  calc
    ∫ u in Ioc (0 : ℝ) 1,
        ∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0)
        =
      ∑ n ∈ Finset.range M,
        ∫ u in Ioc (0 : ℝ) 1,
          (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0) := by
            rw [MeasureTheory.integral_finset_sum]
            intro n hn
            by_cases hjn : j ≤ n
            · simpa [hjn] using (atkinsonResonantShiftedRowSummand_continuous n j).integrableOn_Ioc
            · simp [hjn]
    _ =
      ∑ n ∈ Finset.range M,
        (if j ≤ n then
          ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            atkinsonResonantShiftedPhaseWeightedCell n j)
        else 0) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          by_cases hjn : j ≤ n
          · simpa [hjn] using
              (atkinson_inverse_phase_mul_phaseWeightedCell_eq_rowIntegral n j hj).symm
          · simp [hjn]

/- Once the stronger no-log inverse-phase cell-prefix estimate is available,
the complete resonant packet row bound follows directly in the current tracked
pipeline. This makes the downstream consequence of the remaining cell-prefix
leaf explicit. -/
omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in
theorem atkinson_large_modes_complete_resonant_packet_row_bound_atomic_of_shifted_inversePhaseCellPrefix
    (hshift :
      ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
              atkinsonResonantShiftedPhaseWeightedCell n j)‖
          ≤ C_complete * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j)) :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      ‖∫ u in Ioc (0 : ℝ) 1,
          ∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0)‖
        ≤ C_complete * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_complete, hC_complete, hshift'⟩ := hshift
  refine ⟨2 * C_complete, by positivity, ?_⟩
  intro j hj M
  rw [atkinsonResonantShiftedRowIntegral_eq_inversePhaseCellSum j M hj]
  by_cases hMj : M ≤ j
  · have hzero :
        ∑ n ∈ Finset.range M,
            (if j ≤ n then
              ((((1 / atkinsonShiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                atkinsonResonantShiftedPhaseWeightedCell n j)
            else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnlt : n < j := lt_of_lt_of_le (Finset.mem_range.mp hn) hMj
      simp [hnlt.not_ge]
    have hnonneg :
        0 ≤ (2 * C_complete) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
      positivity
    rw [hzero, norm_zero]
    exact hnonneg
  · exact
      atkinson_large_modes_complete_resonant_packet_row_inversePhaseCellSum_bound_atomic_of_fixedShift_nontrivial
        hC_complete hshift' j M hj (le_of_lt (lt_of_not_ge hMj))

private theorem atkinson_large_modes_complete_resonant_packet_row_bound_atomic
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      ‖∫ u in Ioc (0 : ℝ) 1,
          ∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0)‖
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_complete, hC_complete, hrow⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_bound_atomic_of_shiftedCorrectionPrefix
  refine ⟨C_complete, hC_complete, ?_⟩
  intro j hj M
  exact hrow j hj M

private theorem atkinson_large_modes_complete_shifted_row_bound_atomic
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    ∃ C_complete > 0, ∀ j : ℕ, 1 ≤ j → ∀ M : ℕ,
      |atkinsonShiftedCompleteRow M j|
        ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
  obtain ⟨C_complete, hC_complete, hrow⟩ :=
    atkinson_large_modes_complete_resonant_packet_row_bound_atomic
  refine ⟨C_complete, hC_complete, ?_⟩
  intro j hj M
  rw [atkinsonShiftedCompleteRow_eq_rowIntegral M j hj]
  have hpointwise_re :
      ∀ u : ℝ,
        (∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonComplexShiftedCompleteRowIntegrand n j u else 0)).re
          =
        ∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonShiftedCompleteRowIntegrand n j u else 0) := by
    intro u
    induction M with
    | zero =>
        simp
    | succ M ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        rw [Complex.add_re, ih]
        by_cases hjM : j ≤ M
        · simp [hjM, atkinsonComplexShiftedCompleteRowIntegrand_re]
        · simp [hjM]
  let f : ℝ → ℂ := fun u =>
    ∑ n ∈ Finset.range M, (if j ≤ n then atkinsonComplexShiftedCompleteRowIntegrand n j u else 0)
  have hInt : IntegrableOn f (Ioc (0 : ℝ) 1) := by
    have hcont : Continuous f := by
      unfold f
      exact continuous_finset_sum _ fun n _ =>
        by
          by_cases hjn : j ≤ n
          · simpa [hjn, atkinsonComplexShiftedCompleteRowIntegrand] using
              (continuous_const.mul
                (((HardyCosSmooth.continuous_hardyCosExp_complex n).comp
                  (blockCoord_continuous (n + j))).mul
                  (Complex.continuous_ofReal.comp (blockJacobian_continuous (n + j)))))
          · simpa [hjn] using (continuous_zero : Continuous fun _ : ℝ => (0 : ℂ))
    exact hcont.integrableOn_Ioc
  have hreal_eq :
      ∫ u in Ioc (0 : ℝ) 1,
          ∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonShiftedCompleteRowIntegrand n j u else 0)
        =
      (∫ u in Ioc (0 : ℝ) 1, f u).re := by
    calc
      ∫ u in Ioc (0 : ℝ) 1,
          ∑ n ∈ Finset.range M,
            (if j ≤ n then atkinsonShiftedCompleteRowIntegrand n j u else 0)
          =
        ∫ u in Ioc (0 : ℝ) 1, (f u).re := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
            exact (hpointwise_re u).symm
      _ = (∫ u in Ioc (0 : ℝ) 1, f u).re := by
            simpa using integral_re hInt
  have hcomplex_eq :
      (∫ u in Ioc (0 : ℝ) 1, f u)
        =
      ∫ u in Ioc (0 : ℝ) 1,
        ∑ n ∈ Finset.range M,
          if j ≤ n then atkinsonResonantShiftedRowSummand n j u else 0 := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    unfold f
    refine Finset.sum_congr rfl ?_
    intro n hn
    by_cases hjn : j ≤ n
    · simp [hjn, atkinsonComplexShiftedCompleteRowIntegrand_eq_resonantCarrier_singlePacket]
    · simp [hjn]
  calc
    |∫ u in Ioc (0 : ℝ) 1,
        ∑ n ∈ Finset.range M,
          (if j ≤ n then atkinsonShiftedCompleteRowIntegrand n j u else 0)|
        = |(∫ u in Ioc (0 : ℝ) 1, f u).re| := by
            rw [hreal_eq]
    _ ≤ ‖∫ u in Ioc (0 : ℝ) 1, f u‖ := Complex.abs_re_le_norm _
    _ ≤ C_complete * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
          rw [hcomplex_eq]
          exact hrow j hj M

private theorem atkinson_large_modes_complete_near_band_sqrtlog_bound_atomic
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    ∃ N0 : ℕ, ∃ C_complete > 0, ∀ M : ℕ, N0 ≤ M →
      ∀ T : ℝ, T ≥ 2 →
        |∑ n ∈ Finset.Ico M (hardyN T - 1),
            atkinsonModeWeight n *
              ∫ t in Ioc (hardyStart (n + 1))
                (hardyStart (min (2 * n + 1) (hardyN T - 1))), hardyCos n t|
          ≤ C_complete * ((↑(hardyN T) : ℝ) + 1) := by
  obtain ⟨Crow, hCrow, hrow⟩ := atkinson_large_modes_complete_shifted_row_bound_atomic
  refine ⟨0, 12 * Crow, by positivity, ?_⟩
  intro M _hM T hT
  set N : ℕ := hardyN T
  by_cases hEmpty : N - 1 ≤ M
  · have hnonneg :
        0 ≤ (12 * Crow) * ((↑N : ℝ) + 1) := by
        have hlog_nonneg : 0 ≤ 1 + Real.log ((↑N : ℝ) + 1) := by
          have hlog : 0 ≤ Real.log ((↑N : ℝ) + 1) := by
            have hone : (1 : ℝ) ≤ (↑N : ℝ) + 1 := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
            exact Real.log_nonneg hone
          linarith
        positivity
    have hIco : Finset.Ico M (N - 1) = ∅ := by
      ext x
      simp [Finset.mem_Ico, hEmpty]
    simpa [N, hIco] using hnonneg
  · have hNtwo : 2 ≤ N := by
      omega
    have hhalf_pos : 1 ≤ N / 2 := by
      omega
    have hdecomp :
        ∑ n ∈ Finset.Ico M (N - 1),
          atkinsonModeWeight n *
            ∫ t in Ioc (hardyStart (n + 1))
              (hardyStart (min (2 * n + 1) (N - 1))), hardyCos n t
      =
        ∑ j ∈ Finset.Icc 1 (N / 2),
          ∑ n ∈ Finset.Ico M (N - 1),
            (if j ≤ min n (N - n - 2) then atkinsonShiftedCompleteCell n j else 0) := by
      calc
        ∑ n ∈ Finset.Ico M (N - 1),
            atkinsonModeWeight n *
              ∫ t in Ioc (hardyStart (n + 1))
                (hardyStart (min (2 * n + 1) (N - 1))), hardyCos n t
            =
          ∑ n ∈ Finset.Ico M (N - 1),
            ∑ j ∈ Finset.Icc 1 (min n (N - n - 2)), atkinsonShiftedCompleteCell n j := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              exact atkinson_weighted_complete_integral_eq_shift_sum n N
                ((Finset.mem_Ico.mp hn).2)
        _ =
          ∑ n ∈ Finset.Ico M (N - 1),
            ∑ j ∈ Finset.Icc 1 (N / 2),
              (if j ≤ min n (N - n - 2) then atkinsonShiftedCompleteCell n j else 0) := by
                refine Finset.sum_congr rfl ?_
                intro n hn
                have hJ_le : min n (N - n - 2) ≤ N / 2 := by
                  have hnN : n < N - 1 := (Finset.mem_Ico.mp hn).2
                  omega
                simpa using
                  (atkinson_sum_Icc_pad
                    (f := fun j => atkinsonShiftedCompleteCell n j) hJ_le)
        _ =
          ∑ j ∈ Finset.Icc 1 (N / 2),
            ∑ n ∈ Finset.Ico M (N - 1),
              (if j ≤ min n (N - n - 2) then atkinsonShiftedCompleteCell n j else 0) := by
                rw [Finset.sum_comm]
    have hperj :
        ∀ j ∈ Finset.Icc 1 (N / 2),
          |∑ n ∈ Finset.Ico M (N - 1),
              if j ≤ min n (N - n - 2) then atkinsonShiftedCompleteCell n j else 0|
            ≤ (2 * Crow) * Real.log (↑j + 1) * (Real.sqrt (↑N : ℝ) / j) := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hsum_trim₁ :
          ∑ n ∈ Finset.Ico M (N - 1),
            (if j ≤ min n (N - n - 2) then atkinsonShiftedCompleteCell n j else 0)
            =
          ∑ n ∈ Finset.Ico M (N - j - 1),
            (if j ≤ min n (N - n - 2) then atkinsonShiftedCompleteCell n j else 0) := by
            symm
            refine Finset.sum_subset ?_ ?_
            · intro n hn
              have hn' := Finset.mem_Ico.mp hn
              have hlt : N - j - 1 < N - 1 := by
                omega
              exact Finset.mem_Ico.mpr ⟨hn'.1, lt_trans hn'.2 hlt⟩
            · intro n hnBig hnSmall
              have hnBig' := Finset.mem_Ico.mp hnBig
              have hnot : ¬ n < N - j - 1 := by
                intro hlt
                exact hnSmall (Finset.mem_Ico.mpr ⟨hnBig'.1, by omega⟩)
              have hfalse : ¬ j ≤ min n (N - n - 2) := by
                intro hjmin
                have : n < N - j - 1 := by
                  omega
                exact hnot this
              simp [hfalse]
      have hsum_trim₂ :
          ∑ n ∈ Finset.Ico M (N - j - 1),
            (if j ≤ min n (N - n - 2) then atkinsonShiftedCompleteCell n j else 0)
            =
          ∑ n ∈ Finset.Ico M (N - j - 1),
            (if j ≤ n then atkinsonShiftedCompleteCell n j else 0) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            have hn' := Finset.mem_Ico.mp hn
            have hcond : j ≤ min n (N - n - 2) ↔ j ≤ n := by
              constructor
              · exact fun h => le_trans h (Nat.min_le_left _ _)
              · intro hjn
                have hupper : j ≤ N - n - 2 := by
                  omega
                exact le_min hjn hupper
            by_cases hjn : j ≤ n
            · simp [hcond, hjn]
            · simp [hcond, hjn]
      have hsum_trim := hsum_trim₁.trans hsum_trim₂
      rw [hsum_trim]
      by_cases hMj : N - j - 1 ≤ M
      · have hIco : Finset.Ico M (N - j - 1) = ∅ := by
          ext n
          simp [Finset.mem_Ico, hMj]
        have hnonneg : 0 ≤ (2 * Crow) * Real.log (↑j + 1) * (Real.sqrt (↑N : ℝ) / j) := by
          apply mul_nonneg
          · exact mul_nonneg (by positivity)
              (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega))
          · positivity
        rw [show Finset.Ico M (N - j - 1) = ∅ from hIco, Finset.sum_empty, abs_zero]
        exact hnonneg
      · have hMNj : M ≤ N - j - 1 := le_of_lt (lt_of_not_ge hMj)
        have hsplit :
            ∑ n ∈ Finset.Ico M (N - j - 1),
              (if j ≤ n then atkinsonShiftedCompleteCell n j else 0)
              =
            atkinsonShiftedCompleteRow (N - j - 1) j - atkinsonShiftedCompleteRow M j := by
              unfold atkinsonShiftedCompleteRow
              rw [Finset.sum_Ico_eq_sub
                (fun n => if j ≤ n then atkinsonShiftedCompleteCell n j else 0) hMNj]
        have hNatN : (N - j - 1) + j + 1 = N := by
          omega
        have hCastN : (↑(N - j - 1) : ℝ) + (↑j : ℝ) + 1 = N := by
          exact_mod_cast hNatN
        have hrow_upper :
            |atkinsonShiftedCompleteRow (N - j - 1) j|
              ≤ Crow * Real.log (↑j + 1) * (Real.sqrt (↑N : ℝ) / j) := by
                have hraw := hrow j hj1 (N - j - 1)
                have hCastN' : (↑j : ℝ) + (↑(N - j - 1) : ℝ) + 1 = N := by
                  nlinarith [hCastN]
                calc
                  |atkinsonShiftedCompleteRow (N - j - 1) j|
                      ≤ Crow * Real.log (↑j + 1) * (Real.sqrt ((↑j : ℝ) + (↑(N - j - 1) : ℝ) + 1) / j) := by
                            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hraw
                  _ = Crow * Real.log (↑j + 1) * (Real.sqrt (↑N : ℝ) / j) := by
                        rw [hCastN']
        have hCastM : (((M + j : ℕ) : ℝ) + 1) ≤ N := by
          exact_mod_cast (by omega : M + j + 1 ≤ N)
        have hsqrtM : Real.sqrt (((M + j : ℕ) : ℝ) + 1) ≤ Real.sqrt (↑N : ℝ) := by
          exact Real.sqrt_le_sqrt hCastM
        have hrow_lower_raw :
            |atkinsonShiftedCompleteRow M j|
              ≤ Crow * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := by
                exact hrow j hj1 M
        have hrow_lower :
            |atkinsonShiftedCompleteRow M j|
              ≤ Crow * Real.log (↑j + 1) * (Real.sqrt (↑N : ℝ) / j) := by
                have hfrac :
                    Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j ≤ Real.sqrt (↑N : ℝ) / j := by
                  exact div_le_div_of_nonneg_right hsqrtM (by positivity : (0 : ℝ) ≤ j)
                calc
                  |atkinsonShiftedCompleteRow M j|
                      ≤ Crow * Real.log (↑j + 1) * (Real.sqrt (((M + j : ℕ) : ℝ) + 1) / j) := hrow_lower_raw
                  _ ≤ Crow * Real.log (↑j + 1) * (Real.sqrt (↑N : ℝ) / j) := by
                        exact mul_le_mul_of_nonneg_left hfrac
                          (mul_nonneg (le_of_lt hCrow)
                            (Real.log_nonneg (by exact_mod_cast show 1 ≤ j + 1 by omega)))
        calc
          |∑ n ∈ Finset.Ico M (N - j - 1),
              (if j ≤ n then atkinsonShiftedCompleteCell n j else 0)|
              =
            |atkinsonShiftedCompleteRow (N - j - 1) j - atkinsonShiftedCompleteRow M j| := by
                rw [hsplit]
          _ ≤ |atkinsonShiftedCompleteRow (N - j - 1) j|
                + |atkinsonShiftedCompleteRow M j| := by
                  simpa [sub_eq_add_neg] using
                    (abs_add_le (atkinsonShiftedCompleteRow (N - j - 1) j)
                      (-(atkinsonShiftedCompleteRow M j)))
          _ ≤ (2 * Crow) * Real.log (↑j + 1) * (Real.sqrt (↑N : ℝ) / j) := by
                nlinarith [hrow_upper, hrow_lower]
    calc
      |∑ n ∈ Finset.Ico M (N - 1),
          atkinsonModeWeight n *
            ∫ t in Ioc (hardyStart (n + 1))
              (hardyStart (min (2 * n + 1) (N - 1))), hardyCos n t|
        =
      |∑ j ∈ Finset.Icc 1 (N / 2),
          ∑ n ∈ Finset.Ico M (N - 1),
            (if j ≤ min n (N - n - 2) then atkinsonShiftedCompleteCell n j else 0)| := by
              rw [hdecomp]
      _ ≤
        ∑ j ∈ Finset.Icc 1 (N / 2),
          |∑ n ∈ Finset.Ico M (N - 1),
              (if j ≤ min n (N - n - 2) then atkinsonShiftedCompleteCell n j else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤
        ∑ j ∈ Finset.Icc 1 (N / 2), (2 * Crow) * Real.log (↑j + 1) * (Real.sqrt (↑N : ℝ) / j) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact hperj j hj
      _ ≤
        ∑ j ∈ Finset.Icc 1 (N / 2), (2 * Crow) * (Real.sqrt (↑N : ℝ) / j) *
          Real.log ((↑N : ℝ) + 1) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          have hlog_le : Real.log (↑j + 1) ≤ Real.log ((↑N : ℝ) + 1) :=
            Real.log_le_log (by positivity)
              (by exact_mod_cast show j + 1 ≤ N + 1 by
                    exact Nat.succ_le_succ (le_trans (Finset.mem_Icc.mp hj).2 (Nat.div_le_self N 2)))
          calc (2 * Crow) * Real.log (↑j + 1) * (Real.sqrt (↑N : ℝ) / ↑j)
              = (2 * Crow) * (Real.sqrt (↑N : ℝ) / ↑j) * Real.log (↑j + 1) := by ring
            _ ≤ (2 * Crow) * (Real.sqrt (↑N : ℝ) / ↑j) * Real.log ((↑N : ℝ) + 1) :=
                mul_le_mul_of_nonneg_left hlog_le
                  (mul_nonneg (by positivity) (div_nonneg (Real.sqrt_nonneg _) (by positivity)))
      _ = (2 * Crow * Real.sqrt (↑N : ℝ) * Real.log ((↑N : ℝ) + 1)) *
            ∑ j ∈ Finset.Icc 1 (N / 2), (1 : ℝ) / j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
      _ ≤ (2 * Crow * Real.sqrt (↑N : ℝ) * Real.log ((↑N : ℝ) + 1)) *
            (1 + Real.log ((↑N : ℝ) + 1)) := by
            gcongr
            · apply mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
              exact Real.log_nonneg (by exact_mod_cast show 1 ≤ N + 1 by omega)
            · calc
                ∑ j ∈ Finset.Icc 1 (N / 2), (1 : ℝ) / j
                    ≤ 1 + Real.log (((N / 2 : ℕ) : ℝ)) :=
                      atkinson_harmonic_Icc_le_one_add_log (N / 2) hhalf_pos
                _ ≤ 1 + Real.log ((↑N : ℝ) + 1) := by
                      have : Real.log (↑(N / 2) : ℝ) ≤ Real.log ((↑N : ℝ) + 1) :=
                        Real.log_le_log (by positivity) (by exact_mod_cast show N / 2 ≤ N + 1 by omega)
                      linarith
      _ ≤ (12 * Crow) * ((↑N : ℝ) + 1) := by
            -- Use: log(x)·(1+log(x)) ≤ 6·√x (atkinson_log_mul_succ_le_sqrt)
            -- Then: 2·Crow·√N·6·√(N+1) ≤ 12·Crow·√(N+1)·√(N+1) = 12·Crow·(N+1)
            have hNge2 : 2 ≤ (↑N : ℝ) + 1 := by exact_mod_cast show 2 ≤ N + 1 by omega
            have hNp : 0 ≤ (↑N : ℝ) + 1 := by positivity
            have hkey := atkinson_log_mul_succ_le_sqrt hNge2
            have hsqrt_le := Real.sqrt_le_sqrt (show (↑N : ℝ) ≤ (↑N : ℝ) + 1 by linarith)
            -- 2*Crow*√N*log*(1+log) ≤ 2*Crow*√(N+1)*6*√(N+1) = 12*Crow*(N+1)
            have h1 : Real.sqrt (↑N : ℝ) * (Real.log ((↑N : ℝ) + 1) * (1 + Real.log ((↑N : ℝ) + 1)))
                ≤ Real.sqrt ((↑N : ℝ) + 1) * (6 * Real.sqrt ((↑N : ℝ) + 1)) :=
              mul_le_mul hsqrt_le hkey (by nlinarith [Real.log_nonneg (show (1:ℝ) ≤ ↑N + 1 by linarith)])
                (Real.sqrt_nonneg _)
            nlinarith [Real.sq_sqrt hNp]

private theorem atkinson_large_modes_complete_near_band_bound_atomic
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    ∃ N0 : ℕ, ∃ C_complete > 0, ∀ M : ℕ, N0 ≤ M →
      ∀ T : ℝ, T ≥ 2 →
        |∑ n ∈ Finset.Ico M (hardyN T - 1),
            atkinsonModeWeight n *
              ∫ t in Ioc (hardyStart (n + 1))
                (hardyStart (min (2 * n + 1) (hardyN T - 1))), hardyCos n t|
          ≤ C_complete * ((↑(hardyN T) : ℝ) + 1) := by
  obtain ⟨N0s, Cs, hCs, hs⟩ := atkinson_large_modes_complete_near_band_sqrtlog_bound_atomic
  let N0 : ℕ := max N0s 1
  refine ⟨N0, Cs, hCs, ?_⟩
  intro M hM T hT
  set N : ℕ := hardyN T
  by_cases hEmpty : N - 1 ≤ M
  · have hnonneg : 0 ≤ Cs * ((↑N : ℝ) + 1) := by
      positivity
    have hIco : Finset.Ico M (N - 1) = ∅ := by
      ext x
      simp [Finset.mem_Ico, hEmpty]
    rw [show Finset.Ico M (N - 1) = ∅ from hIco, Finset.sum_empty, abs_zero]
    exact hnonneg
  · have hM_s : N0s ≤ M := le_trans (le_max_left _ _) hM
    have hM_one : 1 ≤ M := le_trans (le_max_right _ _) hM
    have hs_bound :
        |∑ n ∈ Finset.Ico M (N - 1),
            atkinsonModeWeight n *
              ∫ t in Ioc (hardyStart (n + 1))
                (hardyStart (min (2 * n + 1) (N - 1))), hardyCos n t|
          ≤ Cs * ((↑N : ℝ) + 1) := by
      simpa [N] using hs M hM_s T hT
    have hN_ge : M + 2 ≤ N := by
      omega
    have hNplus_ge_two : 2 ≤ (↑N : ℝ) + 1 := by
      have hNat : 1 ≤ N := by omega
      exact_mod_cast Nat.succ_le_succ hNat
    have hlog_le :
        Real.log ((↑N : ℝ) + 1) ≤ Real.sqrt ((↑N : ℝ) + 1) :=
      atkinson_log_le_sqrt_of_ge_two hNplus_ge_two
    have hsqrt_mono :
        Real.sqrt (↑N : ℝ) ≤ Real.sqrt ((↑N : ℝ) + 1) := by
      refine Real.sqrt_le_sqrt ?_
      linarith
    have hfac_nonneg : 0 ≤ 1 + Real.log ((↑N : ℝ) + 1) := by
      have hlog_nonneg : 0 ≤ Real.log ((↑N : ℝ) + 1) := by
        exact Real.log_nonneg (by linarith)
      linarith
    have hsqrt_one : 1 ≤ Real.sqrt ((↑N : ℝ) + 1) := by
      exact (Real.one_le_sqrt).2 (by linarith)
    have hfac :
        1 + Real.log ((↑N : ℝ) + 1) ≤ 2 * Real.sqrt ((↑N : ℝ) + 1) := by
      linarith
    have hprod :
        Real.sqrt (↑N : ℝ) * (1 + Real.log ((↑N : ℝ) + 1)) ≤ 2 * ((↑N : ℝ) + 1) := by
      calc
        Real.sqrt (↑N : ℝ) * (1 + Real.log ((↑N : ℝ) + 1))
            ≤ Real.sqrt ((↑N : ℝ) + 1) * (1 + Real.log ((↑N : ℝ) + 1)) := by
              exact mul_le_mul_of_nonneg_right hsqrt_mono hfac_nonneg
        _ ≤ Real.sqrt ((↑N : ℝ) + 1) * (2 * Real.sqrt ((↑N : ℝ) + 1)) := by
              exact mul_le_mul_of_nonneg_left hfac (Real.sqrt_nonneg _)
        _ = 2 * ((↑N : ℝ) + 1) := by
              ring_nf
              rw [Real.sq_sqrt]
              · ring
              · positivity
    exact hs_bound

private theorem atkinson_large_modes_prefix_near_tail_bound_atomic :
    ∃ N0 : ℕ, ∃ C_prefix > 0, ∀ M : ℕ, N0 ≤ M →
      ∀ T : ℝ, T ≥ 2 →
        |∑ n ∈ Finset.Ico M (hardyN T - 1),
            atkinsonModeWeight n *
              ∫ t in Ioc (hardyStart (min (2 * n + 1) (hardyN T - 1)))
                (min T (hardyStart (2 * n + 1))), hardyCos n t|
          ≤ C_prefix * ((↑(hardyN T) : ℝ) + 1) := by
  obtain ⟨K₁, hTail⟩ := atkinson_global_mode_tail_vdc_bound
  let N0 : ℕ := max K₁ 1
  refine ⟨N0, 24, by positivity, ?_⟩
  intro M hM T hT
  set N : ℕ := hardyN T
  by_cases hEmpty : N - 1 ≤ M
  · have hnonneg : 0 ≤ (24 : ℝ) * ((↑N : ℝ) + 1) := by positivity
    have hIco : Finset.Ico M (N - 1) = ∅ := by
      ext x
      simp [Finset.mem_Ico, hEmpty]
    simpa [N, hIco] using hnonneg
  · have hT_nonneg : 0 ≤ T := by linarith
    have hM_ge_K₁ : K₁ ≤ M := le_trans (le_max_left _ _) hM
    have hN_ge_K₁ : K₁ ≤ N - 1 := by omega
    have hN_pos : 1 ≤ N := by omega
    have hsum_bound :
        ∑ n ∈ Finset.Ico M (N - 1),
            12 * Real.sqrt (↑N : ℝ) / (((N - n - 1 : ℕ) : ℝ))
          ≤
        12 * Real.sqrt (↑N : ℝ) * (1 + Real.log ((↑N : ℝ) + 1)) := by
      let L : ℕ := N - 1 - M
      have hL_pos : 1 ≤ L := by
        dsimp [L]
        omega
      calc
        ∑ n ∈ Finset.Ico M (N - 1),
            12 * Real.sqrt (↑N : ℝ) / (((N - n - 1 : ℕ) : ℝ))
            =
          ∑ q ∈ Finset.range L,
            12 * Real.sqrt (↑N : ℝ) / (((L - q : ℕ) : ℝ)) := by
              rw [Finset.sum_Ico_eq_sum_range]
              refine Finset.sum_congr rfl ?_
              intro q hq
              have hq_lt : q < L := Finset.mem_range.mp hq
              have hnat : N - (M + q) - 1 = L - q := by
                dsimp [L]
                omega
              simp [hnat, add_assoc, add_left_comm, add_comm]
        _ = ∑ q ∈ Finset.range L,
              12 * Real.sqrt (↑N : ℝ) / (((q + 1 : ℕ) : ℝ)) := by
                calc
                  ∑ q ∈ Finset.range L,
                      12 * Real.sqrt (↑N : ℝ) / (((L - q : ℕ) : ℝ))
                      =
                    ∑ q ∈ Finset.range L,
                      12 * Real.sqrt (↑N : ℝ) / ((((L - 1 - q : ℕ) + 1 : ℕ) : ℝ)) := by
                        refine Finset.sum_congr rfl ?_
                        intro q hq
                        have hq_lt : q < L := Finset.mem_range.mp hq
                        have hnat : L - q = (L - 1 - q) + 1 := by omega
                        simp [hnat]
                  _ = ∑ q ∈ Finset.range L,
                        12 * Real.sqrt (↑N : ℝ) / (((q + 1 : ℕ) : ℝ)) := by
                          simpa using
                            (Finset.sum_range_reflect
                              (fun q => 12 * Real.sqrt (↑N : ℝ) / (((q + 1 : ℕ) : ℝ))) L)
        _ = (12 * Real.sqrt (↑N : ℝ)) *
              ∑ q ∈ Finset.range L, (1 : ℝ) / (((q + 1 : ℕ) : ℝ)) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro q hq
                ring
        _ = (12 * Real.sqrt (↑N : ℝ)) * (harmonic L : ℝ) := by
              congr 1
              norm_num [harmonic, one_div]
        _ ≤ (12 * Real.sqrt (↑N : ℝ)) * (1 + Real.log (L : ℝ)) := by
              refine mul_le_mul_of_nonneg_left ?_ ?_
              · simpa using
                  (harmonic_floor_le_one_add_log (L : ℝ) (by exact_mod_cast hL_pos))
              · positivity
        _ ≤ (12 * Real.sqrt (↑N : ℝ)) * (1 + Real.log ((↑N : ℝ) + 1)) := by
              have hcast_le : (L : ℝ) ≤ (↑N : ℝ) + 1 := by
                have hnat : L ≤ N + 1 := by
                  dsimp [L]
                  omega
                exact_mod_cast hnat
              have hlog :
                  Real.log (L : ℝ) ≤ Real.log ((↑N : ℝ) + 1) := by
                exact Real.log_le_log (by positivity) hcast_le
              have hcoeff_nonneg : 0 ≤ 12 * Real.sqrt (↑N : ℝ) := by positivity
              nlinarith
    have hprod :
        Real.sqrt (↑N : ℝ) * (1 + Real.log ((↑N : ℝ) + 1))
          ≤ 2 * ((↑N : ℝ) + 1) := by
      have hNplus_ge_two : 2 ≤ (↑N : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ hN_pos
      have hlog_le :
          Real.log ((↑N : ℝ) + 1) ≤ Real.sqrt ((↑N : ℝ) + 1) :=
        atkinson_log_le_sqrt_of_ge_two hNplus_ge_two
      have hsqrt_mono :
          Real.sqrt (↑N : ℝ) ≤ Real.sqrt ((↑N : ℝ) + 1) := by
        refine Real.sqrt_le_sqrt ?_
        linarith
      have hfac_nonneg : 0 ≤ 1 + Real.log ((↑N : ℝ) + 1) := by
        have hlog_nonneg : 0 ≤ Real.log ((↑N : ℝ) + 1) := by
          exact Real.log_nonneg (by linarith)
        linarith
      have hfac :
          1 + Real.log ((↑N : ℝ) + 1) ≤ 2 * Real.sqrt ((↑N : ℝ) + 1) := by
        have hsqrt_one : 1 ≤ Real.sqrt ((↑N : ℝ) + 1) := by
          exact (Real.one_le_sqrt).2 (by linarith)
        linarith
      calc
        Real.sqrt (↑N : ℝ) * (1 + Real.log ((↑N : ℝ) + 1))
            ≤ Real.sqrt ((↑N : ℝ) + 1) * (1 + Real.log ((↑N : ℝ) + 1)) := by
                exact mul_le_mul_of_nonneg_right hsqrt_mono hfac_nonneg
        _ ≤ Real.sqrt ((↑N : ℝ) + 1) * (2 * Real.sqrt ((↑N : ℝ) + 1)) := by
              exact mul_le_mul_of_nonneg_left hfac (Real.sqrt_nonneg _)
        _ = 2 * ((↑N : ℝ) + 1) := by
              ring_nf
              rw [Real.sq_sqrt]
              · ring
              · positivity
    calc
      |∑ n ∈ Finset.Ico M (N - 1),
          atkinsonModeWeight n *
            ∫ t in Ioc (hardyStart (min (2 * n + 1) (N - 1)))
              (min T (hardyStart (2 * n + 1))), hardyCos n t|
        ≤
      ∑ n ∈ Finset.Ico M (N - 1),
        |atkinsonModeWeight n *
          ∫ t in Ioc (hardyStart (min (2 * n + 1) (N - 1)))
            (min T (hardyStart (2 * n + 1))), hardyCos n t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤
        ∑ n ∈ Finset.Ico M (N - 1),
          12 * Real.sqrt (↑N : ℝ) / (((N - n - 1 : ℕ) : ℝ)) := by
            refine Finset.sum_le_sum ?_
            intro n hn
            have hnN : n < N - 1 := (Finset.mem_Ico.mp hn).2
            have hweight_nonneg : 0 ≤ atkinsonModeWeight n := atkinsonModeWeight_nonneg n
            rw [abs_mul, abs_of_nonneg hweight_nonneg]
            by_cases hlow : 2 * n + 1 ≤ N - 1
            · have hstart : hardyStart (2 * n + 1) ≤ T := by
                exact (hardyN_lt_iff (2 * n + 1) T hT_nonneg).1 (by omega)
              have hzero :
                  ∫ t in Ioc (hardyStart (min (2 * n + 1) (N - 1)))
                    (min T (hardyStart (2 * n + 1))), hardyCos n t = 0 := by
                rw [Nat.min_eq_left hlow, min_eq_right hstart]
                simp
              have hnonneg :
                  0 ≤ 12 * Real.sqrt (↑N : ℝ) / (((N - n - 1 : ℕ) : ℝ)) := by
                positivity
              simpa [hzero] using hnonneg
            · have hhigh : N ≤ 2 * n + 1 := by omega
              have hpred_lt : N - 1 < N := by omega
              have hstartNpred : hardyStart (N - 1) ≤ T := by
                exact (hardyN_lt_iff (N - 1) T hT_nonneg).1 hpred_lt
              have hstart_not : ¬ hardyStart (2 * n + 1) ≤ T := by
                intro hstart
                have : 2 * n + 1 < N := (hardyN_lt_iff (2 * n + 1) T hT_nonneg).2 hstart
                omega
              have htail :
                  |∫ t in Ioc (hardyStart (N - 1)) T, hardyCos n t|
                    ≤ 6 / Real.log ((↑N : ℝ) / ((n : ℝ) + 1)) := by
                have hNcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
                  exact_mod_cast Nat.sub_add_cancel hN_pos
                simpa [hNcast] using hTail (N - 1) n (by omega) hN_ge_K₁ T hstartNpred
              have hratio_gt : 1 < (↑N : ℝ) / ((n : ℝ) + 1) := by
                rw [one_lt_div (by positivity)]
                exact_mod_cast (by omega : n + 1 < N)
              have hlog_lower :
                  (((N - n - 1 : ℕ) : ℝ) / (↑N : ℝ))
                    ≤ Real.log ((↑N : ℝ) / ((n : ℝ) + 1)) := by
                have hx_pos : 0 < (↑N : ℝ) / ((n : ℝ) + 1) := by positivity
                have hbase :
                    1 - (((↑N : ℝ) / ((n : ℝ) + 1))⁻¹)
                      ≤ Real.log ((↑N : ℝ) / ((n : ℝ) + 1)) :=
                  Real.one_sub_inv_le_log_of_pos hx_pos
                have hleft :
                    1 - (((↑N : ℝ) / ((n : ℝ) + 1))⁻¹)
                      =
                    (((N - n - 1 : ℕ) : ℝ) / (↑N : ℝ)) := by
                  have hN_ne : (↑N : ℝ) ≠ 0 := by positivity
                  have hsub :
                      (((N - n - 1 : ℕ) : ℝ))
                        =
                      (↑N : ℝ) - ((n : ℝ) + 1) := by
                    have hle : n + 1 ≤ N := by omega
                    have hnat : N - n - 1 = N - (n + 1) := by omega
                    rw [hnat, Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]
                  calc
                    1 - (((↑N : ℝ) / ((n : ℝ) + 1))⁻¹)
                        = 1 - (((n : ℝ) + 1) / (↑N : ℝ)) := by
                          field_simp [hN_ne]
                    _ = ((↑N : ℝ) - ((n : ℝ) + 1)) / (↑N : ℝ) := by
                          field_simp [hN_ne]
                    _ = (((N - n - 1 : ℕ) : ℝ) / (↑N : ℝ)) := by
                          rw [hsub]
                rw [hleft] at hbase
                exact hbase
              have hlog_inv :
                  (1 : ℝ) / Real.log ((↑N : ℝ) / ((n : ℝ) + 1))
                    ≤
                  (↑N : ℝ) / (((N - n - 1 : ℕ) : ℝ)) := by
                have hnum_pos : 0 < (((N - n - 1 : ℕ) : ℝ)) := by
                  exact_mod_cast (by omega : 0 < N - n - 1)
                have hfrac_pos : 0 < (((N - n - 1 : ℕ) : ℝ) / (↑N : ℝ)) := by
                  exact div_pos hnum_pos (by positivity)
                calc
                  (1 : ℝ) / Real.log ((↑N : ℝ) / ((n : ℝ) + 1))
                      ≤ 1 / ((((N - n - 1 : ℕ) : ℝ) / (↑N : ℝ))) := by
                          exact one_div_le_one_div_of_le hfrac_pos hlog_lower
                  _ = (↑N : ℝ) / (((N - n - 1 : ℕ) : ℝ)) := by
                        field_simp
              have hweight_bound :
                  atkinsonModeWeight n *
                      ((↑N : ℝ) / (((N - n - 1 : ℕ) : ℝ)))
                    ≤
                  2 * Real.sqrt (↑N : ℝ) / (((N - n - 1 : ℕ) : ℝ)) := by
                calc
                  atkinsonModeWeight n * ((↑N : ℝ) / (((N - n - 1 : ℕ) : ℝ)))
                      =
                    (atkinsonModeWeight n * ((n : ℝ) + 1)) *
                      (((↑N : ℝ) / ((n : ℝ) + 1)) / (((N - n - 1 : ℕ) : ℝ))) := by
                        have hnp1_ne : ((n : ℝ) + 1) ≠ 0 := by positivity
                        field_simp [hnp1_ne]
                  _ =
                    Real.sqrt (n + 1) *
                      (((↑N : ℝ) / ((n : ℝ) + 1)) / (((N - n - 1 : ℕ) : ℝ))) := by
                        rw [atkinsonModeWeight_mul_succ_eq_sqrt]
                  _ ≤ Real.sqrt (n + 1) * (2 / (((N - n - 1 : ℕ) : ℝ))) := by
                        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
                        have hratio_le : (↑N : ℝ) / ((n : ℝ) + 1) ≤ 2 := by
                          have hNle : (↑N : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
                            exact_mod_cast (by omega : N ≤ 2 * (n + 1))
                          exact (_root_.div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2 hNle
                        exact div_le_div_of_nonneg_right hratio_le (by positivity)
                  _ ≤ Real.sqrt (↑N : ℝ) * (2 / (((N - n - 1 : ℕ) : ℝ))) := by
                        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                        exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : n + 1 ≤ N))
                  _ = 2 * Real.sqrt (↑N : ℝ) / (((N - n - 1 : ℕ) : ℝ)) := by
                        ring
              calc
                atkinsonModeWeight n *
                    |∫ t in Ioc (hardyStart (min (2 * n + 1) (N - 1)))
                      (min T (hardyStart (2 * n + 1))), hardyCos n t|
                    =
                  atkinsonModeWeight n *
                    |∫ t in Ioc (hardyStart (N - 1)) T, hardyCos n t| := by
                      rw [Nat.min_eq_right (by omega), min_eq_left (le_of_not_ge hstart_not)]
                _ ≤ atkinsonModeWeight n * (6 / Real.log ((↑N : ℝ) / ((n : ℝ) + 1))) := by
                      exact mul_le_mul_of_nonneg_left htail hweight_nonneg
                _ = 6 * (atkinsonModeWeight n *
                      ((1 : ℝ) / Real.log ((↑N : ℝ) / ((n : ℝ) + 1)))) := by
                      ring
                _ ≤ 6 * (2 * Real.sqrt (↑N : ℝ) / (((N - n - 1 : ℕ) : ℝ))) := by
                      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                      calc
                        atkinsonModeWeight n *
                            ((1 : ℝ) / Real.log ((↑N : ℝ) / ((n : ℝ) + 1)))
                            ≤
                          atkinsonModeWeight n *
                            ((↑N : ℝ) / (((N - n - 1 : ℕ) : ℝ))) := by
                              exact mul_le_mul_of_nonneg_left hlog_inv hweight_nonneg
                        _ ≤ 2 * Real.sqrt (↑N : ℝ) / (((N - n - 1 : ℕ) : ℝ)) :=
                            hweight_bound
                _ = 12 * Real.sqrt (↑N : ℝ) / (((N - n - 1 : ℕ) : ℝ)) := by
                      ring
      _ ≤ 12 * Real.sqrt (↑N : ℝ) * (1 + Real.log ((↑N : ℝ) + 1)) := hsum_bound
      _ ≤ 24 * ((↑N : ℝ) + 1) := by
            nlinarith [hprod]
      _ = (24 : ℝ) * ((↑N : ℝ) + 1) := by ring

private theorem atkinson_large_modes_near_tail_bound_atomic
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    ∃ N0 : ℕ, ∃ C_near > 0, ∀ M : ℕ, N0 ≤ M →
      ∀ T : ℝ, T ≥ 2 →
        |∑ n ∈ Finset.Ico M (hardyN T - 1),
            atkinsonModeWeight n *
              ∫ t in Ioc (hardyStart (n + 1))
                (min T (hardyStart (2 * n + 1))), hardyCos n t|
          ≤ C_near * ((↑(hardyN T) : ℝ) + 1) := by
  obtain ⟨N0c, Cc, hCc, hcomplete⟩ := atkinson_large_modes_complete_near_band_bound_atomic
  obtain ⟨N0p, Cp, hCp, hprefix⟩ := atkinson_large_modes_prefix_near_tail_bound_atomic
  let N0 := max N0c N0p
  refine ⟨N0, Cc + Cp, by positivity, ?_⟩
  intro M hM T hT
  set N : ℕ := hardyN T
  set completeTerm : ℝ :=
    ∑ n ∈ Finset.Ico M (N - 1),
      atkinsonModeWeight n *
        ∫ t in Ioc (hardyStart (n + 1))
          (hardyStart (min (2 * n + 1) (N - 1))), hardyCos n t
  set prefixTerm : ℝ :=
    ∑ n ∈ Finset.Ico M (N - 1),
      atkinsonModeWeight n *
        ∫ t in Ioc (hardyStart (min (2 * n + 1) (N - 1)))
          (min T (hardyStart (2 * n + 1))), hardyCos n t
  have hcomplete_bound : |completeTerm| ≤ Cc * ((↑N : ℝ) + 1) := by
    simpa [completeTerm, N] using hcomplete M (le_trans (le_max_left _ _) hM) T hT
  have hprefix_bound : |prefixTerm| ≤ Cp * ((↑N : ℝ) + 1) := by
    simpa [prefixTerm, N] using hprefix M (le_trans (le_max_right _ _) hM) T hT
  have hsplit :
      ∑ n ∈ Finset.Ico M (N - 1),
          atkinsonModeWeight n *
            ∫ t in Ioc (hardyStart (n + 1))
              (min T (hardyStart (2 * n + 1))), hardyCos n t
        = completeTerm + prefixTerm := by
    calc
      ∑ n ∈ Finset.Ico M (N - 1),
          atkinsonModeWeight n *
            ∫ t in Ioc (hardyStart (n + 1))
              (min T (hardyStart (2 * n + 1))), hardyCos n t
        =
      ∑ n ∈ Finset.Ico M (N - 1),
          ((atkinsonModeWeight n *
                ∫ t in Ioc (hardyStart (n + 1))
                  (hardyStart (min (2 * n + 1) (N - 1))), hardyCos n t)
            +
              (atkinsonModeWeight n *
                ∫ t in Ioc (hardyStart (min (2 * n + 1) (N - 1)))
                  (min T (hardyStart (2 * n + 1))), hardyCos n t)) := by
                refine Finset.sum_congr rfl ?_
                intro n hn
                have hnN : n < N - 1 := (Finset.mem_Ico.mp hn).2
                have hac_nat : n + 1 ≤ min (2 * n + 1) (N - 1) := by omega
                have hT_nonneg : 0 ≤ T := by linarith
                have hNpred_lt : N - 1 < N := by omega
                have hstartNpred : hardyStart (N - 1) ≤ T :=
                  (hardyN_lt_iff (N - 1) T hT_nonneg).1 hNpred_lt
                have hab :
                    hardyStart (n + 1) ≤ hardyStart (min (2 * n + 1) (N - 1)) := by
                  exact hardyStart_mono hac_nat
                have hbc :
                    hardyStart (min (2 * n + 1) (N - 1)) ≤ min T (hardyStart (2 * n + 1)) := by
                  refine le_min ?_ ?_
                  · exact le_trans (hardyStart_mono (Nat.min_le_right _ _)) hstartNpred
                  · exact hardyStart_mono (Nat.min_le_left _ _)
                exact atkinson_weighted_ioc_integral_split n hab hbc
      _ = completeTerm + prefixTerm := by
            have hsumfg :
                (∑ n ∈ Finset.Ico M (N - 1),
                    ((atkinsonModeWeight n *
                          ∫ t in Ioc (hardyStart (n + 1))
                            (hardyStart (min (2 * n + 1) (N - 1))), hardyCos n t)
                      +
                        (atkinsonModeWeight n *
                          ∫ t in Ioc (hardyStart (min (2 * n + 1) (N - 1)))
                            (min T (hardyStart (2 * n + 1))), hardyCos n t)))
                  =
                (∑ n ∈ Finset.Ico M (N - 1),
                    atkinsonModeWeight n *
                      ∫ t in Ioc (hardyStart (n + 1))
                        (hardyStart (min (2 * n + 1) (N - 1))), hardyCos n t)
                  +
                ∑ n ∈ Finset.Ico M (N - 1),
                    atkinsonModeWeight n *
                      ∫ t in Ioc (hardyStart (min (2 * n + 1) (N - 1)))
                        (min T (hardyStart (2 * n + 1))), hardyCos n t := by
                  rw [Finset.sum_add_distrib]
            simpa [completeTerm, prefixTerm] using hsumfg
  calc
    |∑ n ∈ Finset.Ico M (N - 1),
        atkinsonModeWeight n *
          ∫ t in Ioc (hardyStart (n + 1))
            (min T (hardyStart (2 * n + 1))), hardyCos n t|
      = |completeTerm + prefixTerm| := by rw [hsplit]
    _ ≤ |completeTerm| + |prefixTerm| := abs_add_le _ _
    _ ≤ Cc * ((↑N : ℝ) + 1) + Cp * ((↑N : ℝ) + 1) := by
          exact add_le_add hcomplete_bound hprefix_bound
    _ = (Cc + Cp) * ((↑N : ℝ) + 1) := by ring

/-! ## Section 3: Atkinson weighted sum bound

The deep analytical content: the weighted sum of per-mode cosine integrals
satisfies a signed cancellation bound.

|Σ_{n<N} (n+1)^{-1/2} · ∫_{hardyStart(n)}^T cos(θ(t) - t·log(n+1)) dt|
≤ C · (N + 1)

PROOF STRUCTURE (Atkinson 1949):
1. Fubini: ∫ MainTerm = 2 Σ (n+1)^{-1/2} ∫ cos(φ_n) — PROVED (hardySum_integral_eq)
2. Per-mode stationary phase evaluation:
   I_n = (-1)^{n+1} · c₀ · (n+1) + R_n, |R_n| ≤ C_rem · √(n+1)
   — Uses Stirling for θ at 2π(n+1)² + Fresnel evaluation + VdC tail
   — cos(π(n+1)²) = (-1)^{n+1} PROVED in CosPiSqSign
3. After weighting by (n+1)^{-1/2}:
   (n+1)^{-1/2} · I_n = (-1)^{n+1} · c₀ · √(n+1) + r_n, |r_n| ≤ C_rem
4. Signed sum: |Σ (-1)^{n+1} c₀ √(n+1)| ≤ c₀·√N — Abel bound (PROVED)
5. Remainder sum: |Σ r_n| ≤ C_rem·N — triangle inequality
6. Assembly: c₀·√N + C_rem·N ≤ (c₀+C_rem)·(N+1)

NOTE: A previous version had `per_mode_weighted_bound` claiming
(n+1)^{-1/2} · |I_n| ≤ B uniformly. This is FALSE: the Fresnel integral
at the stationary point t₀ = 2π(n+1)² gives I_n = Θ(n+1), so the
weighted ABSOLUTE value is Θ(√(n+1)), not O(1). The correct bound
requires signed cancellation across modes (Atkinson's key insight).
-/

/- **Atkinson weighted sum bound**: the weighted sum of per-mode cosine
    integrals satisfies |Σ (n+1)^{-1/2} · ∫ hardyCos n| ≤ C · (N+1).

    This is the analytical heart of the Atkinson formula.
    The per-mode integrals are NOT individually O(√(n+1)) after weighting —
    they grow as Θ(√(n+1)) — but the signed alternation gives cancellation.

    The proof uses:
    (a) Stationary phase: I_n = (-1)^{n+1} c₀(n+1) + O(√(n+1))
        - cos(π(n+1)²) = (-1)^{n+1}  (PROVED: CosPiSqSign)
        - Fresnel evaluation near t₀ = 2π(n+1)²
        - VdC first derivative tail
    (b) After (n+1)^{-1/2} weight: signed sum + O(1) remainders
    (c) Abel alternating bound on √(n+1) terms (PROVED above)
    (d) Triangle inequality on O(1) remainders

    Reference: Atkinson 1949, Acta Math. 81; Titchmarsh 1951 §4.15. -/
/-!
### Per-mode decomposition gap analysis

The O(N+1) bound decomposes via block structure:

  S = Σ w_n I_n = [diagonal] + [off-diagonal tails]

**Diagonal** (resonant block integrals): PROVABLE as O(N).
  - `hardyCos_firstBlock_anchor_main_term_eventually` (StationaryPhaseMainMode)
    gives w_n·J_n = completeModeTarget(n) + O(1) for n ≥ N0.
  - `completeModeTarget_sum_bound_range` (StationaryPhaseDecomposition)
    gives |Σ completeModeTarget| ≤ K·√N via Abel alternating cancellation.
  - Small modes (n < N0) bounded by `small_modes_weighted_sum_bound`.
  - Total diagonal: O(√N) + O(N) + O(1) = O(N).

**Off-diagonal tails** (mode n on blocks k > n): BOTTLENECK.
  - VdC first derivative gives |tail of mode n| ≤ 3/(φ'_n(hardyStart(n+1)))
    ≈ 3(n+1). After weighting: O(√(n+1)). Sum: O(N^{3/2}).
  - VdC second derivative gives |tail of mode n| ≤ 8/√(θ''(T))
    ≈ C·(N+1). After weighting: O(N/√(n+1)). Sum: O(N^{3/2}).
  - The TRUE bound is O(1) after weighting (from Fresnel evaluation
    precision), but requires quantitative control on θ''' that is not
    in the codebase.

**Needed**: A Fresnel tail bound showing that for n ≥ N0,
  |w_n · ∫_{hardyStart(n+1)}^T hardyCos n t dt| ≤ C_tail,
  i.e., the off-resonant tail grows as O(√(n+1)), not O(n+1).
  This follows from the stationary phase remainder estimate and
  requires θ(t) = (t/2)log(t/(2π)) - t/2 - π/8 + O(1/t) precision.

Reference: Atkinson 1949, Acta Math. 81, §3 (evaluation of R_n).
-/

/-- Atomic Atkinson leaf: the signed weighted Hardy cosine sum is `O(hardyN T)`.

    This is the exact field needed by
    `HardyCosIntegralAlternatingSqrtDecompositionHyp`. The remaining gap is
    therefore the raw weighted-sum estimate itself, not the class packaging. -/
private theorem atkinson_weighted_complete_block_bound
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    ∃ C_diag > 0, ∀ N : ℕ,
      |∑ n ∈ Finset.range N,
          atkinsonModeWeight n *
            ∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t|
        ≤ C_diag * ((N : ℝ) + 1) := by
  obtain ⟨C0, hC0, N0, hmain⟩ := atkinson_weighted_complete_block_resonant_eventually
  let blockTerm : ℕ → ℝ := fun n =>
    atkinsonModeWeight n * ∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t
  let Dhead : ℝ := 2 * Real.pi * (2 * (N0 : ℝ) + 3)
  let Chead : ℝ := (N0 : ℝ) * Dhead
  let Ktarget : ℝ := |atkinsonCompleteModeSlope| + 2 * |atkinsonCompleteModeOffset|
  let targetHead : ℝ := |∑ n ∈ Finset.range N0, atkinsonCompleteModeTarget n|
  refine ⟨Chead + Ktarget + targetHead + C0 + 1, by positivity, ?_⟩
  intro N
  have hDhead_nonneg : 0 ≤ Dhead := by
    dsimp [Dhead]
    positivity
  have hChead_nonneg : 0 ≤ Chead := by
    dsimp [Chead]
    positivity
  have hKtarget_nonneg : 0 ≤ Ktarget := by
    dsimp [Ktarget]
    positivity
  have htargetHead_nonneg : 0 ≤ targetHead := by
    dsimp [targetHead]
    positivity
  have hhead_bound :
      ∀ M : ℕ, M ≤ N0 → |∑ n ∈ Finset.range M, blockTerm n| ≤ Chead := by
    intro M hM
    calc
      |∑ n ∈ Finset.range M, blockTerm n|
          ≤ ∑ n ∈ Finset.range M, |blockTerm n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.range M, Dhead := by
            refine Finset.sum_le_sum ?_
            intro n hn
            have hnM : n < M := Finset.mem_range.mp hn
            have hnN0 : n < N0 := lt_of_lt_of_le hnM hM
            have hlen :
                |∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t|
                  ≤ Dhead := by
              calc
                |∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t|
                    ≤ hardyStart (n + 1) - hardyStart n :=
                      hardyCos_integral_abs_le_length n (hardyStart_mono (Nat.le_succ n))
                _ = 2 * Real.pi * (2 * (n : ℝ) + 3) := by
                      simpa using block_length n
                _ ≤ Dhead := by
                      have hcastn : (n : ℝ) ≤ (N0 : ℝ) := by
                        exact_mod_cast Nat.le_of_lt hnN0
                      dsimp [Dhead]
                      nlinarith [Real.pi_pos, hcastn]
            dsimp [blockTerm]
            rw [abs_mul, abs_of_nonneg (atkinsonModeWeight_nonneg n)]
            calc
              atkinsonModeWeight n *
                  |∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t|
                ≤ 1 * |∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t| := by
                    gcongr
                    exact atkinsonModeWeight_le_one n
              _ ≤ 1 * Dhead := by
                    gcongr
              _ = Dhead := by ring
      _ = (M : ℝ) * Dhead := by simp
      _ ≤ (N0 : ℝ) * Dhead := by
            have hcastM : (M : ℝ) ≤ (N0 : ℝ) := by
              exact_mod_cast hM
            nlinarith [hDhead_nonneg, hcastM]
      _ = Chead := by rfl
  have hsqrt_le (m : ℕ) : Real.sqrt m ≤ (m : ℝ) + 1 := by
    calc
      Real.sqrt m ≤ Real.sqrt (((m : ℝ) + 1) ^ 2) := by
        exact Real.sqrt_le_sqrt (by nlinarith : (m : ℝ) ≤ ((m : ℝ) + 1) ^ 2)
      _ = (m : ℝ) + 1 := by
        rw [Real.sqrt_sq_eq_abs]
        exact abs_of_nonneg (by positivity)
  by_cases hN : N ≤ N0
  · calc
      |∑ n ∈ Finset.range N, blockTerm n|
          ≤ Chead := hhead_bound N hN
      _ ≤ (Chead + Ktarget + targetHead + C0 + 1) * ((N : ℝ) + 1) := by
            have hone : 1 ≤ (N : ℝ) + 1 := by
              have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
              linarith
            nlinarith
  · have hN0N : N0 ≤ N := le_of_not_ge hN
    have hhead_small : |∑ n ∈ Finset.range N0, blockTerm n| ≤ Chead := hhead_bound N0 le_rfl
    have htarget_tail :
        |∑ n ∈ Finset.Ico N0 N, atkinsonCompleteModeTarget n|
          ≤ (Ktarget + targetHead) * ((N : ℝ) + 1) := by
      calc
        |∑ n ∈ Finset.Ico N0 N, atkinsonCompleteModeTarget n|
            = |∑ n ∈ Finset.range N, atkinsonCompleteModeTarget n
                - ∑ n ∈ Finset.range N0, atkinsonCompleteModeTarget n| := by
                  rw [Finset.sum_Ico_eq_sub atkinsonCompleteModeTarget hN0N]
        _ = |∑ n ∈ Finset.range N, atkinsonCompleteModeTarget n
              + (-(∑ n ∈ Finset.range N0, atkinsonCompleteModeTarget n))| := by ring_nf
        _ ≤ |∑ n ∈ Finset.range N, atkinsonCompleteModeTarget n|
              + |-(∑ n ∈ Finset.range N0, atkinsonCompleteModeTarget n)| := abs_add_le _ _
        _ = |∑ n ∈ Finset.range N, atkinsonCompleteModeTarget n|
              + |∑ n ∈ Finset.range N0, atkinsonCompleteModeTarget n| := by simp
        _ ≤ Ktarget * Real.sqrt N + targetHead := by
              nlinarith [atkinsonCompleteModeTarget_sum_bound_range N]
        _ ≤ Ktarget * ((N : ℝ) + 1) + targetHead := by
              gcongr
              exact hsqrt_le N
        _ ≤ (Ktarget + targetHead) * ((N : ℝ) + 1) := by
              have hone : 1 ≤ (N : ℝ) + 1 := by
                have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
                linarith
              nlinarith
    have herr_bound :
        |∑ n ∈ Finset.Ico N0 N, (blockTerm n - atkinsonCompleteModeTarget n)|
          ≤ C0 * ((N : ℝ) + 1) := by
      calc
        |∑ n ∈ Finset.Ico N0 N, (blockTerm n - atkinsonCompleteModeTarget n)|
            ≤ ∑ n ∈ Finset.Ico N0 N, |blockTerm n - atkinsonCompleteModeTarget n| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ Finset.Ico N0 N, C0 := by
              refine Finset.sum_le_sum ?_
              intro n hn
              exact hmain n (Finset.mem_Ico.mp hn).1
        _ = (Finset.Ico N0 N).card * C0 := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (N : ℝ) * C0 := by
              have hcard_le : (Finset.Ico N0 N).card ≤ N := by
                rw [Nat.card_Ico]
                omega
              have hcard_cast : ((Finset.Ico N0 N).card : ℝ) ≤ (N : ℝ) := by
                exact_mod_cast hcard_le
              nlinarith [hC0, hcard_cast]
        _ ≤ C0 * ((N : ℝ) + 1) := by
              nlinarith [hC0]
    have htail_split :
        ∑ n ∈ Finset.Ico N0 N, blockTerm n
          =
        (∑ n ∈ Finset.Ico N0 N, atkinsonCompleteModeTarget n)
          +
        ∑ n ∈ Finset.Ico N0 N, (blockTerm n - atkinsonCompleteModeTarget n) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro n hn
      ring
    have htail_bound :
        |∑ n ∈ Finset.Ico N0 N, blockTerm n|
          ≤ (Ktarget + targetHead + C0) * ((N : ℝ) + 1) := by
      calc
        |∑ n ∈ Finset.Ico N0 N, blockTerm n|
            = |(∑ n ∈ Finset.Ico N0 N, atkinsonCompleteModeTarget n)
                + ∑ n ∈ Finset.Ico N0 N, (blockTerm n - atkinsonCompleteModeTarget n)| := by
                  rw [htail_split]
        _ ≤ |∑ n ∈ Finset.Ico N0 N, atkinsonCompleteModeTarget n|
              + |∑ n ∈ Finset.Ico N0 N, (blockTerm n - atkinsonCompleteModeTarget n)| :=
                abs_add_le _ _
        _ ≤ (Ktarget + targetHead) * ((N : ℝ) + 1) + C0 * ((N : ℝ) + 1) := by
              nlinarith [htarget_tail, herr_bound]
        _ = (Ktarget + targetHead + C0) * ((N : ℝ) + 1) := by ring
    have hsplit_total :
        ∑ n ∈ Finset.range N, blockTerm n
          =
        (∑ n ∈ Finset.range N0, blockTerm n) + ∑ n ∈ Finset.Ico N0 N, blockTerm n := by
      simpa using (Finset.sum_range_add_sum_Ico blockTerm hN0N).symm
    calc
      |∑ n ∈ Finset.range N, blockTerm n|
          = |(∑ n ∈ Finset.range N0, blockTerm n) + ∑ n ∈ Finset.Ico N0 N, blockTerm n| := by
              rw [hsplit_total]
      _ ≤ |∑ n ∈ Finset.range N0, blockTerm n| + |∑ n ∈ Finset.Ico N0 N, blockTerm n| :=
            abs_add_le _ _
      _ ≤ Chead + (Ktarget + targetHead + C0) * ((N : ℝ) + 1) := by
            nlinarith [hhead_small, htail_bound]
      _ ≤ (Chead + Ktarget + targetHead + C0 + 1) * ((N : ℝ) + 1) := by
            have hone : 1 ≤ (N : ℝ) + 1 := by
              have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
              linarith
            nlinarith

/-- Remaining Atkinson leaf after the constructive complete-block reduction:
the post-first-block tail sum still needs the true stationary-phase remainder
control that is not yet in the imported infrastructure. -/
private theorem atkinson_weighted_tail_bound_atomic
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    ∃ C_tail > 0, ∀ T : ℝ, T ≥ 2 →
      |∑ n ∈ Finset.range (hardyN T - 1),
          atkinsonModeWeight n *
            ∫ t in Ioc (hardyStart (n + 1)) T, hardyCos n t|
        ≤ C_tail * ((↑(hardyN T) : ℝ) + 1) := by
  obtain ⟨N0near, Cnear, hCnear, hnear⟩ := atkinson_large_modes_near_tail_bound_atomic
  obtain ⟨Kfar, Cfar, hCfar, hfar⟩ := atkinson_large_modes_far_tail_bound
  let M0 : ℕ := max N0near Kfar
  obtain ⟨Csmall, hCsmall, hsmall⟩ := atkinson_small_modes_tail_bound M0
  refine ⟨Csmall + Cnear + Cfar, by positivity, ?_⟩
  intro T hT
  set N : ℕ := hardyN T
  let F : ℕ → ℝ := fun n =>
    atkinsonModeWeight n *
      ∫ t in Ioc (hardyStart (n + 1)) T, hardyCos n t
  by_cases hMN : M0 ≤ N - 1
  · set smallTerm : ℝ := ∑ n ∈ Finset.range M0, F n
    set largeTerm : ℝ := ∑ n ∈ Finset.Ico M0 (N - 1), F n
    set nearTerm : ℝ :=
      ∑ n ∈ Finset.Ico M0 (N - 1),
        atkinsonModeWeight n *
          ∫ t in Ioc (hardyStart (n + 1))
            (min T (hardyStart (2 * n + 1))), hardyCos n t
    set farTerm : ℝ :=
      ∑ n ∈ Finset.Ico M0 (N - 1),
        atkinsonModeWeight n *
          ∫ t in Ioc (min T (hardyStart (2 * n + 1))) T, hardyCos n t
    have hsmall_bound : |smallTerm| ≤ Csmall * ((↑N : ℝ) + 1) := by
      simpa [smallTerm, F, N, Nat.min_eq_left hMN] using hsmall T hT
    have hnear_bound : |nearTerm| ≤ Cnear * ((↑N : ℝ) + 1) := by
      simpa [nearTerm, N] using hnear M0 (le_max_left _ _) T hT
    have hfar_bound : |farTerm| ≤ Cfar * ((↑N : ℝ) + 1) := by
      simpa [farTerm, N] using hfar M0 (le_max_right _ _) T hT
    have hsplit_total :
        ∑ n ∈ Finset.range (N - 1), F n = smallTerm + largeTerm := by
      simpa [smallTerm, largeTerm] using
        (Finset.sum_range_add_sum_Ico F hMN).symm
    have hsplit_large : largeTerm = nearTerm + farTerm := by
      calc
        ∑ n ∈ Finset.Ico M0 (N - 1), F n
            =
        ∑ n ∈ Finset.Ico M0 (N - 1),
            ((atkinsonModeWeight n *
                  ∫ t in Ioc (hardyStart (n + 1))
                    (min T (hardyStart (2 * n + 1))), hardyCos n t)
              +
                (atkinsonModeWeight n *
                  ∫ t in Ioc (min T (hardyStart (2 * n + 1))) T, hardyCos n t)) := by
                  refine Finset.sum_congr rfl ?_
                  intro n hn
                  have hT_nonneg : 0 ≤ T := by linarith
                  have hnN : n < N - 1 := (Finset.mem_Ico.mp hn).2
                  have hstartn : hardyStart (n + 1) ≤ T := by
                    exact (hardyN_lt_iff (n + 1) T hT_nonneg).1 (by omega)
                  have hab : hardyStart (n + 1) ≤ min T (hardyStart (2 * n + 1)) := by
                    refine le_min hstartn ?_
                    exact hardyStart_mono (by omega)
                  have hbc : min T (hardyStart (2 * n + 1)) ≤ T := min_le_left _ _
                  exact atkinson_weighted_ioc_integral_split n hab hbc
        _ = nearTerm + farTerm := by
              have hsumfg :
                  (∑ n ∈ Finset.Ico M0 (N - 1),
                      ((atkinsonModeWeight n *
                            ∫ t in Ioc (hardyStart (n + 1))
                              (min T (hardyStart (2 * n + 1))), hardyCos n t)
                        +
                          (atkinsonModeWeight n *
                            ∫ t in Ioc (min T (hardyStart (2 * n + 1))) T, hardyCos n t)))
                    =
                  (∑ n ∈ Finset.Ico M0 (N - 1),
                      atkinsonModeWeight n *
                        ∫ t in Ioc (hardyStart (n + 1))
                          (min T (hardyStart (2 * n + 1))), hardyCos n t)
                    +
                  ∑ n ∈ Finset.Ico M0 (N - 1),
                      atkinsonModeWeight n *
                        ∫ t in Ioc (min T (hardyStart (2 * n + 1))) T, hardyCos n t := by
                    rw [Finset.sum_add_distrib]
              simpa [largeTerm, nearTerm, farTerm, F] using hsumfg
    calc
      |∑ n ∈ Finset.range (N - 1), F n|
          = |smallTerm + largeTerm| := by rw [hsplit_total]
      _ ≤ |smallTerm| + |largeTerm| := abs_add_le _ _
      _ = |smallTerm| + |nearTerm + farTerm| := by rw [hsplit_large]
      _ ≤ |smallTerm| + (|nearTerm| + |farTerm|) := by
            nlinarith [abs_add_le nearTerm farTerm]
      _ ≤ Csmall * ((↑N : ℝ) + 1) + (Cnear * ((↑N : ℝ) + 1) + Cfar * ((↑N : ℝ) + 1)) := by
            nlinarith [hsmall_bound, hnear_bound, hfar_bound]
      _ ≤ Csmall * ((↑N : ℝ) + 1) + (Cnear * ((↑N : ℝ) + 1) + Cfar * ((↑N : ℝ) + 1)) := by
            have hN1 : 1 ≤ (↑N : ℝ) + 1 := by exact_mod_cast show 1 ≤ N + 1 by omega
            have hNle : (↑N : ℝ) + 1 ≤ ((↑N : ℝ) + 1) := by nlinarith
            nlinarith
      _ = (Csmall + Cnear + Cfar) * ((↑N : ℝ) + 1) := by ring
  · have hsmall_bound :
        |∑ n ∈ Finset.range (N - 1), F n| ≤ Csmall * ((↑N : ℝ) + 1) := by
        have hmin : min M0 (N - 1) = N - 1 := Nat.min_eq_right (le_of_not_ge hMN)
        simpa [F, N, hmin] using hsmall T hT
    calc
      |∑ n ∈ Finset.range (N - 1), F n|
          ≤ Csmall * ((↑N : ℝ) + 1) := hsmall_bound
      _ ≤ Csmall * ((↑N : ℝ) + 1) := by
            have hN1 : 1 ≤ (↑N : ℝ) + 1 := by exact_mod_cast show 1 ≤ N + 1 by omega
            have hNle : (↑N : ℝ) + 1 ≤ ((↑N : ℝ) + 1) := by nlinarith
            nlinarith
      _ ≤ (Csmall + Cnear + Cfar) * ((↑N : ℝ) + 1) := by
            nlinarith [hCnear, hCfar, sq_nonneg ((↑N : ℝ) + 1)]

private theorem atkinson_weighted_sum_bound_atomic
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∑ n ∈ Finset.range (hardyN T),
        ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) *
          ∫ t in Ioc (hardyStart n) T, hardyCos n t|
      ≤ C * ((↑(hardyN T) : ℝ) + 1) := by
  obtain ⟨Cdiag, hCdiag, hdiag⟩ := atkinson_weighted_complete_block_bound
  obtain ⟨Ctail, hCtail, htail⟩ := atkinson_weighted_tail_bound_atomic
  refine ⟨Cdiag + Ctail + 6 * Real.pi, by positivity, ?_⟩
  intro T hT
  set N : ℕ := hardyN T
  let H : ℕ → ℝ := fun n =>
    atkinsonModeWeight n * ∫ t in Ioc (hardyStart n) T, hardyCos n t
  have hbound :
      |∑ n ∈ Finset.range N, H n| ≤ (Cdiag + Ctail + 6 * Real.pi) * ((↑N : ℝ) + 1) := by
    by_cases hN0 : N = 0
    · have hnonneg : 0 ≤ (Cdiag + Ctail + 6 * Real.pi) * ((↑N : ℝ) + 1) := by
        have hC_nonneg : 0 ≤ Cdiag + Ctail + 6 * Real.pi := by positivity
        positivity
      simpa [N, H, hN0] using hnonneg
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
      have hT_nonneg : 0 ≤ T := by linarith
      set completeTerm : ℝ :=
        ∑ n ∈ Finset.range (N - 1),
          atkinsonModeWeight n *
            ∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t
      set tailTerm : ℝ :=
        ∑ n ∈ Finset.range (N - 1),
          atkinsonModeWeight n *
            ∫ t in Ioc (hardyStart (n + 1)) T, hardyCos n t
      set prefixTerm : ℝ := H (N - 1)
      have hdiag_bound : |completeTerm| ≤ Cdiag * ((↑N : ℝ) + 1) := by
        have hdiag_raw :
            |∑ n ∈ Finset.range (N - 1),
                atkinsonModeWeight n *
                  ∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t|
              ≤ Cdiag * ((↑(N - 1) : ℝ) + 1) := by
          simpa using hdiag (N - 1)
        have hstep : Cdiag * ((↑(N - 1) : ℝ) + 1) ≤ Cdiag * ((↑N : ℝ) + 1) := by
          have hcast : ((↑(N - 1) : ℝ) + 1) ≤ ((↑N : ℝ) + 1) := by
            have hpred : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
              exact_mod_cast Nat.pred_le N
            linarith
          gcongr
        exact le_trans (by simpa [completeTerm] using hdiag_raw) hstep
      have htail_bound : |tailTerm| ≤ Ctail * ((↑N : ℝ) + 1) := by
        simpa [tailTerm, N] using htail T hT
      have hprefix_bound : |prefixTerm| ≤ (6 * Real.pi) * ((↑N : ℝ) + 1) := by
        have hstart_prev : hardyStart (N - 1) ≤ T := by
          exact (hardyN_lt_iff (N - 1) T hT_nonneg).1 (Nat.pred_lt hN0)
        have hnot_next : ¬ hardyStart N ≤ T := by
          intro hnext
          have : N < hardyN T := (hardyN_lt_iff N T hT_nonneg).2 hnext
          simpa [N] using this
        have hlen :
            |∫ t in Ioc (hardyStart (N - 1)) T, hardyCos (N - 1) t|
              ≤ hardyStart N - hardyStart (N - 1) := by
          calc
            |∫ t in Ioc (hardyStart (N - 1)) T, hardyCos (N - 1) t|
                ≤ T - hardyStart (N - 1) := hardyCos_integral_abs_le_length (N - 1) hstart_prev
            _ ≤ hardyStart N - hardyStart (N - 1) := by
                  have hnext_le : T ≤ hardyStart N := le_of_not_ge hnot_next
                  linarith
        have hblock :
            hardyStart N - hardyStart (N - 1) ≤ (6 * Real.pi) * ((↑N : ℝ) + 1) := by
          calc
            hardyStart N - hardyStart (N - 1)
                = 2 * Real.pi * (2 * ((N - 1 : ℕ) : ℝ) + 3) := by
                    simpa [Nat.sub_add_cancel hNpos] using block_length (N - 1)
            _ ≤ 2 * Real.pi * (3 * ((↑N : ℝ) + 1)) := by
                  have hlin : 2 * ((N - 1 : ℕ) : ℝ) + 3 ≤ 3 * ((↑N : ℝ) + 1) := by
                    have hpred : (((N - 1 : ℕ) : ℝ)) ≤ (N : ℝ) := by
                      exact_mod_cast Nat.pred_le N
                    nlinarith
                  gcongr
            _ = (6 * Real.pi) * ((↑N : ℝ) + 1) := by ring
        calc
          |prefixTerm|
              = |atkinsonModeWeight (N - 1) *
                  ∫ t in Ioc (hardyStart (N - 1)) T, hardyCos (N - 1) t| := by
                    simp [prefixTerm, H]
          _ ≤ atkinsonModeWeight (N - 1) * (hardyStart N - hardyStart (N - 1)) := by
                rw [abs_mul, abs_of_nonneg (atkinsonModeWeight_nonneg (N - 1))]
                exact mul_le_mul_of_nonneg_left hlen (atkinsonModeWeight_nonneg (N - 1))
          _ ≤ 1 * (hardyStart N - hardyStart (N - 1)) := by
                have hdiff_nonneg : 0 ≤ hardyStart N - hardyStart (N - 1) := by
                  exact sub_nonneg.mpr (hardyStart_mono (Nat.pred_le N))
                exact mul_le_mul_of_nonneg_right
                  (atkinsonModeWeight_le_one (N - 1)) hdiff_nonneg
          _ ≤ (6 * Real.pi) * ((↑N : ℝ) + 1) := by
                simpa using hblock
      have hsplit_prefix :
          ∑ n ∈ Finset.range (N - 1), H n = completeTerm + tailTerm := by
        calc
          ∑ n ∈ Finset.range (N - 1), H n
              =
          ∑ n ∈ Finset.range (N - 1),
              ((atkinsonModeWeight n *
                    ∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t)
                +
                  (atkinsonModeWeight n *
                    ∫ t in Ioc (hardyStart (n + 1)) T, hardyCos n t)) := by
                    refine Finset.sum_congr rfl ?_
                    intro n hn
                    have hstartn : hardyStart (n + 1) ≤ T := by
                      exact (hardyN_lt_iff (n + 1) T hT_nonneg).1 (by
                        have hnN : n < N - 1 := Finset.mem_range.mp hn
                        omega)
                    have hab : hardyStart n ≤ hardyStart (n + 1) := hardyStart_mono (Nat.le_succ n)
                    exact atkinson_weighted_ioc_integral_split n hab hstartn
          _ = completeTerm + tailTerm := by
                have hsumfg :
                    (∑ n ∈ Finset.range (N - 1),
                        ((atkinsonModeWeight n *
                              ∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t)
                          +
                            (atkinsonModeWeight n *
                              ∫ t in Ioc (hardyStart (n + 1)) T, hardyCos n t)))
                      =
                    (∑ n ∈ Finset.range (N - 1),
                        atkinsonModeWeight n *
                          ∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t)
                      +
                    ∑ n ∈ Finset.range (N - 1),
                        atkinsonModeWeight n *
                          ∫ t in Ioc (hardyStart (n + 1)) T, hardyCos n t := by
                      rw [Finset.sum_add_distrib]
                simpa [completeTerm, tailTerm, H] using hsumfg
      have hsum_total :
          ∑ n ∈ Finset.range N, H n = completeTerm + tailTerm + prefixTerm := by
        have hsum_succ :
            ∑ n ∈ Finset.range N, H n
              = ∑ n ∈ Finset.range (N - 1), H n + H (N - 1) := by
                simpa [Nat.sub_add_cancel hNpos] using (Finset.sum_range_succ H (N - 1))
        rw [hsum_succ, hsplit_prefix]
      calc
        |∑ n ∈ Finset.range N, H n|
            = |completeTerm + tailTerm + prefixTerm| := by rw [hsum_total]
        _ ≤ |completeTerm + tailTerm| + |prefixTerm| := abs_add_le _ _
        _ ≤ (|completeTerm| + |tailTerm|) + |prefixTerm| := by
              nlinarith [abs_add_le completeTerm tailTerm]
        _ ≤ Cdiag * ((↑N : ℝ) + 1) + Ctail * ((↑N : ℝ) + 1) + (6 * Real.pi) * ((↑N : ℝ) + 1) := by
              nlinarith [hdiag_bound, htail_bound, hprefix_bound]
        _ ≤ Cdiag * ((↑N : ℝ) + 1) + Ctail * ((↑N : ℝ) + 1) + (6 * Real.pi) * ((↑N : ℝ) + 1) := by
              have hN1 : 1 ≤ (↑N : ℝ) + 1 := by exact_mod_cast show 1 ≤ N + 1 by omega
              have hNle : (↑N : ℝ) + 1 ≤ ((↑N : ℝ) + 1) := by nlinarith
              nlinarith [Real.pi_pos]
        _ = (Cdiag + Ctail + 6 * Real.pi) * ((↑N : ℝ) + 1) := by ring
  simpa [H, N, atkinsonModeWeight] using hbound

/-- Canonical class-valued packaging of the Atkinson signed weighted-sum bound.

    This is now a thin wrapper around the atomic field-shaped theorem above. -/
private theorem atkinson_alternating_sqrt_decomposition_hyp
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    HardyFirstMomentWiring.HardyCosIntegralAlternatingSqrtDecompositionHyp := by
  exact ⟨atkinson_weighted_sum_bound_atomic⟩

/-- Wrapper exposing the exact weighted-sum statement used by the local
    `O(√T)` assembly. -/
private theorem atkinson_weighted_sum_bound
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∑ n ∈ Finset.range (hardyN T),
        ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) *
          ∫ t in Ioc (hardyStart n) T, hardyCos n t|
      ≤ C * ((↑(hardyN T) : ℝ) + 1) := by
  simpa using atkinson_weighted_sum_bound_atomic

/-- Assembly: the weighted sum bound gives the signed Fresnel bound
    on the MainTerm integral via the Fubini result. -/
private theorem atkinson_signed_fresnel_bound
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    ∃ C_atk > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, MainTerm t| ≤ C_atk * ((↑(hardyN T) : ℝ) + 1) := by
  obtain ⟨C, hC, h_sum⟩ := atkinson_weighted_sum_bound
  refine ⟨2 * C, by positivity, fun T hT => ?_⟩
  have hT1 : (1 : ℝ) ≤ T := by linarith
  -- Fubini: ∫ MainTerm = hardySumInt T = 2 · Σ weighted integrals
  have h_fubini : ∫ t in Ioc 1 T, MainTerm t = hardySumInt T := by
    rw [MainTerm_eq_hardySum]
    exact hardySum_integral_eq T hT1
  rw [h_fubini, hardySumInt]
  set N := hardyN T
  calc |2 * ∑ n ∈ Finset.range N,
        ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) *
          ∫ t in Ioc (hardyStart n) T, hardyCos n t|
      = 2 * |∑ n ∈ Finset.range N,
        ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) *
          ∫ t in Ioc (hardyStart n) T, hardyCos n t| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    _ ≤ 2 * (C * ((↑N : ℝ) + 1)) := by
        gcongr; exact h_sum T hT
    _ = 2 * C * ((↑N : ℝ) + 1) := by ring

/-! ## Section 4: Assembly -/

/-- **Atkinson evaluation**: |∫₁ᵀ MainTerm(t) dt| ≤ C_atk · (hardyN(T) + 1). -/
private theorem atkinson_integral_le_N
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    ∃ C_atk > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, MainTerm t| ≤ C_atk * ((↑(hardyN T) : ℝ) + 1) :=
  atkinson_signed_fresnel_bound

/-- **MainTerm first moment O(√T) bound** (Atkinson formula).

    Combines the Atkinson evaluation |∫ MainTerm| ≤ C_atk · (N+1)
    with the hardyN bound N+1 ≤ 2√T to get the O(√T) bound.

    Reference: Atkinson 1949; Titchmarsh 1951 §4.15. -/
theorem mainTerm_first_moment_sqrt
    [AtkinsonShiftedCorrectionPrefixBoundHyp] :
    ∃ C_M > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, MainTerm t| ≤ C_M * T ^ ((1 : ℝ) / 2) := by
  obtain ⟨C_atk, hC_pos, h_atk⟩ := atkinson_integral_le_N
  refine ⟨2 * C_atk, by positivity, fun T hT => ?_⟩
  calc |∫ t in Ioc 1 T, MainTerm t|
      ≤ C_atk * ((↑(hardyN T) : ℝ) + 1) := h_atk T hT
    _ ≤ C_atk * (2 * Real.sqrt T) := by
        gcongr; exact hardyN_add_one_le T (by linarith)
    _ = 2 * C_atk * Real.sqrt T := by ring
    _ = 2 * C_atk * T ^ ((1 : ℝ) / 2) := by
        congr 1; exact Real.sqrt_eq_rpow T

theorem mainTerm_first_moment_sqrt_of_inversePhaseCellPrefix
    [AtkinsonShiftedInversePhaseCellPrefixBoundHyp] :
    ∃ C_M > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, MainTerm t| ≤ C_M * T ^ ((1 : ℝ) / 2) := by
  letI : AtkinsonShiftedCorrectionPrefixBoundHyp :=
    atkinson_shiftedCorrectionPrefixBound_of_inversePhaseCellPrefix
  exact mainTerm_first_moment_sqrt

end Aristotle.Standalone.AtkinsonFormula
