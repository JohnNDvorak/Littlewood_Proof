/-
Stationary phase decomposition for Hardy cosine integrals.

KEY RESULT:
  hardy_cos_integral_weighted_sum_bound :
    ∃ C > 0, ∀ T ≥ 2, |∑ (n+1)^{-1/2} ∫ cos(θ-t·log(n+1))| ≤ C·(N+1)

This directly provides HardyCosIntegralAlternatingSqrtDecompositionHyp,
closing the sorry at CriticalAssumptions.lean.

PROOF STRUCTURE (encapsulated in the atomic sorry):
1. The n-th Hardy cosine integral has stationary point at t₀ = 2π(n+1)² where
   φ'(t₀) = θ'(t₀) - log(n+1) ≈ 0.

2. Stationary phase / Fresnel evaluation on [t₀, t₀ + c(n+1)]:
     ∫ cos(φ_n) = c₁·(n+1)·cos(φ_n(t₀) + π/4) + O(1)
   Phase value: cos(φ_n(t₀)) involves (-1)^n via cos(π(n+1)²) = (-1)^n.

3. VdC first derivative test on the tail [t₀ + c(n+1), T]: |∫_tail| = O(1).

4. Per-mode: ∫ = c₁(n+1)(-1)^n + O(1), so weighted integral ≈ c₁(-1)^n√(n+1).

5. Alternating sum of √(n+1) is O(√N) by Abel summation.
   Error sum is O(N). Last mode (endpoint) contributes O(√N).
   Total: O(N).

REFERENCES:
  - Titchmarsh, "Theory of the Riemann Zeta Function", §7.6
  - θ'(t) asymptotics from ThetaDerivAsymptotic (via DigammaAsymptotic)
  - Van der Corput first derivative test from VdcFirstDerivTest
  - cos(πn²) = (-1)^n from CosPiSqSign
  - alternating_sqrt_sum_bound from CosPiSqSign (Abel summation)

Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.ComplexVdC
import Littlewood.Aristotle.HardyCosSmooth
import Littlewood.Aristotle.HardyCosExpOmega
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.HardyZMeasurability
import Littlewood.Aristotle.OffResonanceSmoothVdC
import Littlewood.Aristotle.ErrorTermExpansion
import Littlewood.Aristotle.StationaryPhaseMainMode
import Littlewood.Aristotle.ThetaDerivMonotone
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

namespace StationaryPhaseDecomposition

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.HardyNProperties
open Aristotle.HardyCosExpOmega
open Aristotle.OffResonanceSmoothVdC
open Aristotle.RSBlockParam
open Aristotle.StationaryPhaseMainMode
open ThetaDerivMonotone

private lemma weight_nonneg (n : ℕ) :
    0 ≤ (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  positivity

private lemma weight_le_one (n : ℕ) :
    (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
  have hpos : 0 < (n + 1 : ℝ) := by positivity
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (n + 1) := by
    have hbase : (1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    simpa using Real.sqrt_le_sqrt hbase
  have hsqrt : ((n + 1 : ℝ) ^ (1 / 2 : ℝ)) = Real.sqrt (n + 1) := by
    rw [Real.sqrt_eq_rpow]
  rw [Real.rpow_neg hpos.le, hsqrt]
  have hsqrt_pos : 0 < Real.sqrt (n + 1) := by positivity
  have hInv : 1 / Real.sqrt (n + 1) ≤ (1 : ℝ) / 1 := by
    exact one_div_le_one_div_of_le (by positivity) hsqrt_ge_one
  simpa [one_div] using hInv

private noncomputable def modeWeight (n : ℕ) : ℝ :=
  (n + 1 : ℝ) ^ (-(1 / 2 : ℝ))

private noncomputable def weightedModeIntegral (n : ℕ) (T : ℝ) : ℝ :=
  modeWeight n * ∫ t in Ioc (hardyStart n) T, hardyCos n t

private noncomputable def completeModeTargetUnweighted (n : ℕ) : ℝ :=
  ((((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
        Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
      (((((n : ℝ) + 1 : ℝ) : ℂ) *
          Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope) +
        Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset)).re)

private noncomputable def completeModeSlope : ℝ :=
  (Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor *
      Aristotle.StationaryPhaseMainMode.firstBlockQuadraticSlope).re

private noncomputable def completeModeOffset : ℝ :=
  (Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor *
      Aristotle.StationaryPhaseMainMode.firstBlockQuadraticOffset).re

private noncomputable def completeModeTarget (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) *
    (completeModeSlope * Real.sqrt (n + 1)
      + completeModeOffset * modeWeight n)

private lemma modeWeight_eq (n : ℕ) :
    modeWeight n = (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := rfl

private lemma modeWeight_eq_neg_half (n : ℕ) :
    modeWeight n = (n + 1 : ℝ) ^ (-1 / 2 : ℝ) := by
  rw [modeWeight_eq]
  congr 1
  ring

private lemma modeWeight_mul_succ_eq_sqrt (n : ℕ) :
    modeWeight n * ((n + 1 : ℝ)) = Real.sqrt (n + 1) := by
  have hpos : 0 < (n + 1 : ℝ) := by positivity
  calc
    modeWeight n * ((n + 1 : ℝ))
        = (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * (n + 1 : ℝ) ^ (1 : ℝ) := by
            rw [modeWeight_eq, Real.rpow_one]
    _ = (n + 1 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hpos]
          norm_num
    _ = Real.sqrt (n + 1) := by rw [Real.sqrt_eq_rpow]

private lemma completeModeTargetUnweighted_eq (n : ℕ) :
    completeModeTargetUnweighted n
      = (-1 : ℝ) ^ (n + 1) *
          (completeModeSlope * ((n : ℝ) + 1) + completeModeOffset) := by
  unfold completeModeTargetUnweighted completeModeSlope completeModeOffset
  set s : ℝ := (-1 : ℝ) ^ (n + 1)
  simp [Complex.mul_re, Complex.add_re, mul_add, add_mul, mul_comm,
    mul_left_comm, mul_assoc]
  ring_nf

private lemma completeModeTarget_eq (n : ℕ) :
    modeWeight n * completeModeTargetUnweighted n = completeModeTarget n := by
  rw [completeModeTargetUnweighted_eq, completeModeTarget]
  have hsqrt : modeWeight n * ((n : ℝ) + 1) = Real.sqrt (n + 1) := by
    simpa using modeWeight_mul_succ_eq_sqrt n
  rw [show modeWeight n * (((-1 : ℝ) ^ (n + 1)) *
      (completeModeSlope * ((n : ℝ) + 1) + completeModeOffset))
      = (-1 : ℝ) ^ (n + 1) *
          (modeWeight n * (completeModeSlope * ((n : ℝ) + 1) + completeModeOffset)) by
        ring]
  rw [show modeWeight n * (completeModeSlope * ((n : ℝ) + 1) + completeModeOffset)
      = completeModeSlope * (modeWeight n * ((n : ℝ) + 1))
          + completeModeOffset * modeWeight n by ring]
  rw [hsqrt]

private lemma blockParam_ge_one_of_ge_hardyStart_succ (n : ℕ) {T : ℝ}
    (hT : hardyStart (n + 1) ≤ T) :
    1 ≤ blockParam n T := by
  unfold blockParam
  have hpi : 0 < 2 * Real.pi := by positivity
  have hsq : (((n : ℝ) + 2) ^ 2) ≤ T / (2 * Real.pi) := by
    rw [le_div_iff₀ hpi]
    have hs :
        hardyStart (n + 1) = 2 * Real.pi * (((n : ℝ) + 2) ^ 2) := by
      simp [hardyStart]
      ring
    linarith [hT]
  have hsqrt : (n : ℝ) + 2 ≤ Real.sqrt (T / (2 * Real.pi)) := by
    calc
      (n : ℝ) + 2 = Real.sqrt (((n : ℝ) + 2) ^ 2) := by
        rw [Real.sqrt_sq]
        positivity
      _ ≤ Real.sqrt (T / (2 * Real.pi)) := Real.sqrt_le_sqrt hsq
  linarith

private lemma last_block_length_le_linear (N : ℕ) :
    hardyStart N - hardyStart (N - 1) ≤ 6 * Real.pi * ((N : ℝ) + 1) := by
  cases N with
  | zero =>
      simp [hardyStart]
      positivity
  | succ k =>
      rw [show Nat.succ k - 1 = k by omega, block_length]
      have hlin : 2 * (k : ℝ) + 3 ≤ 3 * ((k : ℝ) + 2) := by
        nlinarith
      have hpi_nonneg : 0 ≤ 2 * Real.pi := by positivity
      calc
        2 * Real.pi * (2 * (k : ℝ) + 3)
            ≤ 2 * Real.pi * (3 * ((k : ℝ) + 2)) :=
              mul_le_mul_of_nonneg_left hlin hpi_nonneg
        _ = 6 * Real.pi * ((k : ℝ) + 2) := by ring
        _ = 6 * Real.pi * (((k + 1 : ℕ) : ℝ) + 1) := by
              congr 1
              rw [Nat.cast_add]
              ring_nf

private theorem off_diagonal_block_bound :
    ∃ C > 0, ∀ k : ℕ, 1 ≤ k →
      |∑ n ∈ Finset.range k,
          ((n + 1 : ℝ) ^ (-(1 : ℝ) / 2)) *
            ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
              hardyCos n t|
        ≤ C * Real.sqrt ((k : ℝ) + 1) * Real.log ((k : ℝ) + 2) := by
  simpa using Aristotle.ErrorTermExpansion.off_resonance_sum_bound

private lemma hardyStart_mono {m n : ℕ} (hmn : m ≤ n) :
    hardyStart m ≤ hardyStart n := by
  rw [hardyStart_formula, hardyStart_formula]
  have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
  have hsq : ((m : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
    nlinarith
  have hpi_nonneg : 0 ≤ 2 * Real.pi := by positivity
  exact mul_le_mul_of_nonneg_left hsq hpi_nonneg

private lemma modeOmega_le_of_le (n : ℕ) (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    modeOmega n s ≤ modeOmega n t := by
  simp only [modeOmega]
  have hmono : MonotoneOn ThetaDerivAsymptotic.thetaDeriv (Set.Ioi 0) :=
    ThetaDerivMonotone.thetaDeriv_strictMonoOn.monotoneOn
  have htd :
      ThetaDerivAsymptotic.thetaDeriv s ≤ ThetaDerivAsymptotic.thetaDeriv t := by
    exact hmono (Set.mem_Ioi.mpr hs) (Set.mem_Ioi.mpr (lt_of_lt_of_le hs hst)) hst
  linarith [htd]

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
            (intervalIntegral.norm_integral_le_integral_norm
              (f := hardyCos n) hab)
    _ ≤ ∫ t in a..b, (1 : ℝ) := by
          refine intervalIntegral.integral_mono_on hab hInt.norm intervalIntegrable_const ?_
          intro t ht
          simpa [HardyEstimatesPartial.hardyCos] using
            (Real.abs_cos_le_one (hardyTheta t - t * Real.log (n + 1)))
    _ = b - a := by simp [intervalIntegral.integral_const, hab]

/-- Global first-derivative VdC bound for a single off-resonant Hardy mode,
valid from any sufficiently far breakpoint onward. This packages the monotone
tail argument directly on the full interval, instead of summing per-block
absolute values. -/
private theorem global_mode_tail_vdc_bound :
    ∃ K₁ : ℕ, ∀ k n : ℕ, n < k → K₁ ≤ k →
      ∀ T : ℝ, hardyStart k ≤ T →
        |∫ t in Ioc (hardyStart k) T, hardyCos n t|
          ≤ 6 / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
  obtain ⟨K₀, hK₀⟩ := modeOmega_lower_bound_eventually
  refine ⟨K₀, ?_⟩
  intro k n hnk hk T hT
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hratio_gt : 1 < ((k : ℝ) + 1) / ((n : ℝ) + 1) := by
    rw [one_lt_div hn1_pos]
    exact_mod_cast Nat.succ_lt_succ hnk
  have hlog_pos : 0 < Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
    exact Real.log_pos hratio_gt
  set m : ℝ := Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) / 2 with hm_def
  have hm_pos : 0 < m := by positivity
  have ha_pos : 0 < hardyStart k := by
    rw [hardyStart_formula]
    positivity
  have hsucc : hardyStart k ≤ hardyStart (k + 1) := by
    exact hardyStart_mono (Nat.le_succ k)
  have hω_lower :
      ∀ t ∈ Set.Icc (hardyStart k) T, m ≤ modeOmega n t := by
    intro t ht
    have hbase := hK₀ k hk n hnk (hardyStart k) le_rfl hsucc
    exact le_trans hbase (modeOmega_le_of_le n _ t ha_pos ht.1)
  have hBound :=
    Aristotle.ComplexVdC.complex_vdc_angular_re
      (HardyCosSmooth.hardyCosExp n) (modeOmega n)
      (hardyStart k) T m hT hm_pos
      (fun t _ht => by
        simpa [modeOmega, Nat.cast_succ] using
          (Aristotle.HardyCosExpOmega.hardyCosExp_angular_velocity n t))
      (fun t _ht => le_of_eq (norm_hardyCosExp n t))
      (differentiable_modeOmega n)
      (continuous_deriv_modeOmega n)
      hω_lower
      (fun t ht => deriv_modeOmega_nonneg n t (lt_of_lt_of_le ha_pos ht.1))
  have h_cos_eq : (fun t => hardyCos n t)
      = (fun t => (HardyCosSmooth.hardyCosExp n t).re) := by
    funext t
    exact HardyCosSmooth.hardyCos_eq_re_hardyCosExp n t
  calc
    |∫ t in Ioc (hardyStart k) T, hardyCos n t|
        = |∫ t in (hardyStart k)..T, hardyCos n t| := by
            rw [← intervalIntegral.integral_of_le hT]
    _ = |∫ t in (hardyStart k)..T, (HardyCosSmooth.hardyCosExp n t).re| := by
          rw [h_cos_eq]
    _ ≤ 3 / m := hBound
    _ = 6 / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
          rw [hm_def]
          ring

/-- The lower half of the off-diagonal block already satisfies the correct
`O(√k)` collective bound once the global off-resonant tail theorem is used in
place of blockwise absolute values. The only logarithmic loss that remains is
therefore concentrated in the genuinely near-diagonal band. -/
private theorem far_off_diagonal_tail_bound_eventually :
    ∃ C > 0, ∃ K0 : ℕ, ∀ k : ℕ, K0 ≤ k →
      ∀ T : ℝ, hardyStart k ≤ T →
        |∑ n ∈ Finset.range ((k + 1) / 2),
            ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
              ∫ t in Ioc (hardyStart k) T, hardyCos n t|
          ≤ C * Real.sqrt ((k : ℝ) + 1) := by
  obtain ⟨K₁, hTail⟩ := global_mode_tail_vdc_bound
  refine ⟨12 / Real.log 2, by
    have hlog2 : 0 < Real.log 2 := by
      exact Real.log_pos (by norm_num)
    positivity, max 2 K₁, ?_⟩
  intro k hk T hT
  have hk_ge_two : 2 ≤ k := le_trans (le_max_left _ _) hk
  have hk_ge_one : 1 ≤ k := le_trans (by norm_num) hk_ge_two
  have hk_large : K₁ ≤ k := le_trans (le_max_right _ _) hk
  have htri :
      |∑ n ∈ Finset.range ((k + 1) / 2),
          ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
            ∫ t in Ioc (hardyStart k) T, hardyCos n t|
        ≤
      ∑ n ∈ Finset.range ((k + 1) / 2),
        (((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
          |∫ t in Ioc (hardyStart k) T, hardyCos n t|) := by
    calc
      |∑ n ∈ Finset.range ((k + 1) / 2),
          ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
            ∫ t in Ioc (hardyStart k) T, hardyCos n t|
          ≤ ∑ n ∈ Finset.range ((k + 1) / 2),
              |((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
                ∫ t in Ioc (hardyStart k) T, hardyCos n t| :=
            Finset.abs_sum_le_sum_abs _ _
      _ =
          ∑ n ∈ Finset.range ((k + 1) / 2),
            (((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
              |∫ t in Ioc (hardyStart k) T, hardyCos n t|) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [abs_mul, abs_of_nonneg (weight_nonneg n)]
  have hsum :
      ∑ n ∈ Finset.range ((k + 1) / 2),
        (((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
          |∫ t in Ioc (hardyStart k) T, hardyCos n t|)
      ≤
      ∑ n ∈ Finset.range ((k + 1) / 2),
        (((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) * (6 / Real.log 2)) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    have hn_half : n < (k + 1) / 2 := Finset.mem_range.mp hn
    have hnk : n < k := by
      omega
    have hdouble : 2 * (n + 1) ≤ k + 1 := by
      omega
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hratio_ge_two : (2 : ℝ) ≤ ((k : ℝ) + 1) / ((n : ℝ) + 1) := by
      rw [le_div_iff₀ hn1_pos]
      exact_mod_cast hdouble
    have hlog_ge :
        Real.log 2 ≤ Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
      exact Real.log_le_log (by norm_num) hratio_ge_two
    have htail :=
      hTail k n hnk hk_large T hT
    have hden_pos : 0 < Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
      have hratio_gt : 1 < ((k : ℝ) + 1) / ((n : ℝ) + 1) := by
        rw [one_lt_div hn1_pos]
        exact_mod_cast Nat.succ_lt_succ hnk
      exact Real.log_pos hratio_gt
    have hlog2_pos : 0 < Real.log 2 := by
      exact Real.log_pos (by norm_num)
    have hscalar :
        6 / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1))
          ≤ 6 / Real.log 2 := by
      exact div_le_div_of_nonneg_left (by positivity) hlog2_pos hlog_ge
    exact mul_le_mul_of_nonneg_left (le_trans htail hscalar) (weight_nonneg n)
  have hweights :
      ∑ n ∈ Finset.range ((k + 1) / 2), ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)))
        ≤ 2 * Real.sqrt (((k + 1) / 2 : ℕ) : ℝ) := by
    simpa [div_eq_mul_inv, show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by ring_nf] using
      Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le ((k + 1) / 2)
  have hhalf_sqrt :
      Real.sqrt (((k + 1) / 2 : ℕ) : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := by
    refine Real.sqrt_le_sqrt ?_
    exact_mod_cast Nat.div_le_self (k + 1) 2
  calc
    |∑ n ∈ Finset.range ((k + 1) / 2),
        ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
          ∫ t in Ioc (hardyStart k) T, hardyCos n t|
      ≤
      ∑ n ∈ Finset.range ((k + 1) / 2),
        (((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
          |∫ t in Ioc (hardyStart k) T, hardyCos n t|) := htri
    _ ≤
      ∑ n ∈ Finset.range ((k + 1) / 2),
        (((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) * (6 / Real.log 2)) := hsum
    _ = (∑ n ∈ Finset.range ((k + 1) / 2), ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)))) *
        (6 / Real.log 2) := by
          rw [Finset.sum_mul]
    _ = (6 / Real.log 2) *
        (∑ n ∈ Finset.range ((k + 1) / 2), ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)))) := by
          ring
    _ ≤ (6 / Real.log 2) * (2 * Real.sqrt (((k + 1) / 2 : ℕ) : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hweights (by positivity)
    _ ≤ (6 / Real.log 2) * (2 * Real.sqrt ((k : ℝ) + 1)) := by
          gcongr
    _ = (12 / Real.log 2) * Real.sqrt ((k : ℝ) + 1) := by ring

/-- Exact collective rewrite of a shifted off-diagonal band on the complete
`k`-th block.  The individual mode integrals are pulled onto the common block
parameter interval `u ∈ (0, 1]`, indexed by the shift `j = k - n`.  This is
the branch-free starting point for any genuinely collective near-diagonal
analysis in the `j` variable. -/
private theorem shifted_band_common_blockIntegral (k J : ℕ) (hJ : J ≤ k) :
    ∑ j ∈ Finset.Icc 1 J,
      modeWeight (k - j) *
        ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), hardyCos (k - j) t
      = ∫ u in Ioc (0 : ℝ) 1,
          ∑ j ∈ Finset.Icc 1 J,
            modeWeight (k - j) * hardyCos (k - j) (blockCoord k u) * blockJacobian k u := by
  calc
    ∑ j ∈ Finset.Icc 1 J,
        modeWeight (k - j) *
          ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), hardyCos (k - j) t
      =
      ∑ j ∈ Finset.Icc 1 J,
        ∫ u in Ioc (0 : ℝ) 1,
          modeWeight (k - j) * hardyCos (k - j) (blockCoord k u) * blockJacobian k u := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
            have hjJ : j ≤ J := (Finset.mem_Icc.mp hj).2
            have hjk : j ≤ k := le_trans hjJ hJ
            rw [hardyCos_completeBlock_eq_common_blockParamIntegral k j hj1 hjk,
              ← MeasureTheory.integral_const_mul]
            congr with u
            ring
    _ = ∫ u in Ioc (0 : ℝ) 1,
          ∑ j ∈ Finset.Icc 1 J,
            modeWeight (k - j) * hardyCos (k - j) (blockCoord k u) * blockJacobian k u := by
          symm
          refine MeasureTheory.integral_finset_sum (Finset.Icc 1 J) ?_
          intro j hj
          have hcont :
              Continuous fun u : ℝ =>
                modeWeight (k - j) * hardyCos (k - j) (blockCoord k u) * blockJacobian k u := by
            exact ((continuous_const.mul
              ((HardyCosSmooth.continuous_hardyCos (k - j)).comp (blockCoord_continuous k))).mul
              (blockJacobian_continuous k))
          simpa using hcont.integrableOn_Ioc

/-- Complex-valued version of `shifted_band_common_blockIntegral`. This is the
shared-parameter collective representation before taking real parts. -/
private theorem shifted_band_common_blockIntegral_complex (k J : ℕ) (hJ : J ≤ k) :
    ∑ j ∈ Finset.Icc 1 J,
      (((modeWeight (k - j) : ℝ) : ℂ) *
        ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
          HardyCosSmooth.hardyCosExp (k - j) t)
      = ∫ u in Ioc (0 : ℝ) 1,
          ∑ j ∈ Finset.Icc 1 J,
            (((modeWeight (k - j) : ℝ) : ℂ) *
              HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u) *
              blockJacobian k u) := by
  calc
    ∑ j ∈ Finset.Icc 1 J,
        (((modeWeight (k - j) : ℝ) : ℂ) *
          ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
            HardyCosSmooth.hardyCosExp (k - j) t)
      =
      ∑ j ∈ Finset.Icc 1 J,
        ∫ u in Ioc (0 : ℝ) 1,
          (((modeWeight (k - j) : ℝ) : ℂ) *
            HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u) *
            blockJacobian k u) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
            have hjJ : j ≤ J := (Finset.mem_Icc.mp hj).2
            have hjk : j ≤ k := le_trans hjJ hJ
            rw [hardyCosExp_completeBlock_eq_common_blockParamIntegral k j hj1 hjk,
              ← MeasureTheory.integral_const_mul]
            congr with u
            ring
    _ = ∫ u in Ioc (0 : ℝ) 1,
          ∑ j ∈ Finset.Icc 1 J,
            (((modeWeight (k - j) : ℝ) : ℂ) *
              HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u) *
              blockJacobian k u) := by
          symm
          refine MeasureTheory.integral_finset_sum (Finset.Icc 1 J) ?_
          intro j hj
          have hcont :
              Continuous fun u : ℝ =>
                (((modeWeight (k - j) : ℝ) : ℂ) *
                  HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u) *
                  blockJacobian k u) := by
            exact ((continuous_const.mul
              ((HardyCosSmooth.continuous_hardyCosExp_complex (k - j)).comp
                (blockCoord_continuous k))).mul
              (Complex.continuous_ofReal.comp (blockJacobian_continuous k)))
          simpa using hcont.integrableOn_Ioc

private lemma half_log_pi_mul_sq_local (n : ℕ) :
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

/-- The common branch-free carrier on the `k`-th Hardy block. It contains all
`j`-independent normalized-Gamma and `π`-phase factors; the remaining shifted
band is a pure Dirichlet slice. -/
private noncomputable def commonBlockCarrier (k : ℕ) (u : ℝ) : ℂ :=
  let t := blockCoord k u
  Complex.Gamma (1 / 4 + Complex.I * (↑t / 2)) /
      ↑‖Complex.Gamma (1 / 4 + Complex.I * (↑t / 2))‖ *
    Complex.exp (-Complex.I * ↑((t / 2) * Real.log Real.pi))

private lemma commonBlockCarrier_norm (k : ℕ) (u : ℝ) :
    ‖commonBlockCarrier k u‖ = 1 := by
  unfold commonBlockCarrier
  let z : ℂ := Complex.Gamma (1 / 4 + Complex.I * (↑(blockCoord k u) / 2))
  have hz : z ≠ 0 := by
    dsimp [z]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      GammaHalfPlane.gamma_quarter_ne_zero (blockCoord k u)
  have hznorm : ‖z / ↑‖z‖‖ = 1 := by
    have hnorm_ne : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    calc
      ‖z / ↑‖z‖‖ = ‖z‖ / ‖(↑‖z‖ : ℂ)‖ := by rw [norm_div]
      _ = ‖z‖ / ‖z‖ := by simp
      _ = 1 := by field_simp [hnorm_ne]
  calc
    ‖z / ↑‖z‖ * Complex.exp (-Complex.I * ↑((blockCoord k u / 2) * Real.log Real.pi))‖
        = ‖z / ↑‖z‖‖ *
            ‖Complex.exp (-Complex.I * ↑((blockCoord k u / 2) * Real.log Real.pi))‖ := by
              rw [norm_mul]
    _ = ‖z / ↑‖z‖‖ * 1 := by
          have hexp :
              ‖Complex.exp (-Complex.I * ↑((blockCoord k u / 2) * Real.log Real.pi))‖ = 1 := by
            rw [Complex.norm_exp]
            simp
          rw [hexp]
    _ = 1 := by
          rw [hznorm]
          norm_num

/-- Exact factorization of one weighted Hardy mode on the common `k`-block:
after pulling out the shared normalized-Gamma carrier, the remaining dependence
on the shifted mode is the explicit Dirichlet exponential
`(n+1)^(-1/2) * exp(-i t log(n+1))`. -/
private lemma weighted_hardyCosExp_eq_commonBlockCarrier (k n : ℕ) (u : ℝ) :
    (((modeWeight n : ℝ) : ℂ) * HardyCosSmooth.hardyCosExp n (blockCoord k u))
      =
      commonBlockCarrier k u *
        ((((modeWeight n : ℝ) : ℂ) *
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
            rw [half_log_pi_mul_sq_local]
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
    (((modeWeight n : ℝ) : ℂ) * HardyCosSmooth.hardyCosExp n (blockCoord k u))
        =
        (((modeWeight n : ℝ) : ℂ) *
          (Complex.Gamma (1 / 4 + Complex.I * (↑t / 2)) /
              ↑‖Complex.Gamma (1 / 4 + Complex.I * (↑t / 2))‖ *
            Complex.exp (-Complex.I *
              ↑((t / 2) * Real.log (Real.pi * ((n : ℝ) + 1) ^ 2))))) := by
              simp [HardyCosSmooth.hardyCosExp, t]
    _ =
        (Complex.Gamma (1 / 4 + Complex.I * (↑t / 2)) /
            ↑‖Complex.Gamma (1 / 4 + Complex.I * (↑t / 2))‖ *
          Complex.exp (-Complex.I * ↑((t / 2) * Real.log Real.pi))) *
          ((((modeWeight n : ℝ) : ℂ) *
            Complex.exp (-Complex.I * ↑(t * Real.log ((n : ℝ) + 1))))) := by
              rw [hexp_split]
              ring
    _ = commonBlockCarrier k u *
          ((((modeWeight n : ℝ) : ℂ) *
            Complex.exp (-Complex.I *
              ↑(blockCoord k u * Real.log ((n : ℝ) + 1))))) := by
              simp [commonBlockCarrier, t]

/-- Exact collective factorization of the shared shifted-band integrand. The
entire near-diagonal band on the `k`-th block is one common branch-free carrier
times one explicit Dirichlet slice in the shift variable. -/
private theorem shifted_band_common_integrand_eq_commonBlockCarrier (k J : ℕ)
    (hJ : J ≤ k) (u : ℝ) :
    ∑ j ∈ Finset.Icc 1 J,
      ((((modeWeight (k - j) : ℝ) : ℂ) *
        HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u) *
        blockJacobian k u))
      =
      commonBlockCarrier k u *
        (((blockJacobian k u : ℂ)) *
          ∑ j ∈ Finset.Icc 1 J,
            ((((modeWeight (k - j) : ℝ) : ℂ) *
              Complex.exp (-Complex.I *
                ↑(blockCoord k u * Real.log (((k - j : ℝ) + 1))))))) := by
  calc
    ∑ j ∈ Finset.Icc 1 J,
        ((((modeWeight (k - j) : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u) *
          blockJacobian k u))
      =
      ∑ j ∈ Finset.Icc 1 J,
        commonBlockCarrier k u *
          (((blockJacobian k u : ℂ)) *
            ((((modeWeight (k - j) : ℝ) : ℂ) *
              Complex.exp (-Complex.I *
                ↑(blockCoord k u * Real.log (((k - j : ℝ) + 1))))))) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hjk : j ≤ k := le_trans (Finset.mem_Icc.mp hj).2 hJ
            rw [weighted_hardyCosExp_eq_commonBlockCarrier k (k - j) u]
            have hlog :
                Real.log (((k - j : ℕ) : ℝ) + 1) = Real.log (1 + ((k : ℝ) - j)) := by
              congr 1
              rw [Nat.cast_sub hjk]
              ring
            rw [hlog]
            ac_rfl
    _ = commonBlockCarrier k u *
          ∑ j ∈ Finset.Icc 1 J,
            (((blockJacobian k u : ℂ)) *
              ((((modeWeight (k - j) : ℝ) : ℂ) *
                Complex.exp (-Complex.I *
                  ↑(blockCoord k u * Real.log (((k - j : ℝ) + 1))))))) := by
          rw [Finset.mul_sum]
    _ = commonBlockCarrier k u *
          (((blockJacobian k u : ℂ)) *
            ∑ j ∈ Finset.Icc 1 J,
              ((((modeWeight (k - j) : ℝ) : ℂ) *
                Complex.exp (-Complex.I *
                  ↑(blockCoord k u * Real.log (((k - j : ℝ) + 1))))))) := by
          congr 2
          rw [← Finset.mul_sum]
    _ = commonBlockCarrier k u *
          (((blockJacobian k u : ℂ)) *
            ∑ j ∈ Finset.Icc 1 J,
              ((((modeWeight (k - j) : ℝ) : ℂ) *
                Complex.exp (-Complex.I *
                  ↑(blockCoord k u * Real.log (((k - j : ℝ) + 1))))))) := by
          rfl

/-- Norm form of `shifted_band_common_integrand_eq_commonBlockCarrier`: the
shared Gamma carrier is unimodular, so the collective near-diagonal problem is
exactly the norm of one explicit Dirichlet slice, scaled by the block Jacobian. -/
private theorem shifted_band_common_integrand_norm_eq_dirichletSlice
    (k J : ℕ) (hJ : J ≤ k) (u : ℝ) (hu : 0 ≤ u) :
    ‖∑ j ∈ Finset.Icc 1 J,
        ((((modeWeight (k - j) : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u) *
          blockJacobian k u))‖
      =
      blockJacobian k u *
        ‖∑ j ∈ Finset.Icc 1 J,
            ((((modeWeight (k - j) : ℝ) : ℂ) *
              Complex.exp (-Complex.I *
                ↑(blockCoord k u * Real.log (((k - j : ℝ) + 1))))))‖ := by
  rw [shifted_band_common_integrand_eq_commonBlockCarrier k J hJ u]
  rw [norm_mul, norm_mul, commonBlockCarrier_norm]
  have hJ_nonneg : 0 ≤ blockJacobian k u := by
    exact (blockJacobian_pos k hu).le
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hJ_nonneg, one_mul]

private lemma modeWeight_pos (n : ℕ) : 0 < modeWeight n := by
  unfold modeWeight
  positivity

private lemma modeWeight_ne_zero (n : ℕ) : modeWeight n ≠ 0 :=
  ne_of_gt (modeWeight_pos n)

/-- Relative weight of the shifted mode `k-j` against the resonant weight `k`.
This isolates the collective `j`-packet from the common resonant carrier. -/
private noncomputable def shiftedRelativeWeight (k j : ℕ) : ℝ :=
  modeWeight (k - j) / modeWeight k

/-- Relative phase frequency of the shifted mode `k-j` against the resonant
frequency `k+1`. -/
private noncomputable def shiftedRelativePhase (k j : ℕ) : ℝ :=
  Real.log (((k : ℝ) + 1) / (((k - j : ℕ) : ℝ) + 1))

/-- The linear `u`-frequency appearing after splitting the shifted relative
phase using `blockCoord k u = hardyStart k + 4π(k+1)u + 2πu²`. -/
private noncomputable def shiftedLinearFreq (k j : ℕ) : ℝ :=
  4 * Real.pi * ((k : ℝ) + 1) * shiftedRelativePhase k j

/-- The quadratic `u²` coefficient in the shifted relative phase packet. -/
private noncomputable def shiftedQuadraticFreq (k j : ℕ) : ℝ :=
  2 * Real.pi * shiftedRelativePhase k j

private lemma modeWeight_mul_shiftedRelativeWeight (k j : ℕ) :
    modeWeight k * shiftedRelativeWeight k j = modeWeight (k - j) := by
  unfold shiftedRelativeWeight
  field_simp [modeWeight_ne_zero k]

private lemma shiftedRelativePhase_eq_sub_logs (k j : ℕ) :
    shiftedRelativePhase k j
      = Real.log ((k : ℝ) + 1) - Real.log ((((k - j : ℕ) : ℝ) + 1)) := by
  unfold shiftedRelativePhase
  have hk_pos : 0 < (k : ℝ) + 1 := by positivity
  have hkj_pos : 0 < (((k - j : ℕ) : ℝ) + 1) := by positivity
  rw [Real.log_div hk_pos.ne' hkj_pos.ne']

/-- Exact factorization of one shifted mode against the resonant weighted Hardy
mode on the same `k`-block.  The remaining `j`-dependence is a relative weight
times one explicit exponential packet. -/
private theorem weighted_hardyCosExp_eq_resonant_times_shiftedPacket (k j : ℕ)
    (u : ℝ) :
    (((modeWeight (k - j) : ℝ) : ℂ) *
        HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u))
      =
      ((((modeWeight k : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp k (blockCoord k u))) *
        ((((shiftedRelativeWeight k j : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ↑(blockCoord k u * shiftedRelativePhase k j))) := by
  let t : ℝ := blockCoord k u
  have hleft :=
    weighted_hardyCosExp_eq_commonBlockCarrier k (k - j) u
  have hres :=
    weighted_hardyCosExp_eq_commonBlockCarrier k k u
  have hlog :
      Real.log ((((k - j : ℕ) : ℝ) + 1))
        = Real.log ((k : ℝ) + 1) - shiftedRelativePhase k j := by
    rw [shiftedRelativePhase_eq_sub_logs]
    ring
  have hexp :
      Complex.exp (-Complex.I * ↑(t * Real.log ((((k - j : ℕ) : ℝ) + 1))))
        =
      Complex.exp (-Complex.I * ↑(t * Real.log ((k : ℝ) + 1))) *
        Complex.exp (Complex.I * ↑(t * shiftedRelativePhase k j)) := by
    have harg :
        -Complex.I * ↑(t * Real.log ((((k - j : ℕ) : ℝ) + 1)))
          =
        (-Complex.I * ↑(t * Real.log ((k : ℝ) + 1)))
          + (Complex.I * ↑(t * shiftedRelativePhase k j)) := by
      rw [hlog]
      simp [sub_eq_add_neg, mul_add, add_mul, mul_assoc]
    rw [harg, Complex.exp_add]
  calc
    (((modeWeight (k - j) : ℝ) : ℂ) *
        HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u))
      =
      commonBlockCarrier k u *
        ((((modeWeight (k - j) : ℝ) : ℂ) *
          Complex.exp (-Complex.I * ↑(t * Real.log ((((k - j : ℕ) : ℝ) + 1)))))) := by
            simpa [t] using hleft
    _ =
      commonBlockCarrier k u *
        (((((modeWeight k : ℝ) : ℂ) *
            Complex.exp (-Complex.I * ↑(t * Real.log ((k : ℝ) + 1)))) *
          ((((shiftedRelativeWeight k j : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ↑(t * shiftedRelativePhase k j))))) := by
              rw [hexp]
              have hw :
                  (((modeWeight (k - j) : ℝ) : ℂ))
                    = (((modeWeight k : ℝ) : ℂ) *
                        (((shiftedRelativeWeight k j : ℝ) : ℂ))) := by
                  rw [← Complex.ofReal_mul]
                  congr 1
                  exact (modeWeight_mul_shiftedRelativeWeight k j).symm
              rw [hw]
              ac_rfl
    _ =
      ((((modeWeight k : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp k (blockCoord k u))) *
        ((((shiftedRelativeWeight k j : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ↑(t * shiftedRelativePhase k j))) := by
            rw [show commonBlockCarrier k u *
                  (((((modeWeight k : ℝ) : ℂ) *
                      Complex.exp (-Complex.I * ↑(t * Real.log ((k : ℝ) + 1)))) *
                    ((((shiftedRelativeWeight k j : ℝ) : ℂ)) *
                      Complex.exp (Complex.I * ↑(t * shiftedRelativePhase k j)))))
                  =
                (commonBlockCarrier k u *
                  (((modeWeight k : ℝ) : ℂ) *
                    Complex.exp (-Complex.I * ↑(t * Real.log ((k : ℝ) + 1))))) *
                  ((((shiftedRelativeWeight k j : ℝ) : ℂ)) *
                    Complex.exp (Complex.I * ↑(t * shiftedRelativePhase k j))) by
                      ac_rfl]
            rw [← hres]
    _ =
      ((((modeWeight k : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp k (blockCoord k u))) *
        ((((shiftedRelativeWeight k j : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ↑(blockCoord k u * shiftedRelativePhase k j))) := by
              simp [t]

/-- Exact splitting of the shifted relative phase into constant, linear, and
quadratic `u` pieces on the common `k`-block. -/
private theorem shiftedRelativePhaseFactor_split (k j : ℕ) (u : ℝ) :
    Complex.exp (Complex.I * ↑(blockCoord k u * shiftedRelativePhase k j))
      =
      Complex.exp (Complex.I * ↑(hardyStart k * shiftedRelativePhase k j)) *
        Complex.exp (Complex.I * ↑(shiftedLinearFreq k j * u)) *
        Complex.exp (Complex.I * ↑(shiftedQuadraticFreq k j * u ^ 2)) := by
  have hsplit :
      blockCoord k u * shiftedRelativePhase k j
        =
      hardyStart k * shiftedRelativePhase k j
        + shiftedLinearFreq k j * u
        + shiftedQuadraticFreq k j * u ^ 2 := by
    have hcoord : blockCoord k u = hardyStart k + (4 * Real.pi * ((k : ℝ) + 1) * u + 2 * Real.pi * u ^ 2) := by
      linarith [blockCoord_sub_hardyStart k u]
    rw [hcoord]
    unfold shiftedLinearFreq shiftedQuadraticFreq
    ring
  rw [hsplit]
  rw [show hardyStart k * shiftedRelativePhase k j + shiftedLinearFreq k j * u + shiftedQuadraticFreq k j * u ^ 2
        = hardyStart k * shiftedRelativePhase k j
            + (shiftedLinearFreq k j * u + shiftedQuadraticFreq k j * u ^ 2) by ring]
  have harg :
      Complex.I *
          ↑(hardyStart k * shiftedRelativePhase k j
            + (shiftedLinearFreq k j * u + shiftedQuadraticFreq k j * u ^ 2))
        =
      (Complex.I * ↑(hardyStart k * shiftedRelativePhase k j))
        + ((Complex.I * ↑(shiftedLinearFreq k j * u))
            + (Complex.I * ↑(shiftedQuadraticFreq k j * u ^ 2))) := by
    simp [mul_add, add_mul, mul_assoc]
  rw [harg, Complex.exp_add, Complex.exp_add]
  ac_rfl

/-- The shared weighted resonant carrier on the `k`-th Hardy block, including
the block Jacobian. The near-diagonal shifted band will be expressed as this
common carrier times one exact `j`-packet. -/
private noncomputable def resonantBlockCarrier (k : ℕ) (u : ℝ) : ℂ :=
  ((((modeWeight k : ℝ) : ℂ) *
      HardyCosSmooth.hardyCosExp k (blockCoord k u))) *
    (blockJacobian k u : ℂ)

/-- The exact shifted `j`-packet relative to the resonant mode on the common
`k`-block. -/
private noncomputable def shiftedJPacket (k J : ℕ) (u : ℝ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 J,
    ((((shiftedRelativeWeight k j : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ↑(blockCoord k u * shiftedRelativePhase k j)))

/-- Exact constructive factorization of the shifted near-diagonal band on the
`k`-th block as one common resonant carrier times one exact shifted `j`-packet.
-/
private theorem shifted_band_common_integrand_eq_resonantCarrier_packet
    (k J : ℕ) (_hJ : J ≤ k) (u : ℝ) :
    ∑ j ∈ Finset.Icc 1 J,
      ((((modeWeight (k - j) : ℝ) : ℂ) *
        HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u) *
        blockJacobian k u))
      =
      resonantBlockCarrier k u * shiftedJPacket k J u := by
  unfold resonantBlockCarrier shiftedJPacket
  calc
    ∑ j ∈ Finset.Icc 1 J,
        ((((modeWeight (k - j) : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u) *
          blockJacobian k u))
      =
      ∑ j ∈ Finset.Icc 1 J,
        ((((((modeWeight k : ℝ) : ℂ) *
            HardyCosSmooth.hardyCosExp k (blockCoord k u))) *
            (blockJacobian k u : ℂ)) *
          ((((shiftedRelativeWeight k j : ℝ) : ℂ)) *
            Complex.exp (Complex.I *
              ↑(blockCoord k u * shiftedRelativePhase k j)))) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [weighted_hardyCosExp_eq_resonant_times_shiftedPacket]
            ac_rfl
    _ =
      (((((modeWeight k : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp k (blockCoord k u))) *
          (blockJacobian k u : ℂ)) *
        ∑ j ∈ Finset.Icc 1 J,
          ((((shiftedRelativeWeight k j : ℝ) : ℂ)) *
            Complex.exp (Complex.I *
              ↑(blockCoord k u * shiftedRelativePhase k j))) := by
                rw [Finset.mul_sum]
    _ = resonantBlockCarrier k u * shiftedJPacket k J u := by
          simp [resonantBlockCarrier, shiftedJPacket]

/-- Exact split form of the shifted `j`-packet into constant, linear, and
quadratic `u`-frequencies. -/
private theorem shiftedJPacket_eq_split (k J : ℕ) (u : ℝ) :
    shiftedJPacket k J u
      =
      ∑ j ∈ Finset.Icc 1 J,
        ((((shiftedRelativeWeight k j : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ↑(hardyStart k * shiftedRelativePhase k j)) *
          Complex.exp (Complex.I * ↑(shiftedLinearFreq k j * u)) *
          Complex.exp (Complex.I * ↑(shiftedQuadraticFreq k j * u ^ 2))) := by
  unfold shiftedJPacket
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [shiftedRelativePhaseFactor_split]
  ac_rfl

/-- The collective shifted-band integrand admits the exact resonant-carrier /
shifted-packet representation with the packet phase already split into
constant, linear, and quadratic pieces. -/
private theorem shifted_band_common_integrand_eq_resonantCarrier_splitPacket
    (k J : ℕ) (hJ : J ≤ k) (u : ℝ) :
    ∑ j ∈ Finset.Icc 1 J,
      ((((modeWeight (k - j) : ℝ) : ℂ) *
        HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u) *
        blockJacobian k u))
      =
      resonantBlockCarrier k u *
        ∑ j ∈ Finset.Icc 1 J,
          ((((shiftedRelativeWeight k j : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ↑(hardyStart k * shiftedRelativePhase k j)) *
            Complex.exp (Complex.I * ↑(shiftedLinearFreq k j * u)) *
            Complex.exp (Complex.I * ↑(shiftedQuadraticFreq k j * u ^ 2))) := by
  rw [shifted_band_common_integrand_eq_resonantCarrier_packet k J hJ u]
  rw [shiftedJPacket_eq_split]

/-- The common resonant carrier has exact norm `modeWeight k * blockJacobian k
u` because `hardyCosExp` is unimodular. -/
private lemma resonantBlockCarrier_norm (k : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    ‖resonantBlockCarrier k u‖ = modeWeight k * blockJacobian k u := by
  unfold resonantBlockCarrier
  rw [norm_mul, norm_mul, norm_hardyCosExp, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs]
  have hw_nonneg : 0 ≤ modeWeight k := (modeWeight_pos k).le
  have hJ_nonneg : 0 ≤ blockJacobian k u := (blockJacobian_pos k hu).le
  rw [abs_of_nonneg hw_nonneg, abs_of_nonneg hJ_nonneg]
  ring

/-- Norm form of the exact resonant-carrier / shifted-packet factorization. -/
private theorem shifted_band_common_integrand_norm_eq_resonantCarrier_packet
    (k J : ℕ) (hJ : J ≤ k) (u : ℝ) (hu : 0 ≤ u) :
    ‖∑ j ∈ Finset.Icc 1 J,
        ((((modeWeight (k - j) : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u) *
          blockJacobian k u))‖
      =
      (modeWeight k * blockJacobian k u) * ‖shiftedJPacket k J u‖ := by
  rw [shifted_band_common_integrand_eq_resonantCarrier_packet k J hJ u]
  rw [norm_mul, resonantBlockCarrier_norm k u hu]

private lemma shiftedRelativeWeight_nonneg (k j : ℕ) :
    0 ≤ shiftedRelativeWeight k j := by
  unfold shiftedRelativeWeight
  exact div_nonneg (le_of_lt (modeWeight_pos (k - j))) (le_of_lt (modeWeight_pos k))

private lemma shiftedRelativePhase_lower (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    (j : ℝ) / ((k : ℝ) + 1) ≤ shiftedRelativePhase k j := by
  let x : ℝ := ((k : ℝ) + 1) / ((((k - j : ℕ) : ℝ) + 1))
  have hx_pos : 0 < x := by
    dsimp [x]
    positivity
  have hbase : 1 - x⁻¹ ≤ Real.log x := Real.one_sub_inv_le_log_of_pos hx_pos
  have hk1_ne : (k : ℝ) + 1 ≠ 0 := by positivity
  have hlog : Real.log x = shiftedRelativePhase k j := by
    simp [x, shiftedRelativePhase]
  have hleft : 1 - x⁻¹ = (j : ℝ) / ((k : ℝ) + 1) := by
    have hsub : ((((k - j : ℕ) : ℝ) + 1)) = (k : ℝ) + 1 - j := by
      rw [Nat.cast_sub hjk]
      ring
    dsimp [x]
    rw [inv_div, hsub]
    field_simp [hk1_ne]
    ring
  simpa [hleft, hlog] using hbase

private lemma shiftedRelativePhase_pos (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    0 < shiftedRelativePhase k j := by
  have hlower := shiftedRelativePhase_lower k j hj hjk
  have hpos : 0 < (j : ℝ) / ((k : ℝ) + 1) := by positivity
  exact lt_of_lt_of_le hpos hlower

private lemma shiftedRelativePhase_inv_upper
    (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    1 / shiftedRelativePhase k j ≤ ((k : ℝ) + 1) / j := by
  have hphase_pos : 0 < shiftedRelativePhase k j := shiftedRelativePhase_pos k j hj hjk
  have hden_pos : 0 < (j : ℝ) / ((k : ℝ) + 1) := by positivity
  calc
    1 / shiftedRelativePhase k j ≤ 1 / ((j : ℝ) / ((k : ℝ) + 1)) := by
      exact one_div_le_one_div_of_le hden_pos (shiftedRelativePhase_lower k j hj hjk)
    _ = ((k : ℝ) + 1) / j := by
      field_simp [show (j : ℝ) ≠ 0 by positivity,
        show ((k : ℝ) + 1) ≠ 0 by positivity]

private noncomputable def shiftedPacketOmega (k j : ℕ) (u : ℝ) : ℝ :=
  blockJacobian k u * shiftedRelativePhase k j

private noncomputable def shiftedPacketPhase (k j : ℕ) (u : ℝ) : ℂ :=
  Complex.exp (Complex.I * ↑(blockCoord k u * shiftedRelativePhase k j))

private lemma shiftedPacketOmega_hasDerivAt (k j : ℕ) (u : ℝ) :
    HasDerivAt (shiftedPacketOmega k j)
      (4 * Real.pi * shiftedRelativePhase k j) u := by
  unfold shiftedPacketOmega blockJacobian
  convert (((hasDerivAt_id u).const_add ((k : ℝ) + 1)).const_mul (4 * Real.pi)).mul_const
      (shiftedRelativePhase k j) using 1 <;> ring

private lemma deriv_shiftedPacketOmega (k j : ℕ) (u : ℝ) :
    deriv (shiftedPacketOmega k j) u = 4 * Real.pi * shiftedRelativePhase k j := by
  rw [(shiftedPacketOmega_hasDerivAt k j u).deriv]

private lemma differentiable_shiftedPacketOmega (k j : ℕ) :
    Differentiable ℝ (shiftedPacketOmega k j) := by
  intro u
  exact (shiftedPacketOmega_hasDerivAt k j u).differentiableAt

private lemma continuous_deriv_shiftedPacketOmega (k j : ℕ) :
    Continuous (deriv (shiftedPacketOmega k j)) := by
  have hderiv :
      deriv (shiftedPacketOmega k j) = fun _ : ℝ => 4 * Real.pi * shiftedRelativePhase k j := by
    funext u
    rw [deriv_shiftedPacketOmega]
  rw [hderiv]
  exact continuous_const

private lemma shiftedPacketPhase_hasDerivAt (k j : ℕ) (u : ℝ) :
    HasDerivAt (shiftedPacketPhase k j)
      (Complex.I * ↑(shiftedPacketOmega k j u) * shiftedPacketPhase k j u) u := by
  unfold shiftedPacketPhase
  have hinner :
      HasDerivAt (fun u => blockCoord k u * shiftedRelativePhase k j)
        (shiftedPacketOmega k j u) u := by
    unfold shiftedPacketOmega
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (blockCoord_hasDerivAt k u).mul_const (shiftedRelativePhase k j)
  have hcomplex :
      HasDerivAt (fun u => ((blockCoord k u * shiftedRelativePhase k j : ℝ) : ℂ))
        (↑(shiftedPacketOmega k j u)) u := hinner.ofReal_comp
  have hi :
      HasDerivAt
        (fun u => Complex.I * ((blockCoord k u * shiftedRelativePhase k j : ℝ) : ℂ))
        (Complex.I * ↑(shiftedPacketOmega k j u)) u := hcomplex.const_mul Complex.I
  simpa [shiftedPacketPhase, mul_comm, mul_left_comm, mul_assoc] using
    (Complex.hasDerivAt_exp _).comp u hi

private lemma norm_shiftedPacketPhase (k j : ℕ) (u : ℝ) :
    ‖shiftedPacketPhase k j u‖ = 1 := by
  unfold shiftedPacketPhase
  simpa using Complex.norm_exp_I_mul_ofReal (blockCoord k u * shiftedRelativePhase k j)

private lemma shiftedPacketOmega_lower (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, 4 * Real.pi * j ≤ shiftedPacketOmega k j u := by
  intro u hu
  have hphase_lower := shiftedRelativePhase_lower k j hj hjk
  have hphase_nonneg : 0 ≤ shiftedRelativePhase k j := by
    exact le_of_lt (shiftedRelativePhase_pos k j hj hjk)
  have hk1_ne : (k : ℝ) + 1 ≠ 0 := by positivity
  have hbase :
      4 * Real.pi * j
        ≤ (4 * Real.pi * ((k : ℝ) + 1)) * shiftedRelativePhase k j := by
    have hmul :=
      mul_le_mul_of_nonneg_left hphase_lower
        (by positivity : 0 ≤ 4 * Real.pi * ((k : ℝ) + 1))
    have hrewrite :
        (4 * Real.pi * ((k : ℝ) + 1)) * ((j : ℝ) / ((k : ℝ) + 1))
          = 4 * Real.pi * j := by
      field_simp [hk1_ne]
    simpa [hrewrite] using hmul
  have hjac :
      (4 * Real.pi * ((k : ℝ) + 1)) * shiftedRelativePhase k j
        ≤ shiftedPacketOmega k j u := by
    unfold shiftedPacketOmega
    have hbj :
        4 * Real.pi * ((k : ℝ) + 1) ≤ blockJacobian k u := by
      unfold blockJacobian
      nlinarith [hu.1, Real.pi_pos]
    exact mul_le_mul_of_nonneg_right hbj hphase_nonneg
  exact le_trans hbase hjac

private lemma shiftedRelativeWeight_le_sqrt_two (k j : ℕ)
    (hj_half : j ≤ (k + 1) / 2) :
    shiftedRelativeWeight k j ≤ Real.sqrt 2 := by
  have hjk : j ≤ k := by omega
  have hk1_pos : 0 < (k : ℝ) + 1 := by positivity
  have hden_pos : 0 < ((((k - j : ℕ) : ℝ) + 1)) := by positivity
  have hrepr :
      shiftedRelativeWeight k j
        = Real.sqrt ((k : ℝ) + 1) / Real.sqrt ((((k - j : ℕ) : ℝ) + 1)) := by
    unfold shiftedRelativeWeight modeWeight
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

private lemma harmonic_Icc_le_one_add_log (J : ℕ) (hJ : 1 ≤ J) :
    ∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / j ≤ 1 + Real.log (J : ℝ) := by
  have hsum : ∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / j = (harmonic J : ℝ) := by
    norm_num [harmonic_eq_sum_Icc, one_div]
  rw [hsum]
  simpa using harmonic_floor_le_one_add_log (J : ℝ) (by exact_mod_cast hJ)

private theorem shiftedPacketPhase_integral_bound (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    ‖∫ u in (0 : ℝ)..1, shiftedPacketPhase k j u‖ ≤ 3 / (4 * Real.pi * j) := by
  have hm_pos : 0 < 4 * Real.pi * j := by positivity
  have hBound :=
    Aristotle.ComplexVdC.complex_vdc_angular
      (shiftedPacketPhase k j) (shiftedPacketOmega k j) (0 : ℝ) 1 (4 * Real.pi * j)
      (by norm_num) hm_pos
      (fun u hu => shiftedPacketPhase_hasDerivAt k j u)
      (fun u hu => by simpa using (le_of_eq (norm_shiftedPacketPhase k j u)))
      (differentiable_shiftedPacketOmega k j)
      (continuous_deriv_shiftedPacketOmega k j)
      (shiftedPacketOmega_lower k j hj hjk)
      (fun u hu => by
        rw [deriv_shiftedPacketOmega]
        have hphase_nonneg : 0 ≤ shiftedRelativePhase k j := by
          exact le_of_lt (shiftedRelativePhase_pos k j hj hjk)
        nlinarith [Real.pi_pos, hphase_nonneg])
  simpa [shiftedPacketPhase] using hBound

private theorem shiftedJPacket_integral_bound (k J : ℕ)
    (hJ : J ≤ (k + 1) / 2) :
    ‖∫ u in (0 : ℝ)..1, shiftedJPacket k J u‖
      ≤ (3 * Real.sqrt 2 / (4 * Real.pi)) * (1 + Real.log ((J : ℝ) + 1)) := by
  by_cases hJ0 : J = 0
  · subst hJ0
    have hconst : 0 ≤ (3 * Real.sqrt 2 / (4 * Real.pi)) * (1 + Real.log ((0 : ℝ) + 1)) := by
      have hnum : 0 ≤ 3 * Real.sqrt 2 := by positivity
      have hden : 0 ≤ 4 * Real.pi := by positivity
      have hfac : 0 ≤ 1 + Real.log ((0 : ℝ) + 1) := by
        norm_num [Real.log_one]
      exact mul_nonneg (div_nonneg hnum hden) hfac
    simpa [shiftedJPacket, Real.log_one] using hconst
  · have hJ_pos : 1 ≤ J := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hJ0)
    unfold shiftedJPacket
    rw [intervalIntegral.integral_finset_sum]
    · calc
        ‖∑ j ∈ Finset.Icc 1 J,
            ∫ u in (0 : ℝ)..1,
              ((((shiftedRelativeWeight k j : ℝ) : ℂ)) *
                Complex.exp (Complex.I * ↑(blockCoord k u * shiftedRelativePhase k j)))‖
            ≤
          ∑ j ∈ Finset.Icc 1 J,
            ‖∫ u in (0 : ℝ)..1,
                ((((shiftedRelativeWeight k j : ℝ) : ℂ)) *
                  Complex.exp (Complex.I * ↑(blockCoord k u * shiftedRelativePhase k j)))‖ :=
              norm_sum_le _ _
        _ ≤
          ∑ j ∈ Finset.Icc 1 J,
            shiftedRelativeWeight k j * (3 / (4 * Real.pi * j)) := by
              refine Finset.sum_le_sum ?_
              intro j hj_mem
              have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj_mem).1
              have hjJ : j ≤ J := (Finset.mem_Icc.mp hj_mem).2
              have hjk : j ≤ k := by omega
              calc
                ‖∫ u in (0 : ℝ)..1,
                    ((((shiftedRelativeWeight k j : ℝ) : ℂ)) *
                      Complex.exp (Complex.I * ↑(blockCoord k u * shiftedRelativePhase k j)))‖
                    =
                  ‖(((shiftedRelativeWeight k j : ℝ) : ℂ) *
                      ∫ u in (0 : ℝ)..1, shiftedPacketPhase k j u)‖ := by
                        rw [intervalIntegral.integral_const_mul]
                        congr 1 with u
                _ = shiftedRelativeWeight k j * ‖∫ u in (0 : ℝ)..1, shiftedPacketPhase k j u‖ := by
                      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                        abs_of_nonneg (shiftedRelativeWeight_nonneg k j)]
                _ ≤ shiftedRelativeWeight k j * (3 / (4 * Real.pi * j)) := by
                      exact mul_le_mul_of_nonneg_left
                        (shiftedPacketPhase_integral_bound k j hj1 hjk)
                        (shiftedRelativeWeight_nonneg k j)
        _ ≤
          ∑ j ∈ Finset.Icc 1 J,
            Real.sqrt 2 * (3 / (4 * Real.pi * j)) := by
              refine Finset.sum_le_sum ?_
              intro j hj_mem
              have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj_mem).1
              have hjJ : j ≤ J := (Finset.mem_Icc.mp hj_mem).2
              have hweight :
                  shiftedRelativeWeight k j ≤ Real.sqrt 2 := by
                exact shiftedRelativeWeight_le_sqrt_two k j (le_trans hjJ hJ)
              exact mul_le_mul_of_nonneg_right hweight (by positivity)
        _ =
          (3 * Real.sqrt 2 / (4 * Real.pi)) *
            ∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / j := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro j hj_mem
              ring
        _ ≤
          (3 * Real.sqrt 2 / (4 * Real.pi)) * (1 + Real.log (J : ℝ)) := by
            exact mul_le_mul_of_nonneg_left
              (harmonic_Icc_le_one_add_log J hJ_pos)
              (by positivity)
        _ ≤
          (3 * Real.sqrt 2 / (4 * Real.pi)) * (1 + Real.log ((J : ℝ) + 1)) := by
            have hlog : Real.log (J : ℝ) ≤ Real.log ((J : ℝ) + 1) := by
              exact Real.log_le_log (by positivity) (by linarith)
            have hcoeff_nonneg : 0 ≤ 3 * Real.sqrt 2 / (4 * Real.pi) := by positivity
            nlinarith
    · intro j hj_mem
      have harg_cont : Continuous fun u : ℝ =>
          Complex.I * ↑(blockCoord k u * shiftedRelativePhase k j) := by
        exact continuous_const.mul
          (Complex.continuous_ofReal.comp ((blockCoord_continuous k).mul continuous_const))
      have hphase_cont : Continuous fun u : ℝ =>
          Complex.exp (Complex.I * ↑(blockCoord k u * shiftedRelativePhase k j)) := by
        exact Complex.continuous_exp.comp harg_cont
      have hcont : Continuous fun u : ℝ =>
          ((((shiftedRelativeWeight k j : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ↑(blockCoord k u * shiftedRelativePhase k j))) := by
        exact continuous_const.mul hphase_cont
      exact hcont.intervalIntegrable _ _

/-- The weighted resonant mode on the common `k`-block, before inserting the
shared Jacobian factor. This is the natural integration-by-parts partner for
the shifted packet primitive. -/
private noncomputable def weightedResonantBlockMode (k : ℕ) (u : ℝ) : ℂ :=
  (((modeWeight k : ℝ) : ℂ) * blockMode k u)

private lemma weightedResonantBlockMode_hasDerivAt (k : ℕ) (u : ℝ) :
    HasDerivAt (weightedResonantBlockMode k)
      (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) u := by
  unfold weightedResonantBlockMode
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (blockMode_hasDerivAt k u).const_mul (((modeWeight k : ℝ) : ℂ))

private lemma weightedResonantBlockMode_norm (k : ℕ) (u : ℝ) :
    ‖weightedResonantBlockMode k u‖ = modeWeight k := by
  unfold weightedResonantBlockMode
  rw [norm_mul, blockMode_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (le_of_lt (modeWeight_pos k))]

private lemma weightedResonantBlockMode_deriv_norm (k : ℕ) (u : ℝ) :
    ‖Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u‖
      = |blockOmega k u| * modeWeight k := by
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    weightedResonantBlockMode_norm]

private theorem weightedResonantBlockMode_zero_asymptotic :
    ∃ C > 0, ∀ k : ℕ,
      ‖weightedResonantBlockMode k 0
          - (((modeWeight k : ℝ) : ℂ) *
              ((((-1 : ℝ) ^ (k + 1) : ℝ) : ℂ) *
                Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor))‖
        ≤ C / ((k : ℝ) + 1) := by
  obtain ⟨C, hC, hstart⟩ := blockMode_zero_asymptotic
  refine ⟨C, hC, ?_⟩
  intro k
  have hw_nonneg : 0 ≤ modeWeight k := le_of_lt (modeWeight_pos k)
  have hw_le : modeWeight k ≤ 1 := by
    simpa [modeWeight_eq] using weight_le_one k
  calc
    ‖weightedResonantBlockMode k 0
        - (((modeWeight k : ℝ) : ℂ) *
            ((((-1 : ℝ) ^ (k + 1) : ℝ) : ℂ) *
              Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor))‖
        =
      ‖(((modeWeight k : ℝ) : ℂ)) *
          (blockMode k 0
            - ((((-1 : ℝ) ^ (k + 1) : ℝ) : ℂ) *
                Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor))‖ := by
          unfold weightedResonantBlockMode
          ring
    _ = modeWeight k *
        ‖blockMode k 0
          - ((((-1 : ℝ) ^ (k + 1) : ℝ) : ℂ) *
              Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw_nonneg]
    _ ≤ modeWeight k * (C / ((k : ℝ) + 1)) := by
          gcongr
          exact hstart k
    _ ≤ 1 * (C / ((k : ℝ) + 1)) := by
          have hfrac_nonneg : 0 ≤ C / ((k : ℝ) + 1) := by positivity
          exact mul_le_mul_of_nonneg_right hw_le hfrac_nonneg
    _ = C / ((k : ℝ) + 1) := by ring

private lemma weightedResonantBlockMode_one_eq_next_zero_shift (k : ℕ) :
    weightedResonantBlockMode k 1
      =
      weightedResonantBlockMode (k + 1) 0 *
        ((((shiftedRelativeWeight (k + 1) 1 : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ↑(hardyStart (k + 1) * shiftedRelativePhase (k + 1) 1))) := by
  simpa [weightedResonantBlockMode, Aristotle.StationaryPhaseMainMode.blockMode,
    blockCoord_zero, blockCoord_one] using
    (weighted_hardyCosExp_eq_resonant_times_shiftedPacket (k + 1) 1 0)

private lemma shiftedRelativeWeight_step (k j : ℕ) (hjk : j ≤ k) :
    shiftedRelativeWeight (k + 1) 1 * shiftedRelativeWeight k j
      = shiftedRelativeWeight (k + 1) (j + 1) := by
  unfold shiftedRelativeWeight
  have hk : k + 1 - 1 = k := by omega
  have hkj : k + 1 - (j + 1) = k - j := by omega
  rw [show modeWeight (k + 1 - 1) = modeWeight k by simpa [hk]]
  rw [show modeWeight (k + 1 - (j + 1)) = modeWeight (k - j) by simpa [hkj]]
  field_simp [modeWeight_ne_zero k, modeWeight_ne_zero (k + 1)]

private lemma shiftedRelativePhase_step (k j : ℕ) (hjk : j ≤ k) :
    shiftedRelativePhase (k + 1) 1 + shiftedRelativePhase k j
      = shiftedRelativePhase (k + 1) (j + 1) := by
  have hA_ne : (((k : ℝ) + 2) / ((k : ℝ) + 1)) ≠ 0 := by positivity
  have hB_ne : (((k : ℝ) + 1) / (((k - j : ℕ) : ℝ) + 1)) ≠ 0 := by positivity
  have hphi1 :
      shiftedRelativePhase (k + 1) 1 = Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1)) := by
    unfold shiftedRelativePhase
    norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
  have hmul :
      (((k : ℝ) + 2) / ((k : ℝ) + 1)) * (((k : ℝ) + 1) / (((k - j : ℕ) : ℝ) + 1))
        = (((k : ℝ) + 2) / (((k - j : ℕ) : ℝ) + 1)) := by
    field_simp [show ((k : ℝ) + 1) ≠ 0 by positivity]
  calc
    shiftedRelativePhase (k + 1) 1 + shiftedRelativePhase k j
        = Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1))
            + Real.log (((k : ℝ) + 1) / (((k - j : ℕ) : ℝ) + 1)) := by
            rw [hphi1]
            simp [shiftedRelativePhase]
    _ = Real.log ((((k : ℝ) + 2) / ((k : ℝ) + 1)) *
          (((k : ℝ) + 1) / (((k - j : ℕ) : ℝ) + 1))) := by
            rw [Real.log_mul hA_ne hB_ne]
    _ = Real.log (((k : ℝ) + 2) / (((k - j : ℕ) : ℝ) + 1)) := by rw [hmul]
    _ = shiftedRelativePhase (k + 1) (j + 1) := by
          have hkj : k + 1 - (j + 1) = k - j := by omega
          have hk2 : ((k : ℝ) + 2) = ((k : ℝ) + (1 + 1 : ℝ)) := by ring
          unfold shiftedRelativePhase
          simp [hkj, Nat.cast_add, add_assoc, add_comm, add_left_comm, hk2]

private lemma shiftedRelativePhase_step_ratio_sub_one_le
    (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    |shiftedRelativePhase (k + 1) (j + 1) / shiftedRelativePhase k j - 1|
      ≤ 1 / j := by
  have hphase_pos : 0 < shiftedRelativePhase k j := shiftedRelativePhase_pos k j hj hjk
  have hstep := shiftedRelativePhase_step k j hjk
  have hratio :
      shiftedRelativePhase (k + 1) (j + 1) / shiftedRelativePhase k j - 1
        = shiftedRelativePhase (k + 1) 1 / shiftedRelativePhase k j := by
    have hneq : shiftedRelativePhase k j ≠ 0 := ne_of_gt hphase_pos
    field_simp [hneq]
    linarith
  have hnum :
      shiftedRelativePhase (k + 1) 1 ≤ 1 / ((k : ℝ) + 1) := by
    have hphi1 :
        shiftedRelativePhase (k + 1) 1 = Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1)) := by
      unfold shiftedRelativePhase
      norm_num [Nat.cast_add, add_assoc, add_comm, add_left_comm]
    calc
      shiftedRelativePhase (k + 1) 1
          = Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1)) := hphi1
      _ ≤ (((k : ℝ) + 2) / ((k : ℝ) + 1)) - 1 := by
            exact Real.log_le_sub_one_of_pos (by positivity)
      _ = 1 / ((k : ℝ) + 1) := by
            have : (↑k + 2 : ℝ) - (↑k + 1) = 1 := by ring
            field_simp [show ((k : ℝ) + 1) ≠ 0 by positivity]
            linarith
  have hden :
      (j : ℝ) / ((k : ℝ) + 1) ≤ shiftedRelativePhase k j :=
    shiftedRelativePhase_lower k j hj hjk
  have hstep1_nonneg : 0 ≤ shiftedRelativePhase (k + 1) 1 := by
    exact le_of_lt <|
      shiftedRelativePhase_pos (k + 1) 1 (by norm_num) (by omega)
  have hratio_rhs_nonneg :
      0 ≤ shiftedRelativePhase (k + 1) 1 / shiftedRelativePhase k j := by
    exact div_nonneg hstep1_nonneg hphase_pos.le
  rw [hratio, abs_of_nonneg hratio_rhs_nonneg]
  have hj_div_pos : 0 < (j : ℝ) / ((k : ℝ) + 1) := by positivity
  calc
    shiftedRelativePhase (k + 1) 1 / shiftedRelativePhase k j
        ≤ shiftedRelativePhase (k + 1) 1 / ((j : ℝ) / ((k : ℝ) + 1)) := by
            exact div_le_div_of_nonneg_left hstep1_nonneg hj_div_pos hden
    _ ≤ (1 / ((k : ℝ) + 1)) / ((j : ℝ) / ((k : ℝ) + 1)) := by
            exact div_le_div_of_nonneg_right hnum hj_div_pos.le
    _ = (1 : ℝ) / j := by
          field_simp [show (j : ℝ) ≠ 0 by positivity,
            show ((k : ℝ) + 1) ≠ 0 by positivity]

private theorem weightedResonantBlockMode_one_asymptotic :
    ∃ C > 0, ∀ k : ℕ,
      ‖weightedResonantBlockMode k 1
          - (((modeWeight k : ℝ) : ℂ) *
              ((((-1 : ℝ) ^ k : ℝ) : ℂ) *
                Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
              Complex.exp (Complex.I *
                ↑(hardyStart (k + 1) * shiftedRelativePhase (k + 1) 1)))‖
        ≤ C / ((k : ℝ) + 2) := by
  obtain ⟨C, hC, hstart⟩ := blockMode_zero_asymptotic
  refine ⟨C, hC, ?_⟩
  intro k
  let phase : ℂ :=
    Complex.exp (Complex.I * ↑(hardyStart (k + 1) * shiftedRelativePhase (k + 1) 1))
  have hphase_norm : ‖phase‖ = 1 := by
    dsimp [phase]
    rw [Complex.norm_exp]
    simp
  have hw_nonneg : 0 ≤ modeWeight k := le_of_lt (modeWeight_pos k)
  have hw_le : modeWeight k ≤ 1 := by
    simpa [modeWeight_eq] using weight_le_one k
  rw [weightedResonantBlockMode_one_eq_next_zero_shift]
  have hweight :
      (((modeWeight (k + 1) : ℝ) : ℂ) *
          (((shiftedRelativeWeight (k + 1) 1 : ℝ) : ℂ)))
        = (((modeWeight k : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_mul]
    congr 1
    simpa using modeWeight_mul_shiftedRelativeWeight (k + 1) 1
  have hrew :
      weightedResonantBlockMode (k + 1) 0 *
          ((((shiftedRelativeWeight (k + 1) 1 : ℝ) : ℂ)) * phase)
        - (((modeWeight k : ℝ) : ℂ) *
            ((((-1 : ℝ) ^ k : ℝ) : ℂ) *
              Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) * phase)
      =
      (((modeWeight k : ℝ) : ℂ)) *
        ((blockMode (k + 1) 0
            - ((((-1 : ℝ) ^ (k + 2) : ℝ) : ℂ) *
                Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor)) * phase) := by
    unfold weightedResonantBlockMode
    have hsign :
        ((((-1 : ℝ) ^ k : ℝ) : ℂ) *
            Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor)
          =
        ((((-1 : ℝ) ^ (k + 2) : ℝ) : ℂ) *
            Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) := by
      have hsign' : (((-1 : ℝ) ^ k : ℝ) : ℂ) = (((-1 : ℝ) ^ (k + 2) : ℝ) : ℂ) := by
        norm_num [pow_add, mul_assoc]
      rw [hsign']
    calc
      (((modeWeight (k + 1) : ℝ) : ℂ) * blockMode (k + 1) 0) *
            ((((shiftedRelativeWeight (k + 1) 1 : ℝ) : ℂ)) * phase)
          - (((modeWeight k : ℝ) : ℂ) *
              ((((-1 : ℝ) ^ k : ℝ) : ℂ) *
                Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) * phase)
          =
        ((((modeWeight (k + 1) : ℝ) : ℂ) *
            (((shiftedRelativeWeight (k + 1) 1 : ℝ) : ℂ))) *
          (blockMode (k + 1) 0 * phase))
          - (((modeWeight k : ℝ) : ℂ) *
              (((( (-1 : ℝ) ^ (k + 2) : ℝ) : ℂ) *
                Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) * phase)) := by
            rw [hsign]
            ring
      _ =
        (((modeWeight k : ℝ) : ℂ) * (blockMode (k + 1) 0 * phase))
          - (((modeWeight k : ℝ) : ℂ) *
              (((( (-1 : ℝ) ^ (k + 2) : ℝ) : ℂ) *
                Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) * phase)) := by
            rw [hweight]
      _ =
        (((modeWeight k : ℝ) : ℂ)) *
          ((blockMode (k + 1) 0
              - ((((-1 : ℝ) ^ (k + 2) : ℝ) : ℂ) *
                  Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor)) * phase) := by
            ring
  calc
    ‖weightedResonantBlockMode (k + 1) 0 *
          ((((shiftedRelativeWeight (k + 1) 1 : ℝ) : ℂ)) * phase)
        - (((modeWeight k : ℝ) : ℂ) *
            ((((-1 : ℝ) ^ k : ℝ) : ℂ) *
              Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) * phase)‖
        =
      ‖(((modeWeight k : ℝ) : ℂ)) *
          ((blockMode (k + 1) 0
              - ((((-1 : ℝ) ^ (k + 2) : ℝ) : ℂ) *
                  Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor)) *
            phase)‖ := by
          rw [hrew]
    _ = modeWeight k *
        ‖(blockMode (k + 1) 0
            - ((((-1 : ℝ) ^ (k + 2) : ℝ) : ℂ) *
                Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor)) * phase‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw_nonneg]
    _ = modeWeight k *
        ‖blockMode (k + 1) 0
          - ((((-1 : ℝ) ^ (k + 2) : ℝ) : ℂ) *
              Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor)‖ := by
          rw [norm_mul, hphase_norm, mul_one]
    _ ≤ modeWeight k * (C / ((k : ℝ) + 2)) := by
          gcongr
          have hden : (↑k + (1 + 1 : ℝ)) = (↑k + 2) := by ring
          simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm, hden] using hstart (k + 1)
    _ ≤ 1 * (C / ((k : ℝ) + 2)) := by
          have hfrac_nonneg : 0 ≤ C / ((k : ℝ) + 2) := by positivity
          exact mul_le_mul_of_nonneg_right hw_le hfrac_nonneg
    _ = C / ((k : ℝ) + 2) := by ring

private lemma blockOmega_continuous (n : ℕ) : Continuous (blockOmega n) := by
  have htheta : Continuous ThetaDerivAsymptotic.thetaDeriv :=
    continuous_iff_continuousAt.mpr fun t => (thetaDeriv_hasDerivAt t).continuousAt
  unfold blockOmega
  exact ((htheta.comp (blockCoord_continuous n)).sub continuous_const).mul
    (blockJacobian_continuous n)

private lemma weightedResonantBlockMode_continuous (k : ℕ) :
    Continuous (weightedResonantBlockMode k) := by
  unfold weightedResonantBlockMode blockMode
  exact continuous_const.mul
    ((HardyCosSmooth.continuous_hardyCosExp_complex k).comp (blockCoord_continuous k))

private theorem weightedResonantBlockMode_deriv_bound_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ k : ℕ, N0 ≤ k →
      ∀ u ∈ Icc (0 : ℝ) 1,
        ‖Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u‖
          ≤ C * modeWeight k := by
  obtain ⟨C0, hC0, N0, hOmega⟩ := blockOmega_linear_model_eventually
  let C : ℝ := C0 + 4 * Real.pi + 1
  refine ⟨C, by
    dsimp [C]
    positivity, N0, ?_⟩
  intro k hk u hu
  have hω := hOmega k hk u hu
  have hω_bound : |blockOmega k u| ≤ C := by
    dsimp [C]
    have hlin : |4 * Real.pi * u| ≤ 4 * Real.pi := by
      have hnonneg : 0 ≤ 4 * Real.pi * u := by
        nlinarith [hu.1, Real.pi_pos]
      rw [abs_of_nonneg hnonneg]
      nlinarith [Real.pi_pos, hu.1, hu.2]
    have htri :
        |blockOmega k u| ≤ |blockOmega k u - 4 * Real.pi * u| + |4 * Real.pi * u| := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, Real.norm_eq_abs] using
        (norm_add_le (blockOmega k u - 4 * Real.pi * u) (4 * Real.pi * u))
    calc
      |blockOmega k u|
          ≤ |blockOmega k u - 4 * Real.pi * u| + |4 * Real.pi * u| := htri
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
  rw [weightedResonantBlockMode_deriv_norm]
  exact mul_le_mul_of_nonneg_right hω_bound (le_of_lt (modeWeight_pos k))

/-- One exact shifted packet term, isolated from the full near-band sum. -/
private noncomputable def shiftedSinglePacket (k j : ℕ) (u : ℝ) : ℂ :=
  (((shiftedRelativeWeight k j : ℝ) : ℂ)) * shiftedPacketPhase k j u

/-- Exact primitive for `blockJacobian * shiftedSinglePacket`. This is the
fixed-shift version of `shiftedJPacketPrimitive`, and it is the right
integration-by-parts object for one shifted complete block. -/
private noncomputable def shiftedSinglePrimitive (k j : ℕ) (u : ℝ) : ℂ :=
  (-Complex.I) * (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ)) *
    shiftedPacketPhase k j u

private lemma shiftedSinglePrimitive_hasDerivAt (k j : ℕ) (hj : 1 ≤ j)
    (hjk : j ≤ k) (u : ℝ) :
    HasDerivAt (shiftedSinglePrimitive k j)
      (((blockJacobian k u : ℂ)) * shiftedSinglePacket k j u) u := by
  unfold shiftedSinglePrimitive shiftedSinglePacket
  have hphase_ne : shiftedRelativePhase k j ≠ 0 := by
    exact ne_of_gt (shiftedRelativePhase_pos k j hj hjk)
  have hterm :=
    (shiftedPacketPhase_hasDerivAt k j u).const_mul
      (((-Complex.I) * (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ))))
  have hquot :
      (shiftedRelativeWeight k j / shiftedRelativePhase k j) * shiftedPacketOmega k j u
        = shiftedRelativeWeight k j * blockJacobian k u := by
    unfold shiftedPacketOmega
    field_simp [hphase_ne]
  have hquotC :
      ((((shiftedRelativeWeight k j / shiftedRelativePhase k j) * shiftedPacketOmega k j u : ℝ)) : ℂ)
        =
      ((((shiftedRelativeWeight k j * blockJacobian k u : ℝ)) : ℂ)) := by
    exact congrArg (fun x : ℝ => (x : ℂ)) hquot
  have hderiv :
      (-Complex.I * (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ))) *
          (Complex.I * ↑(shiftedPacketOmega k j u) * shiftedPacketPhase k j u)
        =
      (((blockJacobian k u : ℂ)) * shiftedSinglePacket k j u) := by
    have hI : (-Complex.I) * Complex.I = 1 := by norm_num
    calc
      (-Complex.I * (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ))) *
          (Complex.I * ↑(shiftedPacketOmega k j u) * shiftedPacketPhase k j u)
          =
        ((-Complex.I * Complex.I) *
          ((((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ)) *
            (((shiftedPacketOmega k j u : ℝ) : ℂ)) * shiftedPacketPhase k j u)) := by
            ring
      _ =
        ((((shiftedRelativeWeight k j / shiftedRelativePhase k j) * shiftedPacketOmega k j u : ℝ) : ℂ) *
          shiftedPacketPhase k j u) := by
            rw [hI]
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ =
        ((((shiftedRelativeWeight k j * blockJacobian k u : ℝ) : ℂ)) *
          shiftedPacketPhase k j u) := by
            rw [hquotC]
      _ = (((blockJacobian k u : ℂ)) * shiftedSinglePacket k j u) := by
            unfold shiftedSinglePacket
            norm_num
            ring
  exact hterm.congr_deriv hderiv

private lemma shiftedSinglePrimitive_norm_bound (k j : ℕ)
    (hj : 1 ≤ j) (hj_half : j ≤ (k + 1) / 2) (u : ℝ) :
    ‖shiftedSinglePrimitive k j u‖ ≤ Real.sqrt 2 * (((k : ℝ) + 1) / j) := by
  have hjk : j ≤ k := by omega
  unfold shiftedSinglePrimitive
  have hphase_pos : 0 < shiftedRelativePhase k j := shiftedRelativePhase_pos k j hj hjk
  have hweight :
      shiftedRelativeWeight k j ≤ Real.sqrt 2 := by
    exact shiftedRelativeWeight_le_sqrt_two k j hj_half
  have hphase_lower :
      (j : ℝ) / ((k : ℝ) + 1) ≤ shiftedRelativePhase k j :=
    shiftedRelativePhase_lower k j hj hjk
  have hcoeff :
      shiftedRelativeWeight k j / shiftedRelativePhase k j
        ≤ Real.sqrt 2 * (((k : ℝ) + 1) / j) := by
    have hj_pos : 0 < (j : ℝ) := by positivity
    refine (div_le_iff₀ hphase_pos).2 ?_
    have htmp :
        Real.sqrt 2
          ≤ Real.sqrt 2 * ((((k : ℝ) + 1) / j) * shiftedRelativePhase k j) := by
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
    ‖(-Complex.I) * (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ)) *
        shiftedPacketPhase k j u‖
        = shiftedRelativeWeight k j / shiftedRelativePhase k j := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_shiftedPacketPhase]
            simp [div_nonneg, shiftedRelativeWeight_nonneg k j, le_of_lt hphase_pos]
    _ ≤ Real.sqrt 2 * (((k : ℝ) + 1) / j) := hcoeff

private lemma shiftedRelativePhase_mul_shiftedSinglePrimitive
    (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) (u : ℝ) :
    (((shiftedRelativePhase k j : ℝ) : ℂ)) * shiftedSinglePrimitive k j u
      = (-Complex.I) * shiftedSinglePacket k j u := by
  unfold shiftedSinglePrimitive shiftedSinglePacket
  have hphase_pos : 0 < shiftedRelativePhase k j :=
    shiftedRelativePhase_pos k j hj hjk
  have hreal :
      shiftedRelativePhase k j *
          (shiftedRelativeWeight k j / shiftedRelativePhase k j)
        = shiftedRelativeWeight k j := by
    field_simp [ne_of_gt hphase_pos]
  have hrealC :
      ((((shiftedRelativePhase k j) *
          (shiftedRelativeWeight k j / shiftedRelativePhase k j) : ℝ) : ℂ))
        =
      (((shiftedRelativeWeight k j : ℝ) : ℂ)) := by
    exact congrArg (fun x : ℝ => (x : ℂ)) hreal
  calc
    (((shiftedRelativePhase k j : ℝ) : ℂ)) *
        ((-Complex.I) *
          (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ)) *
            shiftedPacketPhase k j u)
        =
      (-Complex.I) *
        ((((shiftedRelativePhase k j) *
            (shiftedRelativeWeight k j / shiftedRelativePhase k j) : ℝ) : ℂ)) *
          shiftedPacketPhase k j u := by
            calc
              (((shiftedRelativePhase k j : ℝ) : ℂ)) *
                  ((-Complex.I) *
                    (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ)) *
                      shiftedPacketPhase k j u)
                  =
                ((((shiftedRelativePhase k j : ℝ) : ℂ)) * (-Complex.I) *
                    (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ))) *
                  shiftedPacketPhase k j u := by
                    simp [mul_assoc]
              _ =
                (((-Complex.I) * (((shiftedRelativePhase k j : ℝ) : ℂ))) *
                    (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ))) *
                  shiftedPacketPhase k j u := by
                    rw [mul_comm (((shiftedRelativePhase k j : ℝ) : ℂ)) (-Complex.I)]
              _ =
                (-Complex.I) *
                  ((((shiftedRelativePhase k j : ℝ) : ℂ)) *
                    (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ))) *
                  shiftedPacketPhase k j u := by
                    simp [mul_assoc]
              _ =
                (-Complex.I) *
                  ((((shiftedRelativePhase k j) *
                      (shiftedRelativeWeight k j / shiftedRelativePhase k j) : ℝ) : ℂ)) *
                    shiftedPacketPhase k j u := by
                      rw [← Complex.ofReal_mul]
    _ =
      (-Complex.I) *
        (((shiftedRelativeWeight k j : ℝ) : ℂ)) *
          shiftedPacketPhase k j u := by
            rw [hrealC]
    _ = (-Complex.I) * shiftedSinglePacket k j u := by
          unfold shiftedSinglePacket
          ring

private lemma weightedResonantBlockMode_one_mul_shiftedSinglePrimitive_step
    (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    weightedResonantBlockMode k 1 * shiftedSinglePrimitive k j 1
      =
      (((shiftedRelativePhase (k + 1) (j + 1) / shiftedRelativePhase k j : ℝ) : ℂ)) *
        (weightedResonantBlockMode (k + 1) 0 *
          shiftedSinglePrimitive (k + 1) (j + 1) 0) := by
  have hphase_pos : 0 < shiftedRelativePhase k j := shiftedRelativePhase_pos k j hj hjk
  have hphase_next_pos : 0 < shiftedRelativePhase (k + 1) (j + 1) := by
    exact shiftedRelativePhase_pos (k + 1) (j + 1)
      (Nat.succ_le_succ (Nat.zero_le j)) (Nat.succ_le_succ hjk)
  have hweight :
      shiftedRelativeWeight (k + 1) 1 * shiftedRelativeWeight k j
        = shiftedRelativeWeight (k + 1) (j + 1) :=
    shiftedRelativeWeight_step k j hjk
  have hphase :
      shiftedRelativePhase (k + 1) 1 + shiftedRelativePhase k j
        = shiftedRelativePhase (k + 1) (j + 1) :=
    shiftedRelativePhase_step k j hjk
  have hcoeff :
      (((shiftedRelativeWeight (k + 1) 1 * shiftedRelativeWeight k j
          / shiftedRelativePhase k j : ℝ) : ℂ))
        =
      (((shiftedRelativePhase (k + 1) (j + 1) / shiftedRelativePhase k j : ℝ) : ℂ)) *
        (((shiftedRelativeWeight (k + 1) (j + 1)
            / shiftedRelativePhase (k + 1) (j + 1) : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [hweight]
    field_simp [ne_of_gt hphase_pos, ne_of_gt hphase_next_pos]
  have harg :
      hardyStart (k + 1) * shiftedRelativePhase (k + 1) 1
        + hardyStart (k + 1) * shiftedRelativePhase k j
        = hardyStart (k + 1) * shiftedRelativePhase (k + 1) (j + 1) := by
    rw [← mul_add, hphase]
  have hargC :
      Complex.I * ↑(hardyStart (k + 1) * shiftedRelativePhase (k + 1) 1)
        + Complex.I * ↑(hardyStart (k + 1) * shiftedRelativePhase k j)
        =
      Complex.I * ↑(hardyStart (k + 1) * shiftedRelativePhase (k + 1) (j + 1)) := by
    calc
      Complex.I * ↑(hardyStart (k + 1) * shiftedRelativePhase (k + 1) 1)
          + Complex.I * ↑(hardyStart (k + 1) * shiftedRelativePhase k j)
          =
        Complex.I * ↑(hardyStart (k + 1) * shiftedRelativePhase (k + 1) 1
          + hardyStart (k + 1) * shiftedRelativePhase k j) := by
            simp [mul_add, add_mul]
      _ = Complex.I * ↑(hardyStart (k + 1) * shiftedRelativePhase (k + 1) (j + 1)) := by
            rw [harg]
  have hexp :
      Complex.exp (Complex.I * ↑(hardyStart (k + 1) * shiftedRelativePhase (k + 1) 1)) *
          Complex.exp (Complex.I * ↑(hardyStart (k + 1) * shiftedRelativePhase k j))
        =
      Complex.exp (Complex.I * ↑(hardyStart (k + 1) * shiftedRelativePhase (k + 1) (j + 1))) := by
    rw [← Complex.exp_add, hargC]
  have hpacket1 :
      Complex.exp (Complex.I * ↑(hardyStart (k + 1) * shiftedRelativePhase (k + 1) 1)) *
          shiftedPacketPhase k j 1
        =
      Complex.exp (Complex.I * ↑(hardyStart (k + 1) * shiftedRelativePhase (k + 1) (j + 1))) := by
    unfold shiftedPacketPhase
    simpa [blockCoord_one] using hexp
  rw [weightedResonantBlockMode_one_eq_next_zero_shift]
  unfold shiftedSinglePrimitive
  calc
    (weightedResonantBlockMode (k + 1) 0 *
          ((((shiftedRelativeWeight (k + 1) 1 : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ↑(hardyStart (k + 1) * shiftedRelativePhase (k + 1) 1)))) *
        ((-Complex.I) * (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ)) *
          shiftedPacketPhase k j 1)
        =
      weightedResonantBlockMode (k + 1) 0 *
        (((-Complex.I) * (((shiftedRelativeWeight (k + 1) 1 * shiftedRelativeWeight k j
              / shiftedRelativePhase k j : ℝ) : ℂ))) *
          (Complex.exp (Complex.I * ↑(hardyStart (k + 1) * shiftedRelativePhase (k + 1) 1)) *
            shiftedPacketPhase k j 1)) := by
            unfold shiftedPacketPhase
            simp [blockCoord_one]
            ring
    _ =
      weightedResonantBlockMode (k + 1) 0 *
        (((-Complex.I) * (((shiftedRelativeWeight (k + 1) 1 * shiftedRelativeWeight k j
              / shiftedRelativePhase k j : ℝ) : ℂ))) *
          Complex.exp (Complex.I * ↑(hardyStart (k + 1) * shiftedRelativePhase (k + 1) (j + 1)))) := by
            rw [hpacket1]
    _ =
      weightedResonantBlockMode (k + 1) 0 *
        ((((shiftedRelativePhase (k + 1) (j + 1) / shiftedRelativePhase k j : ℝ) : ℂ)) *
          (((-Complex.I) * (((shiftedRelativeWeight (k + 1) (j + 1)
                / shiftedRelativePhase (k + 1) (j + 1) : ℝ) : ℂ))) *
            Complex.exp (Complex.I * ↑(hardyStart (k + 1) * shiftedRelativePhase (k + 1) (j + 1))))) := by
            rw [hcoeff]
            ring
    _ =
      (((shiftedRelativePhase (k + 1) (j + 1) / shiftedRelativePhase k j : ℝ) : ℂ)) *
        (weightedResonantBlockMode (k + 1) 0 *
          ((-Complex.I) *
              (((shiftedRelativeWeight (k + 1) (j + 1)
                  / shiftedRelativePhase (k + 1) (j + 1) : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ↑(hardyStart (k + 1) * shiftedRelativePhase (k + 1) (j + 1))))) := by
            ring
    _ =
      (((shiftedRelativePhase (k + 1) (j + 1) / shiftedRelativePhase k j : ℝ) : ℂ)) *
        (weightedResonantBlockMode (k + 1) 0 *
          shiftedSinglePrimitive (k + 1) (j + 1) 0) := by
            unfold shiftedSinglePrimitive shiftedPacketPhase
            simp [blockCoord_zero]

/-- The scaled lower endpoint contribution on the fixed-mode diagonal
`k = n + j`. Multiplying by `shiftedRelativePhase` is the exact normalization
that makes the step relation telescope without any ratio defect. -/
private noncomputable def shiftedSingleBoundaryCore (n j : ℕ) : ℂ :=
  (((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
    (weightedResonantBlockMode (n + j) 0 * shiftedSinglePrimitive (n + j) j 0)

private lemma shiftedSingleBoundaryCore_eq_phase_mul_boundary
    (n j : ℕ) (hj : 1 ≤ j) :
    shiftedSingleBoundaryCore n j
      =
      (((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        (weightedResonantBlockMode (n + j) 0 *
          shiftedSinglePrimitive (n + j) j 0) := by
  rfl

private lemma shiftedSingleBoundaryCore_step
    (n j : ℕ) (hj : 1 ≤ j) :
    (((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        (weightedResonantBlockMode (n + j) 1 *
          shiftedSinglePrimitive (n + j) j 1)
      =
      shiftedSingleBoundaryCore n (j + 1) := by
  have hjk : j ≤ n + j := by omega
  have hstep :=
    weightedResonantBlockMode_one_mul_shiftedSinglePrimitive_step (n + j) j hj hjk
  unfold shiftedSingleBoundaryCore
  have hphase_pos : 0 < shiftedRelativePhase (n + j) j :=
    shiftedRelativePhase_pos (n + j) j hj hjk
  calc
    (((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          (weightedResonantBlockMode (n + j) 1 *
            shiftedSinglePrimitive (n + j) j 1)
        =
      (((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        ((((shiftedRelativePhase (n + j + 1) (j + 1) / shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          (weightedResonantBlockMode (n + j + 1) 0 *
            shiftedSinglePrimitive (n + j + 1) (j + 1) 0)) := by
            rw [hstep]
    _ =
      (((shiftedRelativePhase (n + j + 1) (j + 1) : ℝ) : ℂ)) *
        (weightedResonantBlockMode (n + j + 1) 0 *
          shiftedSinglePrimitive (n + j + 1) (j + 1) 0) := by
            calc
              (((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                    ((((shiftedRelativePhase (n + j + 1) (j + 1) /
                        shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
                      (weightedResonantBlockMode (n + j + 1) 0 *
                        shiftedSinglePrimitive (n + j + 1) (j + 1) 0))
                  =
                ((((shiftedRelativePhase (n + j) j) *
                    (shiftedRelativePhase (n + j + 1) (j + 1) /
                      shiftedRelativePhase (n + j) j) : ℝ) : ℂ)) *
                  (weightedResonantBlockMode (n + j + 1) 0 *
                    shiftedSinglePrimitive (n + j + 1) (j + 1) 0) := by
                      rw [← mul_assoc, ← Complex.ofReal_mul]
              _ =
                (((shiftedRelativePhase (n + j + 1) (j + 1) : ℝ) : ℂ)) *
                  (weightedResonantBlockMode (n + j + 1) 0 *
                    shiftedSinglePrimitive (n + j + 1) (j + 1) 0) := by
                      congr 1
                      field_simp [ne_of_gt hphase_pos]

private lemma shiftedSingleBoundaryCore_norm
    (n j : ℕ) (hj : 1 ≤ j) :
    ‖shiftedSingleBoundaryCore n j‖ = modeWeight n := by
  have hjk : j ≤ n + j := by omega
  have hphase_pos : 0 < shiftedRelativePhase (n + j) j :=
    shiftedRelativePhase_pos (n + j) j hj hjk
  unfold shiftedSingleBoundaryCore shiftedSinglePrimitive
  have hphase_nonneg : 0 ≤ shiftedRelativePhase (n + j) j := le_of_lt hphase_pos
  have hweight_nonneg : 0 ≤ shiftedRelativeWeight (n + j) j :=
    shiftedRelativeWeight_nonneg (n + j) j
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hphase_nonneg]
  rw [norm_mul, weightedResonantBlockMode_norm]
  have hmul :
      modeWeight (n + j) * shiftedRelativeWeight (n + j) j = modeWeight n := by
    simpa using modeWeight_mul_shiftedRelativeWeight (n + j) j
  have habs :
      |shiftedRelativeWeight (n + j) j / shiftedRelativePhase (n + j) j|
        = shiftedRelativeWeight (n + j) j / shiftedRelativePhase (n + j) j := by
    exact abs_of_nonneg (div_nonneg hweight_nonneg hphase_nonneg)
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    norm_shiftedPacketPhase]
  rw [habs]
  simp
  calc
    shiftedRelativePhase (n + j) j *
        (modeWeight (n + j) *
          (shiftedRelativeWeight (n + j) j / shiftedRelativePhase (n + j) j))
      = shiftedRelativePhase (n + j) j *
          ((modeWeight (n + j) * shiftedRelativeWeight (n + j) j) /
            shiftedRelativePhase (n + j) j) := by
            ring
    _ = shiftedRelativePhase (n + j) j *
          (modeWeight n / shiftedRelativePhase (n + j) j) := by
            rw [hmul]
    _ = modeWeight n := by
          field_simp [ne_of_gt hphase_pos]

private lemma shiftedSingleBoundaryCore_eq_weightedModeStart
    (n j : ℕ) (hj : 1 ≤ j) :
    shiftedSingleBoundaryCore n j
      =
      (-Complex.I) *
        ((((modeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (hardyStart (n + j)))) := by
  have hjk : j ≤ n + j := by omega
  calc
    shiftedSingleBoundaryCore n j
        =
      (((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        (weightedResonantBlockMode (n + j) 0 * shiftedSinglePrimitive (n + j) j 0) := by
            rfl
    _ =
      weightedResonantBlockMode (n + j) 0 *
        ((((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          shiftedSinglePrimitive (n + j) j 0) := by
            ring
    _ =
      weightedResonantBlockMode (n + j) 0 *
        ((-Complex.I) * shiftedSinglePacket (n + j) j 0) := by
            rw [shiftedRelativePhase_mul_shiftedSinglePrimitive (n + j) j hj hjk 0]
    _ =
      (-Complex.I) *
        (weightedResonantBlockMode (n + j) 0 *
          shiftedSinglePacket (n + j) j 0) := by
            ring
    _ =
      (-Complex.I) *
        ((((modeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (blockCoord (n + j) 0))) := by
            simpa [shiftedSinglePacket, shiftedPacketPhase] using
              congrArg (fun z : ℂ => (-Complex.I) * z)
                (weighted_hardyCosExp_eq_resonant_times_shiftedPacket (n + j) j 0).symm
    _ =
      (-Complex.I) *
        ((((modeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (hardyStart (n + j)))) := by
            simp [blockCoord_zero]

private lemma shiftedRelativeWeight_antidiagonal_ratio
    (n j : ℕ) :
    shiftedRelativeWeight (n + j + 1) (j + 1) / shiftedRelativeWeight (n + j + 1) j
      = modeWeight n / modeWeight (n + 1) := by
  unfold shiftedRelativeWeight
  have hk_ne : modeWeight (n + j + 1) ≠ 0 := modeWeight_ne_zero (n + j + 1)
  have hn1_ne : modeWeight (n + 1) ≠ 0 := modeWeight_ne_zero (n + 1)
  have hsub1 : n + j + 1 - (j + 1) = n := by omega
  have hsub2 : n + j + 1 - j = n + 1 := by omega
  rw [show modeWeight (n + j + 1 - (j + 1)) = modeWeight n by simpa [hsub1]]
  rw [show modeWeight (n + j + 1 - j) = modeWeight (n + 1) by simpa [hsub2]]
  field_simp [hk_ne, hn1_ne]

private lemma shiftedRelativePhase_antidiagonal_step
    (n j : ℕ) (hj : 1 ≤ j) :
    shiftedRelativePhase (n + j + 1) (j + 1)
      - shiftedRelativePhase (n + j + 1) j
        = shiftedRelativePhase (n + 1) 1 := by
  have hsub1 : n + j + 1 - (j + 1) = n := by omega
  have hsub2 : n + j + 1 - j = n + 1 := by omega
  rw [shiftedRelativePhase_eq_sub_logs, shiftedRelativePhase_eq_sub_logs]
  have h1 : (((n + j + 1 - (j + 1) : ℕ) : ℝ) + 1) = (n : ℝ) + 1 := by
    norm_num [hsub1]
  have h2 : (((n + j + 1 - j : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by
    rw [hsub2]
    norm_num [Nat.cast_add]
    ring
  rw [h1, h2]
  have h3 : shiftedRelativePhase (n + 1) 1 = Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) := by
    rw [shiftedRelativePhase_eq_sub_logs]
    norm_num
    ring
  rw [h3]
  ring

/-- Exact anti-diagonal transport for the weighted Hardy mode at block starts.
This rewrites the shifted start value for mode `n` on block `n+j+1` in terms of
the next mode `n+1` on the same block. -/
private lemma weightedModeStart_antidiagonal_transport
    (n j : ℕ) (hj : 1 ≤ j) :
    (((modeWeight n : ℝ) : ℂ) *
        HardyCosSmooth.hardyCosExp n (hardyStart (n + j + 1)))
      =
      ((((modeWeight (n + 1) : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp (n + 1) (hardyStart (n + j + 1))) *
        ((((modeWeight n / modeWeight (n + 1) : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ↑(hardyStart (n + j + 1) * shiftedRelativePhase (n + 1) 1)))) := by
  let k : ℕ := n + j + 1
  have hkj : j ≤ k := by
    dsimp [k]
    omega
  have hkj1 : j + 1 ≤ k := by
    dsimp [k]
    omega
  have hA :=
    weighted_hardyCosExp_eq_resonant_times_shiftedPacket k (j + 1) 0
  have hB :=
    weighted_hardyCosExp_eq_resonant_times_shiftedPacket k j 0
  have hratio :
      shiftedRelativeWeight k (j + 1) / shiftedRelativeWeight k j
        = modeWeight n / modeWeight (n + 1) := by
    dsimp [k]
    exact shiftedRelativeWeight_antidiagonal_ratio n j
  have hphase_step :
      shiftedRelativePhase k (j + 1) - shiftedRelativePhase k j
        = shiftedRelativePhase (n + 1) 1 := by
    dsimp [k]
    exact shiftedRelativePhase_antidiagonal_step n j hj
  have hphase_ne : shiftedRelativeWeight k j ≠ 0 := by
    exact ne_of_gt <| by
      unfold shiftedRelativeWeight
      exact div_pos (modeWeight_pos (k - j)) (modeWeight_pos k)
  have hexp :
      Complex.exp (Complex.I * ↑(hardyStart k * shiftedRelativePhase k (j + 1)))
        =
      Complex.exp (Complex.I * ↑(hardyStart k * shiftedRelativePhase k j)) *
        Complex.exp (Complex.I * ↑(hardyStart k * shiftedRelativePhase (n + 1) 1)) := by
    rw [← hphase_step]
    have hsplit :
        hardyStart k * shiftedRelativePhase k (j + 1)
          =
        hardyStart k * shiftedRelativePhase k j
          + hardyStart k *
              (shiftedRelativePhase k (j + 1) - shiftedRelativePhase k j) := by
      ring
    have harg :
        Complex.I *
            ↑(hardyStart k * shiftedRelativePhase k j +
                hardyStart k * (shiftedRelativePhase k (j + 1) - shiftedRelativePhase k j))
          =
        Complex.I * ↑(hardyStart k * shiftedRelativePhase k j)
          + Complex.I * ↑(hardyStart k * (shiftedRelativePhase k (j + 1) - shiftedRelativePhase k j)) := by
      simp [mul_add, add_mul]
    rw [hsplit, harg, Complex.exp_add]
  let R : ℂ := (((modeWeight k : ℝ) : ℂ) * HardyCosSmooth.hardyCosExp k (hardyStart k))
  let Pj : ℂ :=
    ((((shiftedRelativeWeight k j : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ↑(hardyStart k * shiftedRelativePhase k j)))
  let Pj1 : ℂ :=
    ((((shiftedRelativeWeight k (j + 1) : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ↑(hardyStart k * shiftedRelativePhase k (j + 1))))
  let F : ℂ :=
    ((((modeWeight n / modeWeight (n + 1) : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ↑(hardyStart k * shiftedRelativePhase (n + 1) 1)))
  have hk_sub_j1 : k - (j + 1) = n := by
    dsimp [k]
    omega
  have hk_sub_j : k - j = n + 1 := by
    dsimp [k]
    omega
  have hA' :
      (((modeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (hardyStart (n + j + 1)))
        = R * Pj1 := by
    simpa [R, Pj1, k, blockCoord_zero, hk_sub_j1] using hA
  have hB' :
      (((modeWeight (n + 1) : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp (n + 1) (hardyStart (n + j + 1)))
        = R * Pj := by
    simpa [R, Pj, k, blockCoord_zero, hk_sub_j] using hB
  have hratio' :
      shiftedRelativeWeight k (j + 1)
        = (modeWeight n / modeWeight (n + 1)) * shiftedRelativeWeight k j := by
    exact (div_eq_iff hphase_ne).mp hratio
  have hpacket :
      Pj1 = Pj * F := by
    unfold Pj1 Pj F
    rw [hexp, hratio']
    simp [mul_assoc, mul_left_comm, mul_comm]
  calc
    (((modeWeight n : ℝ) : ℂ) *
        HardyCosSmooth.hardyCosExp n (hardyStart (n + j + 1)))
        = R * Pj1 := hA'
    _ = R * (Pj * F) := by rw [hpacket]
    _ = (R * Pj) * F := by ring
    _ = ((((modeWeight (n + 1) : ℝ) : ℂ) *
            HardyCosSmooth.hardyCosExp (n + 1) (hardyStart (n + j + 1))) * F) := by
          rw [hB']
    _ =
      ((((modeWeight (n + 1) : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp (n + 1) (hardyStart (n + j + 1))) *
        ((((modeWeight n / modeWeight (n + 1) : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ↑(hardyStart (n + j + 1) * shiftedRelativePhase (n + 1) 1)))) := by
          rfl

/-- Exact anti-diagonal transport for the normalized boundary core.  This is
the fixed-shift recurrence that the global near-band cancellation must exploit. -/
private theorem shiftedSingleBoundaryCore_antidiagonal_transport
    (n j : ℕ) (hj : 1 ≤ j) :
    shiftedSingleBoundaryCore n (j + 1)
      =
      shiftedSingleBoundaryCore (n + 1) j *
        ((((modeWeight n / modeWeight (n + 1) : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ↑(hardyStart (n + j + 1) * shiftedRelativePhase (n + 1) 1))) := by
  have htransport := weightedModeStart_antidiagonal_transport n j hj
  calc
    shiftedSingleBoundaryCore n (j + 1)
      =
      (-Complex.I) *
        ((((modeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (hardyStart (n + j + 1)))) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          shiftedSingleBoundaryCore_eq_weightedModeStart n (j + 1) (by omega)
    _ =
      (-Complex.I) *
        (((((modeWeight (n + 1) : ℝ) : ℂ) *
            HardyCosSmooth.hardyCosExp (n + 1) (hardyStart (n + j + 1))) *
          ((((modeWeight n / modeWeight (n + 1) : ℝ) : ℂ)) *
            Complex.exp (Complex.I *
              ↑(hardyStart (n + j + 1) * shiftedRelativePhase (n + 1) 1))))) := by
        rw [htransport]
    _ =
      ((-Complex.I) *
          ((((modeWeight (n + 1) : ℝ) : ℂ) *
            HardyCosSmooth.hardyCosExp (n + 1) (hardyStart (n + j + 1))))) *
        ((((modeWeight n / modeWeight (n + 1) : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ↑(hardyStart (n + j + 1) * shiftedRelativePhase (n + 1) 1))) := by
        ring
    _ =
      shiftedSingleBoundaryCore (n + 1) j *
        ((((modeWeight n / modeWeight (n + 1) : ℝ) : ℂ)) *
          Complex.exp (Complex.I *
            ↑(hardyStart (n + j + 1) * shiftedRelativePhase (n + 1) 1))) := by
        rw [shiftedSingleBoundaryCore_eq_weightedModeStart (n + 1) j hj]
        simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private lemma shiftedSingleBoundaryCore_antidiagonal_transport_factor_norm
    (n j : ℕ) :
    ‖((((modeWeight n / modeWeight (n + 1) : ℝ) : ℂ)) *
        Complex.exp (Complex.I *
          ↑(hardyStart (n + j + 1) * shiftedRelativePhase (n + 1) 1)))‖
      = modeWeight n / modeWeight (n + 1) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have hnonneg : 0 ≤ modeWeight n / modeWeight (n + 1) := by
    exact div_nonneg (le_of_lt (modeWeight_pos n)) (le_of_lt (modeWeight_pos (n + 1)))
  simp [abs_of_nonneg hnonneg]

private noncomputable def antiDiagonalStepPhase (n j : ℕ) : ℝ :=
  hardyStart (n + j + 1) * shiftedRelativePhase (n + 1) 1

private noncomputable def normalizedShiftedSingleBoundaryCore (n j : ℕ) : ℂ :=
  shiftedSingleBoundaryCore n j / (((modeWeight n : ℝ) : ℂ))

private theorem normalizedShiftedSingleBoundaryCore_antidiagonal_transport
    (n j : ℕ) (hj : 1 ≤ j) :
    normalizedShiftedSingleBoundaryCore n (j + 1)
      =
      normalizedShiftedSingleBoundaryCore (n + 1) j *
        Complex.exp (Complex.I * ↑(antiDiagonalStepPhase n j)) := by
  have hn_ne : (((modeWeight n : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast modeWeight_ne_zero n
  have hn1_ne : (((modeWeight (n + 1) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast modeWeight_ne_zero (n + 1)
  have hratio_div :
      ((((modeWeight n / modeWeight (n + 1) : ℝ) : ℂ)) /
          (((modeWeight n : ℝ) : ℂ)))
        =
      1 / (((modeWeight (n + 1) : ℝ) : ℂ)) := by
    field_simp [hn_ne, hn1_ne]
    have hratio_mul :
        (modeWeight n / modeWeight (n + 1)) * modeWeight (n + 1) = modeWeight n := by
      field_simp [modeWeight_ne_zero (n + 1)]
    exact_mod_cast hratio_mul
  unfold normalizedShiftedSingleBoundaryCore antiDiagonalStepPhase
  rw [shiftedSingleBoundaryCore_antidiagonal_transport n j hj]
  calc
    (shiftedSingleBoundaryCore (n + 1) j *
        ((((modeWeight n / modeWeight (n + 1) : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ↑(hardyStart (n + j + 1) * shiftedRelativePhase (n + 1) 1)))) /
        (((modeWeight n : ℝ) : ℂ))
      =
    shiftedSingleBoundaryCore (n + 1) j *
      (((((modeWeight n / modeWeight (n + 1) : ℝ) : ℂ)) /
          (((modeWeight n : ℝ) : ℂ))) *
        Complex.exp (Complex.I * ↑(hardyStart (n + j + 1) * shiftedRelativePhase (n + 1) 1))) := by
          rw [div_eq_mul_inv]
          ring
    _ =
      shiftedSingleBoundaryCore (n + 1) j *
        ((1 / (((modeWeight (n + 1) : ℝ) : ℂ))) *
          Complex.exp (Complex.I * ↑(hardyStart (n + j + 1) * shiftedRelativePhase (n + 1) 1))) := by
          rw [hratio_div]
    _ =
      (shiftedSingleBoundaryCore (n + 1) j / (((modeWeight (n + 1) : ℝ) : ℂ))) *
        Complex.exp (Complex.I * ↑(hardyStart (n + j + 1) * shiftedRelativePhase (n + 1) 1)) := by
          rw [div_eq_mul_inv]
          ring

private theorem normalizedShiftedSingleBoundaryCore_norm
    (n j : ℕ) (hj : 1 ≤ j) :
    ‖normalizedShiftedSingleBoundaryCore n j‖ = 1 := by
  unfold normalizedShiftedSingleBoundaryCore
  rw [norm_div, shiftedSingleBoundaryCore_norm n j hj, Complex.norm_real, Real.norm_eq_abs]
  simp [abs_of_pos (modeWeight_pos n), modeWeight_ne_zero n]

private lemma mul_exp_I_ofReal_add (z : ℂ) (a b : ℝ) :
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

private lemma exp_I_ofReal_sub_split (a b : ℝ) :
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

private theorem antiDiagonalStepPhase_antidiagonal
    (K j : ℕ) (hj1 : 1 ≤ j) (hjK : j ≤ K) :
    antiDiagonalStepPhase (K - j) j
      =
      hardyStart (K + 1) *
        (Real.log ((((K - j : ℕ) : ℝ) + 2)) - Real.log ((((K - j : ℕ) : ℝ) + 1))) := by
  have hsum : K - j + j + 1 = K + 1 := by omega
  unfold antiDiagonalStepPhase
  rw [shiftedRelativePhase_eq_sub_logs]
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

private theorem antiDiagonalStepPhase_antidiagonal_sum
    (K m : ℕ) (hm : m ≤ K) :
    Finset.sum (Finset.range m) (fun r => antiDiagonalStepPhase (K - (r + 1)) (r + 1))
      =
      hardyStart (K + 1) *
        (Real.log ((K : ℝ) + 1) - Real.log ((((K - m : ℕ) : ℝ) + 1))) := by
  induction' m with m ih
  · simp
  · have hmK : m ≤ K := by omega
    have hm1K : m + 1 ≤ K := by omega
    have hstep := antiDiagonalStepPhase_antidiagonal K (m + 1) (by omega) hm1K
    have hmid : Real.log ((((K - (m + 1) : ℕ) : ℝ) + 2)) = Real.log ((((K - m : ℕ) : ℝ) + 1)) := by
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
      Finset.sum (Finset.range (m + 1)) (fun r => antiDiagonalStepPhase (K - (r + 1)) (r + 1))
          =
        Finset.sum (Finset.range m) (fun r => antiDiagonalStepPhase (K - (r + 1)) (r + 1))
          + antiDiagonalStepPhase (K - (m + 1)) (m + 1) := by
              rw [Finset.sum_range_succ]
      _ =
        hardyStart (K + 1) *
          (Real.log ((K : ℝ) + 1) - Real.log ((((K - m : ℕ) : ℝ) + 1)))
          + antiDiagonalStepPhase (K - (m + 1)) (m + 1) := by
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

private theorem normalizedShiftedSingleBoundaryCore_antidiagonal_expSum
    (K m : ℕ) (hm : m ≤ K) :
    normalizedShiftedSingleBoundaryCore (K - m) (m + 1)
      =
      normalizedShiftedSingleBoundaryCore K 1 *
        Complex.exp
          (Complex.I *
            ↑((Finset.sum (Finset.range m)
              (fun r => antiDiagonalStepPhase (K - (r + 1)) (r + 1))) : ℝ)) := by
  induction' m with m ih
  · simp
  · have hmK : m ≤ K := by omega
    have hsub : K - m = K - (m + 1) + 1 := by omega
    have htransport :
        normalizedShiftedSingleBoundaryCore (K - (m + 1)) ((m + 1) + 1)
          =
        normalizedShiftedSingleBoundaryCore (K - m) (m + 1) *
          Complex.exp (Complex.I * ↑(antiDiagonalStepPhase (K - (m + 1)) (m + 1))) := by
      simpa [hsub, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        normalizedShiftedSingleBoundaryCore_antidiagonal_transport (K - (m + 1)) (m + 1) (by omega)
    calc
      normalizedShiftedSingleBoundaryCore (K - (m + 1)) ((m + 1) + 1)
          =
        normalizedShiftedSingleBoundaryCore (K - m) (m + 1) *
          Complex.exp (Complex.I * ↑(antiDiagonalStepPhase (K - (m + 1)) (m + 1))) := htransport
      _ =
        (normalizedShiftedSingleBoundaryCore K 1 *
          Complex.exp
            (Complex.I *
              ↑((Finset.sum (Finset.range m)
                (fun r => antiDiagonalStepPhase (K - (r + 1)) (r + 1))) : ℝ)) *
          Complex.exp (Complex.I * ↑(antiDiagonalStepPhase (K - (m + 1)) (m + 1)))) := by
              rw [ih hmK]
      _ =
        normalizedShiftedSingleBoundaryCore K 1 *
          Complex.exp
            (Complex.I *
              ↑((Finset.sum (Finset.range m)
                  (fun r => antiDiagonalStepPhase (K - (r + 1)) (r + 1)))
                + antiDiagonalStepPhase (K - (m + 1)) (m + 1))) := by
              simpa using mul_exp_I_ofReal_add
                (normalizedShiftedSingleBoundaryCore K 1)
                (Finset.sum (Finset.range m)
                  (fun r => antiDiagonalStepPhase (K - (r + 1)) (r + 1)))
                (antiDiagonalStepPhase (K - (m + 1)) (m + 1))
      _ =
        normalizedShiftedSingleBoundaryCore K 1 *
          Complex.exp
            (Complex.I *
              ↑((Finset.sum (Finset.range (m + 1))
                (fun r => antiDiagonalStepPhase (K - (r + 1)) (r + 1))) : ℝ)) := by
              rw [Finset.sum_range_succ]

private theorem normalizedShiftedSingleBoundaryCore_antidiagonal_closed_form
    (K m : ℕ) (hm : m ≤ K) :
    normalizedShiftedSingleBoundaryCore (K - m) (m + 1)
      =
      normalizedShiftedSingleBoundaryCore K 1 *
        Complex.exp
          (Complex.I *
            ↑(hardyStart (K + 1) *
              (Real.log ((K : ℝ) + 1) - Real.log ((((K - m : ℕ) : ℝ) + 1))))) := by
  rw [normalizedShiftedSingleBoundaryCore_antidiagonal_expSum K m hm]
  rw [antiDiagonalStepPhase_antidiagonal_sum K m hm]

private theorem normalizedShiftedSingleBoundaryCore_antidiagonal_closed_form'
    (J n : ℕ) (hn : n ≤ J) :
    normalizedShiftedSingleBoundaryCore n (J + 1 - n)
      =
      normalizedShiftedSingleBoundaryCore J 1 *
        Complex.exp
          (Complex.I *
            ↑(hardyStart (J + 1) *
              (Real.log ((J : ℝ) + 1) - Real.log ((n : ℝ) + 1)))) := by
  have h := normalizedShiftedSingleBoundaryCore_antidiagonal_closed_form J (J - n) (by omega)
  have hsub : J - (J - n) = n := by omega
  have hj : J - n + 1 = J + 1 - n := by omega
  simpa [hsub, hj, Nat.cast_add, add_assoc, add_left_comm, add_comm] using h

private theorem normalizedShiftedSingleBoundaryCore_antidiagonal_sum_eq_dirichletSlice
    (J : ℕ) :
    Finset.sum (Finset.range (J + 1))
        (fun n => normalizedShiftedSingleBoundaryCore n (J + 1 - n))
      =
      normalizedShiftedSingleBoundaryCore J 1 *
        Complex.exp (Complex.I * ↑(hardyStart (J + 1) * Real.log ((J : ℝ) + 1))) *
        Finset.sum (Finset.range (J + 1))
          (fun n => Complex.exp (-Complex.I * ↑(hardyStart (J + 1) * Real.log ((n : ℝ) + 1)))) := by
  calc
    Finset.sum (Finset.range (J + 1))
        (fun n => normalizedShiftedSingleBoundaryCore n (J + 1 - n))
        =
      Finset.sum (Finset.range (J + 1)) (fun n =>
        normalizedShiftedSingleBoundaryCore J 1 *
          Complex.exp
            (Complex.I *
              ↑(hardyStart (J + 1) *
                (Real.log ((J : ℝ) + 1) - Real.log ((n : ℝ) + 1))))) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              exact normalizedShiftedSingleBoundaryCore_antidiagonal_closed_form' J n
                (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
    _ =
      Finset.sum (Finset.range (J + 1)) (fun n =>
        normalizedShiftedSingleBoundaryCore J 1 *
          (Complex.exp (Complex.I * ↑(hardyStart (J + 1) * Real.log ((J : ℝ) + 1))) *
            Complex.exp (-Complex.I * ↑(hardyStart (J + 1) * Real.log ((n : ℝ) + 1))))) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              have hsplit :
                  hardyStart (J + 1) *
                      (Real.log ((J : ℝ) + 1) - Real.log ((n : ℝ) + 1))
                    =
                  hardyStart (J + 1) * Real.log ((J : ℝ) + 1) -
                    hardyStart (J + 1) * Real.log ((n : ℝ) + 1) := by
                ring
              rw [hsplit, exp_I_ofReal_sub_split
                (hardyStart (J + 1) * Real.log ((J : ℝ) + 1))
                (hardyStart (J + 1) * Real.log ((n : ℝ) + 1))]
    _ =
      normalizedShiftedSingleBoundaryCore J 1 *
        Complex.exp (Complex.I * ↑(hardyStart (J + 1) * Real.log ((J : ℝ) + 1))) *
        Finset.sum (Finset.range (J + 1))
          (fun n => Complex.exp (-Complex.I * ↑(hardyStart (J + 1) * Real.log ((n : ℝ) + 1)))) := by
              rw [Finset.mul_sum]
              simp_rw [mul_assoc]

private theorem normalizedShiftedSingleBoundaryCore_antidiagonal_sum_norm_eq_dirichletSlice
    (J : ℕ) :
    ‖Finset.sum (Finset.range (J + 1))
        (fun n => normalizedShiftedSingleBoundaryCore n (J + 1 - n))‖
      =
      ‖Finset.sum (Finset.range (J + 1))
          (fun n => Complex.exp (-Complex.I * ↑(hardyStart (J + 1) * Real.log ((n : ℝ) + 1))))‖ := by
  rw [normalizedShiftedSingleBoundaryCore_antidiagonal_sum_eq_dirichletSlice]
  rw [norm_mul, norm_mul]
  have hnorm_anchor :
      ‖normalizedShiftedSingleBoundaryCore J 1‖ = 1 :=
    normalizedShiftedSingleBoundaryCore_norm J 1 (by norm_num)
  have hnorm_phase :
      ‖Complex.exp (Complex.I * ↑(hardyStart (J + 1) * Real.log ((J : ℝ) + 1)))‖ = 1 := by
        rw [Complex.norm_exp]
        simp
  rw [hnorm_anchor, hnorm_phase]
  simp

private lemma shiftedSingleBoundaryCore_eq_modeWeight_mul_normalized
    (n j : ℕ) :
    shiftedSingleBoundaryCore n j
      = (((modeWeight n : ℝ) : ℂ)) * normalizedShiftedSingleBoundaryCore n j := by
  have hne : (((modeWeight n : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast modeWeight_ne_zero n
  unfold normalizedShiftedSingleBoundaryCore
  field_simp [hne]

private theorem shiftedSingleBoundaryCore_antidiagonal_sum_eq_weightedDirichletSlice
    (J : ℕ) :
    Finset.sum (Finset.range (J + 1))
        (fun n => shiftedSingleBoundaryCore n (J + 1 - n))
      =
      normalizedShiftedSingleBoundaryCore J 1 *
        Complex.exp (Complex.I * ↑(hardyStart (J + 1) * Real.log ((J : ℝ) + 1))) *
        Finset.sum (Finset.range (J + 1))
          (fun n =>
            (((modeWeight n : ℝ) : ℂ)) *
              Complex.exp (-Complex.I * ↑(hardyStart (J + 1) * Real.log ((n : ℝ) + 1)))) := by
  calc
    Finset.sum (Finset.range (J + 1))
        (fun n => shiftedSingleBoundaryCore n (J + 1 - n))
        =
      Finset.sum (Finset.range (J + 1))
        (fun n => (((modeWeight n : ℝ) : ℂ)) *
          normalizedShiftedSingleBoundaryCore n (J + 1 - n)) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [shiftedSingleBoundaryCore_eq_modeWeight_mul_normalized]
    _ =
      Finset.sum (Finset.range (J + 1))
        (fun n =>
          normalizedShiftedSingleBoundaryCore J 1 *
            Complex.exp (Complex.I * ↑(hardyStart (J + 1) * Real.log ((J : ℝ) + 1))) *
            ((((modeWeight n : ℝ) : ℂ)) *
              Complex.exp (-Complex.I * ↑(hardyStart (J + 1) * Real.log ((n : ℝ) + 1))))) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [normalizedShiftedSingleBoundaryCore_antidiagonal_closed_form' J n
              (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]
            have hexp :
                Complex.exp
                    (Complex.I *
                      ↑(hardyStart (J + 1) *
                        (Real.log ((J : ℝ) + 1) - Real.log ((n : ℝ) + 1))))
                  =
                Complex.exp (Complex.I * ↑(hardyStart (J + 1) * Real.log ((J : ℝ) + 1))) *
                  Complex.exp (-Complex.I * ↑(hardyStart (J + 1) * Real.log ((n : ℝ) + 1))) := by
                    rw [← Complex.exp_add]
                    congr 1
                    rw [show hardyStart (J + 1) *
                        (Real.log ((J : ℝ) + 1) - Real.log ((n : ℝ) + 1))
                          =
                        hardyStart (J + 1) * Real.log ((J : ℝ) + 1)
                          - hardyStart (J + 1) * Real.log ((n : ℝ) + 1) by ring]
                    rw [Complex.ofReal_sub, mul_sub, sub_eq_add_neg, neg_mul]
            rw [hexp]
            ring
    _ =
      normalizedShiftedSingleBoundaryCore J 1 *
        Complex.exp (Complex.I * ↑(hardyStart (J + 1) * Real.log ((J : ℝ) + 1))) *
        Finset.sum (Finset.range (J + 1))
          (fun n =>
            (((modeWeight n : ℝ) : ℂ)) *
              Complex.exp (-Complex.I * ↑(hardyStart (J + 1) * Real.log ((n : ℝ) + 1)))) := by
            rw [Finset.mul_sum]

private theorem shiftedSingleBoundaryCore_antidiagonal_sum_bound
    (J : ℕ) :
    ‖Finset.sum (Finset.range (J + 1))
        (fun n => shiftedSingleBoundaryCore n (J + 1 - n))‖
      ≤ 2 * Real.sqrt (J + 1) := by
  rw [shiftedSingleBoundaryCore_antidiagonal_sum_eq_weightedDirichletSlice]
  rw [norm_mul, norm_mul]
  have hnorm_anchor :
      ‖normalizedShiftedSingleBoundaryCore J 1‖ = 1 :=
    normalizedShiftedSingleBoundaryCore_norm J 1 (by norm_num)
  have hnorm_phase :
      ‖Complex.exp (Complex.I * ↑(hardyStart (J + 1) * Real.log ((J : ℝ) + 1)))‖ = 1 := by
        rw [Complex.norm_exp]
        simp
  rw [hnorm_anchor, hnorm_phase, one_mul, one_mul]
  calc
    ‖Finset.sum (Finset.range (J + 1))
        (fun n =>
          (((modeWeight n : ℝ) : ℂ)) *
            Complex.exp (-Complex.I * ↑(hardyStart (J + 1) * Real.log ((n : ℝ) + 1))))‖
        ≤ Finset.sum (Finset.range (J + 1))
            (fun n =>
              ‖(((modeWeight n : ℝ) : ℂ)) *
                Complex.exp (-Complex.I * ↑(hardyStart (J + 1) * Real.log ((n : ℝ) + 1)))‖) :=
          norm_sum_le _ _
    _ = Finset.sum (Finset.range (J + 1)) (fun n => modeWeight n) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have hnonneg : 0 ≤ modeWeight n := by
            simpa [modeWeight_eq] using weight_nonneg n
          have hexp :
              ‖Complex.exp (-Complex.I * ↑(hardyStart (J + 1) * Real.log ((n : ℝ) + 1)))‖ = 1 := by
            rw [Complex.norm_exp]
            simp
          rw [hexp]
          simp [abs_of_nonneg hnonneg]
    _ ≤ 2 * Real.sqrt (J + 1) := by
          calc
            Finset.sum (Finset.range (J + 1)) (fun n => modeWeight n)
                = Finset.sum (Finset.range (J + 1))
                    (fun n => ((n + 1 : ℝ) ^ (-1 / 2 : ℝ))) := by
                        refine Finset.sum_congr rfl ?_
                        intro n hn
                        rw [modeWeight_eq_neg_half]
            _ ≤ 2 * Real.sqrt (J + 1) := by
                simpa [div_eq_mul_inv, show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by ring_nf] using
                  Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le (J + 1)

private theorem shiftedSingleBoundaryCore_vertical_sum_bound
    (K : ℕ) :
    ‖Finset.sum (Finset.range (K + 1))
        (fun n => shiftedSingleBoundaryCore n 1)‖
      ≤ 2 * Real.sqrt (K + 1) := by
  calc
    ‖Finset.sum (Finset.range (K + 1))
        (fun n => shiftedSingleBoundaryCore n 1)‖
        ≤ Finset.sum (Finset.range (K + 1))
            (fun n => ‖shiftedSingleBoundaryCore n 1‖) := norm_sum_le _ _
    _ = Finset.sum (Finset.range (K + 1)) (fun n => modeWeight n) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [shiftedSingleBoundaryCore_norm n 1 (by norm_num)]
    _ = Finset.sum (Finset.range (K + 1))
          (fun n => ((n + 1 : ℝ) ^ (-1 / 2 : ℝ))) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [modeWeight_eq_neg_half]
    _ ≤ 2 * Real.sqrt (K + 1) := by
          simpa [div_eq_mul_inv, show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by ring_nf] using
            Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le (K + 1)

private theorem weighted_shifted_completeBlock_commonIntegral_eq_resonantCarrier_singlePacket
    (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    (((modeWeight (k - j) : ℝ) : ℂ) *
      ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
        HardyCosSmooth.hardyCosExp (k - j) t)
      =
      ∫ u in (0 : ℝ)..1, resonantBlockCarrier k u * shiftedSinglePacket k j u := by
  rw [hardyCosExp_completeBlock_eq_common_blockParamIntegral k j hj hjk]
  rw [← MeasureTheory.integral_const_mul]
  calc
    ∫ u in Ioc (0 : ℝ) 1,
        (((modeWeight (k - j) : ℝ) : ℂ) *
          (HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u) * (blockJacobian k u : ℂ)))
      =
      ∫ u in Ioc (0 : ℝ) 1, resonantBlockCarrier k u * shiftedSinglePacket k j u := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
        calc
          (((modeWeight (k - j) : ℝ) : ℂ) *
              (HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u) * (blockJacobian k u : ℂ)))
              =
            ((((modeWeight (k - j) : ℝ) : ℂ) *
                HardyCosSmooth.hardyCosExp (k - j) (blockCoord k u)) *
              (blockJacobian k u : ℂ)) := by ring
          _ = resonantBlockCarrier k u * shiftedSinglePacket k j u := by
                rw [weighted_hardyCosExp_eq_resonant_times_shiftedPacket]
                unfold resonantBlockCarrier shiftedSinglePacket shiftedPacketPhase
                ac_rfl
  _ = ∫ u in (0 : ℝ)..1, resonantBlockCarrier k u * shiftedSinglePacket k j u := by
        rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

private theorem resonantCarrier_shiftedSinglePacket_integral_by_parts
    (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∫ u in (0 : ℝ)..1, resonantBlockCarrier k u * shiftedSinglePacket k j u
      =
      weightedResonantBlockMode k 1 * shiftedSinglePrimitive k j 1
        - weightedResonantBlockMode k 0 * shiftedSinglePrimitive k j 0
        - ∫ u in (0 : ℝ)..1,
            (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
              shiftedSinglePrimitive k j u := by
  let f : ℝ → ℂ := weightedResonantBlockMode k
  let G : ℝ → ℂ := shiftedSinglePrimitive k j
  have hG_deriv :
      ∀ u ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt G (((blockJacobian k u : ℂ)) * shiftedSinglePacket k j u) u := by
    intro u hu
    exact shiftedSinglePrimitive_hasDerivAt k j hj hjk u
  have hf_deriv :
      ∀ u ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f
        (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) u := by
    intro u hu
    exact weightedResonantBlockMode_hasDerivAt k u
  have hf'_int :
      IntervalIntegrable
        (fun u => Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u)
        volume (0 : ℝ) 1 := by
    have hcont : Continuous fun u : ℝ =>
        Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u := by
      exact (continuous_const.mul (Complex.continuous_ofReal.comp (blockOmega_continuous k))).mul
        (weightedResonantBlockMode_continuous k)
    simpa [f] using hcont.intervalIntegrable (0 : ℝ) 1
  have hG'_int :
      IntervalIntegrable (fun u => (((blockJacobian k u : ℂ)) * shiftedSinglePacket k j u))
        volume (0 : ℝ) 1 := by
    have hcont : Continuous fun u : ℝ =>
        (((blockJacobian k u : ℂ)) * shiftedSinglePacket k j u) := by
      exact (Complex.continuous_ofReal.comp (blockJacobian_continuous k)).mul <|
        continuous_const.mul <|
          Complex.continuous_exp.comp <|
            continuous_const.mul <|
              Complex.continuous_ofReal.comp ((blockCoord_continuous k).mul continuous_const)
    simpa [G, shiftedSinglePacket] using hcont.intervalIntegrable (0 : ℝ) 1
  have hibp :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      hf_deriv hG_deriv hf'_int hG'_int
  have hrewrite :
      (fun u => f u * (((blockJacobian k u : ℂ)) * shiftedSinglePacket k j u))
        = fun u => resonantBlockCarrier k u * shiftedSinglePacket k j u := by
    funext u
    unfold f weightedResonantBlockMode resonantBlockCarrier shiftedSinglePacket
    unfold Aristotle.StationaryPhaseMainMode.blockMode
    ac_rfl
  rw [hrewrite] at hibp
  simpa [f, G] using hibp

private theorem shifted_completeBlock_complex_mul_phase_eq_boundaryCore_diff
    (n j : ℕ) (hj : 1 ≤ j) :
    (((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
      ((((modeWeight n : ℝ) : ℂ) *
        ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
          HardyCosSmooth.hardyCosExp n t))
      =
      shiftedSingleBoundaryCore n (j + 1) - shiftedSingleBoundaryCore n j
        - (((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
            ∫ u in (0 : ℝ)..1,
              (Complex.I * ((blockOmega (n + j) u : ℝ) : ℂ) *
                weightedResonantBlockMode (n + j) u) *
                  shiftedSinglePrimitive (n + j) j u := by
  have hjk : j ≤ n + j := by omega
  have hmain :=
    weighted_shifted_completeBlock_commonIntegral_eq_resonantCarrier_singlePacket
      (n + j) j hj hjk
  rw [resonantCarrier_shiftedSinglePacket_integral_by_parts (n + j) j hj hjk] at hmain
  calc
    (((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        ((((modeWeight n : ℝ) : ℂ) *
          ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
            HardyCosSmooth.hardyCosExp n t))
        =
      (((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        (weightedResonantBlockMode (n + j) 1 * shiftedSinglePrimitive (n + j) j 1
          - weightedResonantBlockMode (n + j) 0 * shiftedSinglePrimitive (n + j) j 0
          - ∫ u in (0 : ℝ)..1,
              (Complex.I * ((blockOmega (n + j) u : ℝ) : ℂ) *
                weightedResonantBlockMode (n + j) u) *
                  shiftedSinglePrimitive (n + j) j u) := by
            simpa using congrArg
              (fun z : ℂ => (((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) * z) hmain
    _ =
      (((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        (weightedResonantBlockMode (n + j) 1 * shiftedSinglePrimitive (n + j) j 1)
      - (((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
        (weightedResonantBlockMode (n + j) 0 * shiftedSinglePrimitive (n + j) j 0)
      - (((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          ∫ u in (0 : ℝ)..1,
            (Complex.I * ((blockOmega (n + j) u : ℝ) : ℂ) *
              weightedResonantBlockMode (n + j) u) *
                shiftedSinglePrimitive (n + j) j u := by
            ring
    _ =
      shiftedSingleBoundaryCore n (j + 1) - shiftedSingleBoundaryCore n j
      - (((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
          ∫ u in (0 : ℝ)..1,
            (Complex.I * ((blockOmega (n + j) u : ℝ) : ℂ) *
              weightedResonantBlockMode (n + j) u) *
                shiftedSinglePrimitive (n + j) j u := by
            rw [shiftedSingleBoundaryCore_step n j hj,
              shiftedSingleBoundaryCore_eq_phase_mul_boundary n j hj]

private noncomputable def shiftedCompleteBlockPhaseWeightedCell (n j : ℕ) : ℂ :=
  (((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
    ((((modeWeight n : ℝ) : ℂ) *
      ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
        HardyCosSmooth.hardyCosExp n t))

private noncomputable def shiftedCompleteBlockCorrectionTerm (n j : ℕ) : ℂ :=
  (((shiftedRelativePhase (n + j) j : ℝ) : ℂ)) *
    ∫ u in (0 : ℝ)..1,
      (Complex.I * ((blockOmega (n + j) u : ℝ) : ℂ) *
        weightedResonantBlockMode (n + j) u) *
          shiftedSinglePrimitive (n + j) j u

private theorem shifted_completeBlock_complex_mul_phase_sum_eq_boundaryCore_diff
    (n J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, shiftedCompleteBlockPhaseWeightedCell n j
      =
      shiftedSingleBoundaryCore n (J + 1) - shiftedSingleBoundaryCore n 1
        - ∑ j ∈ Finset.Icc 1 J, shiftedCompleteBlockCorrectionTerm n j := by
  induction J with
  | zero =>
      simp [shiftedCompleteBlockPhaseWeightedCell, shiftedCompleteBlockCorrectionTerm]
  | succ J ih =>
      rw [Finset.sum_Icc_succ_top (a := 1) (b := J)
            (f := fun j => shiftedCompleteBlockPhaseWeightedCell n j) (by omega)]
      rw [Finset.sum_Icc_succ_top (a := 1) (b := J)
            (f := fun j => shiftedCompleteBlockCorrectionTerm n j) (by omega)]
      rw [ih]
      calc
        shiftedSingleBoundaryCore n (J + 1) - shiftedSingleBoundaryCore n 1
              - ∑ j ∈ Finset.Icc 1 J, shiftedCompleteBlockCorrectionTerm n j
              + shiftedCompleteBlockPhaseWeightedCell n (J + 1)
            =
          shiftedSingleBoundaryCore n (J + 1) - shiftedSingleBoundaryCore n 1
              - ∑ j ∈ Finset.Icc 1 J, shiftedCompleteBlockCorrectionTerm n j
              + (shiftedSingleBoundaryCore n (J + 1 + 1) - shiftedSingleBoundaryCore n (J + 1)
                  - shiftedCompleteBlockCorrectionTerm n (J + 1)) := by
                    have hcell :
                        shiftedCompleteBlockPhaseWeightedCell n (J + 1)
                          =
                        shiftedSingleBoundaryCore n (J + 1 + 1)
                          - shiftedSingleBoundaryCore n (J + 1)
                          - shiftedCompleteBlockCorrectionTerm n (J + 1) := by
                            unfold shiftedCompleteBlockPhaseWeightedCell
                            simpa using
                              shifted_completeBlock_complex_mul_phase_eq_boundaryCore_diff
                                n (J + 1) (by omega)
                    rw [hcell]
        _ =
          shiftedSingleBoundaryCore n (J + 1 + 1) - shiftedSingleBoundaryCore n 1
            - (∑ k ∈ Finset.Icc 1 J, shiftedCompleteBlockCorrectionTerm n k
                + shiftedCompleteBlockCorrectionTerm n (J + 1)) := by
                  ring

private theorem shiftedCompleteBlockPhaseWeightedTriangle_eq_boundary_diff_minus_correction
    (K : ℕ) :
    Finset.sum (Finset.range (K + 1))
        (fun n => ∑ j ∈ Finset.Icc 1 (K - n), shiftedCompleteBlockPhaseWeightedCell n j)
      =
      Finset.sum (Finset.range (K + 1))
          (fun n => shiftedSingleBoundaryCore n (K + 1 - n))
        - Finset.sum (Finset.range (K + 1))
            (fun n => shiftedSingleBoundaryCore n 1)
        - Finset.sum (Finset.range (K + 1))
            (fun n => ∑ j ∈ Finset.Icc 1 (K - n), shiftedCompleteBlockCorrectionTerm n j) := by
  calc
    Finset.sum (Finset.range (K + 1))
        (fun n => ∑ j ∈ Finset.Icc 1 (K - n), shiftedCompleteBlockPhaseWeightedCell n j)
        =
      Finset.sum (Finset.range (K + 1))
        (fun n =>
          shiftedSingleBoundaryCore n ((K - n) + 1) - shiftedSingleBoundaryCore n 1
            - ∑ j ∈ Finset.Icc 1 (K - n), shiftedCompleteBlockCorrectionTerm n j) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            exact shifted_completeBlock_complex_mul_phase_sum_eq_boundaryCore_diff n (K - n)
    _ =
      Finset.sum (Finset.range (K + 1))
          (fun n => shiftedSingleBoundaryCore n (K + 1 - n))
        - Finset.sum (Finset.range (K + 1))
            (fun n => shiftedSingleBoundaryCore n 1)
        - Finset.sum (Finset.range (K + 1))
            (fun n => ∑ j ∈ Finset.Icc 1 (K - n), shiftedCompleteBlockCorrectionTerm n j) := by
            have hshift :
                Finset.sum (Finset.range (K + 1))
                    (fun n => shiftedSingleBoundaryCore n ((K - n) + 1))
                  =
                Finset.sum (Finset.range (K + 1))
                    (fun n => shiftedSingleBoundaryCore n (K + 1 - n)) := by
                      refine Finset.sum_congr rfl ?_
                      intro n hn
                      have hn_le : n ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
                      congr 1
                      symm
                      rw [← Nat.succ_eq_add_one, Nat.succ_sub hn_le, Nat.succ_eq_add_one]
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hshift]

private theorem shiftedCompleteBlockPhaseWeightedTriangle_boundary_bound
    (K : ℕ) :
    ‖Finset.sum (Finset.range (K + 1))
          (fun n => shiftedSingleBoundaryCore n (K + 1 - n))
      - Finset.sum (Finset.range (K + 1))
          (fun n => shiftedSingleBoundaryCore n 1)‖
      ≤ 4 * Real.sqrt (K + 1) := by
  calc
    ‖Finset.sum (Finset.range (K + 1))
          (fun n => shiftedSingleBoundaryCore n (K + 1 - n))
      - Finset.sum (Finset.range (K + 1))
          (fun n => shiftedSingleBoundaryCore n 1)‖
        ≤ ‖Finset.sum (Finset.range (K + 1))
              (fun n => shiftedSingleBoundaryCore n (K + 1 - n))‖
            + ‖Finset.sum (Finset.range (K + 1))
                (fun n => shiftedSingleBoundaryCore n 1)‖ := by
              exact norm_sub_le _ _
    _ ≤ 2 * Real.sqrt (K + 1) + 2 * Real.sqrt (K + 1) := by
          exact add_le_add
            (shiftedSingleBoundaryCore_antidiagonal_sum_bound K)
            (shiftedSingleBoundaryCore_vertical_sum_bound K)
    _ = 4 * Real.sqrt (K + 1) := by ring

/-! ## Two-parameter truncated triangles -/

/-- The phase-weighted near-band triangle truncated at total block index `K`
and maximum shift `J`.  This is the right discrete prefix object for extracting
fixed-shift partial sums by taking a difference in `J`. -/
private noncomputable def shiftedCompleteBlockPhaseWeightedTruncatedTriangle
    (K J : ℕ) : ℂ :=
  Finset.sum (Finset.range (K + 1))
    (fun n =>
      ∑ j ∈ Finset.Icc 1 (min J (K - n)),
        shiftedCompleteBlockPhaseWeightedCell n j)

/-- Matching correction triangle for
`shiftedCompleteBlockPhaseWeightedTruncatedTriangle`. -/
private noncomputable def shiftedCompleteBlockCorrectionTruncatedTriangle
    (K J : ℕ) : ℂ :=
  Finset.sum (Finset.range (K + 1))
    (fun n =>
      ∑ j ∈ Finset.Icc 1 (min J (K - n)),
        shiftedCompleteBlockCorrectionTerm n j)

private theorem shiftedCompleteBlockPhaseWeightedTruncatedTriangle_eq_boundary_diff_minus_correction
    (K J : ℕ) :
    shiftedCompleteBlockPhaseWeightedTruncatedTriangle K J
      =
      Finset.sum (Finset.range (K + 1))
          (fun n => shiftedSingleBoundaryCore n (min J (K - n) + 1))
        - Finset.sum (Finset.range (K + 1))
            (fun n => shiftedSingleBoundaryCore n 1)
        - shiftedCompleteBlockCorrectionTruncatedTriangle K J := by
  unfold shiftedCompleteBlockPhaseWeightedTruncatedTriangle
    shiftedCompleteBlockCorrectionTruncatedTriangle
  calc
    Finset.sum (Finset.range (K + 1))
        (fun n =>
          ∑ j ∈ Finset.Icc 1 (min J (K - n)),
            shiftedCompleteBlockPhaseWeightedCell n j)
        =
      Finset.sum (Finset.range (K + 1))
        (fun n =>
          shiftedSingleBoundaryCore n (min J (K - n) + 1) - shiftedSingleBoundaryCore n 1
            - ∑ j ∈ Finset.Icc 1 (min J (K - n)),
                shiftedCompleteBlockCorrectionTerm n j) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            exact
              shifted_completeBlock_complex_mul_phase_sum_eq_boundaryCore_diff
                n (min J (K - n))
    _ =
      Finset.sum (Finset.range (K + 1))
          (fun n => shiftedSingleBoundaryCore n (min J (K - n) + 1))
        - Finset.sum (Finset.range (K + 1))
            (fun n => shiftedSingleBoundaryCore n 1)
        - Finset.sum (Finset.range (K + 1))
            (fun n =>
              ∑ j ∈ Finset.Icc 1 (min J (K - n)),
                shiftedCompleteBlockCorrectionTerm n j) := by
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]

private theorem shiftedCompleteBlockTruncatedBoundary_upper_bound
    (K J : ℕ) :
    ‖Finset.sum (Finset.range (K + 1))
        (fun n => shiftedSingleBoundaryCore n (min J (K - n) + 1))‖
      ≤ 2 * Real.sqrt (K + 1) := by
  calc
    ‖Finset.sum (Finset.range (K + 1))
        (fun n => shiftedSingleBoundaryCore n (min J (K - n) + 1))‖
        ≤ Finset.sum (Finset.range (K + 1))
            (fun n => ‖shiftedSingleBoundaryCore n (min J (K - n) + 1)‖) :=
          norm_sum_le _ _
    _ = Finset.sum (Finset.range (K + 1)) (fun n => modeWeight n) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [shiftedSingleBoundaryCore_norm n (min J (K - n) + 1)]
          omega
    _ = Finset.sum (Finset.range (K + 1))
          (fun n => ((n + 1 : ℝ) ^ (-1 / 2 : ℝ))) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [modeWeight_eq_neg_half]
    _ ≤ 2 * Real.sqrt (K + 1) := by
          simpa [div_eq_mul_inv, show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by ring_nf] using
            Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le (K + 1)

private theorem shiftedCompleteBlockPhaseWeightedTruncatedTriangle_boundary_bound
    (K J : ℕ) :
    ‖Finset.sum (Finset.range (K + 1))
          (fun n => shiftedSingleBoundaryCore n (min J (K - n) + 1))
      - Finset.sum (Finset.range (K + 1))
          (fun n => shiftedSingleBoundaryCore n 1)‖
      ≤ 4 * Real.sqrt (K + 1) := by
  calc
    ‖Finset.sum (Finset.range (K + 1))
          (fun n => shiftedSingleBoundaryCore n (min J (K - n) + 1))
      - Finset.sum (Finset.range (K + 1))
          (fun n => shiftedSingleBoundaryCore n 1)‖
        ≤ ‖Finset.sum (Finset.range (K + 1))
              (fun n => shiftedSingleBoundaryCore n (min J (K - n) + 1))‖
            + ‖Finset.sum (Finset.range (K + 1))
                (fun n => shiftedSingleBoundaryCore n 1)‖ := by
              exact norm_sub_le _ _
    _ ≤ 2 * Real.sqrt (K + 1) + 2 * Real.sqrt (K + 1) := by
          exact add_le_add
            (shiftedCompleteBlockTruncatedBoundary_upper_bound K J)
            (shiftedSingleBoundaryCore_vertical_sum_bound K)
    _ = 4 * Real.sqrt (K + 1) := by ring

private noncomputable def shiftedCompleteBlockTruncatedBoundary
    (K J : ℕ) : ℂ :=
  Finset.sum (Finset.range (K + 1))
      (fun n => shiftedSingleBoundaryCore n (min J (K - n) + 1))
    - Finset.sum (Finset.range (K + 1))
        (fun n => shiftedSingleBoundaryCore n 1)

private lemma shiftedCompleteBlockTruncatedBoundary_bound
    (K J : ℕ) :
    ‖shiftedCompleteBlockTruncatedBoundary K J‖ ≤ 4 * Real.sqrt (K + 1) := by
  simpa [shiftedCompleteBlockTruncatedBoundary] using
    shiftedCompleteBlockPhaseWeightedTruncatedTriangle_boundary_bound K J

private lemma shiftedCompleteBlockTruncatedBoundary_diff_bound
    (K j : ℕ) :
    ‖shiftedCompleteBlockTruncatedBoundary K j
        - shiftedCompleteBlockTruncatedBoundary K (j - 1)‖
      ≤ 8 * Real.sqrt (K + 1) := by
  calc
    ‖shiftedCompleteBlockTruncatedBoundary K j
        - shiftedCompleteBlockTruncatedBoundary K (j - 1)‖
        ≤ ‖shiftedCompleteBlockTruncatedBoundary K j‖
            + ‖shiftedCompleteBlockTruncatedBoundary K (j - 1)‖ := by
              exact norm_sub_le _ _
    _ ≤ 4 * Real.sqrt (K + 1) + 4 * Real.sqrt (K + 1) := by
          exact add_le_add
            (shiftedCompleteBlockTruncatedBoundary_bound K j)
            (shiftedCompleteBlockTruncatedBoundary_bound K (j - 1))
    _ = 8 * Real.sqrt (K + 1) := by ring

private theorem shiftedCompleteBlockPhaseWeightedTruncatedTriangle_diff_eq_fixedShiftPrefix
    (m j : ℕ) (hj : 1 ≤ j) :
    shiftedCompleteBlockPhaseWeightedTruncatedTriangle (m + j) j
      - shiftedCompleteBlockPhaseWeightedTruncatedTriangle (m + j) (j - 1)
      =
      Finset.sum (Finset.range (m + 1))
        (fun n => shiftedCompleteBlockPhaseWeightedCell n j) := by
  unfold shiftedCompleteBlockPhaseWeightedTruncatedTriangle
  calc
    Finset.sum (Finset.range (m + j + 1))
        (fun n =>
          ∑ x ∈ Finset.Icc 1 (min j (m + j - n)),
            shiftedCompleteBlockPhaseWeightedCell n x)
      -
      Finset.sum (Finset.range (m + j + 1))
        (fun n =>
          ∑ x ∈ Finset.Icc 1 (min (j - 1) (m + j - n)),
            shiftedCompleteBlockPhaseWeightedCell n x)
        =
      Finset.sum (Finset.range (m + j + 1))
        (fun n =>
          (∑ x ∈ Finset.Icc 1 (min j (m + j - n)),
            shiftedCompleteBlockPhaseWeightedCell n x)
          -
          (∑ x ∈ Finset.Icc 1 (min (j - 1) (m + j - n)),
            shiftedCompleteBlockPhaseWeightedCell n x)) := by
            rw [Finset.sum_sub_distrib]
    _ =
      Finset.sum (Finset.range (m + 1))
        (fun n => shiftedCompleteBlockPhaseWeightedCell n j) := by
          let F : ℕ → ℂ := fun n =>
            (∑ x ∈ Finset.Icc 1 (min j (m + j - n)),
              shiftedCompleteBlockPhaseWeightedCell n x)
            -
            (∑ x ∈ Finset.Icc 1 (min (j - 1) (m + j - n)),
              shiftedCompleteBlockPhaseWeightedCell n x)
          have hsplit :
              Finset.sum (Finset.range (m + j + 1)) F
                =
              Finset.sum (Finset.range (m + 1)) F
                + Finset.sum (Finset.Ico (m + 1) (m + j + 1)) F := by
                  rw [← Finset.sum_range_add_sum_Ico F (by omega : m + 1 ≤ m + j + 1)]
          have hprefix :
              Finset.sum (Finset.range (m + 1)) F
                =
              Finset.sum (Finset.range (m + 1))
                (fun n => shiftedCompleteBlockPhaseWeightedCell n j) := by
                  refine Finset.sum_congr rfl ?_
                  intro n hn
                  have hn_le : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
                  have hupper : j ≤ m + j - n := by omega
                  have hupper' : j - 1 ≤ m + j - n := by omega
                  have hjsucc : j = (j - 1) + 1 := by omega
                  rw [show F n =
                      (∑ x ∈ Finset.Icc 1 (min j (m + j - n)),
                        shiftedCompleteBlockPhaseWeightedCell n x)
                      -
                      (∑ x ∈ Finset.Icc 1 (min (j - 1) (m + j - n)),
                        shiftedCompleteBlockPhaseWeightedCell n x) by rfl]
                  rw [min_eq_left hupper, min_eq_left hupper']
                  rw [hjsucc]
                  rw [Finset.sum_Icc_succ_top (a := 1) (b := j - 1)
                        (f := fun x => shiftedCompleteBlockPhaseWeightedCell n x) (by omega)]
                  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          have hIco :
              Finset.sum (Finset.Ico (m + 1) (m + j + 1)) F = 0 := by
                refine Finset.sum_eq_zero ?_
                intro n hn
                have hn_gt : m + 1 ≤ n := (Finset.mem_Ico.mp hn).1
                have hn_lt : n < m + j + 1 := (Finset.mem_Ico.mp hn).2
                have hsmall : m + j - n ≤ j - 1 := by omega
                have hsmall' : m + j - n ≤ j := le_trans hsmall (by omega)
                rw [min_eq_right hsmall', min_eq_right hsmall]
                simp
          rw [hsplit, hprefix, hIco, add_zero]

private theorem shiftedCompleteBlockCorrectionTruncatedTriangle_diff_eq_fixedShiftPrefix
    (m j : ℕ) (hj : 1 ≤ j) :
    shiftedCompleteBlockCorrectionTruncatedTriangle (m + j) j
      - shiftedCompleteBlockCorrectionTruncatedTriangle (m + j) (j - 1)
      =
      Finset.sum (Finset.range (m + 1))
        (fun n => shiftedCompleteBlockCorrectionTerm n j) := by
  unfold shiftedCompleteBlockCorrectionTruncatedTriangle
  calc
    Finset.sum (Finset.range (m + j + 1))
        (fun n =>
          ∑ x ∈ Finset.Icc 1 (min j (m + j - n)),
            shiftedCompleteBlockCorrectionTerm n x)
      -
      Finset.sum (Finset.range (m + j + 1))
        (fun n =>
          ∑ x ∈ Finset.Icc 1 (min (j - 1) (m + j - n)),
            shiftedCompleteBlockCorrectionTerm n x)
        =
      Finset.sum (Finset.range (m + j + 1))
        (fun n =>
          (∑ x ∈ Finset.Icc 1 (min j (m + j - n)),
            shiftedCompleteBlockCorrectionTerm n x)
          -
          (∑ x ∈ Finset.Icc 1 (min (j - 1) (m + j - n)),
            shiftedCompleteBlockCorrectionTerm n x)) := by
            rw [Finset.sum_sub_distrib]
    _ =
      Finset.sum (Finset.range (m + 1))
        (fun n => shiftedCompleteBlockCorrectionTerm n j) := by
          let F : ℕ → ℂ := fun n =>
            (∑ x ∈ Finset.Icc 1 (min j (m + j - n)),
              shiftedCompleteBlockCorrectionTerm n x)
            -
            (∑ x ∈ Finset.Icc 1 (min (j - 1) (m + j - n)),
              shiftedCompleteBlockCorrectionTerm n x)
          have hsplit :
              Finset.sum (Finset.range (m + j + 1)) F
                =
              Finset.sum (Finset.range (m + 1)) F
                + Finset.sum (Finset.Ico (m + 1) (m + j + 1)) F := by
                  rw [← Finset.sum_range_add_sum_Ico F (by omega : m + 1 ≤ m + j + 1)]
          have hprefix :
              Finset.sum (Finset.range (m + 1)) F
                =
              Finset.sum (Finset.range (m + 1))
                (fun n => shiftedCompleteBlockCorrectionTerm n j) := by
                  refine Finset.sum_congr rfl ?_
                  intro n hn
                  have hn_le : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
                  have hupper : j ≤ m + j - n := by omega
                  have hupper' : j - 1 ≤ m + j - n := by omega
                  have hjsucc : j = (j - 1) + 1 := by omega
                  rw [show F n =
                      (∑ x ∈ Finset.Icc 1 (min j (m + j - n)),
                        shiftedCompleteBlockCorrectionTerm n x)
                      -
                      (∑ x ∈ Finset.Icc 1 (min (j - 1) (m + j - n)),
                        shiftedCompleteBlockCorrectionTerm n x) by rfl]
                  rw [min_eq_left hupper, min_eq_left hupper']
                  rw [hjsucc]
                  rw [Finset.sum_Icc_succ_top (a := 1) (b := j - 1)
                        (f := fun x => shiftedCompleteBlockCorrectionTerm n x) (by omega)]
                  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          have hIco :
              Finset.sum (Finset.Ico (m + 1) (m + j + 1)) F = 0 := by
                refine Finset.sum_eq_zero ?_
                intro n hn
                have hn_gt : m + 1 ≤ n := (Finset.mem_Ico.mp hn).1
                have hsmall : m + j - n ≤ j - 1 := by omega
                have hsmall' : m + j - n ≤ j := le_trans hsmall (by omega)
                rw [min_eq_right hsmall', min_eq_right hsmall]
                simp
          rw [hsplit, hprefix, hIco, add_zero]

private theorem shiftedCompleteBlockCorrectionTruncatedTriangle_diff_eq_boundaryDiff_minus_phasePrefix
    (m j : ℕ) (hj : 1 ≤ j) :
    shiftedCompleteBlockCorrectionTruncatedTriangle (m + j) j
      - shiftedCompleteBlockCorrectionTruncatedTriangle (m + j) (j - 1)
      =
      (shiftedCompleteBlockTruncatedBoundary (m + j) j
          - shiftedCompleteBlockTruncatedBoundary (m + j) (j - 1))
        - ∑ n ∈ Finset.range (m + 1), shiftedCompleteBlockPhaseWeightedCell n j := by
  have htri_j :=
    shiftedCompleteBlockPhaseWeightedTruncatedTriangle_eq_boundary_diff_minus_correction (m + j) j
  have htri_prev :=
    shiftedCompleteBlockPhaseWeightedTruncatedTriangle_eq_boundary_diff_minus_correction (m + j) (j - 1)
  have hphase :=
    shiftedCompleteBlockPhaseWeightedTruncatedTriangle_diff_eq_fixedShiftPrefix m j hj
  have hcorr :=
    shiftedCompleteBlockCorrectionTruncatedTriangle_diff_eq_fixedShiftPrefix m j hj
  calc
    shiftedCompleteBlockCorrectionTruncatedTriangle (m + j) j
        - shiftedCompleteBlockCorrectionTruncatedTriangle (m + j) (j - 1)
        =
      shiftedCompleteBlockTruncatedBoundary (m + j) j
        - shiftedCompleteBlockTruncatedBoundary (m + j) (j - 1)
        - (shiftedCompleteBlockPhaseWeightedTruncatedTriangle (m + j) j
            - shiftedCompleteBlockPhaseWeightedTruncatedTriangle (m + j) (j - 1)) := by
              rw [htri_j, htri_prev]
              simp [shiftedCompleteBlockTruncatedBoundary]
              ring
    _ =
      shiftedCompleteBlockTruncatedBoundary (m + j) j
        - shiftedCompleteBlockTruncatedBoundary (m + j) (j - 1)
        - ∑ n ∈ Finset.range (m + 1), shiftedCompleteBlockPhaseWeightedCell n j := by
              rw [hphase]

/-- The truncated correction terms on the antidiagonal `n + j = k`, cut off at
maximum shift `J`.  This is the natural slice that appears when the truncated
two-parameter correction triangle is reindexed by total block index. -/
private noncomputable def shiftedCompleteBlockCorrectionAntidiagonalSlice
    (k J : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 (min J k), shiftedCompleteBlockCorrectionTerm (k - j) j

private theorem shiftedCompleteBlockCorrectionAntidiagonalSlice_eq_omega_packetIntegral
    (k J : ℕ) :
    shiftedCompleteBlockCorrectionAntidiagonalSlice k J
      =
      ∫ u in (0 : ℝ)..1,
        ((((blockOmega k u : ℝ) : ℂ)) * weightedResonantBlockMode k u) *
          shiftedJPacket k (min J k) u := by
  unfold shiftedCompleteBlockCorrectionAntidiagonalSlice shiftedJPacket
  calc
    ∑ j ∈ Finset.Icc 1 (min J k), shiftedCompleteBlockCorrectionTerm (k - j) j
        =
      ∑ j ∈ Finset.Icc 1 (min J k),
        ∫ u in (0 : ℝ)..1,
          ((((blockOmega k u : ℝ) : ℂ)) * weightedResonantBlockMode k u) *
            shiftedSinglePacket k j u := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
              have hjk : j ≤ k := le_trans (Finset.mem_Icc.mp hj).2 (Nat.min_le_right _ _)
              have hkj : (k - j) + j = k := Nat.sub_add_cancel hjk
              have hcorr :
                  shiftedCompleteBlockCorrectionTerm (k - j) j
                    =
                  (((shiftedRelativePhase k j : ℝ) : ℂ)) *
                    ∫ u in (0 : ℝ)..1,
                      (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
                        shiftedSinglePrimitive k j u := by
                unfold shiftedCompleteBlockCorrectionTerm
                simp [hkj]
              rw [hcorr, ← intervalIntegral.integral_const_mul]
              refine intervalIntegral.integral_congr ?_
              intro u hu
              calc
                (((shiftedRelativePhase k j : ℝ) : ℂ)) *
                    ((Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
                      shiftedSinglePrimitive k j u)
                    =
                  (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
                    ((((shiftedRelativePhase k j : ℝ) : ℂ)) * shiftedSinglePrimitive k j u) := by
                      ring
                _ =
                  (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
                    ((-Complex.I) * shiftedSinglePacket k j u) := by
                      rw [shiftedRelativePhase_mul_shiftedSinglePrimitive k j hj1 hjk u]
                _ =
                  ((((blockOmega k u : ℝ) : ℂ)) * weightedResonantBlockMode k u) *
                    shiftedSinglePacket k j u := by
                      have hI2 : -(Complex.I ^ 2) = (1 : ℂ) := by norm_num
                      calc
                        (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
                            (-Complex.I * shiftedSinglePacket k j u)
                            =
                          (-(Complex.I ^ 2)) *
                            ((((blockOmega k u : ℝ) : ℂ)) * weightedResonantBlockMode k u *
                              shiftedSinglePacket k j u) := by
                                ring
                        _ =
                          ((((blockOmega k u : ℝ) : ℂ)) * weightedResonantBlockMode k u) *
                            shiftedSinglePacket k j u := by
                              rw [hI2, one_mul]
    _ =
      ∫ u in (0 : ℝ)..1,
        ∑ j ∈ Finset.Icc 1 (min J k),
          ((((blockOmega k u : ℝ) : ℂ)) * weightedResonantBlockMode k u) *
            shiftedSinglePacket k j u := by
              symm
              rw [intervalIntegral.integral_finset_sum]
              intro j hj
              have hpacket_cont : Continuous fun u : ℝ => shiftedSinglePacket k j u := by
                unfold shiftedSinglePacket shiftedPacketPhase
                exact continuous_const.mul <|
                  Complex.continuous_exp.comp <|
                    continuous_const.mul <|
                      Complex.continuous_ofReal.comp ((blockCoord_continuous k).mul continuous_const)
              have hcont : Continuous fun u : ℝ =>
                  ((((blockOmega k u : ℝ) : ℂ)) * weightedResonantBlockMode k u) *
                    shiftedSinglePacket k j u := by
                exact ((Complex.continuous_ofReal.comp (blockOmega_continuous k)).mul
                  (weightedResonantBlockMode_continuous k)).mul hpacket_cont
              exact hcont.intervalIntegrable _ _
    _ =
      ∫ u in (0 : ℝ)..1,
        ((((blockOmega k u : ℝ) : ℂ)) * weightedResonantBlockMode k u) *
          ∑ j ∈ Finset.Icc 1 (min J k), shiftedSinglePacket k j u := by
            refine intervalIntegral.integral_congr ?_
            intro u hu
            change
              ∑ j ∈ Finset.Icc 1 (min J k),
                ((((blockOmega k u : ℝ) : ℂ)) * weightedResonantBlockMode k u) *
                  shiftedSinglePacket k j u
                =
              ((((blockOmega k u : ℝ) : ℂ)) * weightedResonantBlockMode k u) *
                ∑ j ∈ Finset.Icc 1 (min J k), shiftedSinglePacket k j u
            rw [Finset.mul_sum]

private lemma shiftedRelativePhase_upper_of_half
    (k j : ℕ) (hj : 1 ≤ j) (hj_half : j ≤ (k + 1) / 2) :
    shiftedRelativePhase k j ≤ 2 * (j : ℝ) / ((k : ℝ) + 1) := by
  have hjk : j ≤ k := by omega
  have hphi :
      shiftedRelativePhase k j = Real.log (((k : ℝ) + 1) / (((k - j : ℕ) : ℝ) + 1)) := by
    rfl
  calc
    shiftedRelativePhase k j
        = Real.log (((k : ℝ) + 1) / (((k - j : ℕ) : ℝ) + 1)) := hphi
    _ ≤ (((k : ℝ) + 1) / (((k - j : ℕ) : ℝ) + 1)) - 1 := by
          exact Real.log_le_sub_one_of_pos (by positivity)
    _ = (j : ℝ) / (((k - j : ℕ) : ℝ) + 1) := by
          have hcast : (((k : ℝ) + 1) - ((((k - j : ℕ) : ℝ) + 1))) = (j : ℝ) := by
            rw [Nat.cast_sub hjk]
            ring
          field_simp [show ((((k - j : ℕ) : ℝ) + 1)) ≠ 0 by positivity]
          linarith
    _ ≤ 2 * (j : ℝ) / ((k : ℝ) + 1) := by
          have hden :
              ((k : ℝ) + 1) / 2 ≤ (((k - j : ℕ) : ℝ) + 1) := by
            have htwoj_nat : 2 * j ≤ k + 1 := by
              omega
            have htwoj : (2 : ℝ) * j ≤ (k : ℝ) + 1 := by
              exact_mod_cast htwoj_nat
            have hkj_cast : (((k - j : ℕ) : ℝ) + 1) = (k : ℝ) + 1 - j := by
              rw [Nat.cast_sub hjk]
              ring
            rw [hkj_cast]
            linarith
          have hk1_pos : 0 < (k : ℝ) + 1 := by positivity
          have hden_pos : 0 < (((k - j : ℕ) : ℝ) + 1) := by positivity
          have hk1_ne : (k : ℝ) + 1 ≠ 0 := by positivity
          have hden_ne : (((k - j : ℕ) : ℝ) + 1) ≠ 0 := by positivity
          field_simp [hk1_ne, hden_ne]
          nlinarith

private lemma shiftedRelativePhase_inv_lower_of_half
    (k j : ℕ) (hj : 1 ≤ j) (hj_half : j ≤ (k + 1) / 2) :
    ((k : ℝ) + 1) / (2 * j) ≤ 1 / shiftedRelativePhase k j := by
  have hjk : j ≤ k := by omega
  have hphase_pos : 0 < shiftedRelativePhase k j :=
    shiftedRelativePhase_pos k j hj hjk
  have hupper :
      shiftedRelativePhase k j ≤ 2 * (j : ℝ) / ((k : ℝ) + 1) :=
    shiftedRelativePhase_upper_of_half k j hj hj_half
  have hden_pos : 0 < 2 * (j : ℝ) / ((k : ℝ) + 1) := by positivity
  calc
    ((k : ℝ) + 1) / (2 * j) = 1 / (2 * (j : ℝ) / ((k : ℝ) + 1)) := by
      field_simp [show (j : ℝ) ≠ 0 by positivity,
        show ((k : ℝ) + 1) ≠ 0 by positivity]
    _ ≤ 1 / shiftedRelativePhase k j := by
      exact one_div_le_one_div_of_le hphase_pos hupper


private theorem shiftedCompleteBlockCorrectionTerm_bound_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ j : ℕ, 1 ≤ j → j ≤ n + 1 →
        ‖shiftedCompleteBlockCorrectionTerm n j‖ ≤ C * modeWeight (n + j) := by
  obtain ⟨Cω, hCω, N0, hderivBound⟩ := weightedResonantBlockMode_deriv_bound_eventually
  let C : ℝ := 2 * Real.sqrt 2 * Cω
  refine ⟨C, by
    dsimp [C]
    positivity, N0, ?_⟩
  intro n hn j hj hjn
  have hj_half : j ≤ (n + j + 1) / 2 := by omega
  have hjk : j ≤ n + j := by omega
  have hphase_nonneg : 0 ≤ shiftedRelativePhase (n + j) j :=
    (shiftedRelativePhase_pos (n + j) j hj hjk).le
  have hphase_upper :
      shiftedRelativePhase (n + j) j ≤ 2 * (j : ℝ) / ((n : ℝ) + j + 1) := by
    simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
      shiftedRelativePhase_upper_of_half (n + j) j hj hj_half
  have hprim :
      ∀ u : ℝ, ‖shiftedSinglePrimitive (n + j) j u‖
        ≤ Real.sqrt 2 * (((n : ℝ) + j + 1) / j) := by
    intro u
    simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
      shiftedSinglePrimitive_norm_bound (n + j) j hj hj_half u
  have hIntBound :
      ‖∫ u in (0 : ℝ)..1,
          (Complex.I * ((blockOmega (n + j) u : ℝ) : ℂ) *
            weightedResonantBlockMode (n + j) u) *
              shiftedSinglePrimitive (n + j) j u‖
        ≤ Cω * modeWeight (n + j) *
            (Real.sqrt 2 * (((n : ℝ) + j + 1) / j)) := by
    let B : ℝ := Cω * modeWeight (n + j) * (Real.sqrt 2 * (((n : ℝ) + j + 1) / j))
    have h_norm_le :
        ∀ u, u ∈ Set.uIoc (0 : ℝ) 1 →
          ‖(Complex.I * ((blockOmega (n + j) u : ℝ) : ℂ) *
              weightedResonantBlockMode (n + j) u) *
                shiftedSinglePrimitive (n + j) j u‖ ≤ B := by
      intro u hu
      have huIoc : u ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hu
      have hu' : u ∈ Set.Icc (0 : ℝ) 1 := by
        exact ⟨huIoc.1.le, huIoc.2⟩
      have hdu := hderivBound (n + j) (le_trans hn (Nat.le_add_right _ _)) u hu'
      have hGu := hprim u
      have hCω_nonneg : 0 ≤ Cω := le_of_lt hCω
      calc
        ‖(Complex.I * ((blockOmega (n + j) u : ℝ) : ℂ) *
            weightedResonantBlockMode (n + j) u) *
              shiftedSinglePrimitive (n + j) j u‖
            =
          ‖Complex.I * ((blockOmega (n + j) u : ℝ) : ℂ) *
              weightedResonantBlockMode (n + j) u‖ *
            ‖shiftedSinglePrimitive (n + j) j u‖ := by
              rw [norm_mul]
        _ ≤ (Cω * modeWeight (n + j)) * (Real.sqrt 2 * (((n : ℝ) + j + 1) / j)) := by
              exact mul_le_mul hdu hGu (norm_nonneg _) <|
                mul_nonneg hCω_nonneg (le_of_lt (modeWeight_pos _))
        _ = B := by rfl
    simpa [B] using
      (intervalIntegral.norm_integral_le_of_norm_le_const h_norm_le)
  calc
    ‖shiftedCompleteBlockCorrectionTerm n j‖
        =
      shiftedRelativePhase (n + j) j *
        ‖∫ u in (0 : ℝ)..1,
            (Complex.I * ((blockOmega (n + j) u : ℝ) : ℂ) *
              weightedResonantBlockMode (n + j) u) *
              shiftedSinglePrimitive (n + j) j u‖ := by
            unfold shiftedCompleteBlockCorrectionTerm
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hphase_nonneg]
    _ ≤ shiftedRelativePhase (n + j) j *
          (Cω * modeWeight (n + j) *
            (Real.sqrt 2 * (((n : ℝ) + j + 1) / j))) := by
          exact mul_le_mul_of_nonneg_left hIntBound hphase_nonneg
    _ ≤ (2 * (j : ℝ) / ((n : ℝ) + j + 1)) *
          (Cω * modeWeight (n + j) *
            (Real.sqrt 2 * (((n : ℝ) + j + 1) / j))) := by
          have hfactor_nonneg :
              0 ≤ Cω * modeWeight (n + j) * (Real.sqrt 2 * (((n : ℝ) + j + 1) / j)) := by
            have hj_pos : 0 < (j : ℝ) := by exact_mod_cast hj
            have hratio_nonneg : 0 ≤ ((n : ℝ) + j + 1) / j := by
              exact div_nonneg (by positivity) (le_of_lt hj_pos)
            have hsqrt_term_nonneg : 0 ≤ Real.sqrt 2 * (((n : ℝ) + j + 1) / j) := by
              exact mul_nonneg (Real.sqrt_nonneg 2) hratio_nonneg
            exact mul_nonneg
              (mul_nonneg (le_of_lt hCω) (le_of_lt (modeWeight_pos _)))
              hsqrt_term_nonneg
          exact mul_le_mul_of_nonneg_right hphase_upper hfactor_nonneg
    _ = C * modeWeight (n + j) := by
          dsimp [C]
          field_simp [show (j : ℝ) ≠ 0 by positivity,
            show (n : ℝ) + j + 1 ≠ 0 by positivity]

private lemma shiftedModeWeight_sum_Icc_le (n J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, modeWeight (n + j)
      ≤ 2 * Real.sqrt (((n + J : ℕ) : ℝ) + 1) := by
  calc
    ∑ j ∈ Finset.Icc 1 J, modeWeight (n + j)
        = ∑ j ∈ Finset.Ico 1 (J + 1), modeWeight (n + j) := by
            rw [Finset.Ico_add_one_right_eq_Icc]
    _ = ∑ m ∈ Finset.Ico (n + 1) (n + J + 1), modeWeight m := by
          simpa [add_comm, add_left_comm, add_assoc] using
            (Finset.sum_Ico_add (f := fun m => modeWeight m) 1 (J + 1) n)
    _ ≤ ∑ m ∈ Finset.range (n + J + 1), modeWeight m := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (by
              intro m hm
              exact Finset.mem_range.mpr (Finset.mem_Ico.mp hm).2)
            (by
              intro m hm hmem
              exact le_of_lt (modeWeight_pos m))
    _ ≤ 2 * Real.sqrt ((n + J + 1 : ℕ) : ℝ) := by
          calc
            ∑ m ∈ Finset.range (n + J + 1), modeWeight m
                = ∑ m ∈ Finset.range (n + J + 1), ((m + 1 : ℝ) ^ (-(1 : ℝ) / 2)) := by
                    refine Finset.sum_congr rfl ?_
                    intro m hm
                    rw [modeWeight_eq_neg_half]
            _ ≤ 2 * Real.sqrt ((n + J + 1 : ℕ) : ℝ) :=
                  Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le (n + J + 1)
    _ = 2 * Real.sqrt (((n + J : ℕ) : ℝ) + 1) := by
          norm_num [Nat.cast_add]

private theorem shiftedCompleteBlockCorrectionSum_bound_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ J : ℕ, J ≤ n + 1 →
        ‖∑ j ∈ Finset.Icc 1 J, shiftedCompleteBlockCorrectionTerm n j‖
          ≤ C * Real.sqrt (((n + J : ℕ) : ℝ) + 1) := by
  obtain ⟨C0, hC0, N0, hterm⟩ := shiftedCompleteBlockCorrectionTerm_bound_eventually
  let C : ℝ := 2 * C0
  refine ⟨C, by
    dsimp [C]
    positivity, N0, ?_⟩
  intro n hn J hJ
  calc
    ‖∑ j ∈ Finset.Icc 1 J, shiftedCompleteBlockCorrectionTerm n j‖
        ≤ ∑ j ∈ Finset.Icc 1 J, ‖shiftedCompleteBlockCorrectionTerm n j‖ :=
          norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 J, C0 * modeWeight (n + j) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact hterm n hn j (Finset.mem_Icc.mp hj).1 (le_trans (Finset.mem_Icc.mp hj).2 hJ)
    _ = C0 * ∑ j ∈ Finset.Icc 1 J, modeWeight (n + j) := by
          rw [Finset.mul_sum]
    _ ≤ C0 * (2 * Real.sqrt (((n + J : ℕ) : ℝ) + 1)) := by
          exact mul_le_mul_of_nonneg_left (shiftedModeWeight_sum_Icc_le n J) (le_of_lt hC0)
    _ = C * Real.sqrt (((n + J : ℕ) : ℝ) + 1) := by
          dsimp [C]
          ring

private theorem shiftedCompleteBlockPhaseWeightedSum_bound_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ J : ℕ, J ≤ n + 1 →
        ‖∑ j ∈ Finset.Icc 1 J, shiftedCompleteBlockPhaseWeightedCell n j‖
          ≤ C * Real.sqrt (((n + J : ℕ) : ℝ) + 1) := by
  obtain ⟨C0, hC0, N0, hcorr⟩ := shiftedCompleteBlockCorrectionSum_bound_eventually
  let C : ℝ := C0 + 2
  refine ⟨C, by
    dsimp [C]
    positivity, N0, ?_⟩
  intro n hn J hJ
  have hsqrt_ge_one : 1 ≤ Real.sqrt (((n + J : ℕ) : ℝ) + 1) := by
    have hx_nonneg : 0 ≤ (((n + J : ℕ) : ℝ) + 1) := by positivity
    have hsqrt_sq : (1 : ℝ) ≤ ((n + J : ℕ) : ℝ) + 1 := by
      have hsqrt_sq_nat : 1 ≤ n + J + 1 := by omega
      exact_mod_cast hsqrt_sq_nat
    nlinarith [Real.sqrt_nonneg (((n + J : ℕ) : ℝ) + 1), Real.sq_sqrt hx_nonneg, hsqrt_sq]
  have hweight_nonneg : 0 ≤ modeWeight n := by
    simpa [modeWeight_eq] using weight_nonneg n
  have hweight_le : modeWeight n ≤ 1 := by
    simpa [modeWeight_eq] using weight_le_one n
  have hboundary :
      ‖shiftedSingleBoundaryCore n (J + 1) - shiftedSingleBoundaryCore n 1‖ ≤ 2 := by
    have hnormJ : ‖shiftedSingleBoundaryCore n (J + 1)‖ = modeWeight n :=
      shiftedSingleBoundaryCore_norm n (J + 1) (by omega)
    have hnorm1 : ‖shiftedSingleBoundaryCore n 1‖ = modeWeight n :=
      shiftedSingleBoundaryCore_norm n 1 (by norm_num)
    calc
      ‖shiftedSingleBoundaryCore n (J + 1) - shiftedSingleBoundaryCore n 1‖
          ≤ ‖shiftedSingleBoundaryCore n (J + 1)‖ + ‖shiftedSingleBoundaryCore n 1‖ :=
            norm_sub_le _ _
      _ = modeWeight n + modeWeight n := by rw [hnormJ, hnorm1]
      _ ≤ 1 + 1 := by gcongr
      _ = 2 := by ring
  calc
    ‖∑ j ∈ Finset.Icc 1 J, shiftedCompleteBlockPhaseWeightedCell n j‖
        =
      ‖shiftedSingleBoundaryCore n (J + 1) - shiftedSingleBoundaryCore n 1
          - ∑ j ∈ Finset.Icc 1 J, shiftedCompleteBlockCorrectionTerm n j‖ := by
            rw [shifted_completeBlock_complex_mul_phase_sum_eq_boundaryCore_diff]
    _ ≤ ‖shiftedSingleBoundaryCore n (J + 1) - shiftedSingleBoundaryCore n 1‖
          + ‖∑ j ∈ Finset.Icc 1 J, shiftedCompleteBlockCorrectionTerm n j‖ := by
            simpa [sub_eq_add_neg] using
              norm_add_le
                (shiftedSingleBoundaryCore n (J + 1) - shiftedSingleBoundaryCore n 1)
                (-∑ j ∈ Finset.Icc 1 J, shiftedCompleteBlockCorrectionTerm n j)
    _ ≤ 2 + C0 * Real.sqrt (((n + J : ℕ) : ℝ) + 1) := by
          exact add_le_add hboundary (hcorr n hn J hJ)
    _ ≤ (C0 + 2) * Real.sqrt (((n + J : ℕ) : ℝ) + 1) := by
          nlinarith
    _ = C * Real.sqrt (((n + J : ℕ) : ℝ) + 1) := by
          rfl

private theorem weighted_shifted_completeBlock_complex_bound_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ k : ℕ, N0 ≤ k →
      ∀ j : ℕ, 1 ≤ j → j ≤ (k + 1) / 2 →
        ‖(((modeWeight (k - j) : ℝ) : ℂ) *
          ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
            HardyCosSmooth.hardyCosExp (k - j) t)‖
          ≤ C * Real.sqrt ((k : ℝ) + 1) / j := by
  obtain ⟨Cω, hCω, N0, hderivBound⟩ := weightedResonantBlockMode_deriv_bound_eventually
  let C : ℝ := Real.sqrt 2 * (2 + Cω)
  refine ⟨C, by
    dsimp [C]
    positivity, N0, ?_⟩
  intro k hk j hj hj_half
  have hjk : j ≤ k := by omega
  have hmain :=
    weighted_shifted_completeBlock_commonIntegral_eq_resonantCarrier_singlePacket k j hj hjk
  rw [hmain]
  rw [resonantCarrier_shiftedSinglePacket_integral_by_parts k j hj hjk]
  have hprim0 :
      ‖shiftedSinglePrimitive k j 0‖ ≤ Real.sqrt 2 * (((k : ℝ) + 1) / j) :=
    shiftedSinglePrimitive_norm_bound k j hj hj_half 0
  have hprim1 :
      ‖shiftedSinglePrimitive k j 1‖ ≤ Real.sqrt 2 * (((k : ℝ) + 1) / j) :=
    shiftedSinglePrimitive_norm_bound k j hj hj_half 1
  have hnorm_f0 : ‖weightedResonantBlockMode k 0‖ = modeWeight k :=
    weightedResonantBlockMode_norm k 0
  have hnorm_f1 : ‖weightedResonantBlockMode k 1‖ = modeWeight k :=
    weightedResonantBlockMode_norm k 1
  have hIntBound :
      ‖∫ u in (0 : ℝ)..1,
          (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
            shiftedSinglePrimitive k j u‖
        ≤ Cω * modeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
    calc
      ‖∫ u in (0 : ℝ)..1,
          (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
            shiftedSinglePrimitive k j u‖
          ≤ ∫ u in (0 : ℝ)..1,
              ‖(Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
                shiftedSinglePrimitive k j u‖ := by
                simpa [Real.norm_eq_abs] using
                  (intervalIntegral.norm_integral_le_integral_norm
                    (f := fun u =>
                      (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
                        shiftedSinglePrimitive k j u)
                    (by norm_num : (0 : ℝ) ≤ 1))
      _ ≤ ∫ u in (0 : ℝ)..1,
            Cω * modeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
            let B : ℝ := Cω * modeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j))
            have hG_cont : Continuous fun u : ℝ => shiftedSinglePrimitive k j u := by
              unfold shiftedSinglePrimitive
              exact continuous_const.mul <|
                Complex.continuous_exp.comp <|
                  continuous_const.mul <|
                    Complex.continuous_ofReal.comp ((blockCoord_continuous k).mul continuous_const)
            have hcont : Continuous fun u : ℝ =>
                ‖(Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
                    shiftedSinglePrimitive k j u‖ := by
              exact ((continuous_const.mul
                (Complex.continuous_ofReal.comp (blockOmega_continuous k))).mul
                  (weightedResonantBlockMode_continuous k)).mul hG_cont |>.norm
            have hlower_int :
                IntervalIntegrable
                  (fun u =>
                    ‖(Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
                        shiftedSinglePrimitive k j u‖)
                  volume (0 : ℝ) 1 := hcont.intervalIntegrable _ _
            have hupper_int :
                IntervalIntegrable (fun _ : ℝ => B) volume (0 : ℝ) 1 := intervalIntegrable_const
            exact intervalIntegral.integral_mono_on
              (a := (0 : ℝ)) (b := 1)
              (f := fun u =>
                ‖(Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
                    shiftedSinglePrimitive k j u‖)
              (g := fun _ : ℝ => B)
              (hab := by norm_num) (hf := hlower_int) (hg := hupper_int) <|
                by
                  intro u hu
                  have hdu := hderivBound k hk u hu
                  have hGu := shiftedSinglePrimitive_norm_bound k j hj hj_half u
                  calc
                    ‖(Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
                        shiftedSinglePrimitive k j u‖
                        =
                      ‖Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u‖ *
                        ‖shiftedSinglePrimitive k j u‖ := by
                          rw [norm_mul]
                    _ ≤ (Cω * modeWeight k) * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
                          have hCω_nonneg : 0 ≤ Cω := le_of_lt hCω
                          exact mul_le_mul hdu hGu (norm_nonneg _) (mul_nonneg hCω_nonneg
                            (le_of_lt (modeWeight_pos k)))
      _ = Cω * modeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
            simp
  have hmode_sqrt :
      modeWeight k * ((k : ℝ) + 1) = Real.sqrt ((k : ℝ) + 1) := by
    simpa using modeWeight_mul_succ_eq_sqrt k
  calc
    ‖weightedResonantBlockMode k 1 * shiftedSinglePrimitive k j 1
        - weightedResonantBlockMode k 0 * shiftedSinglePrimitive k j 0
        - ∫ u in (0 : ℝ)..1,
            (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
              shiftedSinglePrimitive k j u‖
        ≤ ‖weightedResonantBlockMode k 1 * shiftedSinglePrimitive k j 1‖
            + ‖weightedResonantBlockMode k 0 * shiftedSinglePrimitive k j 0‖
            + ‖∫ u in (0 : ℝ)..1,
                (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
                  shiftedSinglePrimitive k j u‖ := by
              have := norm_sub_le
                (weightedResonantBlockMode k 1 * shiftedSinglePrimitive k j 1
                  - weightedResonantBlockMode k 0 * shiftedSinglePrimitive k j 0)
                (∫ u in (0 : ℝ)..1,
                  (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
                    shiftedSinglePrimitive k j u)
              exact le_trans this <| by
                gcongr
                exact norm_sub_le _ _
    _ ≤ modeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j))
          + modeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j))
          + Cω * modeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
            have hbd0 :
                ‖weightedResonantBlockMode k 0 * shiftedSinglePrimitive k j 0‖
                  ≤ modeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
              rw [norm_mul, hnorm_f0]
              exact mul_le_mul_of_nonneg_left hprim0 (le_of_lt (modeWeight_pos k))
            have hbd1 :
                ‖weightedResonantBlockMode k 1 * shiftedSinglePrimitive k j 1‖
                  ≤ modeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
              rw [norm_mul, hnorm_f1]
              exact mul_le_mul_of_nonneg_left hprim1 (le_of_lt (modeWeight_pos k))
            linarith
    _ = (2 + Cω) * modeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j)) := by
          ring
    _ = C * Real.sqrt ((k : ℝ) + 1) / j := by
          dsimp [C]
          calc
            (2 + Cω) * modeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) / j))
                = (Real.sqrt 2 * (2 + Cω)) * (modeWeight k * ((k : ℝ) + 1)) / j := by
                    field_simp [show (j : ℝ) ≠ 0 by positivity]
            _ = C * Real.sqrt ((k : ℝ) + 1) / j := by
                  rw [hmode_sqrt]

/-- On the genuine near-band `n ≥ j - 1`, the phase-weighted fixed-shift block
prefix is already `O(√(m+j))`. This uses the extra
`shiftedRelativePhase (n+j) j` factor present in
`shiftedCompleteBlockPhaseWeightedCell`, so the per-cell `√(n+j)/j` loss is
reduced to a summable `1 / √(n+j)` bound. -/
private theorem shiftedCompleteBlockPhaseWeightedFixedShiftPrefix_bound_eventually :
    ∃ C > 0, ∃ J0 : ℕ, ∀ j : ℕ, J0 ≤ j →
      ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockPhaseWeightedCell n j‖
          ≤ C * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
  obtain ⟨C0, hC0, N0, hcell⟩ := weighted_shifted_completeBlock_complex_bound_eventually
  let J0 : ℕ := max 1 N0
  let C : ℝ := 4 * C0
  refine ⟨C, by
    dsimp [C]
    positivity, J0, ?_⟩
  intro j hj m
  calc
    ‖∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockPhaseWeightedCell n j‖
        ≤ ∑ n ∈ Finset.Ico (j - 1) (m + 1), ‖shiftedCompleteBlockPhaseWeightedCell n j‖ :=
          norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ico (j - 1) (m + 1), 2 * C0 * modeWeight (n + j) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hn_lo : j - 1 ≤ n := (Finset.mem_Ico.mp hn).1
          have hj1 : 1 ≤ j := by
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
          have hphase_nonneg : 0 ≤ shiftedRelativePhase (n + j) j := by
            exact (shiftedRelativePhase_pos (n + j) j hj1 (by omega)).le
          have hphase_upper :
              shiftedRelativePhase (n + j) j ≤ 2 * (j : ℝ) / ((((n + j : ℕ) : ℝ) + 1)) := by
            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
              shiftedRelativePhase_upper_of_half (n + j) j hj1 hhalf
          have hweighted :
              ‖(((modeWeight n : ℝ) : ℂ) *
                  ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
                    HardyCosSmooth.hardyCosExp n t)‖
                ≤ C0 * Real.sqrt ((((n + j : ℕ) : ℝ) + 1)) / j := by
            simpa using
              hcell (n + j) hk_large j hj1 hhalf
          have hsqrt :
              modeWeight (n + j) * ((((n + j : ℕ) : ℝ) + 1))
                = Real.sqrt ((((n + j : ℕ) : ℝ) + 1)) := by
            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
              modeWeight_mul_succ_eq_sqrt (n + j)
          calc
            ‖shiftedCompleteBlockPhaseWeightedCell n j‖
                = shiftedRelativePhase (n + j) j *
                    ‖(((modeWeight n : ℝ) : ℂ) *
                      ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
                        HardyCosSmooth.hardyCosExp n t)‖ := by
                      unfold shiftedCompleteBlockPhaseWeightedCell
                      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                        abs_of_nonneg hphase_nonneg]
            _ ≤ shiftedRelativePhase (n + j) j *
                  (C0 * Real.sqrt ((((n + j : ℕ) : ℝ) + 1)) / j) := by
                    exact mul_le_mul_of_nonneg_left hweighted hphase_nonneg
            _ ≤ (2 * (j : ℝ) / ((((n + j : ℕ) : ℝ) + 1))) *
                  (C0 * Real.sqrt ((((n + j : ℕ) : ℝ) + 1)) / j) := by
                    have hfac_nonneg :
                        0 ≤ C0 * Real.sqrt ((((n + j : ℕ) : ℝ) + 1)) / j := by
                      positivity
                    exact mul_le_mul_of_nonneg_right hphase_upper hfac_nonneg
            _ = 2 * C0 * modeWeight (n + j) := by
                  rw [← hsqrt]
                  field_simp [show (j : ℝ) ≠ 0 by positivity,
                    show ((((n + j : ℕ) : ℝ) + 1)) ≠ 0 by positivity]
    _ = 2 * C0 * ∑ n ∈ Finset.Ico (j - 1) (m + 1), modeWeight (n + j) := by
          rw [Finset.mul_sum]
    _ = 2 * C0 * ∑ r ∈ Finset.Ico (j - 1 + j) (m + 1 + j), modeWeight r := by
          congr 1
          simpa [add_assoc, add_left_comm, add_comm] using
            (Finset.sum_Ico_add (f := fun r => modeWeight r) (j - 1) (m + 1) j)
    _ ≤ 2 * C0 * ∑ r ∈ Finset.range (m + j + 1), modeWeight r := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (by
              intro r hr
              exact Finset.mem_range.mpr <| by
                simpa [Nat.add_assoc, add_left_comm, add_comm] using (Finset.mem_Ico.mp hr).2)
            (by
              intro r hr hmem
              exact le_of_lt (modeWeight_pos r))
    _ ≤ 2 * C0 * (2 * Real.sqrt ((m + j + 1 : ℕ) : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc
            ∑ r ∈ Finset.range (m + j + 1), modeWeight r
                = ∑ r ∈ Finset.range (m + j + 1), ((r + 1 : ℝ) ^ (-1 / 2 : ℝ)) := by
                    refine Finset.sum_congr rfl ?_
                    intro r hr
                    rw [modeWeight_eq_neg_half]
            _ ≤ 2 * Real.sqrt ((m + j + 1 : ℕ) : ℝ) :=
                  Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le (m + j + 1)
    _ = C * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
          calc
            2 * C0 * (2 * Real.sqrt ((m + j + 1 : ℕ) : ℝ))
                = C0 * Real.sqrt ((m + j + 1 : ℕ) : ℝ) * 4 := by ring
            _ = C0 * Real.sqrt ((((m + j : ℕ) : ℝ) + 1) ) * 4 := by
                  congr 2
                  norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
            _ = C * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
                  dsimp [C]
                  ring

/-- The genuine near-band fixed-shift correction prefix is already `O(√(m+j))`.
This is extracted from the two-parameter truncated triangles by taking the
`J`-difference and combining the resulting exact boundary transport identity
with the phase-weighted fixed-shift prefix bound. -/
private theorem shiftedCompleteBlockCorrectionFixedShiftPrefix_bound_eventually :
    ∃ C > 0, ∃ J0 : ℕ, ∀ j : ℕ, J0 ≤ j →
      ∀ m : ℕ,
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockCorrectionTerm n j‖
          ≤ C * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
  obtain ⟨Cφ, hCφ, Jφ, hphase⟩ :=
    shiftedCompleteBlockPhaseWeightedFixedShiftPrefix_bound_eventually
  let J0 : ℕ := max 2 Jφ
  let C : ℝ := Cφ + 24
  refine ⟨C, by
    dsimp [C]
    positivity, J0, ?_⟩
  intro j hj m
  by_cases hnonempty : j - 1 ≤ m
  · have hj_two : 2 ≤ j := le_trans (by exact Nat.le_max_left 2 Jφ) hj
    have hj_one : 1 ≤ j := le_trans (by norm_num) hj_two
    have hj_phase : Jφ ≤ j := le_trans (by exact Nat.le_max_right 2 Jφ) hj
    have hphase_init :
        shiftedCompleteBlockPhaseWeightedTruncatedTriangle ((j - 2) + j) j
          - shiftedCompleteBlockPhaseWeightedTruncatedTriangle ((j - 2) + j) (j - 1)
        =
        ∑ n ∈ Finset.range (j - 1), shiftedCompleteBlockPhaseWeightedCell n j := by
      simpa [show (j - 2) + 1 = j - 1 by omega] using
        shiftedCompleteBlockPhaseWeightedTruncatedTriangle_diff_eq_fixedShiftPrefix (j - 2) j hj_one
    have hcorr_init :
        shiftedCompleteBlockCorrectionTruncatedTriangle ((j - 2) + j) j
          - shiftedCompleteBlockCorrectionTruncatedTriangle ((j - 2) + j) (j - 1)
        =
        ∑ n ∈ Finset.range (j - 1), shiftedCompleteBlockCorrectionTerm n j := by
      simpa [show (j - 2) + 1 = j - 1 by omega] using
        shiftedCompleteBlockCorrectionTruncatedTriangle_diff_eq_fixedShiftPrefix (j - 2) j hj_one
    have hcorr_init_bd :
        shiftedCompleteBlockCorrectionTruncatedTriangle ((j - 2) + j) j
          - shiftedCompleteBlockCorrectionTruncatedTriangle ((j - 2) + j) (j - 1)
        =
        shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) j
          - shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) (j - 1)
          - ∑ n ∈ Finset.range (j - 1), shiftedCompleteBlockPhaseWeightedCell n j := by
      simpa [show (j - 2) + 1 = j - 1 by omega] using
        shiftedCompleteBlockCorrectionTruncatedTriangle_diff_eq_boundaryDiff_minus_phasePrefix
          (j - 2) j hj_one
    have hIco_corr :
        ∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockCorrectionTerm n j
          =
        (shiftedCompleteBlockCorrectionTruncatedTriangle (m + j) j
            - shiftedCompleteBlockCorrectionTruncatedTriangle (m + j) (j - 1))
          -
        (shiftedCompleteBlockCorrectionTruncatedTriangle ((j - 2) + j) j
            - shiftedCompleteBlockCorrectionTruncatedTriangle ((j - 2) + j) (j - 1)) := by
      rw [Finset.sum_Ico_eq_sub _ (by omega : j - 1 ≤ m + 1)]
      rw [← shiftedCompleteBlockCorrectionTruncatedTriangle_diff_eq_fixedShiftPrefix m j hj_one]
      rw [← hcorr_init]
    have hIco_phase :
        ∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockPhaseWeightedCell n j
          =
        (shiftedCompleteBlockPhaseWeightedTruncatedTriangle (m + j) j
            - shiftedCompleteBlockPhaseWeightedTruncatedTriangle (m + j) (j - 1))
          -
        (shiftedCompleteBlockPhaseWeightedTruncatedTriangle ((j - 2) + j) j
            - shiftedCompleteBlockPhaseWeightedTruncatedTriangle ((j - 2) + j) (j - 1)) := by
      rw [Finset.sum_Ico_eq_sub _ (by omega : j - 1 ≤ m + 1)]
      rw [← shiftedCompleteBlockPhaseWeightedTruncatedTriangle_diff_eq_fixedShiftPrefix m j hj_one]
      rw [← hphase_init]
    have hcorr_m :=
      shiftedCompleteBlockCorrectionTruncatedTriangle_diff_eq_boundaryDiff_minus_phasePrefix m j hj_one
    have hphase_bound_main :
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockPhaseWeightedCell n j‖
          ≤ Cφ * Real.sqrt (((m + j : ℕ) : ℝ) + 1) :=
      hphase j hj_phase m
    have hphase_sub :
        ∑ n ∈ Finset.range (m + 1), shiftedCompleteBlockPhaseWeightedCell n j
          - ∑ n ∈ Finset.range (j - 1), shiftedCompleteBlockPhaseWeightedCell n j
          =
        ∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockPhaseWeightedCell n j := by
      rw [Finset.sum_Ico_eq_sub _ (by omega : j - 1 ≤ m + 1)]
    have hroot_ge :
        Real.sqrt ((((j - 2) + j : ℕ) : ℝ) + 1)
          ≤ Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
      refine Real.sqrt_le_sqrt ?_
      exact_mod_cast (by omega : (j - 2) + j + 1 ≤ m + j + 1)
    calc
      ‖∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockCorrectionTerm n j‖
          =
        ‖(shiftedCompleteBlockCorrectionTruncatedTriangle (m + j) j
              - shiftedCompleteBlockCorrectionTruncatedTriangle (m + j) (j - 1))
            -
            (shiftedCompleteBlockCorrectionTruncatedTriangle ((j - 2) + j) j
              - shiftedCompleteBlockCorrectionTruncatedTriangle ((j - 2) + j) (j - 1))‖ := by
              rw [hIco_corr]
      _ =
        ‖((shiftedCompleteBlockTruncatedBoundary (m + j) j
                - shiftedCompleteBlockTruncatedBoundary (m + j) (j - 1))
              -
              ∑ n ∈ Finset.range (m + 1), shiftedCompleteBlockPhaseWeightedCell n j)
            -
            ((shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) j
                - shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) (j - 1))
              -
              ∑ n ∈ Finset.range (j - 1), shiftedCompleteBlockPhaseWeightedCell n j)‖ := by
              rw [hcorr_m, hcorr_init_bd]
      _ =
        ‖((shiftedCompleteBlockTruncatedBoundary (m + j) j
                - shiftedCompleteBlockTruncatedBoundary (m + j) (j - 1))
              -
              (shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) j
                - shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) (j - 1)))
            -
            (∑ n ∈ Finset.range (m + 1), shiftedCompleteBlockPhaseWeightedCell n j
              - ∑ n ∈ Finset.range (j - 1), shiftedCompleteBlockPhaseWeightedCell n j)‖ := by
              ring
      _ =
        ‖((shiftedCompleteBlockTruncatedBoundary (m + j) j
                - shiftedCompleteBlockTruncatedBoundary (m + j) (j - 1))
              -
              (shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) j
                - shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) (j - 1)))
            -
            ∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockPhaseWeightedCell n j‖ := by
              rw [hphase_sub]
      _ ≤
          ‖(shiftedCompleteBlockTruncatedBoundary (m + j) j
                - shiftedCompleteBlockTruncatedBoundary (m + j) (j - 1))
              -
              (shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) j
                - shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) (j - 1))‖
            + ‖∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockPhaseWeightedCell n j‖ := by
              exact norm_sub_le _ _
      _ ≤
          ‖shiftedCompleteBlockTruncatedBoundary (m + j) j
              - shiftedCompleteBlockTruncatedBoundary (m + j) (j - 1)‖
            + ‖shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) j
                - shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) (j - 1)‖
            + ‖∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockPhaseWeightedCell n j‖ := by
              have := norm_sub_le
                (shiftedCompleteBlockTruncatedBoundary (m + j) j
                  - shiftedCompleteBlockTruncatedBoundary (m + j) (j - 1))
                (shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) j
                  - shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) (j - 1))
              linarith
      _ ≤
          8 * Real.sqrt (((m + j : ℕ) : ℝ) + 1)
            + 8 * Real.sqrt ((((j - 2) + j : ℕ) : ℝ) + 1)
            + Cφ * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
              exact add_le_add
                (add_le_add
                  (shiftedCompleteBlockTruncatedBoundary_diff_bound (m + j) j)
                  (shiftedCompleteBlockTruncatedBoundary_diff_bound ((j - 2) + j) j))
                hphase_bound_main
      _ ≤ (Cφ + 24) * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
              have hsqrt_nonneg : 0 ≤ Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by positivity
              have hinit_le :
                  Real.sqrt ((((j - 2) + j : ℕ) : ℝ) + 1)
                    ≤ Real.sqrt (((m + j : ℕ) : ℝ) + 1) := hroot_ge
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

private theorem shiftedSingleBoundaryCoreFixedShiftPrefix_eq_boundaryDiff
    (m j : ℕ) (hj : 2 ≤ j) (hnonempty : j - 1 ≤ m) :
    (shiftedCompleteBlockTruncatedBoundary (m + j) j
        - shiftedCompleteBlockTruncatedBoundary (m + j) (j - 1))
      -
      (shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) j
        - shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) (j - 1))
      =
    ∑ n ∈ Finset.Ico (j - 1) (m + 1),
      (shiftedSingleBoundaryCore n (j + 1) - shiftedSingleBoundaryCore n j) := by
  have hj_one : 1 ≤ j := le_trans (by norm_num) hj
  have hcorr_main :=
    shiftedCompleteBlockCorrectionTruncatedTriangle_diff_eq_fixedShiftPrefix m j hj_one
  have hrange_init : Finset.range ((j - 2) + 1) = Finset.range (j - 1) := by
    congr
    omega
  have hcorr_init :
      shiftedCompleteBlockCorrectionTruncatedTriangle ((j - 2) + j) j
        - shiftedCompleteBlockCorrectionTruncatedTriangle ((j - 2) + j) (j - 1)
      =
      ∑ n ∈ Finset.range (j - 1), shiftedCompleteBlockCorrectionTerm n j := by
    rw [shiftedCompleteBlockCorrectionTruncatedTriangle_diff_eq_fixedShiftPrefix (j - 2) j hj_one]
    rw [hrange_init]
  have hphase_main :=
    shiftedCompleteBlockPhaseWeightedTruncatedTriangle_diff_eq_fixedShiftPrefix m j hj_one
  have hphase_init :
      shiftedCompleteBlockPhaseWeightedTruncatedTriangle ((j - 2) + j) j
        - shiftedCompleteBlockPhaseWeightedTruncatedTriangle ((j - 2) + j) (j - 1)
      =
      ∑ n ∈ Finset.range (j - 1), shiftedCompleteBlockPhaseWeightedCell n j := by
    rw [shiftedCompleteBlockPhaseWeightedTruncatedTriangle_diff_eq_fixedShiftPrefix (j - 2) j hj_one]
    rw [hrange_init]
  have hbd_main :=
    shiftedCompleteBlockCorrectionTruncatedTriangle_diff_eq_boundaryDiff_minus_phasePrefix m j hj_one
  have hbd_init :=
    shiftedCompleteBlockCorrectionTruncatedTriangle_diff_eq_boundaryDiff_minus_phasePrefix (j - 2) j hj_one
  have hcorr_sub :
      (shiftedCompleteBlockCorrectionTruncatedTriangle (m + j) j
          - shiftedCompleteBlockCorrectionTruncatedTriangle (m + j) (j - 1))
        -
        (shiftedCompleteBlockCorrectionTruncatedTriangle ((j - 2) + j) j
          - shiftedCompleteBlockCorrectionTruncatedTriangle ((j - 2) + j) (j - 1))
      =
      ∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockCorrectionTerm n j := by
    rw [hcorr_main, hcorr_init]
    rw [Finset.sum_Ico_eq_sub _ (by omega : j - 1 ≤ m + 1)]
  have hphase_sub :
      (shiftedCompleteBlockPhaseWeightedTruncatedTriangle (m + j) j
          - shiftedCompleteBlockPhaseWeightedTruncatedTriangle (m + j) (j - 1))
        -
        (shiftedCompleteBlockPhaseWeightedTruncatedTriangle ((j - 2) + j) j
          - shiftedCompleteBlockPhaseWeightedTruncatedTriangle ((j - 2) + j) (j - 1))
      =
      ∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockPhaseWeightedCell n j := by
    rw [hphase_main, hphase_init]
    rw [Finset.sum_Ico_eq_sub _ (by omega : j - 1 ≤ m + 1)]
  have hbd_main' :
      shiftedCompleteBlockTruncatedBoundary (m + j) j
        - shiftedCompleteBlockTruncatedBoundary (m + j) (j - 1)
      =
      (shiftedCompleteBlockCorrectionTruncatedTriangle (m + j) j
          - shiftedCompleteBlockCorrectionTruncatedTriangle (m + j) (j - 1))
        + ∑ n ∈ Finset.range (m + 1), shiftedCompleteBlockPhaseWeightedCell n j := by
    rw [hbd_main]
    ring
  have hbd_init' :
      shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) j
        - shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) (j - 1)
      =
      (shiftedCompleteBlockCorrectionTruncatedTriangle ((j - 2) + j) j
          - shiftedCompleteBlockCorrectionTruncatedTriangle ((j - 2) + j) (j - 1))
        + ∑ n ∈ Finset.range (j - 1), shiftedCompleteBlockPhaseWeightedCell n j := by
    have hbd_init_raw :
        shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) j
          - shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) (j - 1)
        =
        (shiftedCompleteBlockCorrectionTruncatedTriangle ((j - 2) + j) j
            - shiftedCompleteBlockCorrectionTruncatedTriangle ((j - 2) + j) (j - 1))
          + ∑ n ∈ Finset.range ((j - 2) + 1), shiftedCompleteBlockPhaseWeightedCell n j := by
      rw [hbd_init]
      ring
    rw [hbd_init_raw, hrange_init]
  have hphase_range_sub :
      (∑ n ∈ Finset.range (m + 1), shiftedCompleteBlockPhaseWeightedCell n j)
        - (∑ n ∈ Finset.range (j - 1), shiftedCompleteBlockPhaseWeightedCell n j)
      =
      ∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockPhaseWeightedCell n j := by
    rw [Finset.sum_Ico_eq_sub _ (by omega : j - 1 ≤ m + 1)]
  have hcell :
      ∀ n : ℕ,
        shiftedCompleteBlockCorrectionTerm n j + shiftedCompleteBlockPhaseWeightedCell n j
          =
        shiftedSingleBoundaryCore n (j + 1) - shiftedSingleBoundaryCore n j := by
    intro n
    have htmp :
        shiftedCompleteBlockPhaseWeightedCell n j
          =
        shiftedSingleBoundaryCore n (j + 1) - shiftedSingleBoundaryCore n j
          - shiftedCompleteBlockCorrectionTerm n j := by
      unfold shiftedCompleteBlockPhaseWeightedCell
      simpa using shifted_completeBlock_complex_mul_phase_eq_boundaryCore_diff n j hj_one
    rw [htmp]
    ring
  calc
    (shiftedCompleteBlockTruncatedBoundary (m + j) j
        - shiftedCompleteBlockTruncatedBoundary (m + j) (j - 1))
      -
      (shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) j
        - shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) (j - 1))
        =
      ((shiftedCompleteBlockCorrectionTruncatedTriangle (m + j) j
          - shiftedCompleteBlockCorrectionTruncatedTriangle (m + j) (j - 1))
        -
        (shiftedCompleteBlockCorrectionTruncatedTriangle ((j - 2) + j) j
          - shiftedCompleteBlockCorrectionTruncatedTriangle ((j - 2) + j) (j - 1)))
      +
      ((∑ n ∈ Finset.range (m + 1), shiftedCompleteBlockPhaseWeightedCell n j)
        - (∑ n ∈ Finset.range (j - 1), shiftedCompleteBlockPhaseWeightedCell n j)) := by
          rw [hbd_main', hbd_init']
          ring
    _ =
      (∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockCorrectionTerm n j)
        +
      (∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockPhaseWeightedCell n j) := by
          rw [hcorr_sub, hphase_range_sub]
    _ =
      ∑ n ∈ Finset.Ico (j - 1) (m + 1),
        (shiftedCompleteBlockCorrectionTerm n j + shiftedCompleteBlockPhaseWeightedCell n j) := by
          rw [← Finset.sum_add_distrib]
    _ =
      ∑ n ∈ Finset.Ico (j - 1) (m + 1),
        (shiftedSingleBoundaryCore n (j + 1) - shiftedSingleBoundaryCore n j) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          exact hcell n

private theorem shiftedSingleBoundaryCoreFixedShiftPrefix_bound
    (m j : ℕ) (hj : 1 ≤ j) :
    ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
        (shiftedSingleBoundaryCore n (j + 1) - shiftedSingleBoundaryCore n j)‖
      ≤ 16 * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
  by_cases hnonempty : j - 1 ≤ m
  · by_cases hj_two : 2 ≤ j
    · have hEq :=
        shiftedSingleBoundaryCoreFixedShiftPrefix_eq_boundaryDiff m j hj_two hnonempty
      have hroot_ge :
          Real.sqrt ((((j - 2) + j : ℕ) : ℝ) + 1)
            ≤ Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
        refine Real.sqrt_le_sqrt ?_
        exact_mod_cast (by omega : (j - 2) + j + 1 ≤ m + j + 1)
      calc
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            (shiftedSingleBoundaryCore n (j + 1) - shiftedSingleBoundaryCore n j)‖
            =
          ‖(shiftedCompleteBlockTruncatedBoundary (m + j) j
              - shiftedCompleteBlockTruncatedBoundary (m + j) (j - 1))
            -
            (shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) j
              - shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) (j - 1))‖ := by
              rw [← hEq]
        _ ≤ ‖shiftedCompleteBlockTruncatedBoundary (m + j) j
                - shiftedCompleteBlockTruncatedBoundary (m + j) (j - 1)‖
              + ‖shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) j
                  - shiftedCompleteBlockTruncatedBoundary ((j - 2) + j) (j - 1)‖ := by
                exact norm_sub_le _ _
        _ ≤ 8 * Real.sqrt (((m + j : ℕ) : ℝ) + 1)
              + 8 * Real.sqrt ((((j - 2) + j : ℕ) : ℝ) + 1) := by
                exact add_le_add
                  (shiftedCompleteBlockTruncatedBoundary_diff_bound (m + j) j)
                  (shiftedCompleteBlockTruncatedBoundary_diff_bound ((j - 2) + j) j)
        _ ≤ 16 * Real.sqrt (((m + j : ℕ) : ℝ) + 1) := by
                nlinarith
    · have hj_one : j = 1 := by omega
      subst j
      have hIco : Finset.Ico (0 : ℕ) (m + 1) = Finset.range (m + 1) := by
        simp
      calc
        ‖∑ n ∈ Finset.Ico (0 : ℕ) (m + 1),
            (shiftedSingleBoundaryCore n (1 + 1) - shiftedSingleBoundaryCore n 1)‖
            ≤ ∑ n ∈ Finset.Ico (0 : ℕ) (m + 1),
                ‖shiftedSingleBoundaryCore n (1 + 1) - shiftedSingleBoundaryCore n 1‖ := by
                  exact norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.Ico (0 : ℕ) (m + 1),
              (‖shiftedSingleBoundaryCore n (1 + 1)‖ + ‖shiftedSingleBoundaryCore n 1‖) := by
                refine Finset.sum_le_sum ?_
                intro n hn
                exact norm_sub_le _ _
        _ = ∑ n ∈ Finset.range (m + 1), (modeWeight n + modeWeight n) := by
              rw [hIco]
              refine Finset.sum_congr rfl ?_
              intro n hn
              rw [shiftedSingleBoundaryCore_norm n 2 (by norm_num),
                shiftedSingleBoundaryCore_norm n 1 (by norm_num)]
        _ = 2 * ∑ n ∈ Finset.range (m + 1), modeWeight n := by
              calc
                ∑ n ∈ Finset.range (m + 1), (modeWeight n + modeWeight n)
                    = ∑ n ∈ Finset.range (m + 1), (2 * modeWeight n) := by
                        refine Finset.sum_congr rfl ?_
                        intro n hn
                        ring
                _ = 2 * ∑ n ∈ Finset.range (m + 1), modeWeight n := by
                    rw [Finset.mul_sum]
        _ ≤ 2 * (2 * Real.sqrt (m + 1)) := by
              gcongr
              calc
                ∑ n ∈ Finset.range (m + 1), modeWeight n
                    = ∑ n ∈ Finset.range (m + 1), ((n + 1 : ℝ) ^ (-1 / 2 : ℝ)) := by
                        refine Finset.sum_congr rfl ?_
                        intro n hn
                        rw [modeWeight_eq_neg_half]
                _ ≤ 2 * Real.sqrt (m + 1) := by
                    simpa [div_eq_mul_inv, show (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) by ring_nf] using
                      Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le (m + 1)
        _ ≤ 16 * Real.sqrt (((m + 1 : ℕ) : ℝ) + 1) := by
              have hsqrt :
                  Real.sqrt (m + 1) ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) + 1) := by
                refine Real.sqrt_le_sqrt ?_
                have hle : (m : ℝ) + 1 ≤ (m : ℝ) + 2 := by
                  linarith
                simpa [Nat.cast_add, add_assoc] using hle
              calc
                2 * (2 * Real.sqrt (m + 1))
                    = 4 * Real.sqrt (m + 1) := by ring
                _ ≤ 4 * Real.sqrt (((m + 1 : ℕ) : ℝ) + 1) := by
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

/-- The unphased weighted contribution of mode `n` on the shifted complete
block with offset `j`. This is the exact fixed-shift cell whose rowwise
oscillatory cancellation is the remaining analytic target. -/
private noncomputable def shiftedCompleteBlockCell (n j : ℕ) : ℂ :=
  (((modeWeight n : ℝ) : ℂ) *
    ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)),
      HardyCosSmooth.hardyCosExp n t)

/-- The exact block-coordinate integrand for one unphased shifted cell.  A
future fixed-shift row theorem should bound finite sums of this integrand
uniformly in `u ∈ [0, 1]`. -/
private noncomputable def shiftedCompleteBlockRowIntegrand (n j : ℕ) (u : ℝ) : ℂ :=
  (((modeWeight n : ℝ) : ℂ) *
    (HardyCosSmooth.hardyCosExp n (blockCoord (n + j) u) *
      ((blockJacobian (n + j) u : ℝ) : ℂ)))

/-- The common normalized-Gamma carrier for one fixed-shift row cell, after
pulling the `n`-dependent Dirichlet packet off the Hardy exponential. -/
private noncomputable def shiftedCompleteBlockRowCarrier (n j : ℕ) (u : ℝ) : ℂ :=
  commonBlockCarrier (n + j) u * ((blockJacobian (n + j) u : ℝ) : ℂ)

/-- The exact `n`-dependent Dirichlet packet in one fixed-shift row cell. -/
private noncomputable def shiftedCompleteBlockRowPacket (n j : ℕ) (u : ℝ) : ℂ :=
  (((modeWeight n : ℝ) : ℂ) *
    Complex.exp (-Complex.I * ↑(blockCoord (n + j) u * Real.log ((n : ℝ) + 1))))

/-- The row packet phase increment from `n` to `n+1` at fixed shift `j` and
block parameter `u`.  Any future direct oscillatory-sum proof on fixed rows
should analyze this exact increment. -/
private noncomputable def shiftedCompleteBlockRowPacketStepPhase (n j : ℕ) (u : ℝ) : ℝ :=
  blockCoord (n + j + 1) u * Real.log ((n : ℝ) + 2)
    - blockCoord (n + j) u * Real.log ((n : ℝ) + 1)

/-- The finite fixed-shift row of unphased complete-block cells. -/
private noncomputable def shiftedCompleteBlockFixedShiftRow (m j : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockCell n j

private lemma shiftedCompleteBlockRowIntegrand_continuous (n j : ℕ) :
    Continuous (shiftedCompleteBlockRowIntegrand n j) := by
  have hcont :
      Continuous fun u : ℝ =>
        (((modeWeight n : ℝ) : ℂ) *
          (HardyCosSmooth.hardyCosExp n (blockCoord (n + j) u) *
            ((blockJacobian (n + j) u : ℝ) : ℂ))) := by
    exact continuous_const.mul
      (((HardyCosSmooth.continuous_hardyCosExp_complex n).comp
        (blockCoord_continuous (n + j))).mul
        (Complex.continuous_ofReal.comp (blockJacobian_continuous (n + j))))
  simpa [shiftedCompleteBlockRowIntegrand, mul_assoc] using hcont

private theorem shiftedCompleteBlockRowIntegrand_eq_carrier_packet (n j : ℕ) (u : ℝ) :
    shiftedCompleteBlockRowIntegrand n j u
      = shiftedCompleteBlockRowCarrier n j u * shiftedCompleteBlockRowPacket n j u := by
  calc
    shiftedCompleteBlockRowIntegrand n j u
        =
      ((((modeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (blockCoord (n + j) u)) *
        ((blockJacobian (n + j) u : ℝ) : ℂ)) := by
          unfold shiftedCompleteBlockRowIntegrand
          ring
    _ =
      ((commonBlockCarrier (n + j) u *
          ((((modeWeight n : ℝ) : ℂ) *
            Complex.exp (-Complex.I * ↑(blockCoord (n + j) u * Real.log ((n : ℝ) + 1)))))) *
        ((blockJacobian (n + j) u : ℝ) : ℂ)) := by
          rw [weighted_hardyCosExp_eq_commonBlockCarrier (n + j) n u]
    _ = shiftedCompleteBlockRowCarrier n j u * shiftedCompleteBlockRowPacket n j u := by
          unfold shiftedCompleteBlockRowCarrier shiftedCompleteBlockRowPacket
          ac_rfl

private lemma shiftedCompleteBlockRowCarrier_norm (n j : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    ‖shiftedCompleteBlockRowCarrier n j u‖ = blockJacobian (n + j) u := by
  unfold shiftedCompleteBlockRowCarrier
  rw [norm_mul, commonBlockCarrier_norm, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg ((blockJacobian_pos (n + j) hu).le)

private lemma shiftedCompleteBlockRowPacket_norm (n j : ℕ) (u : ℝ) :
    ‖shiftedCompleteBlockRowPacket n j u‖ = modeWeight n := by
  unfold shiftedCompleteBlockRowPacket
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (modeWeight_pos n))]
  have hexp :
      ‖Complex.exp (-Complex.I * ↑(blockCoord (n + j) u * Real.log ((n : ℝ) + 1)))‖ = 1 := by
        rw [Complex.norm_exp]
        simp
  rw [hexp, mul_one]

private lemma shiftedCompleteBlockRowIntegrand_norm (n j : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    ‖shiftedCompleteBlockRowIntegrand n j u‖ = modeWeight n * blockJacobian (n + j) u := by
  rw [shiftedCompleteBlockRowIntegrand_eq_carrier_packet, norm_mul,
    shiftedCompleteBlockRowCarrier_norm _ _ _ hu, shiftedCompleteBlockRowPacket_norm]
  ring

private theorem shiftedCompleteBlockRowPacket_step (n j : ℕ) (u : ℝ) :
    shiftedCompleteBlockRowPacket (n + 1) j u
      =
      shiftedCompleteBlockRowPacket n j u *
        ((((modeWeight (n + 1) / modeWeight n : ℝ) : ℂ)) *
          Complex.exp (-Complex.I * ↑(shiftedCompleteBlockRowPacketStepPhase n j u))) := by
  have hn_ne : (((modeWeight n : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast modeWeight_ne_zero n
  let A : ℝ := blockCoord (n + j + 1) u * Real.log ((n : ℝ) + 2)
  let B : ℝ := blockCoord (n + j) u * Real.log ((n : ℝ) + 1)
  have hweight :
      (((modeWeight (n + 1) : ℝ) : ℂ))
        =
      (((modeWeight n : ℝ) : ℂ) * (((modeWeight (n + 1) / modeWeight n : ℝ) : ℂ))) := by
        rw [← Complex.ofReal_mul]
        norm_num
        field_simp [modeWeight_ne_zero n]
  have hexp :
      Complex.exp (-Complex.I * ↑A)
        =
      Complex.exp (-Complex.I * ↑B) *
        Complex.exp (-Complex.I * ↑(A - B)) := by
          have harg :
              -Complex.I * ↑A
                =
              (-Complex.I * ↑B) + (-Complex.I * ↑(A - B)) := by
                rw [show (((A - B : ℝ) : ℂ)) = ↑A - ↑B by simp]
                ring
          rw [harg, Complex.exp_add]
  calc
    shiftedCompleteBlockRowPacket (n + 1) j u
      =
      (((modeWeight (n + 1) : ℝ) : ℂ) *
        Complex.exp (-Complex.I * ↑A)) := by
            unfold shiftedCompleteBlockRowPacket
            dsimp [A]
            have hcoord : blockCoord (n + 1 + j) u = blockCoord (n + j + 1) u := by
              simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            have harg :
                -Complex.I *
                    ↑(blockCoord (n + 1 + j) u * Real.log ((((n + 1 : ℕ) : ℝ) + 1)))
                  =
                -Complex.I *
                    ↑(blockCoord (n + j + 1) u * Real.log ((n : ℝ) + 2)) := by
                      rw [hcoord]
                      have hcast' : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by
                        ring_nf
                      have hcast : ((((n + 1 : ℕ) : ℝ) + 1) : ℝ) = (n : ℝ) + 2 := by
                        simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hcast'
                      rw [hcast]
            exact congrArg
              (fun z : ℂ => (((modeWeight (n + 1) : ℝ) : ℂ) * z))
              (congrArg Complex.exp harg)
    _ =
      ((((modeWeight n : ℝ) : ℂ) *
          Complex.exp (-Complex.I * ↑B)) *
        ((((modeWeight (n + 1) / modeWeight n : ℝ) : ℂ)) *
          Complex.exp (-Complex.I * ↑(A - B)))) := by
            rw [hweight, hexp]
            ring
    _ =
      shiftedCompleteBlockRowPacket n j u *
        ((((modeWeight (n + 1) / modeWeight n : ℝ) : ℂ)) *
          Complex.exp (-Complex.I * ↑(shiftedCompleteBlockRowPacketStepPhase n j u))) := by
            simp [shiftedCompleteBlockRowPacket, shiftedCompleteBlockRowPacketStepPhase, A, B]

private theorem shiftedCompleteBlockRowIntegrand_eq_resonantCarrier_singlePacket
    (n j : ℕ) (u : ℝ) :
    shiftedCompleteBlockRowIntegrand n j u
      = resonantBlockCarrier (n + j) u * shiftedSinglePacket (n + j) j u := by
  have hpacket := weighted_hardyCosExp_eq_resonant_times_shiftedPacket (n + j) j u
  have hpacket' :
      (((modeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (blockCoord (n + j) u))
        =
      (((modeWeight (n + j) : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp (n + j) (blockCoord (n + j) u)) *
        shiftedSinglePacket (n + j) j u := by
    simpa [shiftedSinglePacket, shiftedPacketPhase, show n + j - j = n by omega] using hpacket
  calc
    shiftedCompleteBlockRowIntegrand n j u
        =
      ((((modeWeight n : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp n (blockCoord (n + j) u)) *
        ((blockJacobian (n + j) u : ℝ) : ℂ)) := by
          unfold shiftedCompleteBlockRowIntegrand
          ring
    _ =
      ((((modeWeight (n + j) : ℝ) : ℂ) *
          HardyCosSmooth.hardyCosExp (n + j) (blockCoord (n + j) u)) *
        shiftedSinglePacket (n + j) j u) *
        ((blockJacobian (n + j) u : ℝ) : ℂ) := by
          rw [hpacket']
    _ =
      resonantBlockCarrier (n + j) u * shiftedSinglePacket (n + j) j u := by
          unfold resonantBlockCarrier
          ring

private theorem shiftedCompleteBlockRowSum_eq_resonantCarrier_singlePacketSum
    (m j : ℕ) (u : ℝ) :
    ∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockRowIntegrand n j u
      =
    ∑ n ∈ Finset.Ico (j - 1) (m + 1),
      resonantBlockCarrier (n + j) u * shiftedSinglePacket (n + j) j u := by
  refine Finset.sum_congr rfl ?_
  intro n hn
  exact shiftedCompleteBlockRowIntegrand_eq_resonantCarrier_singlePacket n j u

private theorem shiftedCompleteBlockCell_eq_rowIntegral (n j : ℕ) (hj : 1 ≤ j) :
    shiftedCompleteBlockCell n j
      = ∫ u in Ioc (0 : ℝ) 1, shiftedCompleteBlockRowIntegrand n j u := by
  have hblock :=
    hardyCosExp_completeBlock_eq_common_blockParamIntegral (n + j) j hj (by omega)
  have hblock' :
      ∫ t in Ioc (hardyStart (n + j)) (hardyStart (n + j + 1)), HardyCosSmooth.hardyCosExp n t
        = ∫ u in Ioc (0 : ℝ) 1,
            HardyCosSmooth.hardyCosExp n (blockCoord (n + j) u) * blockJacobian (n + j) u := by
    simpa using hblock
  unfold shiftedCompleteBlockCell shiftedCompleteBlockRowIntegrand
  rw [MeasureTheory.integral_const_mul]
  exact congrArg (fun z : ℂ => (((modeWeight n : ℝ) : ℂ) * z)) hblock'

private theorem shiftedCompleteBlockFixedShiftRow_eq_rowIntegral (m j : ℕ) (hj : 1 ≤ j) :
    shiftedCompleteBlockFixedShiftRow m j
      = ∫ u in Ioc (0 : ℝ) 1,
          ∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockRowIntegrand n j u := by
  calc
    shiftedCompleteBlockFixedShiftRow m j
        =
      ∑ n ∈ Finset.Ico (j - 1) (m + 1),
        ∫ u in Ioc (0 : ℝ) 1, shiftedCompleteBlockRowIntegrand n j u := by
          unfold shiftedCompleteBlockFixedShiftRow
          refine Finset.sum_congr rfl ?_
          intro n hn
          exact shiftedCompleteBlockCell_eq_rowIntegral n j hj
    _ =
      ∑ n ∈ Finset.Ico (j - 1) (m + 1),
        ∫ u in (0 : ℝ)..1, shiftedCompleteBlockRowIntegrand n j u := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    _ =
      ∫ u in (0 : ℝ)..1,
        ∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockRowIntegrand n j u := by
          rw [intervalIntegral.integral_finset_sum]
          intro n hn
          exact (shiftedCompleteBlockRowIntegrand_continuous n j).intervalIntegrable _ _
    _ =
      ∫ u in Ioc (0 : ℝ) 1,
        ∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockRowIntegrand n j u := by
          rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

private theorem shiftedCompleteBlockFixedShiftRow_eq_resonantCarrier_singlePacket_rowIntegral
    (m j : ℕ) (hj : 1 ≤ j) :
    shiftedCompleteBlockFixedShiftRow m j
      = ∫ u in Ioc (0 : ℝ) 1,
          ∑ n ∈ Finset.Ico (j - 1) (m + 1),
            resonantBlockCarrier (n + j) u * shiftedSinglePacket (n + j) j u := by
  have hfun :
      (fun u : ℝ =>
        ∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockRowIntegrand n j u)
        =
      (fun u : ℝ =>
        ∑ n ∈ Finset.Ico (j - 1) (m + 1),
          resonantBlockCarrier (n + j) u * shiftedSinglePacket (n + j) j u) := by
            funext u
            rw [shiftedCompleteBlockRowSum_eq_resonantCarrier_singlePacketSum m j u]
  rw [shiftedCompleteBlockFixedShiftRow_eq_rowIntegral m j hj, hfun]

/-- Merge-interface reduction theorem for the eventual fixed-shift row bound.
Any uniform pointwise estimate for the exact
`resonantBlockCarrier * shiftedSinglePacket` row kernel upgrades immediately to
the corresponding bound for the actual unphased fixed-shift row of complete
blocks. -/
private theorem shiftedCompleteBlockFixedShiftRow_bound_of_resonantCarrier_singlePacketRow
    {C : ℝ} (hC : 0 ≤ C) {m j : ℕ} (hj : 1 ≤ j)
    (hrow :
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1),
            resonantBlockCarrier (n + j) u * shiftedSinglePacket (n + j) j u‖
          ≤ C * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j)) :
    ‖shiftedCompleteBlockFixedShiftRow m j‖
      ≤ C * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
  rw [shiftedCompleteBlockFixedShiftRow_eq_resonantCarrier_singlePacket_rowIntegral m j hj]
  let f : ℝ → ℂ := fun u =>
    ∑ n ∈ Finset.Ico (j - 1) (m + 1),
      resonantBlockCarrier (n + j) u * shiftedSinglePacket (n + j) j u
  have hInt : IntervalIntegrable f volume (0 : ℝ) 1 := by
    have hcont : Continuous f := by
      unfold f
      exact continuous_finset_sum _ fun n _ =>
        by
          have hres : Continuous (fun u : ℝ => resonantBlockCarrier (n + j) u) := by
            unfold resonantBlockCarrier
            exact (continuous_const.mul
              ((HardyCosSmooth.continuous_hardyCosExp_complex (n + j)).comp
                (blockCoord_continuous (n + j)))).mul
              (Complex.continuous_ofReal.comp (blockJacobian_continuous (n + j)))
          have hpacket : Continuous (fun u : ℝ => shiftedSinglePacket (n + j) j u) := by
            unfold shiftedSinglePacket
            have hphase : Continuous (shiftedPacketPhase (n + j) j) := by
              exact continuous_iff_continuousAt.2 fun u =>
                (shiftedPacketPhase_hasDerivAt (n + j) j u).continuousAt
            exact continuous_const.mul hphase
          exact hres.mul hpacket
    simpa [f] using hcont.intervalIntegrable (0 : ℝ) 1
  have hbound_nonneg : 0 ≤ C * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
    positivity
  calc
    ‖∫ u in Ioc (0 : ℝ) 1, f u‖
        = ‖∫ u in (0 : ℝ)..1, f u‖ := by
            rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    _ ≤ ∫ u in (0 : ℝ)..1, ‖f u‖ := by
          simpa using intervalIntegral.norm_integral_le_integral_norm (f := f)
            (by norm_num : (0 : ℝ) ≤ 1)
    _ ≤ ∫ u in (0 : ℝ)..1, C * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
          refine intervalIntegral.integral_mono_on (by norm_num) hInt.norm
            intervalIntegrable_const ?_
          intro u hu
          simpa [f] using hrow u hu
    _ = C * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
          simp [intervalIntegral.integral_const]

/-- Reduction theorem for the eventual fixed-shift row bound.  Any uniform
pointwise estimate for the inner block-coordinate row sum immediately upgrades
to the corresponding bound for the actual unphased complete-block cells. -/
private theorem shiftedCompleteBlockFixedShiftRow_bound_of_rowIntegrand
    {C : ℝ} (hC : 0 ≤ C) {m j : ℕ} (hj : 1 ≤ j)
    (hrow :
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ‖∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockRowIntegrand n j u‖
          ≤ C * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j)) :
    ‖shiftedCompleteBlockFixedShiftRow m j‖
      ≤ C * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
  rw [shiftedCompleteBlockFixedShiftRow_eq_rowIntegral m j hj]
  let f : ℝ → ℂ := fun u =>
    ∑ n ∈ Finset.Ico (j - 1) (m + 1), shiftedCompleteBlockRowIntegrand n j u
  have hInt : IntervalIntegrable f volume (0 : ℝ) 1 := by
    have hcont : Continuous f := by
      unfold f
      exact continuous_finset_sum _ fun n _ => shiftedCompleteBlockRowIntegrand_continuous n j
    simpa [f] using hcont.intervalIntegrable (0 : ℝ) 1
  have hbound_nonneg : 0 ≤ C * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
    positivity
  calc
    ‖∫ u in Ioc (0 : ℝ) 1, f u‖
        = ‖∫ u in (0 : ℝ)..1, f u‖ := by
            rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    _ ≤ ∫ u in (0 : ℝ)..1, ‖f u‖ := by
          simpa using intervalIntegral.norm_integral_le_integral_norm (f := f)
            (by norm_num : (0 : ℝ) ≤ 1)
    _ ≤ ∫ u in (0 : ℝ)..1, C * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
          refine intervalIntegral.integral_mono_on (by norm_num) hInt.norm
            intervalIntegrable_const ?_
          intro u hu
          simpa [f] using hrow u hu
    _ = C * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j) := by
          simp [intervalIntegral.integral_const]

/-- The complete near-band total, expressed as a sum of fixed-shift rows.  Once
the unphased row theorem is proved, the whole near-band follows by a single
harmonic summation in the shift variable. -/
private noncomputable def shiftedCompleteBlockNearBandTotal (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 (N / 2), shiftedCompleteBlockFixedShiftRow (N - j - 1) j

/-- Assembly lemma for the near band: any fixed-shift row bound of size
`O(√(m+j)/j)` automatically gives a global near-band bound
`O(√N log(N+1))`. This is the deterministic bridge from the remaining hard
oscillatory theorem to the final unconditional weighted-sum bound. -/
private theorem shiftedCompleteBlockNearBandTotal_bound_of_fixedShiftRow
    {C : ℝ} (hC : 0 ≤ C)
    (hrow :
      ∀ j : ℕ, 1 ≤ j → ∀ m : ℕ,
        ‖shiftedCompleteBlockFixedShiftRow m j‖
          ≤ C * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j)) :
    ∀ N : ℕ,
      ‖shiftedCompleteBlockNearBandTotal N‖
        ≤ C * (Real.sqrt (N : ℝ) * (1 + Real.log ((N : ℝ) + 1))) := by
  intro N
  by_cases hJ0 : N / 2 = 0
  · unfold shiftedCompleteBlockNearBandTotal
    have hEmpty : Finset.Icc 1 (N / 2) = ∅ := by simp [hJ0]
    rw [hEmpty, Finset.sum_empty]
    have hlog_nonneg : 0 ≤ 1 + Real.log ((N : ℝ) + 1) := by
      have hone : (1 : ℝ) ≤ (N : ℝ) + 1 := by
        have hnat : (1 : ℕ) ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le N)
        exact_mod_cast hnat
      have hlog : 0 ≤ Real.log ((N : ℝ) + 1) := by
        exact Real.log_nonneg hone
      linarith
    have hnonneg : 0 ≤ C * (Real.sqrt (N : ℝ) * (1 + Real.log ((N : ℝ) + 1))) := by
      exact mul_nonneg hC <| mul_nonneg (Real.sqrt_nonneg _) hlog_nonneg
    simpa using hnonneg
  · have hJ1 : 1 ≤ N / 2 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hJ0)
    calc
      ‖shiftedCompleteBlockNearBandTotal N‖
          ≤ ∑ j ∈ Finset.Icc 1 (N / 2), ‖shiftedCompleteBlockFixedShiftRow (N - j - 1) j‖ :=
            norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.Icc 1 (N / 2), C * (Real.sqrt (N : ℝ) / j) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
            have hjN : j ≤ N / 2 := (Finset.mem_Icc.mp hj).2
            have hNat : j + (N - j - 1) + 1 = N := by
              omega
            have hInside : (j : ℝ) + (((N - j - 1 : ℕ) : ℝ) + 1) = N := by
              exact_mod_cast hNat
            simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm, hInside] using
              hrow j hj1 (N - j - 1)
      _ =
          ∑ j ∈ Finset.Icc 1 (N / 2), (C * Real.sqrt (N : ℝ)) * ((1 : ℝ) / j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [div_eq_mul_inv]
            ring
      _ = (C * Real.sqrt (N : ℝ)) * ∑ j ∈ Finset.Icc 1 (N / 2), (1 : ℝ) / j := by
            rw [Finset.mul_sum]
      _ ≤ (C * Real.sqrt (N : ℝ)) * (1 + Real.log (((N / 2 : ℕ) : ℝ))) := by
            refine mul_le_mul_of_nonneg_left (harmonic_Icc_le_one_add_log (N / 2) hJ1) ?_
            exact mul_nonneg hC (Real.sqrt_nonneg _)
      _ ≤ (C * Real.sqrt (N : ℝ)) * (1 + Real.log ((N : ℝ) + 1)) := by
            have hdiv_le : N / 2 ≤ N := Nat.div_le_self N 2
            have hcast_le : (((N / 2 : ℕ) : ℝ)) ≤ (N : ℝ) + 1 := by
              exact_mod_cast (le_trans hdiv_le (Nat.le_succ N))
            have hlog :
                Real.log (((N / 2 : ℕ) : ℝ)) ≤ Real.log ((N : ℝ) + 1) := by
              exact Real.log_le_log (by positivity) hcast_le
            have hcoeff_nonneg : 0 ≤ C * Real.sqrt (N : ℝ) := by
              exact mul_nonneg hC (Real.sqrt_nonneg _)
            nlinarith
      _ = C * (Real.sqrt (N : ℝ) * (1 + Real.log ((N : ℝ) + 1))) := by
            ring

/-- Harmonic assembly also works directly from the exact
`resonantBlockCarrier * shiftedSinglePacket` row-kernel bound.  This is the
canonical merge target for any later direct oscillatory-sum proof on fixed
shifts. -/
private theorem shiftedCompleteBlockNearBandTotal_bound_of_resonantCarrier_singlePacketRow
    {C : ℝ} (hC : 0 ≤ C)
    (hrow :
      ∀ j : ℕ, 1 ≤ j → ∀ m : ℕ,
        ‖shiftedCompleteBlockFixedShiftRow m j‖
          ≤ C * (Real.sqrt (((m + j : ℕ) : ℝ) + 1) / j)) :
    ∀ N : ℕ,
      ‖shiftedCompleteBlockNearBandTotal N‖
        ≤ C * (Real.sqrt (N : ℝ) * (1 + Real.log ((N : ℝ) + 1))) := by
  intro N
  exact shiftedCompleteBlockNearBandTotal_bound_of_fixedShiftRow hC hrow N

private theorem weighted_shifted_completeBlock_real_bound_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ k : ℕ, N0 ≤ k →
      ∀ j : ℕ, 1 ≤ j → j ≤ (k + 1) / 2 →
        |modeWeight (k - j) *
          ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), hardyCos (k - j) t|
          ≤ C * Real.sqrt ((k : ℝ) + 1) / j := by
  obtain ⟨C, hC, N0, hbound⟩ := weighted_shifted_completeBlock_complex_bound_eventually
  refine ⟨C, hC, N0, ?_⟩
  intro k hk j hj hj_half
  have hjk : j ≤ k := by omega
  have hle : hardyStart k ≤ hardyStart (k + 1) := hardyStart_le_succ' k
  have hInt :
      IntegrableOn (fun t : ℝ => HardyCosSmooth.hardyCosExp (k - j) t)
        (Ioc (hardyStart k) (hardyStart (k + 1))) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
    exact (HardyCosSmooth.continuous_hardyCosExp_complex (k - j)).intervalIntegrable _ _
  have hIntCos :
      ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), hardyCos (k - j) t
        = (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
            HardyCosSmooth.hardyCosExp (k - j) t).re := by
    calc
      ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), hardyCos (k - j) t
          = ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
              (HardyCosSmooth.hardyCosExp (k - j) t).re := by
                refine MeasureTheory.integral_congr_ae ?_
                filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
                exact HardyCosSmooth.hardyCos_eq_re_hardyCosExp (k - j) t
      _ = (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
            HardyCosSmooth.hardyCosExp (k - j) t).re := by
              simpa using integral_re hInt
  have hcomplex :=
    hbound k hk j hj hj_half
  calc
    |modeWeight (k - j) *
        ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), hardyCos (k - j) t|
        =
      |((((modeWeight (k - j) : ℝ) : ℂ) *
          ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
            HardyCosSmooth.hardyCosExp (k - j) t).re)| := by
            rw [hIntCos]
            simp
    _ ≤ ‖(((modeWeight (k - j) : ℝ) : ℂ) *
            ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
              HardyCosSmooth.hardyCosExp (k - j) t)‖ := Complex.abs_re_le_norm _
    _ ≤ C * Real.sqrt ((k : ℝ) + 1) / j := hcomplex

/-- Exact primitive for the shared Jacobian times the shifted packet.  This is
the direct integration-by-parts object for the full near-band product. -/
private noncomputable def shiftedJPacketPrimitive (k J : ℕ) (u : ℝ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 J,
    ((-Complex.I) * (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ))) *
      shiftedPacketPhase k j u

private lemma shiftedJPacketPrimitive_hasDerivAt (k J : ℕ) (hJ : J ≤ k) (u : ℝ) :
    HasDerivAt (shiftedJPacketPrimitive k J)
      (((blockJacobian k u : ℂ)) * shiftedJPacket k J u) u := by
  unfold shiftedJPacketPrimitive shiftedJPacket
  have hsum' :
      HasDerivAt
        (fun u : ℝ =>
          ∑ j ∈ Finset.Icc 1 J,
            ((-Complex.I) *
                (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ))) *
              shiftedPacketPhase k j u)
        (∑ j ∈ Finset.Icc 1 J,
          (((blockJacobian k u : ℂ)) *
            ((((shiftedRelativeWeight k j : ℝ) : ℂ)) * shiftedPacketPhase k j u))) u := by
    refine (HasDerivAt.fun_sum (u := Finset.Icc 1 J)
      (x := u)
      (A := fun j u =>
        ((-Complex.I) * (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ))) *
          shiftedPacketPhase k j u)
      (A' := fun j =>
        (((blockJacobian k u : ℂ)) *
          ((((shiftedRelativeWeight k j : ℝ) : ℂ)) * shiftedPacketPhase k j u))) ?_)
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjk : j ≤ k := le_trans (Finset.mem_Icc.mp hj).2 hJ
    have hphase_ne : shiftedRelativePhase k j ≠ 0 := by
      exact ne_of_gt (shiftedRelativePhase_pos k j hj1 hjk)
    have hterm :=
      (shiftedPacketPhase_hasDerivAt k j u).const_mul
        (((-Complex.I) *
          (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ))))
    have hquot :
        (shiftedRelativeWeight k j / shiftedRelativePhase k j) * shiftedPacketOmega k j u
          = shiftedRelativeWeight k j * blockJacobian k u := by
      unfold shiftedPacketOmega
      field_simp [hphase_ne]
    have hquotC :
        ((((shiftedRelativeWeight k j / shiftedRelativePhase k j) * shiftedPacketOmega k j u : ℝ)) : ℂ)
          =
        ((((shiftedRelativeWeight k j * blockJacobian k u : ℝ)) : ℂ)) := by
      exact congrArg (fun x : ℝ => (x : ℂ)) hquot
    have hderiv :
        (-Complex.I * (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ))) *
            (Complex.I * ↑(shiftedPacketOmega k j u) * shiftedPacketPhase k j u)
          =
        (((blockJacobian k u : ℂ)) *
          ((((shiftedRelativeWeight k j : ℝ) : ℂ)) * shiftedPacketPhase k j u)) := by
      have hI : (-Complex.I) * Complex.I = 1 := by norm_num
      calc
        (-Complex.I * (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ))) *
            (Complex.I * ↑(shiftedPacketOmega k j u) * shiftedPacketPhase k j u)
            =
          ((-Complex.I * Complex.I) *
            ((((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ)) *
              (((shiftedPacketOmega k j u : ℝ) : ℂ)) * shiftedPacketPhase k j u)) := by
              ring
        _ = ((((shiftedRelativeWeight k j / shiftedRelativePhase k j) * shiftedPacketOmega k j u : ℝ) : ℂ) *
              shiftedPacketPhase k j u) := by
              rw [hI]
              simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        _ = ((((shiftedRelativeWeight k j * blockJacobian k u : ℝ) : ℂ)) *
              shiftedPacketPhase k j u) := by
              rw [hquotC]
        _ = (((blockJacobian k u : ℂ)) *
              ((((shiftedRelativeWeight k j : ℝ) : ℂ)) * shiftedPacketPhase k j u)) := by
              norm_num
              ring
    exact hterm.congr_deriv hderiv
  simpa [shiftedJPacket, shiftedPacketPhase, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    using hsum'

private lemma shiftedJPacketPrimitive_norm_bound (k J : ℕ)
    (hJ : J ≤ (k + 1) / 2) (u : ℝ) :
    ‖shiftedJPacketPrimitive k J u‖
      ≤ Real.sqrt 2 * (((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1))) := by
  by_cases hJ0 : J = 0
  · subst hJ0
    have hnonneg : 0 ≤ Real.sqrt 2 * (((k : ℝ) + 1) * (1 + Real.log ((0 : ℝ) + 1))) := by
      norm_num [Real.log_one]
      positivity
    have hzero : shiftedJPacketPrimitive k 0 u = 0 := by
      simp [shiftedJPacketPrimitive]
    rw [hzero]
    simpa [Real.log_one] using hnonneg
  · have hJ_pos : 1 ≤ J := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hJ0)
    unfold shiftedJPacketPrimitive
    calc
      ‖∑ j ∈ Finset.Icc 1 J,
          ((-Complex.I) * (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ))) *
            shiftedPacketPhase k j u‖
          ≤
        ∑ j ∈ Finset.Icc 1 J,
          ‖(((-Complex.I) * (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ))) *
            shiftedPacketPhase k j u)‖ := norm_sum_le _ _
      _ ≤
        ∑ j ∈ Finset.Icc 1 J,
          Real.sqrt 2 * (((k : ℝ) + 1) / j) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
            have hjJ : j ≤ J := (Finset.mem_Icc.mp hj).2
            have hjk : j ≤ k := by omega
            have hphase_pos : 0 < shiftedRelativePhase k j := shiftedRelativePhase_pos k j hj1 hjk
            have hweight :
                shiftedRelativeWeight k j ≤ Real.sqrt 2 := by
              exact shiftedRelativeWeight_le_sqrt_two k j (le_trans hjJ hJ)
            have hphase_lower :
                (j : ℝ) / ((k : ℝ) + 1) ≤ shiftedRelativePhase k j :=
              shiftedRelativePhase_lower k j hj1 hjk
            have hcoeff :
                shiftedRelativeWeight k j / shiftedRelativePhase k j
                  ≤ Real.sqrt 2 * (((k : ℝ) + 1) / j) := by
              have hj_pos : 0 < (j : ℝ) := by positivity
              refine (div_le_iff₀ hphase_pos).2 ?_
              have htmp :
                  Real.sqrt 2
                    ≤ Real.sqrt 2 * ((((k : ℝ) + 1) / j) * shiftedRelativePhase k j) := by
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
              ‖(((-Complex.I) * (((shiftedRelativeWeight k j / shiftedRelativePhase k j : ℝ) : ℂ))) *
                  shiftedPacketPhase k j u)‖
                  = shiftedRelativeWeight k j / shiftedRelativePhase k j := by
                      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                        norm_shiftedPacketPhase]
                      simp [div_nonneg, shiftedRelativeWeight_nonneg k j, le_of_lt hphase_pos]
                _ ≤ Real.sqrt 2 * (((k : ℝ) + 1) / j) := hcoeff
      _ = Real.sqrt 2 * ((k : ℝ) + 1) * ∑ j ∈ Finset.Icc 1 J, (1 : ℝ) / j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
      _ ≤ Real.sqrt 2 * ((k : ℝ) + 1) * (1 + Real.log (J : ℝ)) := by
            exact mul_le_mul_of_nonneg_left (harmonic_Icc_le_one_add_log J hJ_pos)
              (by positivity)
      _ ≤ Real.sqrt 2 * (((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1))) := by
            have hlog : Real.log (J : ℝ) ≤ Real.log ((J : ℝ) + 1) := by
              exact Real.log_le_log (by positivity) (by linarith)
            have hcoeff_nonneg : 0 ≤ Real.sqrt 2 * ((k : ℝ) + 1) := by positivity
            nlinarith

private theorem resonantCarrier_shiftedJPacket_product_bound_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ k : ℕ, N0 ≤ k →
      ∀ J : ℕ, J ≤ (k + 1) / 2 →
        ‖∫ u in (0 : ℝ)..1, resonantBlockCarrier k u * shiftedJPacket k J u‖
          ≤ C * Real.sqrt ((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1)) := by
  obtain ⟨Cω, hCω, N0, hderivBound⟩ := weightedResonantBlockMode_deriv_bound_eventually
  let C : ℝ := Real.sqrt 2 * (2 + Cω)
  refine ⟨C, by
    dsimp [C]
    positivity, N0, ?_⟩
  intro k hk J hJ
  have hJk : J ≤ k := by omega
  let f : ℝ → ℂ := weightedResonantBlockMode k
  let G : ℝ → ℂ := shiftedJPacketPrimitive k J
  have hG_deriv :
      ∀ u ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt G (((blockJacobian k u : ℂ)) * shiftedJPacket k J u) u := by
    intro u hu
    exact shiftedJPacketPrimitive_hasDerivAt k J hJk u
  have hf_deriv :
      ∀ u ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f
        (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) u := by
    intro u hu
    exact weightedResonantBlockMode_hasDerivAt k u
  have hf'_int :
      IntervalIntegrable
        (fun u => Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u)
        volume (0 : ℝ) 1 := by
    have hcont : Continuous fun u : ℝ =>
        Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u := by
      exact (continuous_const.mul (Complex.continuous_ofReal.comp (blockOmega_continuous k))).mul
        (weightedResonantBlockMode_continuous k)
    simpa [f] using hcont.intervalIntegrable (0 : ℝ) 1
  have hG'_int :
      IntervalIntegrable (fun u => (((blockJacobian k u : ℂ)) * shiftedJPacket k J u))
        volume (0 : ℝ) 1 := by
    have hcont : Continuous fun u : ℝ =>
        (((blockJacobian k u : ℂ)) * shiftedJPacket k J u) := by
      exact (Complex.continuous_ofReal.comp (blockJacobian_continuous k)).mul <|
        continuous_finset_sum _ fun j _ =>
          continuous_const.mul <|
            Complex.continuous_exp.comp <|
              continuous_const.mul <|
                Complex.continuous_ofReal.comp ((blockCoord_continuous k).mul continuous_const)
    simpa [G, shiftedJPacket] using hcont.intervalIntegrable (0 : ℝ) 1
  have hG_cont : Continuous G := by
    unfold G shiftedJPacketPrimitive
    exact continuous_finset_sum _ fun j _ =>
      continuous_const.mul <|
        Complex.continuous_exp.comp <|
          continuous_const.mul <|
            Complex.continuous_ofReal.comp ((blockCoord_continuous k).mul continuous_const)
  have hibp :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      hf_deriv hG_deriv hf'_int hG'_int
  have hrewrite :
      (fun u => f u * (((blockJacobian k u : ℂ)) * shiftedJPacket k J u))
        = fun u => resonantBlockCarrier k u * shiftedJPacket k J u := by
    funext u
    unfold f weightedResonantBlockMode resonantBlockCarrier blockMode
    simp [mul_assoc, mul_left_comm, mul_comm]
  rw [hrewrite] at hibp
  have hnorm_G0 :
      ‖G 0‖ ≤ Real.sqrt 2 * (((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1))) :=
    shiftedJPacketPrimitive_norm_bound k J hJ 0
  have hnorm_G1 :
      ‖G 1‖ ≤ Real.sqrt 2 * (((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1))) :=
    shiftedJPacketPrimitive_norm_bound k J hJ 1
  have hnorm_f0 : ‖f 0‖ = modeWeight k := weightedResonantBlockMode_norm k 0
  have hnorm_f1 : ‖f 1‖ = modeWeight k := weightedResonantBlockMode_norm k 1
  have hIntBound :
      ‖∫ u in (0 : ℝ)..1,
          (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) * G u‖
        ≤ Cω * modeWeight k *
            (Real.sqrt 2 * (((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1)))) := by
    calc
      ‖∫ u in (0 : ℝ)..1,
          (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) * G u‖
          ≤ ∫ u in (0 : ℝ)..1,
              ‖(Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) * G u‖ := by
                simpa [Real.norm_eq_abs] using
                  (intervalIntegral.norm_integral_le_integral_norm
                    (f := fun u =>
                      (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
                        G u)
                    (by norm_num : (0 : ℝ) ≤ 1))
      _ ≤ ∫ u in (0 : ℝ)..1,
            Cω * modeWeight k *
              (Real.sqrt 2 * (((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1)))) := by
            let B : ℝ :=
              Cω * modeWeight k *
                (Real.sqrt 2 * (((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1))))
            have hcont : Continuous fun u : ℝ =>
                ‖(Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) * G u‖ := by
              exact ((continuous_const.mul
                (Complex.continuous_ofReal.comp (blockOmega_continuous k))).mul
                  (weightedResonantBlockMode_continuous k)).mul hG_cont |>.norm
            have hlower_int :
                IntervalIntegrable
                  (fun u =>
                    ‖(Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) *
                        G u‖)
                  volume (0 : ℝ) 1 := hcont.intervalIntegrable _ _
            have hupper_int :
                IntervalIntegrable (fun _ : ℝ => B) volume (0 : ℝ) 1 := intervalIntegrable_const
            exact intervalIntegral.integral_mono_on
              (a := (0 : ℝ)) (b := 1)
              (f := fun u =>
                ‖(Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) * G u‖)
              (g := fun _ : ℝ => B)
              (hab := by norm_num) (hf := hlower_int) (hg := hupper_int) <|
                by
                  intro u hu
                  have hdu := hderivBound k hk u hu
                  have hGu := shiftedJPacketPrimitive_norm_bound k J hJ u
                  have hbound_nonneg :
                      0 ≤ Real.sqrt 2 * (((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1))) := by
                    have hlog_nonneg : 0 ≤ Real.log ((J : ℝ) + 1) := by
                      exact Real.log_nonneg (by nlinarith : 1 ≤ (J : ℝ) + 1)
                    positivity
                  calc
                    ‖(Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) * G u‖
                        = ‖Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u‖ *
                            ‖G u‖ := by rw [norm_mul]
                    _ ≤ (Cω * modeWeight k) *
                        (Real.sqrt 2 * (((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1)))) := by
                          have hCω_nonneg : 0 ≤ Cω := le_of_lt hCω
                          exact mul_le_mul hdu hGu (norm_nonneg (G u))
                            (mul_nonneg hCω_nonneg (le_of_lt (modeWeight_pos k)))
      _ = Cω * modeWeight k *
            (Real.sqrt 2 * (((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1)))) := by
            simp
  have hmode_sqrt :
      modeWeight k * ((k : ℝ) + 1) = Real.sqrt ((k : ℝ) + 1) := by
    simpa using modeWeight_mul_succ_eq_sqrt k
  calc
    ‖∫ u in (0 : ℝ)..1, resonantBlockCarrier k u * shiftedJPacket k J u‖
        = ‖f 1 * G 1 - f 0 * G 0
            - ∫ u in (0 : ℝ)..1,
                (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) * G u‖ := by
              exact congrArg norm hibp
    _ ≤ ‖f 1 * G 1‖ + ‖f 0 * G 0‖
          + ‖∫ u in (0 : ℝ)..1,
                (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) * G u‖ := by
            have := norm_sub_le (f 1 * G 1 - f 0 * G 0)
              (∫ u in (0 : ℝ)..1,
                (Complex.I * ((blockOmega k u : ℝ) : ℂ) * weightedResonantBlockMode k u) * G u)
            exact le_trans this <| by
              gcongr
              exact norm_sub_le _ _
    _ ≤ modeWeight k *
          (Real.sqrt 2 * (((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1))))
          + modeWeight k *
              (Real.sqrt 2 * (((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1))))
          + Cω * modeWeight k *
              (Real.sqrt 2 * (((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1)))) := by
            have hbd0 :
                ‖f 0 * G 0‖
                  ≤ modeWeight k *
                      (Real.sqrt 2 * (((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1)))) := by
              rw [norm_mul, hnorm_f0]
              exact mul_le_mul_of_nonneg_left hnorm_G0 (le_of_lt (modeWeight_pos k))
            have hbd1 :
                ‖f 1 * G 1‖
                  ≤ modeWeight k *
                      (Real.sqrt 2 * (((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1)))) := by
              rw [norm_mul, hnorm_f1]
              exact mul_le_mul_of_nonneg_left hnorm_G1 (le_of_lt (modeWeight_pos k))
            linarith
    _ = (2 + Cω) * modeWeight k *
          (Real.sqrt 2 * (((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1)))) := by
            ring
    _ = C * Real.sqrt ((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1)) := by
            dsimp [C]
            calc
              (2 + Cω) * modeWeight k * (Real.sqrt 2 * (((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1))))
                  = (Real.sqrt 2 * (2 + Cω)) * (modeWeight k * ((k : ℝ) + 1))
                      * (1 + Real.log ((J : ℝ) + 1)) := by ring
              _ = C * Real.sqrt ((k : ℝ) + 1) * (1 + Real.log ((J : ℝ) + 1)) := by
                    rw [hmode_sqrt]

private theorem small_modes_weighted_sum_bound (N0 : ℕ) :
    ∃ C > 0, ∀ M : ℕ, M ≤ N0 → ∀ T : ℝ, T ≥ 2 →
      ∑ n ∈ Finset.range M, |weightedModeIntegral n T| ≤ C := by
  by_cases hN0 : N0 = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro M hM T hT
    have hM0 : M = 0 := by omega
    simp [hM0]
  obtain ⟨K1, hTail⟩ := global_mode_tail_vdc_bound
  let K : ℕ := max K1 N0
  have hK_large : K1 ≤ K := le_max_left _ _
  have hN0_le_K : N0 ≤ K := le_max_right _ _
  have hN0_pos : 0 < (N0 : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr hN0
  have hratio_gt : 1 < ((K : ℝ) + 1) / (N0 : ℝ) := by
    rw [one_lt_div hN0_pos]
    exact_mod_cast Nat.lt_succ_of_le hN0_le_K
  have hlog_pos : 0 < Real.log (((K : ℝ) + 1) / (N0 : ℝ)) := Real.log_pos hratio_gt
  let D : ℝ := hardyStart K + 6 / Real.log (((K : ℝ) + 1) / (N0 : ℝ))
  let C : ℝ := (N0 : ℝ) * D
  have hD_pos : 0 < D := by
    dsimp [D]
    have hstart_pos : 0 < hardyStart K := by
      rw [hardyStart_formula]
      positivity
    positivity
  refine ⟨C, by
    dsimp [C]
    positivity, ?_⟩
  intro M hM T hT
  have hM_nonneg : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  calc
    ∑ n ∈ Finset.range M, |weightedModeIntegral n T|
        ≤ ∑ _n ∈ Finset.range M, D := by
              refine Finset.sum_le_sum ?_
              intro n hn
              have hnM : n < M := Finset.mem_range.mp hn
              have hnN0 : n < N0 := lt_of_lt_of_le hnM hM
              have hnk : n < K := lt_of_lt_of_le hnN0 hN0_le_K
              have hw_nonneg : 0 ≤ modeWeight n := by
                simpa [modeWeight_eq] using weight_nonneg n
              have hw_le : modeWeight n ≤ 1 := by
                simpa [modeWeight_eq] using weight_le_one n
              have hterm :
                  |∫ t in Ioc (hardyStart n) T, hardyCos n t| ≤ D := by
                by_cases hstartn : hardyStart n ≤ T
                · by_cases hTK : T ≤ hardyStart K
                  · calc
                      |∫ t in Ioc (hardyStart n) T, hardyCos n t|
                          ≤ T - hardyStart n := hardyCos_integral_abs_le_length n hstartn
                      _ ≤ hardyStart K - hardyStart n := by
                            linarith
                      _ ≤ hardyStart K := by
                            have hstart_nonneg : 0 ≤ hardyStart n := by
                              rw [hardyStart_formula]
                              positivity
                            linarith
                      _ ≤ D := by
                            dsimp [D]
                            have htail_nonneg :
                                0 ≤ 6 / Real.log (((K : ℝ) + 1) / (N0 : ℝ)) := by
                              positivity
                            linarith
                  · have hTK' : hardyStart K ≤ T := le_of_not_ge hTK
                    have hsplit :
                        (∫ t in Ioc (hardyStart n) T, hardyCos n t)
                          = (∫ t in Ioc (hardyStart n) (hardyStart K), hardyCos n t)
                              + (∫ t in Ioc (hardyStart K) T, hardyCos n t) := by
                          have hIntA :
                              IntervalIntegrable (hardyCos n) volume
                                (hardyStart n) (hardyStart K) :=
                            HardyCosSmooth.intervalIntegrable_hardyCos n _ _
                          have hIntB :
                              IntervalIntegrable (hardyCos n) volume
                                (hardyStart K) T :=
                            HardyCosSmooth.intervalIntegrable_hardyCos n _ _
                          have hsplit_int :
                              (∫ x in (hardyStart n)..T, hardyCos n x)
                                = (∫ x in (hardyStart n)..(hardyStart K), hardyCos n x)
                                    + (∫ x in (hardyStart K)..T, hardyCos n x) := by
                            simpa [add_comm, add_left_comm, add_assoc] using
                              (intervalIntegral.integral_add_adjacent_intervals hIntA hIntB).symm
                          rw [← intervalIntegral.integral_of_le hstartn,
                            ← intervalIntegral.integral_of_le
                              (hardyStart_mono (Nat.le_of_lt hnk)),
                            ← intervalIntegral.integral_of_le hTK']
                          exact hsplit_int
                    have hratio_ge :
                        ((K : ℝ) + 1) / (N0 : ℝ)
                          ≤ ((K : ℝ) + 1) / ((n : ℝ) + 1) := by
                      have hn1_pos : 0 < (n : ℝ) + 1 := by positivity
                      have hn1_le : (n : ℝ) + 1 ≤ (N0 : ℝ) := by
                        exact_mod_cast Nat.succ_le_of_lt hnN0
                      rw [div_le_div_iff₀ hN0_pos hn1_pos]
                      nlinarith
                    have hlog_ge :
                        Real.log (((K : ℝ) + 1) / (N0 : ℝ))
                          ≤ Real.log (((K : ℝ) + 1) / ((n : ℝ) + 1)) := by
                      exact Real.log_le_log (lt_trans zero_lt_one hratio_gt) hratio_ge
                    have htail_bound :
                        |∫ t in Ioc (hardyStart K) T, hardyCos n t|
                          ≤ 6 / Real.log (((K : ℝ) + 1) / ((n : ℝ) + 1)) := by
                      exact hTail K n hnk hK_large T hTK'
                    have htail_bound' :
                        |∫ t in Ioc (hardyStart K) T, hardyCos n t|
                          ≤ 6 / Real.log (((K : ℝ) + 1) / (N0 : ℝ)) := by
                      have hden_pos : 0 < Real.log (((K : ℝ) + 1) / (N0 : ℝ)) := hlog_pos
                      have hscalar :
                          6 / Real.log (((K : ℝ) + 1) / ((n : ℝ) + 1))
                            ≤ 6 / Real.log (((K : ℝ) + 1) / (N0 : ℝ)) := by
                        exact div_le_div_of_nonneg_left (by positivity) hden_pos hlog_ge
                      exact le_trans htail_bound hscalar
                    calc
                      |∫ t in Ioc (hardyStart n) T, hardyCos n t|
                          ≤ |∫ t in Ioc (hardyStart n) (hardyStart K), hardyCos n t|
                              + |∫ t in Ioc (hardyStart K) T, hardyCos n t| := by
                                rw [hsplit]
                                exact abs_add_le _ _
                      _ ≤ (hardyStart K - hardyStart n)
                            + |∫ t in Ioc (hardyStart K) T, hardyCos n t| := by
                              gcongr
                              exact hardyCos_integral_abs_le_length n
                                (hardyStart_mono (Nat.le_of_lt hnk))
                      _ ≤ (hardyStart K - hardyStart n)
                            + 6 / Real.log (((K : ℝ) + 1) / (N0 : ℝ)) := by
                              gcongr
                      _ ≤ D := by
                            dsimp [D]
                            have hstart_nonneg : 0 ≤ hardyStart n := by
                              rw [hardyStart_formula]
                              positivity
                            linarith
                · have hzero :
                      ∫ t in Ioc (hardyStart n) T, hardyCos n t = 0 := by
                    have hEmpty : Ioc (hardyStart n) T = ∅ := by
                      exact Set.Ioc_eq_empty (not_lt_of_ge (le_of_not_ge hstartn))
                    simp [hEmpty]
                  simpa [hzero] using (le_of_lt hD_pos)
              calc
                |weightedModeIntegral n T|
                    = |modeWeight n * ∫ t in Ioc (hardyStart n) T, hardyCos n t| := by
                        simp [weightedModeIntegral]
                _ = modeWeight n * |∫ t in Ioc (hardyStart n) T, hardyCos n t| := by
                      rw [abs_mul, abs_of_nonneg hw_nonneg]
                _ ≤ modeWeight n * D := by
                      exact mul_le_mul_of_nonneg_left hterm hw_nonneg
                _ ≤ 1 * D := by
                      exact mul_le_mul_of_nonneg_right hw_le (le_of_lt hD_pos)
                _ = D := by ring
    _ = (M : ℝ) * D := by simp [mul_comm]
    _ ≤ (N0 : ℝ) * D := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hM) (le_of_lt hD_pos)
    _ = C := by rfl

private lemma alternating_shifted_sqrt_sum_bound_range (N : ℕ) :
    |∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1)|
      ≤ Real.sqrt N := by
  have hsign :
      (∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1))
        = -(∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * Real.sqrt ((n : ℝ) + 1)) := by
          calc
            (∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1))
                = ∑ n ∈ Finset.range N, -(((-1 : ℝ) ^ n) * Real.sqrt ((n : ℝ) + 1)) := by
                    refine Finset.sum_congr rfl ?_
                    intro n hn
                    rw [pow_succ]
                    ring
            _ = -(∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * Real.sqrt ((n : ℝ) + 1)) := by
                    rw [Finset.sum_neg_distrib]
  rw [hsign, abs_neg]
  exact HardyFirstMomentWiring.alternating_sqrt_sum_bound_range N

private lemma alternating_shifted_sqrt_sum_Ico_bound (m N : ℕ) :
      |∑ n ∈ Finset.Ico m N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1)|
      ≤ 2 * Real.sqrt N := by
  by_cases hmn : m ≤ N
  · rw [Finset.sum_Ico_eq_sub _ hmn]
    rw [sub_eq_add_neg]
    calc
      |(∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1))
          + -(∑ n ∈ Finset.range m, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1))|
          ≤ |(∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1) : ℝ)|
            + |-(∑ n ∈ Finset.range m, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1) : ℝ)| := by
              exact abs_add_le _ _
      _ = |(∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1) : ℝ)|
            + |(∑ n ∈ Finset.range m, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1) : ℝ)| := by
              rw [abs_neg]
      _ ≤ Real.sqrt N + Real.sqrt m := by
            gcongr
            exact alternating_shifted_sqrt_sum_bound_range N
            exact alternating_shifted_sqrt_sum_bound_range m
      _ ≤ 2 * Real.sqrt N := by
            have hm_le : Real.sqrt m ≤ Real.sqrt N := by
              exact Real.sqrt_le_sqrt (by exact_mod_cast hmn)
            linarith
  · have hEmpty : Finset.Ico m N = ∅ := Finset.Ico_eq_empty_of_le (Nat.le_of_not_ge hmn)
    simp [hEmpty]

/-- The resonant block contribution already has the expected affine main term
after weighting by `(n+1)^(-1/2)`, with uniformly bounded error for large
enough modes. This isolates the diagonal piece of the eventual unconditional
stationary-phase decomposition. -/
private theorem weighted_complete_block_resonant_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      |modeWeight n * (∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t)
          - completeModeTarget n| ≤ C := by
  obtain ⟨C, hC, N0, hmain⟩ := hardyCos_firstBlock_anchor_main_term_eventually
  refine ⟨C, hC, N0, ?_⟩
  intro n hn
  have hmain' :
      |(∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t)
          - completeModeTargetUnweighted n| ≤ C := by
    simpa [completeModeTargetUnweighted] using hmain n hn
  have hw_nonneg : 0 ≤ modeWeight n := by
    simpa [modeWeight_eq] using weight_nonneg n
  have hw_le : modeWeight n ≤ 1 := by
    simpa [modeWeight_eq] using weight_le_one n
  have hfactor :
      modeWeight n * (∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t)
        - completeModeTarget n
        =
      modeWeight n *
        ((∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t)
          - completeModeTargetUnweighted n) := by
    rw [← completeModeTarget_eq n]
    ring
  calc
    |modeWeight n * (∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t)
        - completeModeTarget n|
        =
        |modeWeight n *
            ((∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t)
              - completeModeTargetUnweighted n)| := by
          rw [hfactor]
    _ = modeWeight n *
          |(∫ t in Ioc (hardyStart n) (hardyStart (n + 1)), hardyCos n t)
            - completeModeTargetUnweighted n| := by
          rw [abs_mul, abs_of_nonneg hw_nonneg]
    _ ≤ modeWeight n * C := by
          gcongr
    _ ≤ 1 * C := by
          gcongr
    _ = C := by ring

/-- Prefix-block version of `weighted_complete_block_resonant_eventually` for
the final partial block in the Hardy decomposition. -/
private theorem weighted_prefix_block_resonant_eventually :
    ∃ C > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ P ∈ Icc (0 : ℝ) 1,
        |modeWeight n * (∫ t in Ioc (hardyStart n) (blockCoord n P), hardyCos n t)
            - modeWeight n *
                ((((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
                    Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
                  (((((n : ℝ) + 1 : ℝ) : ℂ) *
                        firstBlockQuadraticSlopeUpTo P)
                    + firstBlockQuadraticOffsetUpTo P)).re)| ≤ C := by
  obtain ⟨C, hC, N0, hmain⟩ := hardyCos_firstBlock_anchor_main_term_upto_eventually
  refine ⟨C, hC, N0, ?_⟩
  intro n hn P hP
  have hmain' :
      |(∫ t in Ioc (hardyStart n) (blockCoord n P), hardyCos n t)
          - ((((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
                Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
              (((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlopeUpTo P)
                + firstBlockQuadraticOffsetUpTo P)).re)| ≤ C := by
    simpa using hmain n hn P hP
  have hw_nonneg : 0 ≤ modeWeight n := by
    simpa [modeWeight_eq] using weight_nonneg n
  have hw_le : modeWeight n ≤ 1 := by
    simpa [modeWeight_eq] using weight_le_one n
  have hfactor :
      modeWeight n * (∫ t in Ioc (hardyStart n) (blockCoord n P), hardyCos n t)
        - modeWeight n *
            ((((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
                Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
              (((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlopeUpTo P)
                + firstBlockQuadraticOffsetUpTo P)).re)
        =
      modeWeight n *
        ((∫ t in Ioc (hardyStart n) (blockCoord n P), hardyCos n t)
          - ((((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
                Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
              (((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlopeUpTo P)
                + firstBlockQuadraticOffsetUpTo P)).re)) := by
    ring
  calc
    |modeWeight n * (∫ t in Ioc (hardyStart n) (blockCoord n P), hardyCos n t)
        - modeWeight n *
            ((((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
                Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
              (((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlopeUpTo P)
                + firstBlockQuadraticOffsetUpTo P)).re)|
        =
        |modeWeight n *
            ((∫ t in Ioc (hardyStart n) (blockCoord n P), hardyCos n t)
              - ((((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
                    Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
                  (((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlopeUpTo P)
                    + firstBlockQuadraticOffsetUpTo P)).re))| := by
          rw [hfactor]
    _ = modeWeight n *
          |(∫ t in Ioc (hardyStart n) (blockCoord n P), hardyCos n t)
            - ((((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
                  Aristotle.StationaryPhaseStartValue.hardyStationaryAnchor) *
                (((((n : ℝ) + 1 : ℝ) : ℂ) * firstBlockQuadraticSlopeUpTo P)
                  + firstBlockQuadraticOffsetUpTo P)).re)| := by
          rw [abs_mul, abs_of_nonneg hw_nonneg]
    _ ≤ modeWeight n * C := by
          gcongr
    _ ≤ 1 * C := by
          gcongr
    _ = C := by ring

/-- The diagonal main-term target already sums with `O(√N)` growth, which is
the alternating cancellation expected from the stationary-phase model. -/
private lemma completeModeTarget_sum_bound_range (N : ℕ) :
    |∑ n ∈ Finset.range N, completeModeTarget n|
      ≤ (|completeModeSlope| + 2 * |completeModeOffset|) * Real.sqrt N := by
  have hsplit :
      ∑ n ∈ Finset.range N, completeModeTarget n
        =
      completeModeSlope *
          ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1)
        + completeModeOffset *
          ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * modeWeight n := by
    calc
      ∑ n ∈ Finset.range N, completeModeTarget n
          =
          ∑ n ∈ Finset.range N,
            (completeModeSlope * ((-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1))
              + completeModeOffset * ((-1 : ℝ) ^ (n + 1) * modeWeight n)) := by
                refine Finset.sum_congr rfl ?_
                intro n hn
                unfold completeModeTarget
                ring
      _ =
          completeModeSlope *
              ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1)
            + completeModeOffset *
              ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * modeWeight n := by
                rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hweight_sum :
      |∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * modeWeight n|
        ≤ 2 * Real.sqrt N := by
    have habs_term (n : ℕ) :
        |(-1 : ℝ) ^ (n + 1) * modeWeight n| = modeWeight n := by
      have hw_nonneg : 0 ≤ modeWeight n := by
        simpa [modeWeight_eq] using weight_nonneg n
      rw [abs_mul, abs_of_nonneg hw_nonneg]
      simp
    calc
      |∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * modeWeight n|
          ≤ ∑ n ∈ Finset.range N, |(-1 : ℝ) ^ (n + 1) * modeWeight n| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ n ∈ Finset.range N, modeWeight n := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [habs_term n]
      _ ≤ 2 * Real.sqrt N := by
            calc
              ∑ n ∈ Finset.range N, modeWeight n
                  = ∑ n ∈ Finset.range N, ((n + 1 : ℝ) ^ (-(1 : ℝ) / 2)) := by
                      refine Finset.sum_congr rfl ?_
                      intro n hn
                      rw [modeWeight_eq_neg_half]
              _ ≤ 2 * Real.sqrt N := Aristotle.ErrorTermExpansion.sum_rpow_neg_half_le N
  calc
    |∑ n ∈ Finset.range N, completeModeTarget n|
        =
        |completeModeSlope *
            ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1)
          + completeModeOffset *
            ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * modeWeight n| := by
            rw [hsplit]
    _ ≤
        |completeModeSlope *
            ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1)|
          + |completeModeOffset *
              ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * modeWeight n| := by
            exact abs_add_le _ _
    _ =
        |completeModeSlope| *
            |∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * Real.sqrt ((n : ℝ) + 1)|
          + |completeModeOffset| *
              |∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * modeWeight n| := by
            rw [abs_mul, abs_mul]
    _ ≤ |completeModeSlope| * Real.sqrt N + |completeModeOffset| * (2 * Real.sqrt N) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left
              (alternating_shifted_sqrt_sum_bound_range N) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hweight_sum (abs_nonneg _))
    _ = (|completeModeSlope| + 2 * |completeModeOffset|) * Real.sqrt N := by
          ring

/-! ## Atomic sorry: weighted sum bound -/

/-- **Atomic sorry**: The weighted sum of Hardy cosine integrals is O(N+1).

MATHEMATICAL PROOF SKETCH:
1. Per-mode stationary phase (for n + 1 < hardyN T, ensuring a proper
   integration interval):
   The phase φ_n(t) = θ(t) - t·log(n+1) has stationary point at
   t₀ = hardyStart(n) = 2π(n+1)², giving:
     ∫_{hardyStart(n)}^T cos(φ_n(t)) dt = c₀·(-1)^n·(n+1) + O(1)
   where c₀ involves the Fresnel integral √(2π) and the phase curvature.

2. Weighting by (n+1)^{-1/2}:
   (n+1)^{-1/2} · [c₀·(-1)^n·(n+1) + O(1)] = c₀·(-1)^n·√(n+1) + O(1)

3. Summing over n < N-1 (all but the last mode):
   ∑ = c₀ · ∑(-1)^n√(n+1) + ∑ O(1)
     = c₀ · O(√N) + O(N)     [alternating sum bound from CosPiSqSign]
     = O(N)

4. Last mode n = N-1: the integral is over [hardyStart(N-1), T] which has
   length ≤ hardyStart(N) - hardyStart(N-1) = O(N). With coefficient
   N^{-1/2}, the contribution is O(√N) ⊂ O(N).

5. Total: O(N) = O(N+1). -/
theorem hardy_cos_integral_weighted_sum_bound
    [HardyFirstMomentWiring.HardyCosIntegralSqrtModeBoundHyp] :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∑ n ∈ Finset.range (hardyN T),
          ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
            ∫ t in Ioc (hardyStart n) T,
              hardyCos n t|
        ≤ C * ((hardyN T : ℝ) + 1) := by
  obtain ⟨B, hB, hmode⟩ := HardyFirstMomentWiring.HardyCosIntegralSqrtModeBoundHyp.bound
  refine ⟨B, hB, ?_⟩
  intro T hT
  set N : ℕ := hardyN T
  calc
    |∑ n ∈ Finset.range N,
        ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
          ∫ t in Ioc (hardyStart n) T,
            hardyCos n t|
      ≤ ∑ n ∈ Finset.range N,
          |((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
            ∫ t in Ioc (hardyStart n) T,
              hardyCos n t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range N, B := by
        refine Finset.sum_le_sum fun n _hn => ?_
        have hcoef_nonneg : 0 ≤ (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
        rw [abs_mul, abs_of_nonneg hcoef_nonneg]
        have hI := hmode n T hT
        have hcoef_sqrt_one : (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (n + 1) = 1 := by
          have h_pos : 0 < (n + 1 : ℝ) := by positivity
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add h_pos]
          norm_num
        calc
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
              |∫ t in Ioc (hardyStart n) T,
                hardyCos n t|
            ≤ (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * (B * Real.sqrt (n + 1)) :=
              mul_le_mul_of_nonneg_left hI hcoef_nonneg
          _ = B * ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (n + 1)) := by ring
          _ = B := by rw [hcoef_sqrt_one, mul_one]
    _ = (N : ℝ) * B := by simp [mul_comm]
    _ ≤ B * ((N : ℝ) + 1) := by
        have hN_nonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith

end StationaryPhaseDecomposition

/-! ## Typeclass wiring -/

/-- Wire the sum-level bound into the typeclass instance.
This provides `HardyCosIntegralAlternatingSqrtDecompositionHyp`, which
auto-wires to `MainTermFirstMomentBoundHyp` via HardyFirstMomentWiring. -/
instance [HardyFirstMomentWiring.HardyCosIntegralSqrtModeBoundHyp] :
    HardyFirstMomentWiring.HardyCosIntegralAlternatingSqrtDecompositionHyp :=
  ⟨StationaryPhaseDecomposition.hardy_cos_integral_weighted_sum_bound⟩
