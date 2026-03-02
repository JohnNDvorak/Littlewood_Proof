/-
Pringsheim extension for the π generating function.

Under PiLiHardBound(α, C, σ_sign), proves that
  primeZeta(s) + log(s-1)
extends analytically from {Re > 1} to {Re > α}.

Strategy: Adapt the ψ-case Pringsheim bootstrap (SigmaLtOneFromPringsheimExtension.lean)
to the π generating function piGenFun(t) = C·t^α - σ_sign·(π(⌊t⌋) - li(t)).

Key differences from the ψ case:
  - Center σ₁ = 3 (not 2), since piGenFun ≤ D·t makes ∫ piGenFun·t^{-3} diverge
  - Formula matching uses primeZeta + li-Mellin instead of witnessG
  - The "corrected formula" piCF uses Real.log(zrf(σ)) instead of correctedFormula

SORRY COUNT: 3 (piAnticoeff_summable_at_center, tonelli_pi_hasSum_lt_one,
                  formula_matching_real)

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.PiAtomHardCaseCorrectedCore
import Littlewood.Aristotle.Standalone.PringsheimRealBootstrap
import Littlewood.Aristotle.Standalone.LandauPringsheimRealLine
import Littlewood.Aristotle.Standalone.E1CancellationProof
import Littlewood.Aristotle.Standalone.PrimeZetaExtensionProof
import Littlewood.Aristotle.CorrectionTermAnalyticity
import Littlewood.Aristotle.LandauLogZetaObstruction
import Littlewood.Aristotle.ZetaPoleCancellation

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Aristotle.Standalone.PiPringsheimExtension

open Complex Real Filter Topology MeasureTheory Set
open Aristotle.ZetaPoleCancellation
open Aristotle.CorrectionTermAnalyticity
open Aristotle.LandauLogZetaObstruction
open Aristotle.Standalone.PiAtomHardCaseCorrectedCore
open Aristotle.Standalone.LandauPringsheimRealLine
open Aristotle.Standalone.PrimeZetaExtensionProof
open Aristotle.Standalone.PringsheimRealBootstrap

/-! ## Section 1: piGenFun definition and basic properties

We redefine piGenFun locally to avoid import cycles with
CorrectedPrimeZetaExtensionDirect.lean. -/

/-- The π generating function: R(t) = C·t^α - σ_sign·(π(⌊t⌋₊) - li(t)).
Under PiLiHardBound, R(t) ≥ 0 eventually. -/
def piGenFun (C α σ_sign : ℝ) (t : ℝ) : ℝ :=
  C * t ^ α - σ_sign * ((↑(Nat.primeCounting ⌊t⌋₊) : ℝ) -
    LogarithmicIntegral.logarithmicIntegral t)

/-- piGenFun ≥ 0 eventually, from PiLiHardBound. -/
theorem piGenFun_eventually_nonneg
    (α C σ_sign : ℝ)
    (hbound : PiLiHardBound α C σ_sign) :
    ∀ᶠ t in atTop, 0 ≤ piGenFun C α σ_sign t := by
  filter_upwards [hbound] with t ht
  simp only [piGenFun]
  linarith

/-- piGenFun is measurable. -/
theorem piGenFun_measurable (C α σ_sign : ℝ) :
    Measurable (piGenFun C α σ_sign) := by
  unfold piGenFun
  -- Piece 1: fun t => t ^ α is measurable (MeasurablePow ℝ ℝ via Real.hasMeasurablePow)
  have h_rpow : Measurable (fun t : ℝ => t ^ α) := measurable_id.pow measurable_const
  -- Piece 2: fun t => (↑(Nat.primeCounting ⌊t⌋₊) : ℝ) is measurable (monotone ℝ → ℝ)
  have h_pc : Measurable (fun t : ℝ => (↑(Nat.primeCounting ⌊t⌋₊) : ℝ)) :=
    (show Monotone (fun t : ℝ => (↑(Nat.primeCounting ⌊t⌋₊) : ℝ)) from
      fun _ _ hab => Nat.cast_le.mpr (Nat.monotone_primeCounting (Nat.floor_mono hab))).measurable
  -- Piece 3: li is measurable (continuous on Ioi 2, zero on Iic 2)
  have h_li : Measurable LogarithmicIntegral.logarithmicIntegral := by
    apply measurable_of_restrict_of_restrict_compl (measurableSet_Ioi (a := (2 : ℝ)))
    · exact LogarithmicIntegral.logarithmicIntegral_continuousOn.restrict.measurable
    · have h_eq : (Set.Ioi (2 : ℝ))ᶜ.restrict LogarithmicIntegral.logarithmicIntegral =
          fun _ => (0 : ℝ) := by
        ext ⟨x, hx⟩
        simp only [Set.restrict, Set.mem_compl_iff, Set.mem_Ioi, not_lt] at hx ⊢
        exact LogarithmicIntegral.logarithmicIntegral_of_le_two hx
      rw [h_eq]; exact measurable_const
  exact (measurable_const.mul h_rpow).sub (measurable_const.mul (h_pc.sub h_li))

/-- piGenFun ≤ D·t for t ≥ 1. Uses π(t) ≤ t and |li(t)| ≤ D'·t for t ≥ 1. -/
theorem piGenFun_le_linear (C : ℝ) (hC : 0 < C) (α : ℝ) (hα1 : α ≤ 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 1 ≤ t → |piGenFun C α σ_sign t| ≤ D * t := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  refine ⟨C + 3 + 1 / Real.log 2, by positivity, fun t ht => ?_⟩
  unfold piGenFun
  have ht_pos : 0 < t := by linarith
  -- t^α ≤ t for α ≤ 1, t ≥ 1
  have htα : t ^ α ≤ t := by
    calc t ^ α ≤ t ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht hα1
      _ = t := Real.rpow_one t
  have h_Ctα_le : C * t ^ α ≤ C * t := mul_le_mul_of_nonneg_left htα hC.le
  -- π(⌊t⌋₊) ≤ ⌊t⌋₊ + 1 ≤ t + 1
  have hpc_le : (↑(Nat.primeCounting ⌊t⌋₊) : ℝ) ≤ t + 1 := by
    have h1 : Nat.primeCounting ⌊t⌋₊ ≤ ⌊t⌋₊ + 1 := by
      unfold Nat.primeCounting Nat.primeCounting'
      exact Nat.count_le Nat.Prime
    calc (↑(Nat.primeCounting ⌊t⌋₊) : ℝ)
        ≤ (↑(⌊t⌋₊ + 1) : ℝ) := by exact_mod_cast h1
      _ ≤ t + 1 := by push_cast; linarith [Nat.floor_le ht_pos.le]
  have hpc_nn : (0 : ℝ) ≤ ↑(Nat.primeCounting ⌊t⌋₊) := Nat.cast_nonneg _
  -- li bounds
  have hli_nn : 0 ≤ LogarithmicIntegral.logarithmicIntegral t := by
    by_cases ht2 : 2 ≤ t
    · exact LogarithmicIntegral.logarithmicIntegral_nonneg ht2
    · rw [LogarithmicIntegral.logarithmicIntegral_of_le_two (by linarith)]
  have hli_le : LogarithmicIntegral.logarithmicIntegral t ≤ (1 / Real.log 2) * t := by
    by_cases ht2 : 2 ≤ t
    · calc LogarithmicIntegral.logarithmicIntegral t
          ≤ t / Real.log 2 := LogarithmicIntegral.logarithmicIntegral_lt_bound ht2
        _ = (1 / Real.log 2) * t := by ring
    · rw [LogarithmicIntegral.logarithmicIntegral_of_le_two (by linarith)]
      exact mul_nonneg (div_nonneg one_pos.le hlog2.le) ht_pos.le
  have h_Ctα_nn : 0 ≤ C * t ^ α := mul_nonneg hC.le (rpow_nonneg ht_pos.le _)
  rcases hσ with rfl | rfl
  · -- σ_sign = 1: piGenFun = C*t^α - (π - li)
    rw [abs_le]; constructor
    · -- Lower: -(C+3+1/log2)*t ≤ C*t^α - (π - li)
      -- Since π ≤ t+1 and li ≥ 0: -(π-li) ≥ -(t+1)
      -- So val ≥ 0 - (t+1) = -(t+1) ≥ -(C+3+1/log2)*t for t ≥ 1
      have h_aux : 0 ≤ (C + 2 + 1 / Real.log 2) * (t - 1) :=
        mul_nonneg (by positivity) (by linarith)
      nlinarith
    · -- Upper: C*t^α - (π - li) ≤ (C+3+1/log2)*t
      -- val ≤ C*t + li ≤ C*t + t/log2 ≤ (C+3+1/log2)*t
      nlinarith
  · -- σ_sign = -1: piGenFun = C*t^α + (π - li)
    rw [abs_le]; constructor
    · -- Lower: -(C+3+1/log2)*t ≤ C*t^α + π - li
      -- val ≥ 0 + 0 - t/log2 ≥ -(C+3+1/log2)*t
      nlinarith
    · -- Upper: C*t^α + π - li ≤ (C+3+1/log2)*t
      -- val ≤ C*t + (t+1) ≤ (C+3+1/log2)*t for t ≥ 1
      have h_aux : 0 ≤ (2 + 1 / Real.log 2) * (t - 1) :=
        mul_nonneg (by positivity) (by linarith)
      nlinarith

/-! ## Section 2: Anti-coefficients at center σ₁ = 3

The anti-coefficients B_k = ∫_{T₀}^∞ piGenFun(t) · t^{-(3+1)} · (log t)^k / k! dt
are non-negative (from piGenFun ≥ 0) and summable (from piGenFun ≤ D·t). -/

/-- Anti-coefficients of piGenFun at center 3 are non-negative. -/
theorem piAntiCoeff_nonneg (C α σ_sign : ℝ) (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ piGenFun C α σ_sign t) (k : ℕ) :
    0 ≤ antiCoeff (piGenFun C α σ_sign) T₀ 3 k :=
  antiCoeff_nonneg (piGenFun C α σ_sign) T₀ 3 hT₀ hg_nn k

/-- Summability of anti-coefficients at center 3.
∑ B_k = ∫ piGenFun · t^{-4} · t = ∫ piGenFun · t^{-3} ≤ D · ∫ t^{-2} < ∞. -/
theorem piAnticoeff_summable_at_center
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : PiLiHardBound α C σ_sign)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ piGenFun C α σ_sign t) :
    Summable (fun k => antiCoeff (piGenFun C α σ_sign) T₀ 3 k) := by
  set g := piGenFun C α σ_sign with hg_def
  -- Step 1: g · t^{-3} is integrable on Ioi T₀ (domination by D·t^{-2})
  obtain ⟨D, hD, hg_le⟩ := piGenFun_le_linear C hC α (by linarith : α ≤ 1) σ_sign hσ
  have h_dom_int : IntegrableOn (fun t : ℝ => g t * t ^ (-(3 : ℝ))) (Ioi T₀) := by
    have h_bound : IntegrableOn (fun t : ℝ => D * t ^ (-(2 : ℝ))) (Ioi T₀) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : -(2 : ℝ) < -1) (by linarith)).const_mul D
    apply h_bound.mono'
    · exact ((piGenFun_measurable C α σ_sign).mul (measurable_id.pow_const _)).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht)
      have ht_pos : 0 < t := by linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht_pos _)]
      calc |g t| * t ^ (-(3 : ℝ))
          ≤ D * t * t ^ (-(3 : ℝ)) := by
            exact mul_le_mul_of_nonneg_right (hg_le t ht1) (Real.rpow_nonneg ht_pos.le _)
        _ = D * (t ^ (1 : ℝ) * t ^ (-(3 : ℝ))) := by rw [Real.rpow_one]; ring
        _ = D * t ^ (-(2 : ℝ)) := by
            rw [← Real.rpow_add ht_pos]; ring_nf
  -- Step 2: Each profile at center 3 is integrable (dominated by g · t^{-3})
  -- profile_k(t) = g(t) · t^{-4} · (log t)^k / k!
  -- |profile_k| ≤ g(t) · t^{-4} · t = g(t) · t^{-3} (since (log t)^k/k! ≤ exp(log t) = t)
  -- Step 3: ∑_{k<N} B_k ≤ ∫ g · t^{-3}
  refine summable_of_sum_range_le
    (c := ∫ t in Ioi T₀, g t * t ^ (-(3 : ℝ)))
    (fun k => antiCoeff_nonneg g T₀ 3 hT₀ hg_nn k) ?_
  intro N
  -- Exchange sum and integral
  have hN_eq :
      (∑ k ∈ Finset.range N, antiCoeff g T₀ 3 k)
        = ∫ t in Ioi T₀,
          ∑ k ∈ Finset.range N,
            (g t * t ^ (-(3 + 1 : ℝ)) * ((Real.log t) ^ k / (k.factorial : ℝ))) := by
    simp_rw [antiCoeff]
    symm
    exact MeasureTheory.integral_finset_sum (Finset.range N) (fun k _ => by
      apply h_dom_int.mono'
      · -- AEStronglyMeasurable: piGenFun * rpow * (log^k / k!)
        have h_log_meas : Measurable Real.log :=
          measurable_of_measurable_on_compl_singleton 0 Real.continuous_log.measurable
        exact ((piGenFun_measurable C α σ_sign).mul
          (measurable_id.pow measurable_const)).mul
          ((h_log_meas.pow_const k).div_const
            _) |>.aestronglyMeasurable.restrict
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht)
        have ht_pos : 0 < t := by linarith
        have hlog_nn : 0 ≤ Real.log t := Real.log_nonneg ht1
        have hfac_pos : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
        have hg_nn_t' : 0 ≤ g t := hg_nn t (le_of_lt ht)
        rw [Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg ht_pos.le _),
          abs_of_nonneg (div_nonneg (pow_nonneg hlog_nn _) hfac_pos.le),
          abs_of_nonneg hg_nn_t']
        have hpow_le : (Real.log t) ^ k / (k.factorial : ℝ) ≤ t :=
          (Real.pow_div_factorial_le_exp (Real.log t) hlog_nn k).trans
            (by rw [Real.exp_log ht_pos])
        have hrpow_merge : t ^ (-(3 + 1 : ℝ)) * t = t ^ (-(3 : ℝ)) := by
          calc t ^ (-(3 + 1 : ℝ)) * t = t ^ (-(3 + 1 : ℝ)) * t ^ (1 : ℝ) := by
                rw [Real.rpow_one]
            _ = t ^ ((-(3 + 1 : ℝ)) + 1) := by rw [← Real.rpow_add ht_pos]
            _ = t ^ (-(3 : ℝ)) := by ring_nf
        calc g t * t ^ (-(3 + 1 : ℝ)) * ((Real.log t) ^ k / ↑k.factorial)
            ≤ g t * t ^ (-(3 + 1 : ℝ)) * t := by
              exact mul_le_mul_of_nonneg_left hpow_le
                (mul_nonneg hg_nn_t' (Real.rpow_nonneg ht_pos.le _))
          _ = g t * (t ^ (-(3 + 1 : ℝ)) * t) := by ring
          _ = g t * t ^ (-(3 : ℝ)) := by rw [hrpow_merge])
  -- Bound the finite sum pointwise
  rw [hN_eq]
  apply MeasureTheory.integral_mono_of_nonneg
  · exact (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono (fun t _ =>
      Finset.sum_nonneg (fun k _ => by
        have ht_T₀ : T₀ ≤ t := le_of_lt ‹_›
        have ht_pos : 0 < t := by linarith
        exact mul_nonneg (mul_nonneg (hg_nn t ht_T₀) (Real.rpow_nonneg ht_pos.le _))
          (div_nonneg (pow_nonneg (Real.log_nonneg (by linarith)) _)
            (by exact_mod_cast (Nat.factorial_pos k).le))))
  · exact h_dom_int
  · exact (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono (fun t ht => by
      have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht)
      have ht_pos : 0 < t := by linarith
      have hg_nn_t : 0 ≤ g t := hg_nn t (le_of_lt ht)
      -- ∑_{k<N} g·t^{-4}·(log t)^k/k! = g·t^{-4} · ∑ (log t)^k/k! ≤ g·t^{-4}·t = g·t^{-3}
      calc ∑ k ∈ Finset.range N,
            (g t * t ^ (-(3 + 1 : ℝ)) * ((Real.log t) ^ k / (k.factorial : ℝ)))
          = g t * t ^ (-(3 + 1 : ℝ)) *
            ∑ k ∈ Finset.range N, ((Real.log t) ^ k / (k.factorial : ℝ)) := by
            simp [Finset.mul_sum]
        _ ≤ g t * t ^ (-(3 + 1 : ℝ)) * t := by
            apply mul_le_mul_of_nonneg_left
            · exact (Real.sum_le_exp_of_nonneg (Real.log_nonneg ht1) N).trans
                (by rw [Real.exp_log ht_pos])
            · exact mul_nonneg hg_nn_t (Real.rpow_nonneg ht_pos.le _)
        _ = g t * t ^ (-(3 : ℝ)) := by
            rw [mul_assoc]
            congr 1
            calc t ^ (-(3 + 1 : ℝ)) * t = t ^ (-(3 + 1 : ℝ)) * t ^ (1 : ℝ) := by
                  rw [Real.rpow_one]
              _ = t ^ (-(3 + 1 : ℝ) + 1) := by rw [← Real.rpow_add ht_pos]
              _ = t ^ (-(3 : ℝ)) := by ring_nf)

/-! ## Section 3: Tonelli exchange at center 3

For w ∈ [0, 1): HasSum(B_k · w^k, ∫_{T₀}^∞ piGenFun(t) · t^{w-4} dt).
Analogous to tonelli_hasSum_lt_one in SigmaLtOneFromPringsheimExtension.lean. -/

theorem tonelli_pi_hasSum_lt_one
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : PiLiHardBound α C σ_sign)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ piGenFun C α σ_sign t)
    (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1) :
    HasSum (fun k => antiCoeff (piGenFun C α σ_sign) T₀ 3 k * w ^ k)
      (∫ t in Ioi T₀, piGenFun C α σ_sign t * t ^ (w - 4)) := by
  set g := piGenFun C α σ_sign with hg_def
  -- Profile at center 3: g(t) · t^{-(3+1)} · (log t)^k / k!
  set profile := fun (k : ℕ) (t : ℝ) =>
    g t * t ^ (-(3 + 1 : ℝ)) * ((Real.log t) ^ k / (k.factorial : ℝ)) with hprofile_def
  -- Log measurability (used below)
  have h_log_meas : Measurable Real.log :=
    measurable_of_measurable_on_compl_singleton 0 Real.continuous_log.measurable
  -- Dominator: g · t^{-3} is integrable on Ioi T₀
  obtain ⟨D, hD, hg_le⟩ := piGenFun_le_linear C hC α (by linarith : α ≤ 1) σ_sign hσ
  have h_dom_int : IntegrableOn (fun t : ℝ => g t * t ^ (-(3 : ℝ))) (Ioi T₀) := by
    apply (integrableOn_Ioi_rpow_of_lt (by norm_num : -(2 : ℝ) < -1)
      (by linarith)).const_mul D |>.mono'
    · exact ((piGenFun_measurable C α σ_sign).mul
        (measurable_id.pow measurable_const)).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht)
      have ht_pos : 0 < t := by linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (rpow_pos_of_pos ht_pos _)]
      calc |g t| * t ^ (-(3 : ℝ)) ≤ D * t * t ^ (-(3 : ℝ)) :=
            mul_le_mul_of_nonneg_right (hg_le t ht1) (rpow_nonneg ht_pos.le _)
        _ = D * (t ^ (1 : ℝ) * t ^ (-(3 : ℝ))) := by rw [rpow_one]; ring
        _ = D * t ^ (-(2 : ℝ)) := by rw [← rpow_add ht_pos]; ring_nf
  -- antiCoeff g T₀ 3 k = ∫ profile k (definitional)
  have hB_eq : ∀ k, antiCoeff g T₀ 3 k = ∫ t in Ioi T₀, profile k t := fun _ => rfl
  -- Profile nonneg on tail
  have hprofile_nn : ∀ k t, t ∈ Ioi T₀ → 0 ≤ profile k t := by
    intro k t ht
    simp only [Set.mem_Ioi] at ht
    have ht1 : 1 ≤ t := by linarith
    exact mul_nonneg (mul_nonneg (hg_nn t (le_of_lt ht))
      (rpow_nonneg (by linarith) _))
      (div_nonneg (pow_nonneg (Real.log_nonneg ht1) _) (by positivity))
  -- Profile AEStronglyMeasurable on Ioi T₀
  have hprofile_aesm : ∀ k, AEStronglyMeasurable (fun t => profile k t)
      (Measure.restrict volume (Ioi T₀)) := fun k =>
    ((piGenFun_measurable C α σ_sign).mul (measurable_id.pow measurable_const)).mul
      ((h_log_meas.pow_const k).div_const _) |>.aestronglyMeasurable.restrict
  -- Each profile k is integrable on Ioi T₀ (dominated by g · t^{-3})
  have hprofile_int : ∀ k, IntegrableOn (fun t => profile k t) (Ioi T₀) := by
    intro k; apply h_dom_int.mono' (hprofile_aesm k)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht)
    have ht_pos : 0 < t := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (hprofile_nn k t ht)]
    have hlog_nn : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hpow_le : (Real.log t) ^ k / (k.factorial : ℝ) ≤ t := by
      have h1 : (Real.log t) ^ k / (k.factorial : ℝ) ≤
          ∑ j ∈ Finset.range (k + 1), (Real.log t) ^ j / (j.factorial : ℝ) :=
        Finset.single_le_sum (f := fun j => (Real.log t) ^ j / (j.factorial : ℝ))
          (fun j _ => div_nonneg (pow_nonneg hlog_nn j) (Nat.cast_nonneg _))
          (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr le_rfl))
      exact h1.trans ((Real.sum_le_exp_of_nonneg hlog_nn (k + 1)).trans
        (by rw [Real.exp_log ht_pos]))
    calc profile k t ≤ g t * t ^ (-(3 + 1 : ℝ)) * t :=
          mul_le_mul_of_nonneg_left hpow_le
            (mul_nonneg (hg_nn t (le_of_lt ht)) (rpow_nonneg ht_pos.le _))
      _ = g t * (t ^ (-(3 + 1 : ℝ)) * t ^ (1 : ℝ)) := by rw [rpow_one]; ring
      _ = g t * t ^ (-(3 : ℝ)) := by rw [← rpow_add ht_pos]; ring_nf
  -- F_k = profile_k · w^k is integrable
  have hF_int : ∀ k, Integrable (fun t => profile k t * w ^ k)
      (Measure.restrict volume (Ioi T₀)) := fun k => (hprofile_int k).mul_const _
  -- Summable(∫ ‖F_k‖) dominated by Summable(B_k)
  have hB_sum : Summable (fun k => antiCoeff g T₀ 3 k) :=
    piAnticoeff_summable_at_center C hC α hα hα1 σ_sign hσ hbound T₀ hT₀ hg_nn
  have habs_w : |w| ≤ 1 := by rw [abs_of_nonneg hw]; exact le_of_lt hw1
  have hF_norm_sum : Summable (fun k => ∫ t in Ioi T₀, ‖profile k t * w ^ k‖) :=
    .of_nonneg_of_le
      (fun k => integral_nonneg_of_ae ((ae_restrict_mem measurableSet_Ioi).mono
        (fun _ _ => norm_nonneg _)))
      (fun k => by
        rw [hB_eq]
        apply integral_mono_of_nonneg
        · exact (ae_restrict_mem measurableSet_Ioi).mono (fun _ _ => norm_nonneg _)
        · exact hprofile_int k
        · exact (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => by
            simp only [norm_mul, Real.norm_eq_abs]
            rw [abs_of_nonneg (hprofile_nn k t ht), abs_pow, abs_of_nonneg hw]
            calc profile k t * w ^ k ≤ profile k t * 1 :=
                  mul_le_mul_of_nonneg_left (pow_le_one₀ hw (le_of_lt hw1))
                    (hprofile_nn k t ht)
              _ = profile k t := mul_one _))
      hB_sum
  -- Tonelli exchange
  have hmain := hasSum_integral_of_summable_integral_norm hF_int hF_norm_sum
  -- LHS: ∫ F_k = B_k · w^k
  simp_rw [show ∀ k, ∫ t in Ioi T₀, profile k t * w ^ k =
    antiCoeff g T₀ 3 k * w ^ k from fun k => by rw [integral_mul_const, hB_eq]] at hmain
  -- RHS: ∑' profile_k(t) · w^k = g(t) · t^{w-4} (exp series identity)
  have h_rhs : (∫ t in Ioi T₀, ∑' k, profile k t * w ^ k) =
      ∫ t in Ioi T₀, g t * t ^ (w - 4) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have htT₀ : T₀ < t := ht
    have ht_pos : 0 < t := by linarith
    show ∑' k, profile k t * w ^ k = g t * t ^ (w - 4)
    -- Step A: factor out g(t) * t^{-(3+1)} from the tsum
    have h_factor : ∑' k, profile k t * w ^ k =
        g t * t ^ (-(3 + 1 : ℝ)) *
        ∑' k : ℕ, ((w * Real.log t) ^ k / (k.factorial : ℝ)) := by
      rw [← tsum_mul_left]
      congr 1; ext k
      simp only [hprofile_def, mul_pow]; ring
    -- Step B: the tsum is exp(w * log t)
    have h_exp_series : ∑' k : ℕ, ((w * Real.log t) ^ k / (k.factorial : ℝ)) =
        Real.exp (w * Real.log t) := by
      simpa [Real.exp_eq_exp_ℝ] using
        (congrArg (fun f : ℝ → ℝ => f (w * Real.log t))
          (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ))).symm
    -- Step C: exp(w * log t) = t^w
    have h_rpow : Real.exp (w * Real.log t) = t ^ w := by
      rw [rpow_def_of_pos ht_pos]; ring_nf
    -- Step D: g * t^{-(3+1)} * t^w = g * t^{w-4}
    have h_merge : g t * t ^ (-(3 + 1 : ℝ)) * t ^ w = g t * t ^ (w - 4) := by
      rw [mul_assoc, ← rpow_add ht_pos]; ring_nf
    rw [h_factor, h_exp_series, h_rpow, h_merge]
  rw [h_rhs] at hmain; exact hmain

/-! ## Section 4: piCorrectedFormula and real-analyticity

The "corrected formula" for π at center 3 is:
  piCF(σ) = C·σ/(σ-α) + σ_sign · [Re(correctionTerm(↑σ)) + Re(K_ext(↑σ)) - Real.log(zrf(σ))]

where K_ext is the entire function from li_mellin_plus_log_extends.

piCF is real-analytic on (α, ∞) because each piece is. -/

/-- The π corrected formula function on the real axis.
For real σ > 1: piCF(σ) = (3-σ) · ∫_{Ioi 1} piGenFun · t^{σ-4} dt
(via formula matching). -/
def piCF (K_ext : ℂ → ℂ) (C α σ_sign : ℝ) (σ : ℝ) : ℝ :=
  C * σ / (σ - α) + σ_sign * ((correctionTerm (↑σ)).re +
    (K_ext (↑σ)).re - Real.log (Complex.normSq (zrf (↑σ))) / 2)

/-- piCF is real-analytic at any real σ₀ > α. -/
theorem piCF_analyticAt_real (K_ext : ℂ → ℂ)
    (hK : Differentiable ℂ K_ext)
    (α : ℝ) (hα : 1 / 2 < α) (C σ_sign : ℝ)
    (σ₀ : ℝ) (hσ₀ : α < σ₀) :
    AnalyticAt ℝ (piCF K_ext C α σ_sign) σ₀ := by
  unfold piCF
  -- C·σ/(σ-α) is analytic at σ₀ ≠ α
  have h_frac : AnalyticAt ℝ (fun σ : ℝ => C * σ / (σ - α)) σ₀ := by
    exact ((analyticAt_const.mul analyticAt_id).div
      (analyticAt_id.sub analyticAt_const) (by linarith))
  -- correctionTerm is ℂ-analytic on {Re > 1/2} ⊃ {Re > α}
  have h_ct : AnalyticAt ℝ (fun σ : ℝ => (correctionTerm (↑σ)).re) σ₀ := by
    have h := correctionTerm_analyticOnNhd α hα
    exact (h (↑σ₀) (by simp; linarith)).re_ofReal
  -- K_ext is entire, so K_ext(↑σ).re is real-analytic
  have h_K : AnalyticAt ℝ (fun σ : ℝ => (K_ext (↑σ)).re) σ₀ := by
    exact (hK.analyticAt (↑σ₀)).re_ofReal
  -- Real.log(normSq(zrf(↑σ))) / 2 is real-analytic at σ₀ > 0
  -- since zrf(↑σ₀) ≠ 0 for real σ₀ > 0
  have h_log : AnalyticAt ℝ (fun σ : ℝ => Real.log (Complex.normSq (zrf (↑σ))) / 2) σ₀ := by
    have hσ₀_pos : 0 < σ₀ := by linarith
    have h_ne := zrf_ne_zero_of_real_pos σ₀ hσ₀_pos
    have h_ns_pos : 0 < Complex.normSq (zrf (↑σ₀)) :=
      Complex.normSq_pos.mpr h_ne
    -- zrf is entire → zrf(↑σ).re, zrf(↑σ).im are ℝ-analytic
    have h_zrf_anal := zrf_analyticAt (↑σ₀)
    have h_re : AnalyticAt ℝ (fun σ : ℝ => (zrf (↑σ)).re) σ₀ := h_zrf_anal.re_ofReal
    have h_im : AnalyticAt ℝ (fun σ : ℝ => (zrf (↑σ)).im) σ₀ := h_zrf_anal.im_ofReal
    -- normSq z = z.re * z.re + z.im * z.im
    have h_nsq : AnalyticAt ℝ (fun σ : ℝ => Complex.normSq (zrf (↑σ))) σ₀ := by
      show AnalyticAt ℝ (fun σ : ℝ => (zrf (↑σ)).re * (zrf (↑σ)).re +
        (zrf (↑σ)).im * (zrf (↑σ)).im) σ₀
      exact (h_re.mul h_re).add (h_im.mul h_im)
    exact (h_nsq.log h_ns_pos).div analyticAt_const (by norm_num : (2 : ℝ) ≠ 0)
  exact h_frac.add (analyticAt_const.mul ((h_ct.add h_K).sub h_log))

/-! ## Section 4b: Core integral identities

The real version relates the Lebesgue integral to piCF.
The complex version relates the complex Dirichlet integral to primeZeta + log(s-1).

Both encode the same mathematical content:
  Mellin of t^α, Abel summation for π, IBP for li (with li(2)=0), H_zeta_log_eq_add.

The real version serves formula_matching_real (for Pringsheim bootstrap).
The complex version serves the Q verification. -/

/-! ### Integrability lemmas for integral identity proofs -/

/-- t^α * t^{-(σ+1)} is integrable on Ioi 1 when σ > α (real version). -/
private theorem integrableOn_rpow_rpow (α σ : ℝ) (hσ : α < σ) :
    IntegrableOn (fun t => t ^ α * t ^ (-(σ + 1))) (Ioi (1 : ℝ)) :=
  (integrableOn_Ioi_rpow_of_lt (show α - σ - 1 < -1 by linarith) one_pos).congr_fun
    (fun t ht => by
      rw [← rpow_add (show (0:ℝ) < t by linarith [show (1:ℝ) < t from ht])]; congr 1; ring)
    measurableSet_Ioi

/-- π(⌊t⌋₊) * t^{-(σ+1)} is integrable on Ioi 1 when σ > 1 (real version). -/
private theorem integrableOn_primeCounting_rpow (σ : ℝ) (hσ : 1 < σ) :
    IntegrableOn (fun t => (↑(Nat.primeCounting ⌊t⌋₊) : ℝ) * t ^ (-(σ + 1)))
      (Ioi (1 : ℝ)) := by
  have h_pc_meas : Measurable (fun t : ℝ => (↑(Nat.primeCounting ⌊t⌋₊) : ℝ)) :=
    (show Monotone (fun t : ℝ => (↑(Nat.primeCounting ⌊t⌋₊) : ℝ)) from
      fun _ _ hab => Nat.cast_le.mpr (Nat.monotone_primeCounting (Nat.floor_mono hab))).measurable
  apply (integrableOn_Ioi_rpow_of_lt (show -(σ : ℝ) < -1 by linarith) one_pos).const_mul 2 |>.mono'
  · exact (h_pc_meas.mul (measurable_id.pow measurable_const)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [mem_Ioi] at ht
    have ht_pos : 0 < t := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rpow_nonneg ht_pos.le _)]
    have hpc_le : |(↑(Nat.primeCounting ⌊t⌋₊) : ℝ)| ≤ 2 * t := by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      have : Nat.primeCounting ⌊t⌋₊ ≤ ⌊t⌋₊ + 1 := by
        unfold Nat.primeCounting Nat.primeCounting'; exact Nat.count_le _
      calc (↑(Nat.primeCounting ⌊t⌋₊) : ℝ) ≤ ↑(⌊t⌋₊ + 1) := by exact_mod_cast this
        _ ≤ t + 1 := by push_cast; linarith [Nat.floor_le ht_pos.le]
        _ ≤ 2 * t := by linarith
    calc |↑(Nat.primeCounting ⌊t⌋₊)| * t ^ (-(σ + 1))
        ≤ 2 * t * t ^ (-(σ + 1)) :=
          mul_le_mul_of_nonneg_right hpc_le (rpow_nonneg ht_pos.le _)
      _ = 2 * (t ^ (1:ℝ) * t ^ (-(σ + 1))) := by rw [rpow_one]; ring
      _ = 2 * t ^ (-σ) := by rw [← rpow_add ht_pos]; ring_nf

/-- li(t) * t^{-(σ+1)} is integrable on Ioi 1 when σ > 1 (real version). -/
private theorem integrableOn_li_rpow (σ : ℝ) (hσ : 1 < σ) :
    IntegrableOn (fun t => LogarithmicIntegral.logarithmicIntegral t * t ^ (-(σ + 1)))
      (Ioi (1 : ℝ)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have h_li_meas : Measurable LogarithmicIntegral.logarithmicIntegral := by
    apply measurable_of_restrict_of_restrict_compl (measurableSet_Ioi (a := (2 : ℝ)))
    · exact LogarithmicIntegral.logarithmicIntegral_continuousOn.restrict.measurable
    · have h_eq : (Set.Ioi (2 : ℝ))ᶜ.restrict LogarithmicIntegral.logarithmicIntegral =
            fun _ => (0 : ℝ) := by
        ext ⟨x, hx⟩; simp only [Set.restrict, Set.mem_compl_iff, Set.mem_Ioi, not_lt] at hx ⊢
        exact LogarithmicIntegral.logarithmicIntegral_of_le_two hx
      rw [h_eq]; exact measurable_const
  apply (integrableOn_Ioi_rpow_of_lt (show -(σ : ℝ) < -1 by linarith) one_pos).const_mul
    (1 / Real.log 2) |>.mono'
  · exact (h_li_meas.mul (measurable_id.pow measurable_const)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [mem_Ioi] at ht
    have ht_pos : 0 < t := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rpow_nonneg ht_pos.le _)]
    have hli_le : |LogarithmicIntegral.logarithmicIntegral t| ≤ (1 / Real.log 2) * t := by
      by_cases ht2 : 2 ≤ t
      · rw [abs_of_nonneg (LogarithmicIntegral.logarithmicIntegral_nonneg ht2)]
        calc LogarithmicIntegral.logarithmicIntegral t
            ≤ t / Real.log 2 := LogarithmicIntegral.logarithmicIntegral_lt_bound ht2
          _ = (1 / Real.log 2) * t := by ring
      · rw [LogarithmicIntegral.logarithmicIntegral_of_le_two (by linarith), abs_zero]
        exact mul_nonneg (by positivity) ht_pos.le
    calc |LogarithmicIntegral.logarithmicIntegral t| * t ^ (-(σ + 1))
        ≤ (1 / Real.log 2) * t * t ^ (-(σ + 1)) :=
          mul_le_mul_of_nonneg_right hli_le (rpow_nonneg ht_pos.le _)
      _ = (1 / Real.log 2) * (t ^ (1:ℝ) * t ^ (-(σ + 1))) := by rw [rpow_one]; ring
      _ = (1 / Real.log 2) * t ^ (-σ) := by rw [← rpow_add ht_pos]; ring_nf

/-- (t/log t) * t^{-(σ+1)} is integrable on Ioi 2 when σ > 1 (real version). -/
private theorem integrableOn_tDivLog_rpow (σ : ℝ) (hσ : 1 < σ) :
    IntegrableOn (fun t => (t / Real.log t) * t ^ (-(σ + 1)))
      (Ioi (2 : ℝ)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  -- Bound: t/log t ≤ t/log 2 for t > 2. Dominate by (1/log 2) * t^{-σ}.
  apply (integrableOn_Ioi_rpow_of_lt (show -(σ : ℝ) < -1 by linarith)
    (show (0:ℝ) < 2 by norm_num)).const_mul (1 / Real.log 2) |>.mono'
  · exact (((measurable_id.div (Real.measurable_log.comp measurable_id)).mul
      (measurable_id.pow measurable_const))).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [mem_Ioi] at ht
    have ht_pos : 0 < t := by linarith
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rpow_nonneg ht_pos.le _)]
    have h_tdl_le : |t / Real.log t| ≤ (1 / Real.log 2) * t := by
      rw [abs_of_nonneg (div_nonneg ht_pos.le hlogt.le),
        show (1 / Real.log 2) * t = t / Real.log 2 from by ring]
      exact div_le_div_of_nonneg_left ht_pos.le hlog2
        (Real.log_le_log (by norm_num : (0:ℝ) < 2) (by linarith))
    calc |t / Real.log t| * t ^ (-(σ + 1))
        ≤ (1 / Real.log 2) * t * t ^ (-(σ + 1)) :=
          mul_le_mul_of_nonneg_right h_tdl_le (rpow_nonneg ht_pos.le _)
      _ = (1 / Real.log 2) * (t ^ (1:ℝ) * t ^ (-(σ + 1))) := by rw [rpow_one]; ring
      _ = (1 / Real.log 2) * t ^ (-σ) := by rw [← rpow_add ht_pos]; ring_nf

/-! ### Real Mellin evaluation -/

/-- ∫_{Ioi 1} t^α * t^{-(σ+1)} = 1/(σ-α) for real σ > α. -/
private theorem mellin_rpow_alpha_real (α σ : ℝ) (hσ : α < σ) :
    ∫ t in Ioi (1 : ℝ), t ^ α * t ^ (-(σ + 1)) = 1 / (σ - α) := by
  have h_eq : ∀ t ∈ Ioi (1 : ℝ),
      t ^ α * t ^ (-(σ + 1)) = t ^ (α - σ - 1) := by
    intro t ht
    rw [← rpow_add (show (0:ℝ) < t by linarith [show (1:ℝ) < t from ht])]; congr 1; ring
  rw [setIntegral_congr_fun measurableSet_Ioi h_eq]
  rw [integral_Ioi_rpow_of_lt (show α - σ - 1 < -1 by linarith) one_pos]
  simp only [one_rpow]
  rw [show α - σ - 1 + 1 = α - σ from by ring,
    div_eq_div_iff (show α - σ ≠ 0 from by linarith) (show σ - α ≠ 0 from by linarith)]
  ring

/-! ### Real integral splitting -/

/-- The piGenFun integral splits into three sub-integrals for σ > 1, σ > α. -/
private theorem piGenFun_integral_split (C α σ_sign σ : ℝ) (hσ : 1 < σ) (hα : α < σ) :
    ∫ t in Ioi (1 : ℝ), piGenFun C α σ_sign t * t ^ (-(σ + 1)) =
      C * (∫ t in Ioi 1, t ^ α * t ^ (-(σ + 1))) -
      σ_sign * (∫ t in Ioi 1, (↑(Nat.primeCounting ⌊t⌋₊) : ℝ) * t ^ (-(σ + 1))) +
      σ_sign * (∫ t in Ioi 1, LogarithmicIntegral.logarithmicIntegral t * t ^ (-(σ + 1))) := by
  have h1 := integrableOn_rpow_rpow α σ hα
  have h2 := integrableOn_primeCounting_rpow σ hσ
  have h3 := integrableOn_li_rpow σ hσ
  have h_eq : ∀ t ∈ Ioi (1 : ℝ),
      piGenFun C α σ_sign t * t ^ (-(σ + 1)) =
      (C * (t ^ α * t ^ (-(σ + 1))) +
       σ_sign * (LogarithmicIntegral.logarithmicIntegral t * t ^ (-(σ + 1)))) -
      σ_sign * ((↑(Nat.primeCounting ⌊t⌋₊) : ℝ) * t ^ (-(σ + 1))) := by
    intro t _; unfold piGenFun; ring
  rw [setIntegral_congr_fun measurableSet_Ioi h_eq]
  have h_ab : IntegrableOn (fun (x : ℝ) =>
      C * (x ^ α * x ^ (-(σ + 1))) +
      σ_sign * (LogarithmicIntegral.logarithmicIntegral x * x ^ (-(σ + 1)))) (Ioi (1 : ℝ)) :=
    (h1.const_mul _).add (h3.const_mul _)
  have h_c : IntegrableOn (fun (x : ℝ) =>
      σ_sign * ((↑(Nat.primeCounting ⌊x⌋₊) : ℝ) * x ^ (-(σ + 1)))) (Ioi (1 : ℝ)) :=
    h2.const_mul _
  exact (integral_sub h_ab h_c).trans (by
    have h_a : IntegrableOn (fun (x : ℝ) =>
        C * (x ^ α * x ^ (-(σ + 1)))) (Ioi (1 : ℝ)) := h1.const_mul _
    have h_b : IntegrableOn (fun (x : ℝ) =>
        σ_sign * (LogarithmicIntegral.logarithmicIntegral x * x ^ (-(σ + 1)))) (Ioi (1 : ℝ)) :=
      h3.const_mul _
    rw [integral_add h_a h_b, integral_const_mul, integral_const_mul, integral_const_mul]; ring)

/-! ### li integral IBP -/

/-- σ * ∫_{Ioi 1} li(t) * t^{-(σ+1)} = ∫_{Ioi 2} (t/log t) * t^{-(σ+1)} for σ > 2.
Proof via FTC: F(t) = li(t) * t^{-σ} has F(2) = 0 and F → 0. -/
private theorem li_integral_ibp (σ : ℝ) (hσ : 2 < σ) :
    σ * ∫ t in Ioi (1 : ℝ), LogarithmicIntegral.logarithmicIntegral t * t ^ (-(σ + 1)) =
    ∫ t in Ioi (2 : ℝ), (t / Real.log t) * t ^ (-(σ + 1)) := by
  have hσ1 : 1 < σ := by linarith
  have hσ_pos : 0 < σ := by linarith
  open LogarithmicIntegral in
  -- Step 1: li = 0 on (1,2], so ∫_{Ioi 1} = ∫_{Ioi 2}
  have h_vanish : ∫ t in Ioi (1 : ℝ), logarithmicIntegral t * t ^ (-(σ + 1)) =
      ∫ t in Ioi (2 : ℝ), logarithmicIntegral t * t ^ (-(σ + 1)) := by
    have h_eq : ∀ t ∈ Ioi (1 : ℝ),
        logarithmicIntegral t * t ^ (-(σ + 1)) =
        (Set.Ioi 2).indicator (fun t => logarithmicIntegral t * t ^ (-(σ + 1))) t := by
      intro t ht; simp only [Set.indicator]
      split_ifs with h
      · rfl
      · rw [logarithmicIntegral_of_le_two (not_lt.mp h), zero_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi h_eq,
      setIntegral_indicator measurableSet_Ioi,
      Set.Ioi_inter_Ioi, sup_eq_right.mpr (show (1:ℝ) ≤ 2 by norm_num)]
  rw [h_vanish]
  -- Step 2: FTC with F(t) = li(t) * t^{-σ}
  -- F'(t) via product rule = (1/log t) * t^{-σ} + li(t) * (-σ * t^{-σ-1})
  --                        = (t/log t) * t^{-(σ+1)} - σ * li(t) * t^{-(σ+1)}
  -- F(2) = 0, F(∞) = 0, so ∫ F' = 0, giving the identity.
  set F : ℝ → ℝ := fun t => logarithmicIntegral t * t ^ (-σ) with hF_def
  set F' : ℝ → ℝ := fun t =>
    (1 / Real.log t) * t ^ (-σ) + logarithmicIntegral t * ((-σ) * t ^ (-σ - 1)) with hF'_def
  -- F(2) = 0
  have hF2 : F 2 = 0 := by simp [F, logarithmicIntegral_two, zero_mul]
  -- HasDerivAt F F'(t) t for t > 2
  have hF_deriv : ∀ t ∈ Ioi (2 : ℝ), HasDerivAt F (F' t) t := by
    intro t ht; simp only [F, F']
    exact (logarithmicIntegral_hasDerivAt ht).mul
      (hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_trans (by norm_num : (0:ℝ) < 2) ht))))
  -- ContinuousWithinAt F (Ici 2) 2: use Metric.tendsto definition
  have hF_cont : ContinuousWithinAt F (Ici 2) 2 := by
    rw [ContinuousWithinAt, hF2, Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
    refine ⟨ε * Real.log 2, mul_pos hε hlog2_pos, fun t ht_mem ht_dist => ?_⟩
    simp only [mem_Ici] at ht_mem
    have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) ht_mem
    rw [Real.dist_eq]
    -- |F(t) - 0| = |li(t) * t^{-σ}| = li(t) * t^{-σ} (both nonneg)
    rw [sub_zero, abs_of_nonneg (mul_nonneg (logarithmicIntegral_nonneg ht_mem)
      (rpow_nonneg ht_pos.le _))]
    -- Bound: li(t) ≤ (t-2)/log 2, t^{-σ} ≤ 1 (since t ≥ 2 > 1 and σ > 0)
    have h_rpow_le_one : t ^ (-σ) ≤ 1 := by
      rw [rpow_neg ht_pos.le]
      exact inv_le_one_of_one_le₀ (one_le_rpow (le_trans one_le_two ht_mem) hσ_pos.le)
    have h_li_bound : logarithmicIntegral t ≤ (t - 2) / Real.log 2 := by
      rcases eq_or_lt_of_le ht_mem with rfl | ht2'
      · simp [logarithmicIntegral_two]
      · unfold logarithmicIntegral
        have h_norm := norm_setIntegral_le_of_norm_le_const
          (show volume (Ioc (2:ℝ) t) < ⊤ from by
            rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
          (fun u (hu : u ∈ Ioc (2:ℝ) t) => by
            have hlogu_pos : 0 < Real.log u := Real.log_pos (by linarith [hu.1] : (1:ℝ) < u)
            have : ‖(1 : ℝ) / Real.log u‖ = 1 / Real.log u := by
              rw [Real.norm_eq_abs, abs_div, abs_one, abs_of_nonneg hlogu_pos.le]
            rw [this]
            exact div_le_div_of_nonneg_left one_pos.le hlog2_pos
              (Real.log_le_log (by norm_num : (0:ℝ) < 2) hu.1.le))
        -- h_norm: ‖∫_{Ioc 2 t} 1/log u‖ ≤ 1/log 2 * volume.real(Ioc 2 t)
        -- unfold li to ∫, simplify volume.real
        simp only [Measure.real, Real.volume_Ioc,
          ENNReal.toReal_ofReal (show (0:ℝ) ≤ t - 2 by linarith)] at h_norm
        -- h_norm: ‖∫_{Ioc 2 t} 1/log u‖ ≤ 1/log 2 * (t-2)
        unfold logarithmicIntegral at *
        calc ∫ u in Ioc 2 t, 1 / Real.log u
            ≤ ‖∫ u in Ioc 2 t, 1 / Real.log u‖ := le_abs_self _
          _ ≤ 1 / Real.log 2 * (t - 2) := h_norm
          _ = (t - 2) / Real.log 2 := by ring
    -- |t - 2| < ε * log 2 and t ≥ 2, so t - 2 < ε * log 2
    rw [Real.dist_eq] at ht_dist
    have ht_sub : t - 2 < ε * Real.log 2 := by
      rwa [abs_of_nonneg (sub_nonneg.mpr ht_mem)] at ht_dist
    calc logarithmicIntegral t * t ^ (-σ)
        ≤ ((t - 2) / Real.log 2) * 1 := by
          exact mul_le_mul h_li_bound h_rpow_le_one (rpow_nonneg ht_pos.le _)
            (div_nonneg (sub_nonneg.mpr ht_mem) hlog2_pos.le)
      _ = (t - 2) / Real.log 2 := by ring
      _ < (ε * Real.log 2) / Real.log 2 :=
          div_lt_div_of_pos_right ht_sub hlog2_pos
      _ = ε := by field_simp
  -- F → 0 at ∞: squeeze 0 ≤ li(t)*t^{-σ} ≤ (1/log 2)*t^{-(σ-1)} → 0
  have hF_tend : Tendsto F atTop (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
      exact mul_nonneg (logarithmicIntegral_nonneg ht) (rpow_nonneg (by linarith : (0:ℝ) ≤ t) _)
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
      have ht_pos : 0 < t := by linarith
      calc logarithmicIntegral t * t ^ (-σ)
          ≤ (t / Real.log 2) * t ^ (-σ) :=
            mul_le_mul_of_nonneg_right (logarithmicIntegral_lt_bound ht)
              (rpow_nonneg ht_pos.le _)
        _ = (1 / Real.log 2) * (t ^ (1:ℝ) * t ^ (-σ)) := by rw [rpow_one]; ring
        _ = (1 / Real.log 2) * t ^ (-(σ - 1)) := by
            rw [← rpow_add ht_pos]; congr 1; ring
    · rw [show (0:ℝ) = (1 / Real.log 2) * 0 from by ring]
      exact (tendsto_rpow_neg_atTop (show 0 < σ - 1 by linarith)).const_mul _
  -- F' integrable on Ioi 2: show F' = nice form, then each piece is integrable
  have h_nice : ∀ t ∈ Ioi (2 : ℝ), F' t =
      (t / Real.log t) * t ^ (-(σ + 1)) - σ * (logarithmicIntegral t * t ^ (-(σ + 1))) := by
    intro t ht; simp only [F']
    have ht_pos : 0 < t := lt_trans (by norm_num : (0:ℝ) < 2) ht
    rw [show (-σ - 1 : ℝ) = -(σ + 1) from by ring,
      show (-σ : ℝ) = 1 + -(σ + 1) from by ring, rpow_add ht_pos, rpow_one]
    ring
  have h_li_int_ioi2 := (integrableOn_li_rpow σ hσ1).mono_set
    (Ioi_subset_Ioi (show (1:ℝ) ≤ 2 by norm_num))
  have hF'_int : IntegrableOn F' (Ioi 2) := by
    have h_sub : IntegrableOn
        (fun t => (t / Real.log t) * t ^ (-(σ + 1)) - σ * (logarithmicIntegral t * t ^ (-(σ + 1))))
        (Ioi 2) :=
      (integrableOn_tDivLog_rpow σ hσ1).sub (h_li_int_ioi2.const_mul σ)
    exact h_sub.congr_fun (fun t ht => by rw [← h_nice t ht]) measurableSet_Ioi
  -- Apply FTC: ∫_{Ioi 2} F' = 0 - F(2) = 0
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hF_cont hF_deriv hF'_int hF_tend
  rw [hF2, sub_zero] at hFTC
  rw [setIntegral_congr_fun measurableSet_Ioi h_nice] at hFTC
  -- hFTC: ∫_{Ioi 2} (tDivLog*rpow - σ*(li*rpow)) = 0
  -- Use integral_sub to split, then integral_const_mul to factor
  have h_split := integral_sub (integrableOn_tDivLog_rpow σ hσ1)
    (h_li_int_ioi2.const_mul σ)
  -- h_split : ∫(tDivLog) - ∫(σ * li*rpow) = ∫(tDivLog - σ*(li*rpow))
  -- The RHS of h_split has integrand (tDivLog - σ*(li*rpow)), same as hFTC up to ring
  have h_rhs_eq : ∫ t in Ioi (2:ℝ),
      (t / Real.log t * t ^ (-(σ + 1)) - σ * (logarithmicIntegral t * t ^ (-(σ + 1)))) =
      ∫ t in Ioi (2:ℝ),
      ((t / Real.log t) * t ^ (-(σ + 1)) - σ * (logarithmicIntegral t * t ^ (-(σ + 1)))) :=
    rfl
  have h_factor : ∫ t in Ioi (2:ℝ), σ * (logarithmicIntegral t * t ^ (-(σ + 1))) =
      σ * ∫ t in Ioi (2:ℝ), logarithmicIntegral t * t ^ (-(σ + 1)) :=
    integral_const_mul σ _
  linarith [h_split, h_factor, hFTC]

/-! ### Real-to-complex integral bridges -/

/-- Bridge: σ * ∫ π(t) * t^{-(σ+1)} (real) = (primeZeta(↑σ)).re for σ > 1. -/
private theorem primeCounting_integral_eq_primeZeta_re (σ : ℝ) (hσ : 1 < σ) :
    σ * ∫ t in Ioi (1 : ℝ), (↑(Nat.primeCounting ⌊t⌋₊) : ℝ) * t ^ (-(σ + 1)) =
    (primeZeta (↑σ)).re := by
  have h := primeZeta_eq_primeCounting_integral (show 1 < (↑σ : ℂ).re by simp; exact hσ)
  -- Show: complex integral = ↑(real integral)
  have h_eq : ∫ t in Ioi (1 : ℝ),
      (↑(Nat.primeCounting ⌊t⌋₊) : ℂ) * (↑t : ℂ) ^ (-((↑σ : ℂ) + 1)) =
      ↑(∫ t in Ioi (1 : ℝ), (↑(Nat.primeCounting ⌊t⌋₊) : ℝ) * t ^ (-(σ + 1))) := by
    have h_congr : ∀ t ∈ Ioi (1 : ℝ),
        (↑(Nat.primeCounting ⌊t⌋₊) : ℂ) * (↑t : ℂ) ^ (-((↑σ : ℂ) + 1)) =
        (((↑(Nat.primeCounting ⌊t⌋₊) : ℝ) * t ^ (-(σ + 1)) : ℝ) : ℂ) := by
      intro t ht
      have ht_pos : 0 ≤ t := by linarith [show (1:ℝ) < t from ht]
      rw [show -((↑σ : ℂ) + 1) = ((-(σ + 1) : ℝ) : ℂ) from by push_cast; ring,
        show (↑t : ℂ) ^ ((-(σ + 1) : ℝ) : ℂ) = ((t ^ (-(σ + 1)) : ℝ) : ℂ) from
          (Complex.ofReal_cpow ht_pos _).symm]
      norm_cast
    rw [setIntegral_congr_fun measurableSet_Ioi h_congr]
    exact integral_ofReal
  rw [h, h_eq, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Bridge: ∫_{Ioi 2} (t/log t) * t^{-(σ+1)} (real) = (K_ext(↑σ) - Complex.log(↑σ - 1)).re. -/
private theorem tDivLog_integral_eq_K_ext_re (K_ext : ℂ → ℂ)
    (hK_eq : ∀ s : ℂ, 1 < s.re →
        K_ext s = (∫ t in Ioi (2 : ℝ), (↑(t / Real.log t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
          + Complex.log (s - 1))
    (σ : ℝ) (hσ : 1 < σ) :
    ∫ t in Ioi (2 : ℝ), (t / Real.log t) * t ^ (-(σ + 1)) =
    (K_ext (↑σ) - Complex.log ((↑σ : ℂ) - 1)).re := by
  have h_K := hK_eq (↑σ) (by simp; exact hσ)
  -- K_ext(↑σ) - log(↑σ - 1) = ∫ ↑(tDivLog) * cpow (complex)
  have h_cpx : K_ext (↑σ) - Complex.log ((↑σ : ℂ) - 1) =
      ∫ t in Ioi (2 : ℝ), (↑(t / Real.log t) : ℂ) * (↑t : ℂ) ^ (-((↑σ : ℂ) + 1)) := by
    rw [h_K, add_sub_cancel_right]
  rw [h_cpx]
  -- The complex integral at real σ reduces to ofReal of the real integral
  have h_congr : ∀ t ∈ Ioi (2 : ℝ),
      (↑(t / Real.log t) : ℂ) * (↑t : ℂ) ^ (-((↑σ : ℂ) + 1)) =
      (((t / Real.log t) * t ^ (-(σ + 1)) : ℝ) : ℂ) := by
    intro t ht
    have ht_pos : 0 ≤ t := by linarith [show (2:ℝ) < t from ht]
    rw [show -((↑σ : ℂ) + 1) = ((-(σ + 1) : ℝ) : ℂ) from by push_cast; ring,
      show (↑t : ℂ) ^ ((-(σ + 1) : ℝ) : ℂ) = ((t ^ (-(σ + 1)) : ℝ) : ℂ) from
        (Complex.ofReal_cpow ht_pos _).symm]
    push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi h_congr]
  have h_ofR : ∫ t in Ioi (2 : ℝ), (((t / Real.log t) * t ^ (-(σ + 1)) : ℝ) : ℂ) =
      ↑(∫ t in Ioi (2 : ℝ), (t / Real.log t) * t ^ (-(σ + 1))) := integral_ofReal
  rw [h_ofR, Complex.ofReal_re]

/-! ### Algebraic bridge -/

/-- Key algebraic identity: for σ > 2,
correctionTerm.re - log(normSq(zrf))/2 = -primeZeta.re - log(σ-1).
Uses: exp(H_zeta_log) = ζ, H_zeta_log = primeZeta + correctionTerm, zrf = (s-1)*ζ. -/
private theorem algebraic_bridge (σ : ℝ) (hσ : 2 < σ) :
    (correctionTerm (↑σ)).re - Real.log (Complex.normSq (zrf (↑σ))) / 2 =
    -(primeZeta (↑σ)).re - Real.log (σ - 1) := by
  have hσ_gt1 : 1 < σ := by linarith
  have hσ_pos : 0 < σ := by linarith
  have hσ_ne1 : (↑σ : ℂ) ≠ 1 := by exact_mod_cast show σ ≠ 1 by linarith
  have hσ1_pos : 0 < σ - 1 := by linarith
  -- Step 1: H_zeta_log = primeZeta + correctionTerm
  have h_decomp := H_zeta_log_eq_add (show 1 < (↑σ : ℂ).re by simp; exact hσ_gt1)
  -- Step 2: exp(H_zeta_log(↑σ)) = ζ(↑σ)
  have h_exp := H_zeta_log_exp_eq (show 1 < (↑σ : ℂ).re by simp; exact hσ_gt1)
  -- Step 3: H_zeta_log.re = log(‖ζ(↑σ)‖) from ‖exp(z)‖ = exp(Re(z))
  have h_hzl_re : (LandauLogZetaObstruction.H_zeta_log (↑σ)).re = Real.log ‖riemannZeta (↑σ)‖ := by
    have key : Real.exp (LandauLogZetaObstruction.H_zeta_log (↑σ)).re = ‖riemannZeta (↑σ)‖ := by
      rw [← Complex.norm_exp]; exact congr_arg (‖·‖) h_exp
    rw [← congrArg Real.log key, Real.log_exp]
  -- Step 4: zrf(↑σ) = (↑σ - 1) * ζ(↑σ)
  have h_zrf := zrf_of_ne hσ_ne1
  -- Step 5: normSq(zrf) = (σ-1)² * normSq(ζ)
  have h_nsq : Complex.normSq (zrf (↑σ)) = (σ - 1) ^ 2 * Complex.normSq (riemannZeta (↑σ)) := by
    rw [h_zrf, map_mul]
    congr 1
    rw [show (↑σ : ℂ) - 1 = ↑(σ - 1) from by push_cast; ring, Complex.normSq_ofReal]
    ring
  -- Step 6: log(normSq(zrf))/2 = log(σ-1) + log(‖ζ‖)
  have h_zrf_ne := zrf_ne_zero_of_real_pos σ hσ_pos
  have h_zeta_ne : riemannZeta (↑σ) ≠ 0 := by
    intro h; apply h_zrf_ne; rw [h_zrf, h, mul_zero]
  have h_nsq_pos : 0 < Complex.normSq (zrf (↑σ)) := Complex.normSq_pos.mpr h_zrf_ne
  have h_nsq_zeta_pos : 0 < Complex.normSq (riemannZeta (↑σ)) :=
    Complex.normSq_pos.mpr h_zeta_ne
  have h_log_nsq : Real.log (Complex.normSq (zrf (↑σ))) / 2 =
      Real.log (σ - 1) + Real.log ‖riemannZeta (↑σ)‖ := by
    rw [h_nsq, Real.log_mul (pow_ne_zero 2 hσ1_pos.ne') h_nsq_zeta_pos.ne',
      Real.log_pow, Complex.normSq_eq_norm_sq, Real.log_pow]
    push_cast; ring
  -- Step 7: Assembly
  -- corrTerm.re = H_zeta_log.re - primeZeta.re (from decomposition)
  have h_ct_re : (correctionTerm (↑σ)).re =
      (LandauLogZetaObstruction.H_zeta_log (↑σ)).re - (primeZeta (↑σ)).re := by
    have := congr_arg Complex.re h_decomp; simp only [Complex.add_re] at this; linarith
  rw [h_ct_re, h_hzl_re, h_log_nsq]
  ring

/-- Real integral identity: ∫_{Ioi 1} piGenFun · t^{-(σ+1)} = piCF(σ)/σ for σ > 2. -/
theorem piGenFun_integral_eq_piCF_div (K_ext : ℂ → ℂ)
    (hK_diff : Differentiable ℂ K_ext)
    (hK_eq : ∀ s : ℂ, 1 < s.re →
        K_ext s = (∫ t in Ioi (2 : ℝ), (↑(t / Real.log t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
          + Complex.log (s - 1))
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (σ : ℝ) (hσ_gt : 2 < σ) :
    ∫ t in Ioi (1 : ℝ), piGenFun C α σ_sign t * t ^ (-(σ + 1)) =
      piCF K_ext C α σ_sign σ / σ := by
  have hσ1 : 1 < σ := by linarith
  have hσ_pos : 0 < σ := by linarith
  have hα_lt : α < σ := by linarith
  -- Step 1: Split integral into 3 pieces
  have h_split := piGenFun_integral_split C α σ_sign σ hσ1 hα_lt
  -- Step 2: Evaluate each piece
  have hI₁ := mellin_rpow_alpha_real α σ hα_lt
  have hI₂ := primeCounting_integral_eq_primeZeta_re σ hσ1
  have hI₃_ibp := li_integral_ibp σ hσ_gt
  have hI₃_bridge := tDivLog_integral_eq_K_ext_re K_ext hK_eq σ hσ1
  -- Step 3: (K_ext - log).re = K_ext.re - log(σ-1)
  have h_re_split : (K_ext (↑σ) - Complex.log ((↑σ : ℂ) - 1)).re =
      (K_ext (↑σ)).re - Real.log (σ - 1) := by
    rw [Complex.sub_re, show (↑σ : ℂ) - 1 = ↑(σ - 1) from by push_cast; ring,
      ← Complex.ofReal_log (show 0 ≤ σ - 1 by linarith), Complex.ofReal_re]
  -- Step 4: Algebraic identity
  have h_alg := algebraic_bridge σ hσ_gt
  -- Step 5: Multiply both sides by σ and assemble
  rw [eq_div_iff (ne_of_gt hσ_pos), h_split, hI₁]
  -- Goal: ((C * (1/(σ-α)) - σ_sign * ∫π) + σ_sign * ∫li) * σ = piCF
  -- Distribute σ: ring handles field operations over ℝ
  have h_dist : ∀ (a b : ℝ),
      ((C * (1 / (σ - α)) - σ_sign * a) + σ_sign * b) * σ =
      C * σ / (σ - α) - σ_sign * (σ * a) + σ_sign * (σ * b) := by intros; ring
  rw [h_dist]
  -- Substitute σ * ∫π = primeZeta.re, σ * ∫li = K_ext.re - log(σ-1)
  have h₃ : σ * ∫ t in Ioi (1 : ℝ),
      LogarithmicIntegral.logarithmicIntegral t * t ^ (-(σ + 1)) =
      (K_ext (↑σ)).re - Real.log (σ - 1) := by linarith [hI₃_ibp, hI₃_bridge, h_re_split]
  rw [hI₂, h₃]
  -- Goal: C*σ/(σ-α) - σ_sign*primeZeta.re + σ_sign*(K_ext.re - log(σ-1)) = piCF
  unfold piCF
  -- Reduce to algebraic_bridge: corr.re - log(normSq)/2 = -primeZeta.re - log(σ-1)
  -- σ_sign factor requires linear_combination (linarith can't handle sign-variable products)
  linear_combination -σ_sign * h_alg


/-! ## Section 5: Formula matching on the real axis

For real σ > 2:
  (3-σ) · ∫_{Ioi T₀} piGenFun · t^{σ-4} = piCF(σ) - boundary terms

This identifies the Tonelli integral with piCF for σ close to 3. -/

/-- Formula matching: the Tonelli integral equals piCF on the overlap.
For real σ with 2 < σ < 4:
  ∫_{Ioi T₀} piGenFun · t^{(3-σ)-4} relates to piCF via Pringsheim identification. -/
theorem formula_matching_real (K_ext : ℂ → ℂ)
    (hK_diff : Differentiable ℂ K_ext)
    (hK_eq : ∀ s : ℂ, 1 < s.re →
        K_ext s = (∫ t in Ioi (2 : ℝ), (↑(t / Real.log t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
          + Complex.log (s - 1))
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : PiLiHardBound α C σ_sign)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ piGenFun C α σ_sign t) :
    ∀ w : ℝ, 0 ≤ w → w < 1 →
      HasSum (fun k => antiCoeff (piGenFun C α σ_sign) T₀ 3 k * w ^ k)
        (piCF K_ext C α σ_sign (3 - w) / (3 - w) -
          ∫ t in Icc 1 T₀, piGenFun C α σ_sign t * t ^ (w - 4)) := by
  intro w hw hw1
  -- Step 1: Tonelli gives HasSum = ∫_{Ioi T₀}
  have h_tonelli := tonelli_pi_hasSum_lt_one C hC α hα hα1 σ_sign hσ hbound T₀ hT₀ hg_nn w hw hw1
  -- Step 2: Show the Tonelli integral = piCF/(3-w) - boundary
  -- via ∫_{Ioi 1} = ∫_{Icc 1 T₀} + ∫_{Ioi T₀} and the integral identity
  suffices h : ∫ t in Ioi T₀, piGenFun C α σ_sign t * t ^ (w - 4) =
      piCF K_ext C α σ_sign (3 - w) / (3 - w) -
        ∫ t in Icc 1 T₀, piGenFun C α σ_sign t * t ^ (w - 4) by
    rwa [h] at h_tonelli
  -- Use the integral identity with σ = 3 - w
  have hσ_val : 2 < 3 - w := by linarith
  have h_full := piGenFun_integral_eq_piCF_div K_ext hK_diff hK_eq C hC α hα hα1 σ_sign hσ
    (3 - w) hσ_val
  -- Convert w-4 to -(σ+1): w - 4 = w - 4 = -(3-w) - 1 = -(σ+1)
  have h_exp_eq : ∀ t : ℝ, t ^ (w - 4) = t ^ (-(3 - w + 1)) := by
    intro t; congr 1; ring
  -- Split ∫_{Ioi 1} = ∫_{Icc 1 T₀} + ∫_{Ioi T₀}
  have h_disj : Disjoint (Icc (1 : ℝ) T₀) (Ioi T₀) :=
    Set.disjoint_left.mpr (fun _ ⟨_, ht⟩ h => not_lt.mpr ht h)
  obtain ⟨D, hD, hg_le⟩ := piGenFun_le_linear C hC α (by linarith : α ≤ 1) σ_sign hσ
  have hg_meas := piGenFun_measurable C α σ_sign
  -- IntegrableOn on Icc 1 T₀ (bounded on compact)
  have hf_Icc : IntegrableOn (fun t => piGenFun C α σ_sign t * t ^ (w - 4))
      (Icc 1 T₀) := by
    apply Measure.integrableOn_of_bounded (isCompact_Icc.measure_lt_top.ne)
      ((hg_meas.mul (measurable_id.pow_const _)).aestronglyMeasurable) (M := D * T₀)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ⟨ht1, htT₀⟩
    rw [Real.norm_eq_abs, abs_mul]
    have ht_pos : 0 < t := by linarith
    have h_abs_rpow : |t ^ (w - 4)| ≤ 1 := by
      rw [abs_of_pos (Real.rpow_pos_of_pos ht_pos _)]
      exact Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith)
    calc |piGenFun C α σ_sign t| * |t ^ (w - 4)|
        ≤ (D * t) * 1 := mul_le_mul (hg_le t ht1) h_abs_rpow (abs_nonneg _) (by positivity)
      _ = D * t := mul_one _
      _ ≤ D * T₀ := by nlinarith [hD]
  -- IntegrableOn on Ioi T₀ (dominated by D * t^{w-3})
  have hf_Ioi_T₀ : IntegrableOn (fun t => piGenFun C α σ_sign t * t ^ (w - 4))
      (Ioi T₀) := by
    have h_bound : IntegrableOn (fun t : ℝ => D * t ^ (w - 3)) (Ioi T₀) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith : w - 3 < -1)
        (by linarith : (0 : ℝ) < T₀)).const_mul D
    apply h_bound.mono'
    · exact (hg_meas.mul (measurable_id.pow_const _)).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 ≤ t := by linarith [show T₀ < t from ht]
      have ht_pos : 0 < t := by linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht_pos _)]
      calc |piGenFun C α σ_sign t| * t ^ (w - 4)
          ≤ D * t * t ^ (w - 4) :=
            mul_le_mul_of_nonneg_right (hg_le t ht1) (Real.rpow_nonneg ht_pos.le _)
        _ = D * (t ^ (1 : ℝ) * t ^ (w - 4)) := by rw [Real.rpow_one]; ring
        _ = D * t ^ (1 + (w - 4)) := by rw [← Real.rpow_add ht_pos]
        _ = D * t ^ (w - 3) := by ring_nf
  -- ∫_{Ici 1} = ∫_{Icc 1 T₀} + ∫_{Ioi T₀}
  have h_split := setIntegral_union h_disj measurableSet_Ioi hf_Icc hf_Ioi_T₀
  rw [Icc_union_Ioi_eq_Ici hT₀, integral_Ici_eq_integral_Ioi] at h_split
  -- h_split : ∫_{Ioi 1} f = ∫_{Icc 1 T₀} f + ∫_{Ioi T₀} f
  -- h_full : ∫_{Ioi 1} g = piCF(3-w)/(3-w) where g uses -(σ+1) exponent
  -- Rewrite exponents using h_exp_eq
  have h_full' : ∫ t in Ioi (1 : ℝ), piGenFun C α σ_sign t * t ^ (w - 4) =
      piCF K_ext C α σ_sign (3 - w) / (3 - w) := by
    conv at h_full => rw [show -(3 - w + 1) = w - 4 by ring]
    exact h_full
  linarith

/-! ## Section 5b: Parametric integral analyticity on compact sets

Helper: ∫_{Icc 1 T₀} g(t) · t^(z-c) dt is ℂ-differentiable in z.
Adapted from SigmaLtOneFromPringsheimExtension.finite_integral_analyticAt (center 2 → general c).
Via complexification bridge, this gives ℝ-analyticity. Via composition, ℂ-differentiability
of ∫ g(t)·t^{-(s+1)}. -/

set_option maxHeartbeats 3200000 in
/-- Core lemma: ∫_{Icc 1 T₀} g(t)·t^(z-c) is ℂ-differentiable in z, for any c : ℝ. -/
private theorem compact_integral_diff_cpow
    (g : ℝ → ℝ) (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_meas : Measurable g)
    (hg_bound : ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 1 ≤ t → |g t| ≤ D * t)
    (c : ℝ) :
    Differentiable ℂ (fun (z : ℂ) => ∫ t in Icc (1 : ℝ) T₀,
      ((g t : ℝ) : ℂ) * (↑t : ℂ) ^ (z - (↑c : ℂ))) := by
  obtain ⟨D, hD, hg_le⟩ := hg_bound
  intro z₀
  set s := Metric.ball z₀ 1
  set μ := MeasureTheory.Measure.restrict MeasureTheory.volume (Icc (1 : ℝ) T₀)
  set M := max (T₀ ^ (z₀.re + 1 - c)) 1 with hM_def
  set bound_val := D * T₀ * Real.log T₀ * M with hbound_def
  have hM_pos : 0 < M := lt_max_of_lt_right one_pos
  have h_deriv : ∀ t : ℝ, 1 ≤ t → t ≤ T₀ →
      ∀ z : ℂ, HasDerivAt (fun z => ((g t : ℝ) : ℂ) * (↑t : ℂ) ^ (z - (↑c : ℂ)))
        (((g t : ℝ) : ℂ) * Complex.log (↑t) * (↑t : ℂ) ^ (z - (↑c : ℂ))) z := by
    intro t ht1 _htT₀ z
    have ht_pos : (0 : ℝ) < t := by linarith
    have ht_ne : (↑t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht_pos)
    have h_sub : HasDerivAt (fun z : ℂ => z - (↑c : ℂ)) 1 z :=
      (hasDerivAt_id z).sub_const (↑c : ℂ)
    have h_cpow : HasDerivAt (fun z : ℂ => (↑t : ℂ) ^ (z - (↑c : ℂ)))
        ((↑t : ℂ) ^ (z - (↑c : ℂ)) * Complex.log (↑t) * 1) z :=
      HasDerivAt.const_cpow h_sub (Or.inl ht_ne)
    simp only [mul_one] at h_cpow
    exact (h_cpow.const_mul _).congr_deriv (by ring)
  have h_norm_bound : ∀ t : ℝ, t ∈ Icc 1 T₀ → ∀ z ∈ s,
      ‖((g t : ℝ) : ℂ) * Complex.log (↑t) * (↑t : ℂ) ^ (z - (↑c : ℂ))‖ ≤ bound_val := by
    intro t ⟨ht1, htT₀⟩ z hz
    have ht_pos : (0 : ℝ) < t := by linarith
    have h1 : ‖((g t : ℝ) : ℂ)‖ ≤ D * T₀ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (hg_le t ht1).trans (by nlinarith)
    have h2 : ‖Complex.log (↑t)‖ ≤ Real.log T₀ := by
      rw [show Complex.log (↑t) = ↑(Real.log t) from by
        rw [Complex.ofReal_log (le_of_lt ht_pos)]]
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg ht1)]
      exact Real.log_le_log ht_pos htT₀
    have h3 : ‖(↑t : ℂ) ^ (z - (↑c : ℂ))‖ ≤ M := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos (z - (↑c : ℂ))]
      have hre : (z - (↑c : ℂ)).re = z.re - c := by simp
      rw [hre]
      by_cases hexp : z.re - c ≥ 0
      · calc t ^ (z.re - c) ≤ T₀ ^ (z.re - c) :=
              Real.rpow_le_rpow (by linarith) htT₀ hexp
          _ ≤ T₀ ^ (z₀.re + 1 - c) := by
              apply Real.rpow_le_rpow_of_exponent_le (by linarith)
              have h_dist : dist z z₀ < 1 := Metric.mem_ball.mp hz
              have h_abs_re : |z.re - z₀.re| ≤ dist z z₀ := by
                calc |z.re - z₀.re| = |(z - z₀).re| := by congr 1
                  _ ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
                  _ = dist z z₀ := (dist_eq_norm z z₀).symm
              linarith [(abs_le.mp (h_abs_re.trans h_dist.le)).2]
          _ ≤ M := le_max_left _ _
      · push_neg at hexp
        calc t ^ (z.re - c) ≤ 1 :=
              Real.rpow_le_one_of_one_le_of_nonpos ht1 (le_of_lt hexp)
          _ ≤ M := le_max_right _ _
    calc ‖((g t : ℝ) : ℂ) * Complex.log (↑t) * (↑t : ℂ) ^ (z - (↑c : ℂ))‖
        = ‖((g t : ℝ) : ℂ)‖ * ‖Complex.log (↑t)‖ * ‖(↑t : ℂ) ^ (z - (↑c : ℂ))‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ (D * T₀) * Real.log T₀ * M := by
          have : 0 ≤ Real.log T₀ := Real.log_nonneg (by linarith)
          gcongr
      _ = bound_val := by ring
  have h_slit : ∀ t : ℝ, t ∈ Icc 1 T₀ → (↑t : ℂ) ∈ Complex.slitPlane := by
    intro t ⟨ht1, _⟩; left; simp [Complex.ofReal_re]; linarith
  have h_cpow_cont : ∀ z : ℂ, ContinuousOn
      (fun t : ℝ => (↑t : ℂ) ^ (z - (↑c : ℂ))) (Icc 1 T₀) :=
    fun z => (Complex.continuous_ofReal.continuousOn.cpow_const (fun t ht => h_slit t ht))
  have h_g_aesm : AEStronglyMeasurable (fun t : ℝ => ((g t : ℝ) : ℂ)) μ :=
    (Complex.measurable_ofReal.comp hg_meas).aestronglyMeasurable
  have h_aesm : ∀ z : ℂ, AEStronglyMeasurable
      (fun t : ℝ => ((g t : ℝ) : ℂ) * (↑t : ℂ) ^ (z - (↑c : ℂ))) μ :=
    fun z => h_g_aesm.mul ((h_cpow_cont z).aestronglyMeasurable measurableSet_Icc)
  have h_result := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => h_aesm z)
    (by
      refine Integrable.mono'
        (integrableOn_const (C := D * T₀ * M) (hs := isCompact_Icc.measure_lt_top.ne))
        (h_aesm z₀) ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ⟨ht1, htT₀⟩
      have ht_pos : (0 : ℝ) < t := by linarith
      calc ‖((g t : ℝ) : ℂ) * (↑t : ℂ) ^ (z₀ - (↑c : ℂ))‖
          = ‖((g t : ℝ) : ℂ)‖ * ‖(↑t : ℂ) ^ (z₀ - (↑c : ℂ))‖ := norm_mul _ _
        _ ≤ (D * T₀) * M := by
            apply mul_le_mul
            · rw [Complex.norm_real, Real.norm_eq_abs]
              exact (hg_le t ht1).trans (by nlinarith)
            · rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
              simp only [Complex.sub_re, Complex.ofReal_re]
              by_cases hexp : z₀.re - c ≥ 0
              · exact (Real.rpow_le_rpow (by linarith) htT₀ hexp).trans
                  ((Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)).trans
                    (le_max_left _ _))
              · push_neg at hexp
                exact (Real.rpow_le_one_of_one_le_of_nonpos ht1 hexp.le).trans (le_max_right _ _)
            · exact norm_nonneg _
            · positivity)
    ((h_g_aesm.mul ((Complex.continuous_ofReal.continuousOn.clog
        (fun t ht => h_slit t ht)).aestronglyMeasurable measurableSet_Icc)).mul
      ((h_cpow_cont z₀).aestronglyMeasurable measurableSet_Icc))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht z hz
      exact h_norm_bound t ht z hz)
    (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ⟨ht1, htT₀⟩ z _hz
      exact h_deriv t ht1 htT₀ z)
  exact h_result.2.differentiableAt

set_option maxHeartbeats 3200000 in
/-- ∫_{Icc 1 T₀} g(t) · t^(w-c) is ℝ-analytic in w, via complexification bridge. -/
private theorem compact_integral_analyticAt
    (g : ℝ → ℝ) (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_meas : Measurable g)
    (hg_bound : ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 1 ≤ t → |g t| ≤ D * t)
    (c : ℝ) (w₀ : ℝ) :
    AnalyticAt ℝ (fun w => ∫ t in Icc 1 T₀, g t * t ^ (w - c)) w₀ := by
  set Φ : ℂ → ℂ := fun z => ∫ t in Icc (1 : ℝ) T₀,
    ((g t : ℝ) : ℂ) * (↑t : ℂ) ^ (z - (↑c : ℂ)) with hΦ_def
  have hΦ_diff : Differentiable ℂ Φ := compact_integral_diff_cpow g T₀ hT₀ hg_meas hg_bound c
  have hΦ_anal : AnalyticAt ℂ Φ (↑w₀) := hΦ_diff.analyticAt (↑w₀)
  have h_bridge : (fun w : ℝ => (Φ (↑w)).re) =
      fun w => ∫ t in Icc 1 T₀, g t * t ^ (w - c) := by
    ext w
    show (∫ t in Icc (1 : ℝ) T₀, ((g t : ℝ) : ℂ) * (↑t : ℂ) ^ ((↑w : ℂ) - (↑c : ℂ))).re =
      ∫ t in Icc 1 T₀, g t * t ^ (w - c)
    rw [show (↑w : ℂ) - (↑c : ℂ) = ((w - c : ℝ) : ℂ) from by push_cast; ring]
    have h_eq : ∀ t ∈ Icc (1 : ℝ) T₀,
        ((g t : ℝ) : ℂ) * (↑t : ℂ) ^ ((w - c : ℝ) : ℂ) =
        ((g t * t ^ (w - c) : ℝ) : ℂ) := by
      intro t ⟨ht1, _⟩
      rw [show (↑t : ℂ) ^ ((w - c : ℝ) : ℂ) = ((t ^ (w - c) : ℝ) : ℂ) from
        (Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ t) _).symm,
        ← Complex.ofReal_mul]
    rw [setIntegral_congr_fun measurableSet_Icc h_eq]
    have : ∫ x in Icc (1 : ℝ) T₀, ((g x * x ^ (w - c) : ℝ) : ℂ) =
        (↑(∫ x in Icc 1 T₀, g x * x ^ (w - c)) : ℂ) := integral_ofReal
    rw [this, Complex.ofReal_re]
  rw [← h_bridge]
  exact hΦ_anal.re_ofReal

/-- The ℂ-valued parametric integral ∫ g(t)·t^{-(s+1)} on [1,T₀] is ℂ-differentiable.
Derived from compact_integral_diff_cpow via composition with s ↦ -s. -/
private theorem compact_integral_complex_differentiable
    (g : ℝ → ℝ) (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_meas : Measurable g)
    (hg_bound : ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 1 ≤ t → |g t| ≤ D * t) :
    Differentiable ℂ (fun (s : ℂ) => ∫ t in Icc (1 : ℝ) T₀,
      (↑(g t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))) := by
  -- -(s+1) = (-s) - 1, so compose z ↦ ∫ g·t^(z-1) with s ↦ -s
  have h := compact_integral_diff_cpow g T₀ hT₀ hg_meas hg_bound 1
  have h_compose : (fun s : ℂ => ∫ t in Icc (1 : ℝ) T₀,
      (↑(g t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))) =
    (fun z => ∫ t in Icc (1 : ℝ) T₀,
      ((g t : ℝ) : ℂ) * (↑t : ℂ) ^ (z - (↑(1 : ℝ) : ℂ))) ∘ (fun s : ℂ => -s) := by
    ext s; congr 1; ext t; congr 1
    push_cast; ring_nf
  rw [h_compose]
  exact h.comp differentiable_neg

/-! ## Section 6: Pringsheim extension application

Apply pringsheim_real_extension to get Summable(B_k · W^k) for W = 3 - σ₀ > 1,
i.e., for σ₀ < 2 (which includes σ₀ > α since α < 1 < 2). -/

theorem piAnticoeff_summable_at_target
    (K_ext : ℂ → ℂ) (hK_diff : Differentiable ℂ K_ext)
    (hK_eq : ∀ s : ℂ, 1 < s.re →
        K_ext s = (∫ t in Ioi (2 : ℝ), (↑(t / Real.log t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
          + Complex.log (s - 1))
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : PiLiHardBound α C σ_sign)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ piGenFun C α σ_sign t)
    (σ₀ : ℝ) (hσ₀ : α < σ₀) (hσ₀_lt3 : σ₀ < 3) :
    Summable (fun k => antiCoeff (piGenFun C α σ_sign) T₀ 3 k *
      (3 - σ₀) ^ k) := by
  set B := fun k => antiCoeff (piGenFun C α σ_sign) T₀ 3 k
  have hB_nn : ∀ k, 0 ≤ B k := piAntiCoeff_nonneg C α σ_sign T₀ hT₀ hg_nn
  have hB_sum : Summable B :=
    piAnticoeff_summable_at_center C hC α hα hα1 σ_sign hσ hbound T₀ hT₀ hg_nn
  set W := (3 : ℝ) - σ₀
  have hW_nn : 0 ≤ W := by simp [W]; linarith
  -- Case split: W ≤ 1 (σ₀ ≥ 2) vs W > 1 (σ₀ < 2)
  by_cases hW1 : W ≤ 1
  · -- W ≤ 1: direct comparison with Summable B
    exact Summable.of_nonneg_of_le (fun k => mul_nonneg (hB_nn k) (pow_nonneg hW_nn k))
      (fun k => by
        calc B k * W ^ k ≤ B k * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ hW_nn hW1) (hB_nn k)
          _ = B k := mul_one _)
      hB_sum
  push_neg at hW1
  -- F(w) for the Pringsheim extension
  -- Matches ψ-case: F(w) = correctedFormula(σ₁-w)/(σ₁-w) - ∫_{Icc 1 T₀} g·t^{w-(σ₁+1)}
  set F := fun w : ℝ =>
    piCF K_ext C α σ_sign (3 - w) / (3 - w) -
    ∫ t in Icc 1 T₀, piGenFun C α σ_sign t * t ^ (w - 4) with hF_def
  have hF_hasSum : ∀ w, 0 ≤ w → w < 1 →
      HasSum (fun k => B k * w ^ k) (F w) :=
    formula_matching_real K_ext hK_diff hK_eq C hC α hα hα1 σ_sign hσ hbound T₀ hT₀ hg_nn
  -- F is analytic at every w ∈ (0, W] since piCF is analytic at 3-w > α
  -- and the finite integral is analytic in w
  have hF_anal : ∀ w : ℝ, 0 < w → w ≤ W → AnalyticAt ℝ F w := by
    intro w hw hwW
    have h3w : α < 3 - w := by simp [W] at hwW; linarith
    -- piCF(3-w)/(3-w) is analytic: piCF analytic, 3-w ≠ 0
    have h1 : AnalyticAt ℝ (fun w => piCF K_ext C α σ_sign (3 - w) / (3 - w)) w := by
      have h1a := (piCF_analyticAt_real K_ext hK_diff α hα C σ_sign (3 - w) h3w).comp_of_eq
        (analyticAt_const.sub analyticAt_id) rfl
      exact h1a.div (analyticAt_const.sub analyticAt_id) (by linarith)
    -- finite integral ∫_{Icc 1 T₀} piGenFun · t^{w-4} is analytic in w
    have h2 : AnalyticAt ℝ (fun w => ∫ t in Icc 1 T₀, piGenFun C α σ_sign t * t ^ (w - 4)) w :=
      compact_integral_analyticAt (piGenFun C α σ_sign) T₀ hT₀
        (piGenFun_measurable C α σ_sign)
        (piGenFun_le_linear C hC α (by linarith : α ≤ 1) σ_sign hσ) 4 w
    exact h1.sub h2
  exact pringsheim_real_extension B hB_nn hB_sum F hF_hasSum W hW1 hF_anal

/-! ## Section 7: IntegrableOn at σ₀ > α

Convert Pringsheim summability to IntegrableOn for the Dirichlet integral. -/

theorem piGenFun_integrableOn_at_sigma
    (K_ext : ℂ → ℂ) (hK_diff : Differentiable ℂ K_ext)
    (hK_eq : ∀ s : ℂ, 1 < s.re →
        K_ext s = (∫ t in Ioi (2 : ℝ), (↑(t / Real.log t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
          + Complex.log (s - 1))
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : PiLiHardBound α C σ_sign)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ piGenFun C α σ_sign t)
    (σ₀ : ℝ) (hσ₀ : α < σ₀) :
    IntegrableOn (fun t : ℝ => piGenFun C α σ_sign t * t ^ (-(σ₀ + 1))) (Ioi T₀) := by
  set g := piGenFun C α σ_sign with hg_def
  have hg_meas := piGenFun_measurable C α σ_sign
  obtain ⟨D, hD, hg_le⟩ := piGenFun_le_linear C hC α (by linarith : α ≤ 1) σ_sign hσ
  by_cases hσ₀_gt1 : 1 < σ₀
  · -- Case 1: σ₀ > 1. Dominate by D * t^{-σ₀}
    apply (integrableOn_Ioi_rpow_of_lt (show -(σ₀ : ℝ) < -1 by linarith)
      (show (0 : ℝ) < T₀ by linarith)).const_mul D |>.mono'
    · exact (hg_meas.mul (measurable_id.pow measurable_const)).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht)
      have ht_pos : 0 < t := by linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (rpow_pos_of_pos ht_pos _)]
      calc |g t| * t ^ (-(σ₀ + 1))
          ≤ D * t * t ^ (-(σ₀ + 1)) :=
            mul_le_mul_of_nonneg_right (hg_le t ht1) (rpow_nonneg ht_pos.le _)
        _ = D * (t ^ (1 : ℝ) * t ^ (-(σ₀ + 1))) := by rw [rpow_one]; ring
        _ = D * t ^ (-(σ₀ : ℝ)) := by rw [← rpow_add ht_pos]; ring_nf
  · -- Case 2: α < σ₀ ≤ 1. Use integrable_tsum + Pringsheim.
    push_neg at hσ₀_gt1
    set W := (3 : ℝ) - σ₀ with hW_def
    have hW_pos : 0 < W := by linarith
    have hσ₀_lt3 : σ₀ < 3 := by linarith
    -- Pringsheim summability: Summable(B_k * W^k)
    have hB_sum := piAnticoeff_summable_at_target K_ext hK_diff hK_eq C hC α hα hα1
      σ_sign hσ hbound T₀ hT₀ hg_nn σ₀ hσ₀ hσ₀_lt3
    -- Profile at center 3: f_k(t) = g(t) * t^{-4} * (log t)^k / k! * W^k
    set fk := fun (k : ℕ) (t : ℝ) =>
      g t * t ^ (-(3 + 1 : ℝ)) * ((Real.log t) ^ k / (k.factorial : ℝ)) * W ^ k
    have h_log_meas : Measurable Real.log :=
      measurable_of_measurable_on_compl_singleton 0 Real.continuous_log.measurable
    -- Each fk is AEStronglyMeasurable
    have hfk_aesm : ∀ k, AEStronglyMeasurable (fun t => fk k t)
        (volume.restrict (Ioi T₀)) := fun k =>
      (((hg_meas.mul (measurable_id.pow measurable_const)).mul
        ((h_log_meas.pow_const k).div_const _)).mul_const _).aestronglyMeasurable.restrict
    -- Each fk is nonneg on Ioi T₀
    have hfk_nn : ∀ k t, t ∈ Ioi T₀ → 0 ≤ fk k t := by
      intro k t ht
      have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht)
      exact mul_nonneg (mul_nonneg (mul_nonneg (hg_nn t (le_of_lt ht))
        (rpow_nonneg (by linarith) _))
        (div_nonneg (pow_nonneg (Real.log_nonneg ht1) _) (by positivity)))
        (pow_nonneg hW_pos.le _)
    -- Dominator: g*t^{-3} is integrable on Ioi T₀
    have h_dom_int : IntegrableOn (fun t : ℝ => g t * t ^ (-(3 : ℝ))) (Ioi T₀) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : -(2 : ℝ) < -1)
        (by linarith)).const_mul D |>.mono'
      ((hg_meas.mul (measurable_id.pow measurable_const)).aestronglyMeasurable.restrict)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht)
          have ht_pos : 0 < t := by linarith
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (rpow_pos_of_pos ht_pos _)]
          calc |g t| * t ^ (-(3 : ℝ)) ≤ D * t * t ^ (-(3 : ℝ)) :=
                mul_le_mul_of_nonneg_right (hg_le t ht1) (rpow_nonneg ht_pos.le _)
            _ = D * (t ^ (1 : ℝ) * t ^ (-(3 : ℝ))) := by rw [rpow_one]; ring
            _ = D * t ^ (-(2 : ℝ)) := by rw [← rpow_add ht_pos]; ring_nf)
    -- Profile integrability (dominated by g*t^{-3})
    have hprofile_int : ∀ k, IntegrableOn (fun t => g t * t ^ (-(3 + 1 : ℝ)) *
        ((Real.log t) ^ k / (k.factorial : ℝ))) (Ioi T₀) := by
      intro k; apply h_dom_int.mono'
      · exact ((hg_meas.mul (measurable_id.pow measurable_const)).mul
          ((h_log_meas.pow_const k).div_const _)).aestronglyMeasurable.restrict
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht)
        have ht_pos : 0 < t := by linarith
        have hg_nn_t : 0 ≤ g t := hg_nn t (le_of_lt ht)
        have hlog_nn : 0 ≤ Real.log t := Real.log_nonneg ht1
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hg_nn_t
          (rpow_nonneg ht_pos.le _)) (div_nonneg (pow_nonneg hlog_nn _) (by positivity)))]
        calc g t * t ^ (-(3 + 1 : ℝ)) * ((Real.log t) ^ k / ↑k.factorial)
            ≤ g t * t ^ (-(3 + 1 : ℝ)) * t := mul_le_mul_of_nonneg_left
              ((Real.pow_div_factorial_le_exp _ hlog_nn k).trans (by rw [Real.exp_log ht_pos]))
              (mul_nonneg hg_nn_t (rpow_nonneg ht_pos.le _))
          _ = g t * (t ^ (-(3 + 1 : ℝ)) * t ^ (1 : ℝ)) := by rw [rpow_one]; ring
          _ = g t * t ^ (-(3 : ℝ)) := by rw [← rpow_add ht_pos]; ring_nf
    -- Norm summability: ∫ ‖fk‖ = B_k * W^k
    have hnorm_sum : Summable (fun k => ∫ t in Ioi T₀, ‖fk k t‖) := by
      have h_eq : ∀ k, ∫ t in Ioi T₀, ‖fk k t‖ = antiCoeff g T₀ 3 k * W ^ k := by
        intro k
        -- Step 1: ‖fk‖ = fk a.e. on Ioi T₀ (nonneg)
        have h1 : ∫ t in Ioi T₀, ‖fk k t‖ = ∫ t in Ioi T₀, fk k t :=
          setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hfk_nn k t ht)])
        -- Step 2: factor out W^k
        have h2 : ∫ t in Ioi T₀, fk k t =
            (∫ t in Ioi T₀, g t * t ^ (-(3 + 1 : ℝ)) *
              ((Real.log t) ^ k / (k.factorial : ℝ))) * W ^ k := by
          show ∫ t in Ioi T₀, fk k t = _
          simp_rw [show ∀ t, fk k t = (g t * t ^ (-(3 + 1 : ℝ)) *
            ((Real.log t) ^ k / (k.factorial : ℝ))) * W ^ k from fun t => by
              simp only [fk]]
          exact MeasureTheory.integral_mul_const _ _
        rw [h1, h2]; congr 1
      simp_rw [h_eq]; exact hB_sum
    -- Pointwise identity: g*t^{-(σ₀+1)} = ∑' fk on Ioi T₀
    have h_ae_eq : ∀ t, t ∈ Ioi T₀ → g t * t ^ (-(σ₀ + 1)) = ∑' k, fk k t := by
      intro t ht
      have ht_pos : 0 < t := by linarith [show T₀ < t from ht]
      have h_factor : ∑' k, fk k t =
          g t * t ^ (-(3 + 1 : ℝ)) *
          ∑' k : ℕ, ((W * Real.log t) ^ k / (k.factorial : ℝ)) := by
        rw [← tsum_mul_left]
        congr 1; ext k; simp only [fk, mul_pow]; ring
      have h_exp : ∑' k : ℕ, ((W * Real.log t) ^ k / (k.factorial : ℝ)) =
          Real.exp (W * Real.log t) := by
        simpa [Real.exp_eq_exp_ℝ] using
          (congrArg (fun f : ℝ → ℝ => f (W * Real.log t))
            (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ))).symm
      have h_rpow : Real.exp (W * Real.log t) = t ^ W := by
        rw [rpow_def_of_pos ht_pos]; ring_nf
      have h_merge : g t * t ^ (-(3 + 1 : ℝ)) * t ^ W = g t * t ^ (-(σ₀ + 1)) := by
        rw [mul_assoc, ← rpow_add ht_pos]; congr 1; rw [hW_def]; ring
      rw [h_factor, h_exp, h_rpow, h_merge]
    -- Term summability on Ioi T₀
    have hfk_int : ∀ k, IntegrableOn (fun t => fk k t) (Ioi T₀) :=
      fun k => (hprofile_int k).mul_const (W ^ k)
    have hfk_meas : ∀ k, Measurable (fun t => fk k t) := fun k =>
      ((hg_meas.mul (measurable_id.pow measurable_const)).mul
        ((h_log_meas.pow_const k).div_const _)).mul_const _
    have hfk_sum : Summable (fun k => ∫ t in Ioi T₀, fk k t) := by
      have h_eq : ∀ k, ∫ t in Ioi T₀, fk k t = antiCoeff g T₀ 3 k * W ^ k := by
        intro k
        simp_rw [show ∀ t, fk k t = (g t * t ^ (-(3 + 1 : ℝ)) *
          ((Real.log t) ^ k / (k.factorial : ℝ))) * W ^ k from fun t => by
            simp only [fk]]
        rw [MeasureTheory.integral_mul_const]; congr 1
      simp_rw [h_eq]; exact hB_sum
    -- ENNReal pointwise majorant
    have hmajorant : ∀ t, t ∈ Ioi T₀ →
        ENNReal.ofReal ‖g t * t ^ (-(σ₀ + 1))‖ ≤
          ∑' k, ENNReal.ofReal (fk k t) := by
      intro t ht
      have h_nn : 0 ≤ g t * t ^ (-(σ₀ + 1)) :=
        mul_nonneg (hg_nn t (le_of_lt ht))
          (rpow_nonneg (by linarith [show T₀ < t from ht]) _)
      rw [Real.norm_eq_abs, abs_of_nonneg h_nn, h_ae_eq t ht]
      exact le_of_eq (ENNReal.ofReal_tsum_of_nonneg
        (fun k => hfk_nn k t ht)
        ((Real.summable_pow_div_factorial (W * Real.log t)).mul_left
          (g t * t ^ (-(3 + 1 : ℝ))) |>.congr
          (fun k => by simp only [fk, mul_pow]; ring)))
    -- IntegrableOn on finite pieces (bounded measurable on finite-measure set)
    have hσ₀_pos : 0 < σ₀ := by linarith
    have hfi : ∀ N : ℕ,
        IntegrableOn (fun t => g t * t ^ (-(σ₀ + 1))) (Ioc T₀ (T₀ + N)) := by
      intro N
      apply Integrable.mono'
        (integrableOn_const (C := D * T₀ ^ (-σ₀)) (hs := measure_Ioc_lt_top.ne))
      · exact (hg_meas.mul (measurable_id.pow measurable_const)).aestronglyMeasurable.restrict
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ⟨ht_low, _⟩
        have ht1 : 1 ≤ t := le_of_lt (lt_of_le_of_lt hT₀ ht_low)
        have ht_pos : 0 < t := by linarith
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (rpow_pos_of_pos ht_pos _)]
        calc |g t| * t ^ (-(σ₀ + 1))
            ≤ D * t * t ^ (-(σ₀ + 1)) :=
              mul_le_mul_of_nonneg_right (hg_le t ht1) (rpow_nonneg ht_pos.le _)
          _ = D * (t ^ (1 : ℝ) * t ^ (-(σ₀ + 1))) := by rw [rpow_one]; ring
          _ = D * t ^ (-σ₀) := by rw [← rpow_add ht_pos]; ring_nf
          _ ≤ D * T₀ ^ (-σ₀) := by
              apply mul_le_mul_of_nonneg_left _ hD.le
              rw [rpow_neg ht_pos.le, rpow_neg (by linarith : (0:ℝ) ≤ T₀)]
              exact (inv_le_inv₀ (rpow_pos_of_pos ht_pos _)
                (rpow_pos_of_pos (by linarith) _)).mpr
                (rpow_le_rpow (by linarith) (le_of_lt ht_low) hσ₀_pos.le)
    -- IntegrableOn ‖g*t^{-(σ₀+1)}‖ on finite pieces
    have hmain_int : ∀ N : ℕ,
        IntegrableOn (fun t => ‖g t * t ^ (-(σ₀ + 1))‖) (Ioc T₀ (T₀ + N)) :=
      fun N => (hfi N).norm
    -- Bounded partial integrals via abstract Tonelli
    open Aristotle.Standalone.LandauSigmaLessThanOneTonelliLIntegral in
    have hpartial := partial_integral_le_tsum_tail_coeffs
      g T₀ σ₀ (fun k t => fk k t) hfk_meas hfk_nn hmajorant hmain_int hfk_int hfk_sum
    -- IntegrableOn via bounded partial integrals
    have h_tendsto : Tendsto (fun n : ℕ => T₀ + (↑n : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ T₀ tendsto_natCast_atTop_atTop
    exact integrableOn_Ioi_of_intervalIntegral_norm_bounded
      (∑' k, ∫ t in Ioi T₀, fk k t) T₀ (fun N => hfi N) h_tendsto
      (by filter_upwards with N
          rw [intervalIntegral.integral_of_le (by linarith : T₀ ≤ T₀ + (↑N : ℝ))]
          exact hpartial N)

/-! ## Section 8: Parametric analyticity via dominated convergence

The complex Dirichlet integral F_pi(s) = s · ∫_{T₀}^∞ piGenFun(t) · t^{-(s+1)} dt
is analytic on {Re(s) > α}.

We use nonneg_dirichlet_integral_analyticOnNhd with β = 1 to get analyticity on
{Re > 1}, then extend to {Re > α} using the Pringsheim integrability. -/

/-- The complex Dirichlet integral of piGenFun is analytic on {Re > α}. -/
theorem pi_dirichlet_integral_analyticOnNhd
    (K_ext : ℂ → ℂ) (hK_diff : Differentiable ℂ K_ext)
    (hK_eq : ∀ s : ℂ, 1 < s.re →
        K_ext s = (∫ t in Ioi (2 : ℝ), (↑(t / Real.log t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
          + Complex.log (s - 1))
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : PiLiHardBound α C σ_sign)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ piGenFun C α σ_sign t) :
    AnalyticOnNhd ℂ
      (fun s => s * ∫ t in Ioi T₀, (↑(piGenFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
      {s : ℂ | α < s.re} := by
  -- Use DifferentiableOn.analyticOnNhd on the open half-plane {Re > α}
  have hopen : IsOpen {s : ℂ | α < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  rw [analyticOnNhd_iff_differentiableOn hopen]
  intro s₀ hs₀
  -- Product rule: s * F(s) where F(s) = ∫ g(t)·t^{-(s+1)}
  set g := piGenFun C α σ_sign with hg_def
  have hg_meas := piGenFun_measurable C α σ_sign
  apply DifferentiableAt.mul differentiableAt_id
    (show DifferentiableAt ℂ
      (fun s => ∫ t in Ioi T₀, (↑(g t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))) s₀ from ?_)
    |>.differentiableWithinAt
  -- Show the inner integral is ℂ-differentiable at s₀ via dominated convergence
  -- Pick ε = (Re(s₀) - α) / 4
  set ε := (s₀.re - α) / 4 with hε_def
  have hε : 0 < ε := by simp [hε_def]; linarith [show α < s₀.re from hs₀]
  set σ₁ := s₀.re - 2 * ε with hσ₁_def
  have hσ₁ : α < σ₁ := by simp [hσ₁_def, hε_def]; linarith
  -- Pringsheim-proved integrability at σ₁ (dominator for derivative)
  have h_dom := piGenFun_integrableOn_at_sigma K_ext hK_diff hK_eq
    C hC α hα hα1 σ_sign hσ hbound T₀ hT₀ hg_nn σ₁ hσ₁
  -- Integrability of integrand at s₀
  have h_int_s₀ := piGenFun_integrableOn_at_sigma K_ext hK_diff hK_eq
    C hC α hα hα1 σ_sign hσ hbound T₀ hT₀ hg_nn s₀.re (by linarith : α < s₀.re)
  -- Measure and integrand setup
  set μ := MeasureTheory.Measure.restrict volume (Ioi T₀) with hμ_def
  -- HasDerivAt for cpow chain: d/ds [↑(g t) · (↑t)^{-(s+1)}]
  --   = ↑(g t) · (↑t)^{-(s+1)} · log(↑t) · (-1)
  have h_cpow_deriv : ∀ t : ℝ, T₀ < t → ∀ s : ℂ,
      HasDerivAt (fun s => (↑(g t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
        ((↑(g t) : ℂ) * ((↑t : ℂ) ^ (-(s + 1)) * Complex.log (↑t) * (-1))) s := by
    intro t ht s
    have ht_ne : (↑t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith))
    have h_sub : HasDerivAt (fun s : ℂ => -(s + 1)) (-1) s :=
      ((hasDerivAt_id s).add_const (1 : ℂ)).neg
    exact (HasDerivAt.const_cpow h_sub (Or.inl ht_ne)).const_mul _
  -- Slit plane membership for t > 0
  have h_slit : ∀ t : ℝ, T₀ < t → (↑t : ℂ) ∈ Complex.slitPlane := by
    intro t ht; left; simp [Complex.ofReal_re]; linarith
  -- AEStronglyMeasurable for integrand
  have h_cpow_cont : ∀ s : ℂ, ContinuousOn
      (fun t : ℝ => (↑t : ℂ) ^ (-(s + 1))) (Ioi T₀) := fun s =>
    Complex.continuous_ofReal.continuousOn.cpow_const (fun t ht => h_slit t ht)
  have h_g_aesm : AEStronglyMeasurable (fun t : ℝ => ((g t : ℝ) : ℂ)) μ :=
    (Complex.measurable_ofReal.comp hg_meas).aestronglyMeasurable
  have h_aesm : ∀ s : ℂ, AEStronglyMeasurable
      (fun t : ℝ => ((g t : ℝ) : ℂ) * (↑t : ℂ) ^ (-(s + 1))) μ := fun s =>
    h_g_aesm.mul ((h_cpow_cont s).aestronglyMeasurable measurableSet_Ioi)
  -- Complex integrand integrability at s₀ (from real integrability)
  have h_F_int : Integrable (fun t => (↑(g t) : ℂ) * (↑t : ℂ) ^ (-(s₀ + 1))) μ := by
    apply h_int_s₀.mono' (h_aesm s₀)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := by linarith [show T₀ < t from ht]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    rw [abs_of_nonneg (hg_nn t (le_of_lt ht))]
  -- Norm bound on derivative: ‖F'(s,t)‖ ≤ (1/ε) · g(t) · t^{-(σ₁+1)}
  have h_bound : ∀ᵐ t ∂μ, ∀ s ∈ Metric.ball s₀ ε,
      ‖(↑(g t) : ℂ) * ((↑t : ℂ) ^ (-(s + 1)) * Complex.log (↑t) * (-1))‖ ≤
        (1 / ε) * (g t * t ^ (-(σ₁ + 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s hs
    have ht_T₀ : T₀ < t := ht
    have ht_pos : 0 < t := by linarith
    have ht1 : 1 ≤ t := by linarith
    -- Factor norms
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hg_nn t (le_of_lt ht)),
      Complex.norm_cpow_eq_rpow_re_of_pos ht_pos,
      show Complex.log (↑t) = ↑(Real.log t) from (Complex.ofReal_log (le_of_lt ht_pos)).symm,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg ht1),
      norm_neg, norm_one]
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    -- σ_low = s₀.re - ε: lower bound on Re(s) for s ∈ ball(s₀, ε)
    have h_re : s₀.re - ε < s.re := by
      have h_dist : dist s s₀ < ε := Metric.mem_ball.mp hs
      have h_abs_re : |s.re - s₀.re| ≤ dist s s₀ := by
        calc |s.re - s₀.re| = |(s - s₀).re| := by congr 1
          _ ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
          _ = dist s s₀ := (dist_eq_norm s s₀).symm
      linarith [(abs_lt.mp (h_abs_re.trans_lt h_dist)).1]
    -- t^{-(Re(s)+1)} ≤ t^{-(σ_low+1)} where σ_low = s₀.re - ε
    -- because Re(s) ≥ σ_low and t ≥ 1
    have h_exp_le : t ^ (-(s.re + 1)) ≤ t ^ (-(s₀.re - ε + 1)) :=
      rpow_le_rpow_of_exponent_le ht1 (by linarith)
    -- log(t) ≤ t^ε / ε from log_le_rpow_div
    have h_log_le : Real.log t ≤ t ^ ε / ε :=
      Real.log_le_rpow_div (le_of_lt ht_pos) hε
    -- Key: t^{-(σ_low+1)} * t^ε = t^{-(σ₁+1)} since σ₁ = σ_low - ε
    have h_rpow_combine : t ^ (-(s₀.re - ε + 1)) * t ^ ε = t ^ (-(σ₁ + 1)) := by
      rw [← rpow_add ht_pos]; congr 1; simp [hσ₁_def, hε_def]; ring
    -- Combine: g(t) · t^{-(Re(s)+1)} · log(t) ≤ (1/ε) · g(t) · t^{-(σ₁+1)}
    have hg_t : 0 ≤ g t := hg_nn t ht_T₀.le
    -- Normalize to standard form for calc
    show g t * (t ^ (-(s.re + 1)) * Real.log t * 1) ≤
      (1 / ε) * (g t * t ^ (-(σ₁ + 1)))
    calc g t * (t ^ (-(s.re + 1)) * Real.log t * 1)
        = g t * (t ^ (-(s.re + 1)) * Real.log t) := by ring
      _ ≤ g t * (t ^ (-(s₀.re - ε + 1)) * (t ^ ε / ε)) := by
          apply mul_le_mul_of_nonneg_left _ hg_t
          apply mul_le_mul h_exp_le h_log_le (Real.log_nonneg ht1)
            (rpow_nonneg ht_pos.le _)
      _ = (1 / ε) * (g t * (t ^ (-(s₀.re - ε + 1)) * t ^ ε)) := by ring
      _ = (1 / ε) * (g t * t ^ (-(σ₁ + 1))) := by rw [h_rpow_combine]
  -- Integrability of the bound
  have h_bound_int : Integrable (fun t => (1 / ε) * (g t * t ^ (-(σ₁ + 1)))) μ :=
    h_dom.const_mul (1 / ε)
  -- AEStronglyMeasurable for derivative at s₀
  have h_log_meas : Measurable Real.log :=
    measurable_of_measurable_on_compl_singleton 0 Real.continuous_log.measurable
  have h_F'_meas : AEStronglyMeasurable
      (fun t => (↑(g t) : ℂ) * ((↑t : ℂ) ^ (-(s₀ + 1)) * Complex.log (↑t) * (-1))) μ := by
    apply AEStronglyMeasurable.mul h_g_aesm
    apply AEStronglyMeasurable.mul
    · apply AEStronglyMeasurable.mul
      · exact (h_cpow_cont s₀).aestronglyMeasurable measurableSet_Ioi
      · exact (Complex.continuous_ofReal.continuousOn.clog
          (fun t ht => h_slit t ht)).aestronglyMeasurable measurableSet_Ioi
    · exact aestronglyMeasurable_const
  -- Apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s₀ hε)
    (Eventually.of_forall fun s => h_aesm s)
    h_F_int h_F'_meas h_bound h_bound_int
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s _hs
        exact h_cpow_deriv t ht s)).2.differentiableAt

/-- Complex Dirichlet integral identity: For Re(s) > 1,
  s · ∫_{Ioi 1} ↑(piGenFun t) · (↑t)^{-(s+1)} =
    ↑C · s/(s - ↑α) − ↑σ_sign · primeZeta(s) + ↑σ_sign · (K_ext(s) − Complex.log(s − 1))

Derived from piGenFun_integral_eq_piCF_div (real version) via the identity theorem:
both sides are analytic on {Re > 1} and agree on the real interval (2, ∞). -/
theorem piGenFun_complex_integral_identity (K_ext : ℂ → ℂ)
    (hK_diff : Differentiable ℂ K_ext)
    (hK_eq : ∀ s : ℂ, 1 < s.re →
        K_ext s = (∫ t in Ioi (2 : ℝ), (↑(t / Real.log t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
          + Complex.log (s - 1))
    (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : PiLiHardBound α C σ_sign)
    (T₀ : ℝ) (hT₀ : 1 ≤ T₀)
    (hg_nn : ∀ t, T₀ ≤ t → 0 ≤ piGenFun C α σ_sign t)
    (s : ℂ) (hs : 1 < s.re) :
    s * ∫ t in Ioi (1 : ℝ), (↑(piGenFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)) =
      (↑C : ℂ) * s / (s - (↑α : ℂ)) - (↑σ_sign : ℂ) * primeZeta s +
      (↑σ_sign : ℂ) * (K_ext s - Complex.log (s - 1)) := by
  -- Strategy: identity theorem on {Re > 1}.
  -- Both sides are analytic and agree for real σ > 2 (piGenFun_integral_eq_piCF_div).
  set LHS : ℂ → ℂ := fun s =>
    s * ∫ t in Ioi (1 : ℝ), (↑(piGenFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))
  set RHS : ℂ → ℂ := fun s =>
    (↑C : ℂ) * s / (s - (↑α : ℂ)) - (↑σ_sign : ℂ) * primeZeta s +
    (↑σ_sign : ℂ) * (K_ext s - Complex.log (s - 1))
  suffices h : LHS s = RHS s by exact h
  set U : Set ℂ := {s : ℂ | 1 < s.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_preconn : IsPreconnected U := (convex_halfSpace_re_gt 1).isPreconnected
  have h3_mem : (3 : ℂ) ∈ U := by
    show 1 < (3 : ℂ).re; simp [Complex.ofReal_re]
  -- LHS analytic on U: split ∫_{Ioi 1} = ∫_{Icc 1 T₀} + ∫_{Ioi T₀}
  -- Use: s * ∫_{Ioi T₀} is analytic (pi_dirichlet_integral_analyticOnNhd)
  --      s * ∫_{Icc 1 T₀} is analytic (compact_integral_complex_differentiable)
  have hU_sub : U ⊆ {s : ℂ | α < s.re} := fun s hs => lt_trans hα1 hs
  have hg_meas := piGenFun_measurable C α σ_sign
  have hg_bound := piGenFun_le_linear C hC α (by linarith : α ≤ 1) σ_sign hσ
  have hLHS_anal : AnalyticOnNhd ℂ LHS U := by
    -- LHS(s) = s * ∫_{Icc 1 T₀} f + s * ∫_{Ioi T₀} f (where they split)
    -- The tail s * ∫_{Ioi T₀} is analytic on {Re > α} ⊃ U
    have hF_anal := (pi_dirichlet_integral_analyticOnNhd K_ext hK_diff hK_eq C hC α hα hα1
      σ_sign hσ hbound T₀ hT₀ hg_nn).mono hU_sub
    -- The compact part s * ∫_{Icc 1 T₀} is entire
    have hfinite_diff := compact_integral_complex_differentiable
      (piGenFun C α σ_sign) T₀ hT₀ hg_meas hg_bound
    have hfinite_anal : AnalyticOnNhd ℂ
        (fun s => s * ∫ t in Icc (1 : ℝ) T₀,
          (↑(piGenFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))) U :=
      fun s _ => (analyticAt_id.mul (hfinite_diff.analyticAt s))
    -- Sum: LHS = finite + tail. Need to verify the splitting.
    -- For this, we show LHS = finite + tail on U and both are analytic
    exact (hfinite_anal.add hF_anal).congr hU_open (fun s hs => by
      simp only [Pi.add_apply, LHS]
      rw [← mul_add]
      congr 1
      -- ∫_{Ioi 1} = ∫_{Icc 1 T₀} + ∫_{Ioi T₀}
      obtain ⟨D, hD, hg_le⟩ := hg_bound
      have hs_re : 1 < s.re := hs
      -- Measurability helper for complex integrand
      have hf_aesm : ∀ (S : Set ℝ) (_ : MeasurableSet S) (_ : ∀ t ∈ S, (0:ℝ) < t),
          AEStronglyMeasurable (fun t : ℝ =>
            (↑(piGenFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
            (volume.restrict S) :=
        fun S hS h_pos => AEStronglyMeasurable.mul
          ((measurable_ofReal.comp hg_meas).aestronglyMeasurable)
          (ContinuousOn.aestronglyMeasurable (fun t ht =>
            (continuousAt_ofReal_cpow_const t (-(s + 1))
              (Or.inr (ne_of_gt (h_pos t ht)))).continuousWithinAt) hS)
      -- IntegrableOn on Icc 1 T₀ (bounded on compact)
      have hf_Icc : IntegrableOn (fun t : ℝ =>
          (↑(piGenFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
          (Icc (1 : ℝ) T₀) :=
        ⟨hf_aesm _ measurableSet_Icc (fun t ht => by linarith [ht.1]),
         HasFiniteIntegral.restrict_of_bounded (D * T₀) isCompact_Icc.measure_lt_top
          (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ⟨ht1, htT₀⟩
              have ht_pos : (0:ℝ) < t := by linarith
              have h1 : ‖(↑(piGenFun C α σ_sign t) : ℂ)‖ = |piGenFun C α σ_sign t| :=
                RCLike.norm_ofReal _
              have h2 : ‖(↑t : ℂ) ^ (-(s + 1))‖ ≤ 1 := by
                rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
                exact rpow_le_one_of_one_le_of_nonpos ht1
                  (by simp only [neg_add_rev, neg_neg, add_re, one_re, neg_re]; linarith)
              calc ‖(↑(piGenFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))‖
                  = ‖(↑(piGenFun C α σ_sign t) : ℂ)‖ * ‖(↑t : ℂ) ^ (-(s + 1))‖ := norm_mul _ _
                _ ≤ D * t * 1 := by
                    rw [h1]; exact mul_le_mul (hg_le t ht1) h2 (norm_nonneg _) (by positivity)
                _ ≤ D * T₀ := by nlinarith)⟩
      -- IntegrableOn on Ioi T₀ (dominated by D * t^{-s.re})
      have hf_Ioi_T₀ : IntegrableOn (fun t : ℝ =>
          (↑(piGenFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
          (Ioi T₀) := by
        have h_dom : IntegrableOn (fun t : ℝ => D * t ^ (-s.re)) (Ioi T₀) :=
          (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re < -1)
            (by linarith : (0:ℝ) < T₀)).const_mul D
        exact h_dom.mono'
          (hf_aesm _ measurableSet_Ioi (fun t ht => by linarith [show T₀ < t from ht]))
          (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              have ht1 : 1 ≤ t := by linarith [show T₀ < t from ht]
              have ht_pos : (0:ℝ) < t := by linarith
              have h1 : ‖(↑(piGenFun C α σ_sign t) : ℂ)‖ = |piGenFun C α σ_sign t| :=
                RCLike.norm_ofReal _
              have h2 : ‖(↑t : ℂ) ^ (-(s + 1))‖ = t ^ (-(s + 1)).re :=
                Complex.norm_cpow_eq_rpow_re_of_pos ht_pos _
              calc ‖(↑(piGenFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))‖
                  = ‖(↑(piGenFun C α σ_sign t) : ℂ)‖ * ‖(↑t : ℂ) ^ (-(s + 1))‖ := norm_mul _ _
                _ = |piGenFun C α σ_sign t| * t ^ (-(s + 1)).re := by rw [h1, h2]
                _ ≤ D * t * t ^ (-(s + 1)).re :=
                    mul_le_mul_of_nonneg_right (hg_le t ht1)
                      (rpow_nonneg ht_pos.le _)
                _ = D * (t ^ (1 : ℝ) * t ^ (-(s + 1)).re) := by rw [rpow_one]; ring
                _ = D * t ^ ((1 : ℝ) + (-(s + 1)).re) := by
                    rw [← rpow_add ht_pos]
                _ = D * t ^ (-s.re) := by
                    congr 1; simp [neg_add_rev, add_re, one_re, neg_re])
      -- Split: Icc 1 T₀ ∪ Ioi T₀ = Ici 1 ≈ Ioi 1
      have h_disj : Disjoint (Icc (1:ℝ) T₀) (Ioi T₀) :=
        Set.disjoint_left.mpr (fun _ ⟨_, ht⟩ h => not_lt.mpr ht h)
      have h_split := setIntegral_union h_disj measurableSet_Ioi hf_Icc hf_Ioi_T₀
      rw [Icc_union_Ioi_eq_Ici hT₀, integral_Ici_eq_integral_Ioi] at h_split
      exact h_split.symm)
  -- RHS analytic on U
  have hRHS_anal : AnalyticOnNhd ℂ RHS U := by
    intro s₀ hs₀
    show AnalyticAt ℂ RHS s₀
    simp only [RHS]
    -- C*s/(s-α) is analytic (s-α ≠ 0 on U)
    have hne : s₀ - (↑α : ℂ) ≠ 0 := by
      intro h; have := congr_arg Complex.re h; simp at this
      have : 1 < s₀.re := hs₀; linarith
    have h1 : AnalyticAt ℂ (fun s => (↑C : ℂ) * s / (s - (↑α : ℂ))) s₀ :=
      ((analyticAt_const (𝕜 := ℂ)).mul analyticAt_id).div
        (analyticAt_id.sub analyticAt_const) hne
    -- primeZeta is analytic on {Re > 1}: use midpoint α' = (1 + s₀.re)/2
    have hs₀' : 1 < s₀.re := hs₀
    have hα' : (1 : ℝ) < (1 + s₀.re) / 2 := by linarith
    have h2 := primeZeta_analyticOnNhd ((1 + s₀.re) / 2) hα' s₀
      (show (1 + s₀.re) / 2 < s₀.re from by linarith)
    -- K_ext is entire
    have h3 := hK_diff.analyticAt s₀
    -- Complex.log(s-1) is analytic when s-1 ∈ slitPlane (Re(s-1) > 0 suffices)
    have h4 : AnalyticAt ℂ (fun s => Complex.log (s - 1)) s₀ := by
      apply AnalyticAt.clog (analyticAt_id.sub analyticAt_const)
      rw [Complex.mem_slitPlane_iff]
      left; simp; linarith
    -- Assembly: RHS = C*s/(s-α) - σ_sign * primeZeta + σ_sign * (K_ext - log(s-1))
    exact ((h1.sub (analyticAt_const.mul h2)).add
      (analyticAt_const.mul (h3.sub h4)))
  -- Agreement for real σ > 2: LHS(↑σ) = RHS(↑σ)
  have h_agree : ∀ σ' : ℝ, 2 < σ' → LHS (↑σ') = RHS (↑σ') := by
    intro σ' hσ'
    have hσ'1 : 1 < σ' := by linarith
    have hσ'_pos : (0 : ℝ) < σ' := by linarith
    -- Bridge: complex piGenFun integral at ↑σ' = ↑(real integral)
    have h_int_congr : ∀ t ∈ Ioi (1 : ℝ),
        (↑(piGenFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-((↑σ' : ℂ) + 1)) =
        ((piGenFun C α σ_sign t * t ^ (-(σ' + 1)) : ℝ) : ℂ) := by
      intro t ht
      have ht_pos : (0 : ℝ) ≤ t := by linarith [show (1:ℝ) < t from ht]
      rw [show -((↑σ' : ℂ) + 1) = ((-(σ' + 1) : ℝ) : ℂ) from by push_cast; ring,
        show (↑t : ℂ) ^ ((-(σ' + 1) : ℝ) : ℂ) = ((t ^ (-(σ' + 1)) : ℝ) : ℂ) from
          (Complex.ofReal_cpow ht_pos _).symm]
      norm_cast
    have h_int_bridge : ∫ t in Ioi (1 : ℝ),
        (↑(piGenFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-((↑σ' : ℂ) + 1)) =
        ↑(∫ t in Ioi (1 : ℝ), piGenFun C α σ_sign t * t ^ (-(σ' + 1))) := by
      rw [setIntegral_congr_fun measurableSet_Ioi h_int_congr]
      exact integral_ofReal
    -- primeZeta(↑σ') is real-valued (= ↑(its .re))
    have h_pz_real : primeZeta (↑σ') = ↑((primeZeta (↑σ')).re) := by
      have h_pz := primeZeta_eq_primeCounting_integral
        (show 1 < (↑σ' : ℂ).re by simp; exact hσ'1)
      have h_pz_congr : ∀ t ∈ Ioi (1 : ℝ),
          (↑(Nat.primeCounting ⌊t⌋₊) : ℂ) * (↑t : ℂ) ^ (-((↑σ' : ℂ) + 1)) =
          (((↑(Nat.primeCounting ⌊t⌋₊) : ℝ) * t ^ (-(σ' + 1)) : ℝ) : ℂ) := by
        intro t ht
        have ht_pos : (0 : ℝ) ≤ t := by linarith [show (1:ℝ) < t from ht]
        rw [show -((↑σ' : ℂ) + 1) = ((-(σ' + 1) : ℝ) : ℂ) from by push_cast; ring,
          show (↑t : ℂ) ^ ((-(σ' + 1) : ℝ) : ℂ) = ((t ^ (-(σ' + 1)) : ℝ) : ℂ) from
            (Complex.ofReal_cpow ht_pos _).symm]
        norm_cast
      have h_pz_bridge : ∫ t in Ioi (1 : ℝ),
          (↑(Nat.primeCounting ⌊t⌋₊) : ℂ) * (↑t : ℂ) ^ (-((↑σ' : ℂ) + 1)) =
          ↑(∫ t in Ioi (1 : ℝ), (↑(Nat.primeCounting ⌊t⌋₊) : ℝ) * t ^ (-(σ' + 1))) := by
        rw [setIntegral_congr_fun measurableSet_Ioi h_pz_congr]
        exact integral_ofReal
      rw [h_pz, h_pz_bridge, ← Complex.ofReal_mul, Complex.ofReal_re]
    -- K_ext(↑σ') - Complex.log(↑σ'-1) is real-valued
    have h_kl_real : K_ext (↑σ') - Complex.log ((↑σ' : ℂ) - 1) =
        ↑((K_ext (↑σ') - Complex.log ((↑σ' : ℂ) - 1)).re) := by
      have h_cpx : K_ext (↑σ') - Complex.log ((↑σ' : ℂ) - 1) =
          ∫ t in Ioi (2 : ℝ), (↑(t / Real.log t) : ℂ) * (↑t : ℂ) ^ (-((↑σ' : ℂ) + 1)) := by
        rw [hK_eq (↑σ') (by simp; exact hσ'1), add_sub_cancel_right]
      have h_kl_congr : ∀ t ∈ Ioi (2 : ℝ),
          (↑(t / Real.log t) : ℂ) * (↑t : ℂ) ^ (-((↑σ' : ℂ) + 1)) =
          (((t / Real.log t) * t ^ (-(σ' + 1)) : ℝ) : ℂ) := by
        intro t ht
        have ht_pos : (0 : ℝ) ≤ t := by linarith [show (2:ℝ) < t from ht]
        rw [show -((↑σ' : ℂ) + 1) = ((-(σ' + 1) : ℝ) : ℂ) from by push_cast; ring,
          show (↑t : ℂ) ^ ((-(σ' + 1) : ℝ) : ℂ) = ((t ^ (-(σ' + 1)) : ℝ) : ℂ) from
            (Complex.ofReal_cpow ht_pos _).symm]
        push_cast; ring
      have h_kl_bridge : ∫ t in Ioi (2 : ℝ),
          (↑(t / Real.log t) : ℂ) * (↑t : ℂ) ^ (-((↑σ' : ℂ) + 1)) =
          ↑(∫ t in Ioi (2 : ℝ), (t / Real.log t) * t ^ (-(σ' + 1))) := by
        rw [setIntegral_congr_fun measurableSet_Ioi h_kl_congr]
        exact integral_ofReal
      rw [h_cpx, h_kl_bridge, Complex.ofReal_re]
    -- Real identity: ∫ piGenFun * rpow = piCF/σ'
    have h_real := piGenFun_integral_eq_piCF_div K_ext hK_diff hK_eq C hC α hα hα1
      σ_sign hσ σ' hσ'
    -- Simplify σ' * (piCF/σ') = piCF at the real level
    have h_piCF : σ' * (piCF K_ext C α σ_sign σ' / σ') = piCF K_ext C α σ_sign σ' :=
      mul_div_cancel₀ _ hσ'_pos.ne'
    -- Assemble: LHS(↑σ') = ↑piCF, then show ↑piCF = RHS(↑σ')
    simp only [LHS, RHS]
    rw [h_int_bridge, h_pz_real, h_kl_real, ← Complex.ofReal_mul, h_real, h_piCF]
    -- Goal: ↑piCF = ↑C * ↑σ' / (↑σ' - ↑α) - ↑σ_sign * ↑(pz_re) + ↑σ_sign * ↑(kl_re)
    -- Reduce to real equality via ofReal injectivity
    -- Factor RHS into single ofReal
    rw [← Complex.ofReal_mul C σ', ← Complex.ofReal_sub σ' α, ← Complex.ofReal_div,
      ← Complex.ofReal_mul σ_sign, ← Complex.ofReal_mul σ_sign,
      ← Complex.ofReal_sub, ← Complex.ofReal_add]
    congr 1
    -- Real equality: piCF = C*σ'/(σ'-α) - σ_sign*pz_re + σ_sign*kl_re
    -- Use algebraic_bridge + (K_ext-log).re = K_ext.re - log(σ'-1)
    have h_alg := algebraic_bridge σ' hσ'
    have h_re_split : (K_ext (↑σ') - Complex.log ((↑σ' : ℂ) - 1)).re =
        (K_ext (↑σ')).re - Real.log (σ' - 1) := by
      rw [Complex.sub_re, show (↑σ' : ℂ) - 1 = ↑(σ' - 1) from by push_cast; ring,
        ← Complex.ofReal_log (show 0 ≤ σ' - 1 by linarith), Complex.ofReal_re]
    unfold piCF
    -- Cancel C*σ'/(σ'-α) and reduce to σ_sign equation
    suffices σ_sign * ((correctionTerm (↑σ')).re + (K_ext (↑σ')).re -
        Real.log (Complex.normSq (zrf (↑σ'))) / 2) =
        -σ_sign * (primeZeta (↑σ')).re +
        σ_sign * (K_ext (↑σ') - Complex.log ((↑σ' : ℂ) - 1)).re by linarith
    rw [h_re_split]
    linear_combination σ_sign * h_alg
  -- Closure: 3 ∈ closure({z | LHS z = RHS z} \ {3})
  have h_closure : (3 : ℂ) ∈ closure ({z | LHS z = RHS z} \ {(3 : ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set δ := min (ε / 2) 1 with hδ_def
    have hδ_pos : 0 < δ := lt_min (by linarith) one_pos
    refine ⟨↑(3 + δ), ⟨h_agree (3 + δ) (by linarith), ?_⟩, ?_⟩
    · -- ↑(3 + δ) ≠ (3 : ℂ)
      intro h; have := congr_arg Complex.re h; simp at this; linarith
    · -- dist < ε
      rw [dist_comm]
      calc dist (↑(3 + δ) : ℂ) (3 : ℂ)
          = ‖(↑(3 + δ) : ℂ) - (3 : ℂ)‖ := dist_eq_norm _ _
        _ = ‖(↑δ : ℂ)‖ := by congr 1; push_cast; ring
        _ = |δ| := by rw [Complex.norm_real, Real.norm_eq_abs]
        _ = δ := abs_of_pos hδ_pos
        _ ≤ ε / 2 := min_le_left _ _
        _ < ε := by linarith
  -- Identity theorem (closure version)
  have h_eqOn := hLHS_anal.eqOn_of_preconnected_of_mem_closure
    hRHS_anal hU_preconn h3_mem h_closure
  exact h_eqOn hs

/-! ## Section 9: Q construction and verification

Construct Q(s) = primeZeta(s) + log(s-1) on {Re > α} from the Dirichlet integral. -/

/-- **Main theorem**: primeZeta(s) + log(s-1) extends analytically to {Re > α}
under PiLiHardBound. -/
theorem primeZeta_plus_log_extends_of_piLiHardBound
    (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (C : ℝ) (hC : 0 < C)
    (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : PiLiHardBound α C σ_sign) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        Q s = primeZeta s + Complex.log (s - 1) := by
  -- Step 0: Extract T₀ from PiLiHardBound
  have hev := piGenFun_eventually_nonneg α C σ_sign hbound
  obtain ⟨T₀', hT₀'⟩ := (Filter.eventually_atTop.mp hev)
  set T₀ := max T₀' 1 with hT₀_def
  have hT₀ : 1 ≤ T₀ := le_max_right T₀' 1
  have hg_nn : ∀ t, T₀ ≤ t → 0 ≤ piGenFun C α σ_sign t := by
    intro t ht
    exact hT₀' t (le_trans (le_max_left T₀' 1) ht)
  -- Step 1: Get K_ext from E₁ cancellation
  obtain ⟨K_ext, hK_diff, hK_eq⟩ :=
    Aristotle.Standalone.E1CancellationProof.li_mellin_plus_log_extends
  -- Step 2: The Dirichlet integral F_pi is analytic on {Re > α}
  have hF_anal := pi_dirichlet_integral_analyticOnNhd K_ext hK_diff hK_eq
    C hC α hα hα1 σ_sign hσ hbound T₀ hT₀ hg_nn
  -- Step 3: Define Q by rearranging:
  -- On {Re > 1}: s·∫ piGenFun·t^{-(s+1)} = C·s/(s-α) - σ_sign·primeZeta(s)
  --              + σ_sign·(K_ext(s) - log(s-1)) + boundary
  -- So: primeZeta + log(s-1) = σ_sign·[C·s/(s-α) + K_ext(s) - F_pi(s)] + boundary
  -- Define Q(s) using the analytic pieces
  set F_pi := fun s : ℂ => s * ∫ t in Ioi T₀,
    (↑(piGenFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))
  -- Q(s) = K_ext(s) + σ_sign · [C·s/(s-α) - F_pi(s)]
  -- plus boundary terms from splitting ∫_{Ioi 1} = ∫_{Icc 1 T₀} + ∫_{Ioi T₀}
  -- For now, construct Q directly:
  set Q := fun s : ℂ =>
    K_ext s + (↑σ_sign : ℂ) * ((↑C : ℂ) * s / (s - (↑α : ℂ)) - F_pi s) -
    (↑σ_sign : ℂ) * s * ∫ t in Icc (1 : ℝ) T₀,
      (↑(piGenFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))
  refine ⟨Q, ?_, ?_⟩
  · -- Q is analytic on {Re > α}
    have hopen : IsOpen {s : ℂ | α < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    -- K_ext is entire
    have hK_anal : AnalyticOnNhd ℂ K_ext {s | α < s.re} :=
      fun s _ => hK_diff.analyticAt s
    -- C·s/(s-α) is analytic on {Re > α}
    have hfrac_anal : AnalyticOnNhd ℂ
        (fun s => (↑C : ℂ) * s / (s - (↑α : ℂ))) {s | α < s.re} := by
      intro s (hs : α < s.re)
      have h_ne : s - (↑α : ℂ) ≠ 0 := by
        intro h; have := congr_arg Complex.re h; simp at this; linarith
      exact (analyticAt_const.mul analyticAt_id).div
        (analyticAt_id.sub analyticAt_const) h_ne
    -- F_pi is analytic on {Re > α} (from step 2)
    -- Finite integral is analytic on {Re > α} (compact domain, analytic integrand)
    have hfinite_anal : AnalyticOnNhd ℂ
        (fun (s : ℂ) => ∫ t in Icc (1 : ℝ) T₀,
          (↑(piGenFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
        {s : ℂ | α < s.re} := fun s _ =>
      (compact_integral_complex_differentiable (piGenFun C α σ_sign) T₀ hT₀
        (piGenFun_measurable C α σ_sign)
        (piGenFun_le_linear C hC α (by linarith : α ≤ 1) σ_sign hσ)).analyticAt s
    -- Combine: Q = K_ext + σ_sign * (frac - F_pi) - σ_sign * s * finite
    intro s hs
    show AnalyticAt ℂ Q s
    simp only [Q]
    exact ((hK_anal s hs).add (analyticAt_const.mul
      ((hfrac_anal s hs).sub (hF_anal s hs)))).sub
      ((analyticAt_const.mul analyticAt_id).mul (hfinite_anal s hs))
  · -- Q(s) = primeZeta(s) + log(s-1) for Re(s) > 1
    intro s hs
    -- Step A: Use the complex integral identity (∫ over Ioi 1)
    have h_identity := piGenFun_complex_integral_identity K_ext hK_diff hK_eq C hC α hα hα1
      σ_sign hσ hbound T₀ hT₀ hg_nn s hs
    -- Step B: Split ∫_{Ioi 1} = ∫_{Icc 1 T₀} + ∫_{Ioi T₀} (complex integrals)
    have h_disj : Disjoint (Icc (1 : ℝ) T₀) (Ioi T₀) :=
      Set.disjoint_left.mpr (fun _ ⟨_, ht⟩ h => not_lt.mpr ht h)
    obtain ⟨D, hD, hg_le⟩ := piGenFun_le_linear C hC α (by linarith : α ≤ 1) σ_sign hσ
    have hg_meas := piGenFun_measurable C α σ_sign
    set f := fun t : ℝ => (↑(piGenFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))
    -- Complex-valued AEStronglyMeasurable of piGenFun
    have h_g_aesm : ∀ (S : Set ℝ), AEStronglyMeasurable
        (fun t : ℝ => (↑(piGenFun C α σ_sign t) : ℂ)) (volume.restrict S) :=
      fun _ => (Complex.measurable_ofReal.comp hg_meas).aestronglyMeasurable
    -- IntegrableOn on Icc 1 T₀ (bounded on compact)
    have hf_Icc : IntegrableOn f (Icc 1 T₀) := by
      apply Integrable.mono'
        (integrableOn_const (C := D * T₀) (hs := isCompact_Icc.measure_lt_top.ne))
      · exact (h_g_aesm _).mul
          ((Complex.continuous_ofReal.continuousOn.cpow_const
            (fun t (ht : t ∈ Icc 1 T₀) => by left; simp; linarith [ht.1])).aestronglyMeasurable
            measurableSet_Icc)
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ⟨ht1, htT₀⟩
        simp only [f]
        rw [norm_mul]
        have ht_pos : 0 < t := by linarith
        have h1 : ‖(↑(piGenFun C α σ_sign t) : ℂ)‖ ≤ D * T₀ := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact (hg_le t ht1).trans (by nlinarith)
        have h2 : ‖(↑t : ℂ) ^ (-(s + 1))‖ ≤ 1 := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
          simp only [neg_add_rev, neg_re, add_re, one_re]
          apply Real.rpow_le_one_of_one_le_of_nonpos ht1; linarith
        calc ‖(↑(piGenFun C α σ_sign t) : ℂ)‖ * ‖(↑t : ℂ) ^ (-(s + 1))‖
            ≤ (D * T₀) * 1 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          _ = D * T₀ := mul_one _
    -- IntegrableOn on Ioi T₀ (dominated by D * t^{-Re(s)})
    have hf_Ioi : IntegrableOn f (Ioi T₀) := by
      have h_bound : IntegrableOn (fun t : ℝ => D * t ^ (-(s.re : ℝ))) (Ioi T₀) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re : ℝ) < -1)
          (by linarith : (0 : ℝ) < T₀)).const_mul D
      apply h_bound.mono'
      · exact (h_g_aesm _).mul
          ((Complex.continuous_ofReal.continuousOn.cpow_const
            (fun t (ht : t ∈ Ioi T₀) => by left; simp; linarith [show T₀ < t from ht])).aestronglyMeasurable
            measurableSet_Ioi)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        simp only [f]
        rw [norm_mul]
        have ht_pos : 0 < t := by linarith [show T₀ < t from ht]
        have ht1 : 1 ≤ t := by linarith [show T₀ < t from ht]
        have h1 : ‖(↑(piGenFun C α σ_sign t) : ℂ)‖ ≤ D * t := by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact hg_le t ht1
        have h2 : ‖(↑t : ℂ) ^ (-(s + 1))‖ = t ^ (-(s.re + 1)) := by
          have := Complex.norm_cpow_eq_rpow_re_of_pos ht_pos (y := -(s + 1))
          simp only [neg_add_rev, neg_re, add_re, one_re] at this
          rw [show -(s + 1 : ℂ) = -1 + -s from by ring,
              show -(s.re + 1) = -1 + -s.re from by ring]
          exact this
        rw [h2]
        calc ‖(↑(piGenFun C α σ_sign t) : ℂ)‖ * t ^ (-(s.re + 1))
            ≤ D * t * t ^ (-(s.re + 1)) :=
              mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht_pos.le _)
          _ = D * (t ^ (1 : ℝ) * t ^ (-(s.re + 1))) := by rw [Real.rpow_one]; ring
          _ = D * t ^ (1 + (-(s.re + 1))) := by rw [← Real.rpow_add ht_pos]
          _ = D * t ^ (-(s.re : ℝ)) := by ring_nf
    have h_split := setIntegral_union h_disj measurableSet_Ioi hf_Icc hf_Ioi
    rw [Icc_union_Ioi_eq_Ici hT₀, integral_Ici_eq_integral_Ioi] at h_split
    -- h_split: ∫_{Ioi 1} f = ∫_{Icc 1 T₀} f + ∫_{Ioi T₀} f
    rw [h_split, mul_add] at h_identity
    -- Step C: σ_sign² = 1
    have hσ_sq : (↑σ_sign : ℂ) * (↑σ_sign : ℂ) = 1 := by
      rcases hσ with rfl | rfl <;> simp <;> ring
    -- Step D: Algebraic verification via case split on σ_sign
    -- Q(s) = K_ext + σ*(C*s/(s-α) - s*∫_{Ioi T₀}) - σ*s*∫_{Icc}
    -- h_identity: s*∫_{Icc} + s*∫_{Ioi T₀} = C*s/(s-α) - σ*primeZeta + σ*(K_ext - log)
    -- After substitution and σ² = 1 cancellation: Q = primeZeta + log
    -- Easiest approach: case split on σ_sign = 1 or σ_sign = -1, then linear_combination
    show Q s = primeZeta s + Complex.log (s - 1)
    simp only [Q, F_pi]
    set A := ∫ t in Icc (1 : ℝ) T₀, f t
    set B := ∫ t in Ioi T₀, f t
    change s * A + s * B =
      (↑C : ℂ) * s / (s - ↑α) - ↑σ_sign * primeZeta s +
      ↑σ_sign * (K_ext s - Complex.log (s - 1)) at h_identity
    -- Algebra: Q = K + σ*(C*s/(s-α) - s*B) - σ*s*A
    -- From h_identity after split: s*A + s*B = C*s/(s-α) - σ*P + σ*(K-L)
    -- So: C*s/(s-α) - s*B = s*A + s*B + (C*s/(s-α) - s*A - s*B) - s*B
    --   ... skip the algebra and just prove the goal directly.
    -- Key insight: Q - (P+L) = K + σ*(C/(s-α)-s*B) - σ*s*A - P - L
    -- Sub C/(s-α) = s*A + s*B + σ*P - σ*(K-L):
    -- = K + σ*(s*A + s*B + σ*P - σ*(K-L) - s*B) - σ*s*A - P - L
    -- = K + σ*(s*A + σ*P - σ*K + σ*L) - σ*s*A - P - L
    -- = K + σ*s*A + σ²*P - σ²*K + σ²*L - σ*s*A - P - L
    -- = K(1-σ²) + P(σ²-1) + L(σ²-1) = 0 for σ²=1
    -- Prove using: substitute h_identity (C*s/(s-α) = ...), then use σ²=1
    -- Since linear_combination struggles with division, let's set D := C*s/(s-α)
    set D_val := (↑C : ℂ) * s / (s - ↑α) with hD_val_def
    -- h_identity: s*A + s*B = D_val - σ*P + σ*(K-L)
    -- Goal: K + σ*(D_val - s*B) - σ*s*A = P + L
    -- From h_identity: D_val = s*A + s*B + σ*P - σ*(K-L)
    have hD : D_val = s * A + s * B + ↑σ_sign * primeZeta s -
        ↑σ_sign * (K_ext s - Complex.log (s - 1)) := by
      -- From h_identity: s*A + s*B = D_val - σ*P + σ*(K-L)
      linear_combination -h_identity
    rw [hD]
    -- Goal: K + σ*((s*A + s*B + σ*P - σ*(K-L)) - s*B) - σ*s*A = P + L
    -- = K + σ*(s*A + σ*P - σ*K + σ*L) - σ*s*A = P + L
    -- = K + σ*s*A + σ²*P - σ²*K + σ²*L - σ*s*A = P + L
    -- = K - σ²*K + σ²*P + σ²*L = P + L   [σ²=1 ⇒ K-K=0]
    have h1 : K_ext s + ↑σ_sign *
        (s * A + s * B + ↑σ_sign * primeZeta s -
        ↑σ_sign * (K_ext s - Complex.log (s - 1)) - s * B) -
        ↑σ_sign * s * A =
        K_ext s * (1 - ↑σ_sign * ↑σ_sign) +
        ↑σ_sign * ↑σ_sign * (primeZeta s + Complex.log (s - 1)) := by ring
    rw [h1, hσ_sq]; ring

end Aristotle.Standalone.PiPringsheimExtension
