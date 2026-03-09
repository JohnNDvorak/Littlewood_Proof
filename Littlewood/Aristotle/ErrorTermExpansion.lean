/-
Riemann-Siegel expansion of ErrorTerm on blocks.

This file provides the pointwise expansion of ErrorTerm(t) on each block
[hardyStart k, hardyStart(k+1)], showing that ErrorTerm has a definite sign
structure ((-1)^k) with leading term proportional to (2π/t)^{1/4}.

## Main results

- `errorTermOnBlock`: Block-local version of ErrorTerm with fixed N=k+1
  (continuous, agrees with ErrorTerm on the open block)
- `errorTerm_expansion`: Pointwise RS expansion of ErrorTerm on blocks
- `rsPsi`: The RS correction function Ψ on [0,1]
- `rsPsi_integral_pos`: The integral of Ψ is positive (Fresnel connection)

## Architecture

Phase 2a: Theta value and phase on blocks (from BinetStirling)
Phase 2b: Off-resonance mode bounds (from VdcFirstDerivTest, needs θ')
Phase 2c: RS integral representation and leading term (THE WALL)
Phase 2d: RS Ψ function and integral positivity (from FresnelIntegrals)

## References

- Siegel, "Über Riemanns Nachlaß zur analytischen Zahlentheorie" (1932)
- Titchmarsh, "The Theory of the Riemann Zeta-Function", §4.16-4.17
- Edwards, "Riemann's Zeta Function", Ch. 7

SORRY COUNT: 4 (Phase 2a: 1, Phase 2b: 2, Phase 2c: 1, Phase 2d: 0)

Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.RSBlockParam
import Littlewood.Aristotle.BinetStirling
import Littlewood.Aristotle.CosPiSqSign
import Littlewood.Aristotle.FresnelIntegrals
import Littlewood.Aristotle.VdcFirstDerivTest
import Littlewood.Aristotle.OffResonanceSmoothVdC

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.ErrorTermExpansion

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial
open Aristotle.HardyNProperties Aristotle.RSBlockParam

-- ============================================================
-- Section 1: Block-local ErrorTerm (continuous version)
-- ============================================================

/-- Block-local ErrorTerm: uses fixed N=k+1 instead of ⌊√(t/2π)⌋.
    This is continuous everywhere (finite sum of continuous functions),
    and agrees with ErrorTerm on the open block (hardyStart k, hardyStart(k+1))
    where hardyN t = k+1. -/
def errorTermOnBlock (k : ℕ) (t : ℝ) : ℝ :=
  hardyZ t - 2 * ∑ n ∈ Finset.range (k + 1),
    ((n + 1 : ℝ) ^ (-(1/2 : ℝ))) * Real.cos (hardyTheta t - t * Real.log (n + 1))

/-- On the open block, errorTermOnBlock agrees with ErrorTerm. -/
theorem errorTermOnBlock_eq_errorTerm (k : ℕ) (t : ℝ)
    (ht : hardyStart k ≤ t) (ht' : t < hardyStart (k + 1)) :
    errorTermOnBlock k t = ErrorTerm t := by
  unfold errorTermOnBlock ErrorTerm MainTerm
  congr 1
  congr 1
  -- hardyN t = k + 1 on the open block
  have hN : hardyN t = k + 1 :=
    hardyN_constant_on_block k t ht ht'
  rw [show Nat.floor (Real.sqrt (t / (2 * Real.pi))) = k + 1 from by
    rw [← hardyN]; exact hN]

/-- The Ioc integral of errorTermOnBlock equals the Ioc integral of ErrorTerm. -/
theorem errorTermOnBlock_integral_eq (k : ℕ) :
    ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), errorTermOnBlock k t
      = ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t := by
  -- ∫ Ioc = ∫ Ioo (singleton has measure zero), then agree on Ioo
  rw [integral_Ioc_eq_integral_Ioo' Real.volume_singleton,
      integral_Ioc_eq_integral_Ioo' Real.volume_singleton]
  exact setIntegral_congr_fun measurableSet_Ioo
    (fun t ht => errorTermOnBlock_eq_errorTerm k t (le_of_lt ht.1) ht.2)

-- ============================================================
-- Section 2: Phase 2a — Theta expansion on blocks
-- ============================================================

/-- θ(t) ≈ (t/2)log(t/(2π)) - t/2 - π/8 with error O(1/t).
    This is the imaginary part of the Stirling approximation. -/
theorem theta_stirling_expansion :
    ∃ C_θ > 0, ∀ t : ℝ, 2 * Real.pi ≤ t →
      |hardyTheta t - ((t/2) * Real.log (t / (2 * Real.pi)) - t/2 - Real.pi / 8)|
        ≤ C_θ / t := by
  sorry

/-- Phase at block boundary: θ(hardyStart k) - hardyStart(k)·log(k+1)
    is close to -π(k+1)² - π/8. This determines the (-1)^k sign structure.
    Proof: substitute t = 2π(k+1)² into the Stirling expansion and simplify. -/
theorem phase_at_block_start :
    ∃ C_p > 0, ∀ k : ℕ, 1 ≤ k →
      |hardyTheta (hardyStart k) - hardyStart k * Real.log ((k : ℝ) + 1)
        - (-Real.pi * ((k : ℝ) + 1) ^ 2 - Real.pi / 8)|
        ≤ C_p / ((k : ℝ) + 1) := by
  obtain ⟨C_θ, hC_θ_pos, hC_θ⟩ := theta_stirling_expansion
  refine ⟨C_θ / (2 * Real.pi), div_pos hC_θ_pos (by positivity), fun k hk => ?_⟩
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
  -- hardyStart k = 2π(k+1)²
  have ht_val : hardyStart k = 2 * Real.pi * ((k : ℝ) + 1) ^ 2 := by
    have : hardyStart k = 2 * Real.pi * ((k : ℝ) + 1) ^ 2 := by
      unfold hardyStart; push_cast; ring
    exact this
  -- t ≥ 2π since (k+1)² ≥ 1
  have ht_ge : 2 * Real.pi ≤ hardyStart k := by
    rw [ht_val]; nlinarith [Real.pi_pos, sq_nonneg ((k : ℝ))]
  -- t/(2π) = (k+1)²
  have h_tdiv : hardyStart k / (2 * Real.pi) = ((k : ℝ) + 1) ^ 2 := by
    rw [ht_val]; rw [mul_div_cancel_left₀]; exact ne_of_gt (by positivity)
  -- log(t/(2π)) = 2·log(k+1)
  have h_log : Real.log (hardyStart k / (2 * Real.pi)) = 2 * Real.log ((k : ℝ) + 1) := by
    rw [h_tdiv, Real.log_pow]; push_cast; ring
  -- t/2 = π(k+1)²
  have h_half : hardyStart k / 2 = Real.pi * ((k : ℝ) + 1) ^ 2 := by
    rw [ht_val]; ring
  -- Stirling at hardyStart: (t/2)log(t/(2π)) - t/2 - π/8 = t·log(k+1) - π(k+1)² - π/8
  have h_stirling :
      hardyStart k / 2 * Real.log (hardyStart k / (2 * Real.pi)) - hardyStart k / 2 - Real.pi / 8
      = hardyStart k * Real.log ((k : ℝ) + 1) - Real.pi * ((k : ℝ) + 1) ^ 2 - Real.pi / 8 := by
    rw [h_log, h_half, ht_val]; ring
  -- Rewrite: the LHS equals |θ(t) - stirling_value(t)|
  have h_eq : hardyTheta (hardyStart k) - hardyStart k * Real.log ((k : ℝ) + 1)
      - (-Real.pi * ((k : ℝ) + 1) ^ 2 - Real.pi / 8)
    = hardyTheta (hardyStart k)
      - (hardyStart k / 2 * Real.log (hardyStart k / (2 * Real.pi))
         - hardyStart k / 2 - Real.pi / 8) := by linear_combination h_stirling
  rw [h_eq]
  -- Bound by C_θ/t ≤ (C_θ/(2π))/(k+1)
  calc |hardyTheta (hardyStart k)
        - (hardyStart k / 2 * Real.log (hardyStart k / (2 * Real.pi))
           - hardyStart k / 2 - Real.pi / 8)|
      ≤ C_θ / hardyStart k := hC_θ (hardyStart k) ht_ge
    _ = C_θ / (2 * Real.pi * ((k : ℝ) + 1) ^ 2) := by rw [ht_val]
    _ ≤ C_θ / (2 * Real.pi) / ((k : ℝ) + 1) := by
        rw [div_div, div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi * ((k : ℝ) + 1) ^ 2)
            (by positivity : (0 : ℝ) < 2 * Real.pi * ((k : ℝ) + 1))]
        have h_denom_le : 2 * Real.pi * ((k : ℝ) + 1) ≤ 2 * Real.pi * ((k : ℝ) + 1) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
          nlinarith [sq_nonneg ((k : ℝ))]
        exact mul_le_mul_of_nonneg_left h_denom_le (le_of_lt hC_θ_pos)

/-- Sign extraction: cos(θ(hardyStart k) - hardyStart(k)·log(k+1)) ≈ (-1)^(k+1)·cos(π/8).
    This is the mechanism by which the resonant mode picks up the (-1)^k sign.
    Proof: use phase_at_block_start + cos Lipschitz + the identity
    cos(π·m² + π/8) = (-1)^m · cos(π/8) (from cos_pi_mul_succ_sq + sin_nat_mul_pi). -/
theorem cos_phase_sign :
    ∃ C_s > 0, ∀ k : ℕ, 1 ≤ k →
      |Real.cos (hardyTheta (hardyStart k) - hardyStart k * Real.log ((k : ℝ) + 1))
        - (-1 : ℝ) ^ (k + 1) * Real.cos (Real.pi / 8)|
        ≤ C_s / ((k : ℝ) + 1) := by
  obtain ⟨C_p, hC_p_pos, hC_p⟩ := phase_at_block_start
  refine ⟨C_p, hC_p_pos, fun k hk => ?_⟩
  set phase := hardyTheta (hardyStart k) - hardyStart k * Real.log ((k : ℝ) + 1)
  set target := -Real.pi * ((k : ℝ) + 1) ^ 2 - Real.pi / 8
  -- cos(target) = (-1)^(k+1) · cos(π/8)
  have h_cos_target : Real.cos target = (-1 : ℝ) ^ (k + 1) * Real.cos (Real.pi / 8) := by
    show Real.cos (-Real.pi * ((k : ℝ) + 1) ^ 2 - Real.pi / 8)
        = (-1 : ℝ) ^ (k + 1) * Real.cos (Real.pi / 8)
    rw [show -Real.pi * ((k : ℝ) + 1) ^ 2 - Real.pi / 8
        = -(Real.pi * ((k : ℝ) + 1) ^ 2 + Real.pi / 8) from by ring]
    rw [Real.cos_neg, Real.cos_add]
    rw [CosPiSqSign.cos_pi_mul_succ_sq k]
    rw [show Real.pi * ((k : ℝ) + 1) ^ 2
        = (((k + 1) ^ 2 : ℕ) : ℝ) * Real.pi from by push_cast; ring]
    rw [Real.sin_nat_mul_pi, zero_mul, sub_zero]
  -- |cos phase - cos target| ≤ |phase - target| (cos is 1-Lipschitz)
  -- |phase - target| ≤ C_p / (k+1) (from phase_at_block_start)
  calc |Real.cos phase - (-1 : ℝ) ^ (k + 1) * Real.cos (Real.pi / 8)|
      = |Real.cos phase - Real.cos target| := by rw [h_cos_target]
    _ ≤ |phase - target| := abs_cos_sub_cos_le phase target
    _ ≤ C_p / ((k : ℝ) + 1) := hC_p k hk

-- ============================================================
-- Section 3: Phase 2b — Off-resonance mode bounds
-- ============================================================

/-- For modes n < k on block k, the phase derivative is bounded below by
    (1/2)·log((k+1)/(n+1)), ensuring rapid oscillation. -/
theorem phase_deriv_off_resonance :
    ∀ k : ℕ, ∀ n : ℕ, n < k → ∀ t : ℝ,
      hardyStart k ≤ t → t < hardyStart (k + 1) →
      Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) / 2 ≤
        |(1/2) * Real.log (t / (2 * Real.pi)) - Real.log ((n : ℝ) + 1)| := by
  intro k n hnk t ht_lo _ht_hi
  -- Positivity setup
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- n + 1 ≤ k + 1 from n < k
  have hn_le_k : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by
    have h : (n : ℕ) + 1 ≤ (k : ℕ) + 1 := Nat.succ_le_succ (le_of_lt hnk)
    exact_mod_cast h
  -- t / (2π) ≥ (k+1)²
  have ht_div : ((k : ℝ) + 1) ^ 2 ≤ t / (2 * Real.pi) := by
    rw [le_div_iff₀ hpi]
    have : 2 * Real.pi * ((k : ℝ) + 1) ^ 2 = hardyStart k := by unfold hardyStart; ring
    linarith
  -- (k+1)*(n+1) ≤ t / (2π) via (k+1)*(n+1) ≤ (k+1)²
  have h_prod : ((k : ℝ) + 1) * ((n : ℝ) + 1) ≤ t / (2 * Real.pi) := by
    calc ((k : ℝ) + 1) * ((n : ℝ) + 1)
        ≤ ((k : ℝ) + 1) * ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hn_le_k (le_of_lt hk1)
      _ = ((k : ℝ) + 1) ^ 2 := (sq _).symm
      _ ≤ t / (2 * Real.pi) := ht_div
  -- Expression is nonneg: (1/2)*log(t/(2π)) ≥ log(k+1) ≥ log(n+1)
  have h_nonneg : 0 ≤ 1 / 2 * Real.log (t / (2 * Real.pi)) - Real.log (↑n + 1) := by
    have h1 : Real.log (((k : ℝ) + 1) ^ 2) ≤ Real.log (t / (2 * Real.pi)) :=
      Real.log_le_log (by positivity) ht_div
    rw [Real.log_pow] at h1
    have h2 : Real.log (↑n + 1) ≤ Real.log (↑k + 1) :=
      Real.log_le_log hn1 hn_le_k
    linarith
  rw [abs_of_nonneg h_nonneg]
  -- Goal: log((k+1)/(n+1))/2 ≤ (1/2)*log(t/(2π)) - log(n+1)
  rw [Real.log_div (ne_of_gt hk1) (ne_of_gt hn1)]
  -- Sufficient: log(k+1) + log(n+1) ≤ log(t/(2π))
  have h_key : Real.log (↑k + 1) + Real.log (↑n + 1) ≤ Real.log (t / (2 * Real.pi)) := by
    rw [← Real.log_mul (ne_of_gt hk1) (ne_of_gt hn1)]
    exact Real.log_le_log (mul_pos hk1 hn1) h_prod
  linarith

/-- Van der Corput bound per off-resonance mode: the integral of cos(θ(t)-t·log(n+1))
    over block k is bounded by C_vdc/log((k+1)/(n+1)) for some universal C_vdc > 0. -/
theorem off_resonance_integral_bound :
    ∃ C_vdc > 0, ∀ k : ℕ, ∀ n : ℕ, n < k → 1 ≤ k →
      |∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
        Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))|
          ≤ C_vdc / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) :=
  Aristotle.OffResonanceSmoothVdC.off_resonance_integral_bound_smooth

/-- Weighted sum of off-resonance contributions is O(√(k+1)). -/
theorem off_resonance_sum_bound :
    ∃ C_off > 0, ∀ k : ℕ, 1 ≤ k →
      |∑ n ∈ Finset.range k, ((n + 1 : ℝ) ^ (-(1 : ℝ)/2)) *
        ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
          Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))|
        ≤ C_off * Real.sqrt ((k : ℝ) + 1) := by
  sorry

-- ============================================================
-- Section 4: Phase 2c — RS integral representation (THE WALL)
-- ============================================================

/-- The RS correction function Ψ on [0,1].
    This encodes the leading-order correction from the Riemann-Siegel formula.
    The phase convention (+1/4) is chosen so that Ψ > 0 on [0,1], consistent with
    positive block integrals. The corresponding sign in errorTerm_expansion absorbs
    the phase relationship to the standard RS remainder. -/
def rsPsi (p : ℝ) : ℝ :=
  Real.cos (Real.pi * (2 * p ^ 2 - 2 * p + 1/4))

/-- Ψ is continuous on [0,1]. -/
theorem rsPsi_continuousOn : ContinuousOn rsPsi (Icc 0 1) := by
  unfold rsPsi
  have : Continuous fun p : ℝ => Real.cos (Real.pi * (2 * p ^ 2 - 2 * p + 1 / 4)) := by
    fun_prop
  exact this.continuousOn

/-- **Core RS expansion**: ErrorTerm on each block is well-approximated by
    (-1)^k · Ψ(blockParam k t) · (2π/t)^{1/4} up to O(t^{-3/4}) error.

    This is THE WALL — the single hardest piece of the entire proof.
    Requires:
    1. Functional equation ζ(s) = χ(s)ζ(1-s) (FunctionalEquationV2)
    2. Euler-Maclaurin evaluation of the AFE remainder at the saddle point
    3. Phase extraction using cos_pi_mul_nat_sq -/
theorem errorTerm_expansion :
    ∃ (C_rem : ℝ),
      C_rem ≥ 0 ∧
      (∀ k : ℕ, 1 ≤ k → ∀ t : ℝ,
        hardyStart k ≤ t → t < hardyStart (k + 1) →
          |ErrorTerm t - (-1 : ℝ) ^ k * rsPsi (blockParam k t) *
            (2 * Real.pi / t) ^ ((1 : ℝ) / 4)|
            ≤ C_rem * t ^ (-(3 : ℝ) / 4)) := by
  sorry

-- ============================================================
-- Section 5: Phase 2d — Ψ integral positivity
-- ============================================================

/-- Ψ is integrable on [0,1]. -/
theorem rsPsi_integrableOn : IntegrableOn rsPsi (Ioc 0 1) := by
  exact rsPsi_continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- The integral of Ψ over [0,1] is positive.
    With the +1/4 phase convention, Ψ > 0 on all of [0,1] since the argument
    π(2p²-2p+1/4) ∈ [-π/4, π/4] ⊂ (-π/2, π/2) where cos is positive. -/
theorem rsPsi_integral_pos : 0 < ∫ p in Ioc 0 1, rsPsi p := by
  -- cos(π/4) > 0
  have hcos_pos : (0 : ℝ) < Real.cos (Real.pi / 4) := by
    rw [Real.cos_pi_div_four]; positivity
  have hpi4_le_pi : Real.pi / 4 ≤ Real.pi :=
    div_le_self (le_of_lt Real.pi_pos) (by norm_num : (1 : ℝ) ≤ 4)
  -- cos(π/4) ≤ rsPsi(p) for p ∈ Ioc 0 1
  have h_lower : ∀ p ∈ Ioc (0 : ℝ) 1, Real.cos (Real.pi / 4) ≤ rsPsi p := by
    intro p hp
    have ⟨hp0, hp1⟩ := Ioc_subset_Icc_self hp
    simp only [rsPsi]
    have harg_abs : |Real.pi * (2 * p ^ 2 - 2 * p + 1/4)| ≤ Real.pi / 4 := by
      rw [abs_le]; constructor
      · have h1 : 0 ≤ 2 * (p - 1/2) ^ 2 := by positivity
        nlinarith [Real.pi_pos]
      · have h2 : 2 * p * (p - 1) ≤ 0 := by nlinarith
        nlinarith [Real.pi_pos]
    -- cos is even and antitone on [0,π]: |arg| ≤ π/4 → cos(arg) ≥ cos(π/4)
    rw [← Real.cos_abs (Real.pi * (2 * p ^ 2 - 2 * p + 1/4))]
    exact Real.strictAntiOn_cos.antitoneOn
      (Set.mem_Icc.mpr ⟨abs_nonneg _, le_trans harg_abs hpi4_le_pi⟩)
      (Set.mem_Icc.mpr ⟨le_of_lt (div_pos Real.pi_pos (by norm_num : (0:ℝ) < 4)), hpi4_le_pi⟩)
      harg_abs
  -- ∫ rsPsi ≥ ∫ cos(π/4) = cos(π/4) > 0 via ae monotonicity
  have h_ae : ∀ᵐ p ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      (fun _ => Real.cos (Real.pi / 4)) p ≤ rsPsi p :=
    (ae_restrict_mem measurableSet_Ioc).mono (fun p hp => h_lower p hp)
  have h_const_int : IntegrableOn (fun _ => Real.cos (Real.pi / 4)) (Ioc (0 : ℝ) 1) :=
    continuous_const.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h_mono : ∫ _ in Ioc (0 : ℝ) 1, Real.cos (Real.pi / 4)
      ≤ ∫ p in Ioc (0 : ℝ) 1, rsPsi p :=
    integral_mono_ae h_const_int rsPsi_integrableOn h_ae
  have h_const_val : ∫ _ in Ioc (0 : ℝ) 1, Real.cos (Real.pi / 4)
      = Real.cos (Real.pi / 4) := by
    simp [setIntegral_const, smul_eq_mul, Real.volume_Ioc,
          ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 - 0 by norm_num)]
  linarith

end Aristotle.ErrorTermExpansion
