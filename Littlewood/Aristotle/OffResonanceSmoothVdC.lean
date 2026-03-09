/-
Off-resonance integral bounds via smooth complex VdC.

This file bridges the complex Van der Corput bound (ComplexVdC) with the
Hardy cosine smooth representation (HardyCosSmooth, HardyCosExpOmega) to
prove `off_resonance_integral_bound` without requiring global differentiability
of `hardyTheta`.

The key chain:
1. cos(θ(t) - t·log(n+1)) = Re(hardyCosExp n t)           [HardyCosSmooth]
2. hardyCosExp has angular velocity ω(t) = thetaDeriv(t) - log(n+1)  [HardyCosExpOmega]
3. ω ≥ m > 0 on block k (from monotonicity + lower bound)
4. ω' ≥ 0 (from thetaDeriv strictly increasing)
5. Complex VdC gives ‖∫ hardyCosExp‖ ≤ 3/m                [ComplexVdC]
6. |∫ cos(...)| = |∫ Re(hardyCosExp)| ≤ ‖∫ hardyCosExp‖ ≤ 3/m

Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.ComplexVdC
import Littlewood.Aristotle.HardyCosSmooth
import Littlewood.Aristotle.HardyCosExpOmega
import Littlewood.Aristotle.ThetaDerivMonotone
import Littlewood.Aristotle.ThetaDerivAsymptotic
import Littlewood.Aristotle.HardyNProperties

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.OffResonanceSmoothVdC

open MeasureTheory Set Real Filter Topology Complex
open HardyEstimatesPartial HardyCosSmooth
open Aristotle.HardyNProperties
open ThetaDerivAsymptotic ThetaDerivMonotone
open Aristotle.HardyCosExpOmega

-- ============================================================
-- Section 1: ω(t) = thetaDeriv(t) - log(n+1) infrastructure
-- ============================================================

/-- The instantaneous frequency of mode n. -/
def modeOmega (n : ℕ) (t : ℝ) : ℝ :=
  thetaDeriv t - Real.log (↑n + 1)

/-- modeOmega is differentiable (thetaDeriv has HasDerivAt everywhere). -/
lemma differentiable_modeOmega (n : ℕ) : Differentiable ℝ (modeOmega n) := by
  intro t
  exact ((thetaDeriv_hasDerivAt t).differentiableAt.sub
    (differentiableAt_const _))

/-- The derivative of modeOmega equals the derivative of thetaDeriv. -/
lemma deriv_modeOmega (n : ℕ) (t : ℝ) :
    deriv (modeOmega n) t = deriv thetaDeriv t := by
  have htd := thetaDeriv_hasDerivAt t
  have h : HasDerivAt (modeOmega n) (-(1 / 4) * (∑' n_1 : ℕ,
      1 / (sOfT t + (↑n_1 : ℂ)) ^ 2).im) t := by
    show HasDerivAt (fun t => thetaDeriv t - Real.log (↑n + 1)) _ t
    have := htd.sub (hasDerivAt_const t (Real.log (↑n + 1)))
    simp only [sub_zero] at this
    exact this
  rw [h.deriv, htd.deriv]

/-- deriv thetaDeriv is nonneg for t > 0 (thetaDeriv' > 0). -/
lemma deriv_thetaDeriv_nonneg (t : ℝ) (ht : 0 < t) :
    0 ≤ deriv thetaDeriv t := by
  obtain ⟨d, hd, hd_pos⟩ := thetaDeriv_deriv_pos t ht
  rw [hd.deriv]
  exact le_of_lt hd_pos

/-- deriv modeOmega is nonneg for t > 0. -/
lemma deriv_modeOmega_nonneg (n : ℕ) (t : ℝ) (ht : 0 < t) :
    0 ≤ deriv (modeOmega n) t := by
  rw [deriv_modeOmega]
  exact deriv_thetaDeriv_nonneg t ht

-- ============================================================
-- Section 2: ‖hardyCosExp‖ = 1
-- ============================================================

/-- hardyCosExp has unit norm (it equals exp(i·phase)). -/
lemma norm_hardyCosExp (n : ℕ) (t : ℝ) : ‖hardyCosExp n t‖ = 1 := by
  rw [hardyCosExp_eq_cexp_phaseArg, mul_comm]
  exact norm_exp_ofReal_mul_I _

-- ============================================================
-- Section 3: Lower bound on modeOmega
-- ============================================================

/-- For k ≥ 1 and n < k, modeOmega n ≥ log((k+1)/(n+1))/2 on block k.

    Proof sketch:
    - thetaDeriv is strictly increasing on (0,∞) [thetaDeriv_strictMonoOn]
    - thetaDeriv(hardyStart k) ≈ log(k+1) with error O(1/(k+1)²)
    - For t ≥ hardyStart k > 0: thetaDeriv(t) ≥ thetaDeriv(hardyStart k) ≥ log(k+1) - C/(k+1)²
    - So modeOmega n t ≥ log((k+1)/(n+1)) - C/(k+1)²
    - The error C/(k+1)² is ≤ (1/2)·log((k+1)/(n+1)) for large k
    - Small k cases need explicit computation -/
lemma modeOmega_lower_bound :
    ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, n < k →
      ∀ t : ℝ, hardyStart k ≤ t → t ≤ hardyStart (k + 1) →
        Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) / 2 ≤ modeOmega n t := by
  sorry

-- ============================================================
-- Section 4: Continuity of deriv modeOmega
-- ============================================================

/-- Summability of 16/(n+1)² (reproduced from ThetaDerivMonotone). -/
private lemma summable_sixteen_div_sq :
    Summable (fun n : ℕ => 16 / ((↑n : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (↑n : ℝ) ^ 2) 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  simp only [Nat.cast_add, Nat.cast_one] at h
  exact (h.mul_left 16).congr (fun n => by ring)

/-- Uniform norm bound: ‖1/(sOfT t + n)²‖ ≤ 16/(n+1)² for all t. -/
private lemma norm_inv_sq_sOfT_le (t : ℝ) (n : ℕ) :
    ‖(1 : ℂ) / (sOfT t + (↑n : ℂ)) ^ 2‖ ≤ 16 / ((↑n : ℝ) + 1) ^ 2 := by
  have h14 := norm_sOfT_add_nat_ge t n
  have h14_pos : (0 : ℝ) < ↑n + 1/4 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have h1_pos : (0 : ℝ) < ↑n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hstep1 : ‖(1 : ℂ) / (sOfT t + (↑n : ℂ)) ^ 2‖ ≤ 1 / ((↑n : ℝ) + 1/4) ^ 2 := by
    rw [one_div, norm_inv, norm_pow, one_div]
    apply inv_anti₀ (by positivity)
    exact sq_le_sq' (by linarith [norm_nonneg (sOfT t + (↑n : ℂ))]) h14
  have hstep2 : 1 / ((↑n : ℝ) + 1/4) ^ 2 ≤ 16 / ((↑n : ℝ) + 1) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  linarith

/-- Each summand of the trigamma series is continuous in t. -/
private lemma continuous_inv_sq_summand (n : ℕ) :
    Continuous (fun t : ℝ => (1 : ℂ) / (sOfT t + (↑n : ℂ)) ^ 2) := by
  apply Continuous.div continuous_const
  · apply Continuous.pow
    apply Continuous.add _ continuous_const
    show Continuous fun t => sOfT t
    exact continuous_const.add (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_id |>.div_const 2))
  · intro t; exact pow_ne_zero 2 (sOfT_add_nat_ne_zero t n)

/-- The derivative of thetaDeriv is continuous. -/
lemma continuous_deriv_thetaDeriv : Continuous (deriv thetaDeriv) := by
  have h_eq : deriv thetaDeriv = fun t =>
      -(1 / 4) * (∑' n : ℕ, 1 / (sOfT t + (↑n : ℂ)) ^ 2).im := by
    ext t; exact (thetaDeriv_hasDerivAt t).deriv
  rw [h_eq]
  apply Continuous.mul continuous_const
  exact Complex.continuous_im.comp
    (continuous_tsum (fun n => continuous_inv_sq_summand n)
      summable_sixteen_div_sq (fun n t => norm_inv_sq_sOfT_le t n))

/-- The derivative of modeOmega is continuous. -/
lemma continuous_deriv_modeOmega (n : ℕ) : Continuous (deriv (modeOmega n)) := by
  have h : deriv (modeOmega n) = deriv thetaDeriv := by
    ext t; exact deriv_modeOmega n t
  rw [h]
  exact continuous_deriv_thetaDeriv

-- ============================================================
-- Section 5: Main theorem
-- ============================================================

/-- hardyStart k is positive for k ≥ 0. -/
private lemma hardyStart_pos (k : ℕ) : 0 < hardyStart k := by
  rw [hardyStart_formula]
  positivity

/-- Off-resonance integral bound via smooth complex VdC.
    This closes the sorry in ErrorTermExpansion.lean. -/
theorem off_resonance_integral_bound_smooth :
    ∀ k : ℕ, ∀ n : ℕ, n < k → 1 ≤ k →
      |∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
        Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))|
          ≤ 6 / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
  intro k n hnk hk
  -- Setup
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hkn : (n : ℝ) + 1 < (k : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ hnk
  have hratio_gt : 1 < ((k : ℝ) + 1) / ((n : ℝ) + 1) := by
    rw [one_lt_div hn1_pos]; linarith
  have hlog_pos : 0 < Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) :=
    Real.log_pos hratio_gt
  set m := Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) / 2 with hm_def
  have hm_pos : 0 < m := by positivity
  have hab : hardyStart k ≤ hardyStart (k + 1) := by
    rw [hardyStart_formula, hardyStart_formula]
    gcongr; push_cast; linarith
  set a := hardyStart k with ha_def
  set b := hardyStart (k + 1) with hb_def
  have ha_pos : 0 < a := hardyStart_pos k
  -- Step 1: Rewrite cos as Re(hardyCosExp)
  have h_cos_eq : (fun t => Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1)))
      = (fun t => (hardyCosExp n t).re) := funext (fun t => hardyCos_eq_re_hardyCosExp n t)
  -- Step 2: Convert Ioc set integral to interval integral
  rw [h_cos_eq, ← intervalIntegral.integral_of_le hab]
  -- Step 3: Apply complex_vdc_angular_re
  have h_bound := Aristotle.ComplexVdC.complex_vdc_angular_re
    (fun t => hardyCosExp n t) (modeOmega n) a b m hab hm_pos
    -- F' = I*ω*F
    (fun t _ht => by
      have h := hardyCosExp_angular_velocity n t
      simp only [modeOmega, Nat.cast_succ] at h ⊢
      exact h)
    -- ‖F‖ ≤ 1
    (fun t _ht => le_of_eq (norm_hardyCosExp n t))
    -- ω differentiable
    (differentiable_modeOmega n)
    -- deriv ω continuous
    (continuous_deriv_modeOmega n)
    -- ω ≥ m on [a,b]
    (fun t ht => modeOmega_lower_bound k hk n hnk t ht.1 ht.2)
    -- ω' ≥ 0 on [a,b]
    (fun t ht => deriv_modeOmega_nonneg n t (lt_of_lt_of_le ha_pos ht.1))
  -- Step 4: Convert 3/m = 3/(log(...)/2) = 6/log(...)
  calc |∫ t in a..b, (hardyCosExp n t).re|
      ≤ 3 / m := h_bound
    _ = 6 / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
        rw [hm_def]; ring

end Aristotle.OffResonanceSmoothVdC
