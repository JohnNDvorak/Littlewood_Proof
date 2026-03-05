import Mathlib
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.HardyZMeasurability
import Littlewood.Aristotle.VdcFirstDerivTest

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.OffResonanceInfra

open MeasureTheory Set Real intervalIntegral HardyEstimatesPartial

/--
If a Hardy mode phase satisfies the first-derivative VdC hypotheses on the full
`k`-block and has derivative lower bound
`log((k+1)/(n+1))/2`, then the block integral is bounded by
`6 / log((k+1)/(n+1))`.

This is the exact quantitative wrapper used in `ErrorTermExpansion`.
-/
theorem off_resonance_integral_bound_of_vdc
    (k n : ℕ) (hnk : n < k) (hk : 1 ≤ k)
    (hphi : Differentiable ℝ (fun t => hardyTheta t - t * Real.log ((n : ℝ) + 1)))
    (hphi' : Differentiable ℝ (deriv (fun t => hardyTheta t - t * Real.log ((n : ℝ) + 1))))
    (hphi'' : Continuous (deriv (deriv (fun t => hardyTheta t - t * Real.log ((n : ℝ) + 1)))))
    (hphi'_lower : ∀ t ∈ Icc (hardyStart k) (hardyStart (k + 1)),
      Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) / 2
        ≤ deriv (fun t => hardyTheta t - t * Real.log ((n : ℝ) + 1)) t)
    (hphi''_nonneg : ∀ t ∈ Icc (hardyStart k) (hardyStart (k + 1)),
      0 ≤ deriv (deriv (fun t => hardyTheta t - t * Real.log ((n : ℝ) + 1))) t) :
    |∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
      Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))|
      ≤ 6 / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
  have hab : hardyStart k ≤ hardyStart (k + 1) := by
    rw [Aristotle.HardyNProperties.hardyStart_formula, Aristotle.HardyNProperties.hardyStart_formula]
    have hk_le : ((k : ℝ) + 1) ≤ ((k + 1 : ℕ) : ℝ) + 1 := by
      norm_num
    have hsq : ((k : ℝ) + 1) ^ 2 ≤ ((((k + 1 : ℕ) : ℝ) + 1) ^ 2) := by
      nlinarith [hk_le]
    exact mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hkn : (n : ℝ) + 1 < (k : ℝ) + 1 := by
    exact_mod_cast Nat.succ_lt_succ hnk
  have hratio_gt_one : 1 < ((k : ℝ) + 1) / ((n : ℝ) + 1) := by
    have hsub_pos : 0 < ((k : ℝ) + 1) - ((n : ℝ) + 1) := sub_pos.mpr hkn
    have hdecomp : ((k : ℝ) + 1) / ((n : ℝ) + 1)
        = 1 + (((k : ℝ) + 1) - ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
      field_simp [ne_of_gt hn1_pos]
      ring
    rw [hdecomp]
    have hfrac_pos : 0 < (((k : ℝ) + 1) - ((n : ℝ) + 1)) / ((n : ℝ) + 1) :=
      div_pos hsub_pos hn1_pos
    linarith
  have hlog_pos : 0 < Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) :=
    Real.log_pos hratio_gt_one
  have hm : 0 < Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) / 2 := by
    nlinarith
  have hbase :
      |∫ t in hardyStart k..hardyStart (k + 1),
        Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))|
      ≤ 3 / (Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) / 2) :=
    VdcFirstDerivTest.vdc_cos_bound
      (phi := fun t => hardyTheta t - t * Real.log ((n : ℝ) + 1))
      (a := hardyStart k) (b := hardyStart (k + 1))
      (m := Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) / 2)
      hab hm hphi hphi' hphi'' hphi'_lower hphi''_nonneg
  have hlog_ne : Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) ≠ 0 := ne_of_gt hlog_pos
  calc
    |∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
      Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))|
        = |∫ t in hardyStart k..hardyStart (k + 1),
            Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))| := by
            rw [← intervalIntegral.integral_of_le hab]
    _ ≤ 3 / (Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) / 2) := hbase
    _ = 6 / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)) := by
      field_simp [hlog_ne]
      ring

/--
Abstract reduction for the weighted off-resonance block sum:
- if each mode has the `6/log` bound,
- and the weighted `6/log` kernel sum is bounded by `C_off * sqrt(k+1)`,
then the weighted cosine-integral sum has the same bound.
-/
theorem off_resonance_sum_bound_of_mode_and_kernel
    (C_off : ℝ)
    (hkernel : ∀ k : ℕ, 1 ≤ k →
      ∑ n ∈ Finset.range k,
        ((n + 1 : ℝ) ^ (-(1 : ℝ) / 2))
          * (6 / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1)))
        ≤ C_off * Real.sqrt ((k : ℝ) + 1))
    (hmode : ∀ k : ℕ, ∀ n : ℕ, n < k → 1 ≤ k →
      |∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
        Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))|
        ≤ 6 / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1))) :
    ∀ k : ℕ, 1 ≤ k →
      |∑ n ∈ Finset.range k,
        ((n + 1 : ℝ) ^ (-(1 : ℝ)/2)) *
          ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
            Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))|
      ≤ C_off * Real.sqrt ((k : ℝ) + 1) := by
  intro k hk
  calc
    |∑ n ∈ Finset.range k,
      ((n + 1 : ℝ) ^ (-(1 : ℝ) / 2))
        * ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
            Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))|
      ≤ ∑ n ∈ Finset.range k,
          |((n + 1 : ℝ) ^ (-(1 : ℝ) / 2))
            * ∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                Real.cos (hardyTheta t - t * Real.log ((n : ℝ) + 1))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range k,
          ((n + 1 : ℝ) ^ (-(1 : ℝ) / 2))
            * (6 / Real.log (((k : ℝ) + 1) / ((n : ℝ) + 1))) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hn_lt_k : n < k := Finset.mem_range.mp hn
          have hcoef_nonneg : 0 ≤ ((n + 1 : ℝ) ^ (-(1 : ℝ) / 2)) := by positivity
          rw [abs_mul, abs_of_nonneg hcoef_nonneg]
          exact mul_le_mul_of_nonneg_left (hmode k n hn_lt_k hk) hcoef_nonneg
    _ ≤ C_off * Real.sqrt ((k : ℝ) + 1) := hkernel k hk

end Aristotle.OffResonanceInfra
