/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Growth Domination Lemmas

Pure real analysis lemmas comparing growth rates of functions relevant to
Littlewood's theorem. These are used to upgrade √x oscillation to
√x · log log log x oscillation via the Ω± monotonicity lemma.

## Main Results

* `sqrt_eventually_le_sqrt_mul_lll` : √x ≤ √x · log(log(log x)) eventually
* `sqrt_mul_lll_eventually_nonneg` : √x · log(log(log x)) ≥ 0 eventually
* `sqrt_div_log_eventually_le_mul_lll` : √x/log x ≤ (√x/log x)·lll x eventually
* `sqrt_div_log_mul_lll_eventually_nonneg` : (√x/log x)·lll x ≥ 0 eventually
-/

noncomputable section

open Real Filter

namespace GrowthDomination

/-- Abbreviation: log log log x -/
def lll (x : ℝ) : ℝ := Real.log (Real.log (Real.log x))

/-- log(log(log x)) ≥ 1 for x sufficiently large. -/
theorem lll_eventually_ge_one : ∀ᶠ x in atTop, 1 ≤ lll x := by
  -- log(log(log x)) ≥ 1 ⟺ log(log x) ≥ e ⟺ log x ≥ e^e ⟺ x ≥ e^{e^e}
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp (Real.exp 1)))] with x hx
  unfold lll
  have hlog1 : Real.exp (Real.exp 1) ≤ Real.log x := by
    rwa [← Real.log_exp (Real.exp (Real.exp 1)), Real.log_le_log_iff (Real.exp_pos _)
      (lt_of_lt_of_le (Real.exp_pos _) hx)]
  have hlog2 : Real.exp 1 ≤ Real.log (Real.log x) := by
    rwa [← Real.log_exp (Real.exp 1), Real.log_le_log_iff (Real.exp_pos _)
      (lt_of_lt_of_le (Real.exp_pos _) hlog1)]
  rwa [← Real.log_exp 1, Real.log_le_log_iff (Real.exp_pos _)
    (lt_of_lt_of_le (Real.exp_pos _) hlog2)]

/-- √x · log(log(log x)) ≥ 0 eventually. -/
theorem sqrt_mul_lll_eventually_nonneg :
    ∀ᶠ x in atTop, 0 ≤ Real.sqrt x * lll x := by
  filter_upwards [lll_eventually_ge_one] with x hlll
  exact mul_nonneg (Real.sqrt_nonneg x) (le_trans zero_le_one hlll)

/-- √x ≤ √x · log(log(log x)) eventually. -/
theorem sqrt_eventually_le_sqrt_mul_lll :
    ∀ᶠ x in atTop, Real.sqrt x ≤ Real.sqrt x * lll x := by
  filter_upwards [lll_eventually_ge_one] with x hlll
  calc Real.sqrt x = Real.sqrt x * 1 := (mul_one _).symm
    _ ≤ Real.sqrt x * lll x := mul_le_mul_of_nonneg_left hlll (Real.sqrt_nonneg x)

/-- √x / log x ≤ (√x / log x) · log(log(log x)) eventually. -/
theorem sqrt_div_log_eventually_le_mul_lll :
    ∀ᶠ x in atTop, Real.sqrt x / Real.log x ≤
      Real.sqrt x / Real.log x * lll x := by
  filter_upwards [lll_eventually_ge_one, eventually_gt_atTop 1] with x hlll hx
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  calc Real.sqrt x / Real.log x = Real.sqrt x / Real.log x * 1 := (mul_one _).symm
    _ ≤ Real.sqrt x / Real.log x * lll x :=
      mul_le_mul_of_nonneg_left hlll (div_nonneg (Real.sqrt_nonneg x) hlogpos.le)

/-- (√x / log x) · log(log(log x)) ≥ 0 eventually. -/
theorem sqrt_div_log_mul_lll_eventually_nonneg :
    ∀ᶠ x in atTop, 0 ≤ Real.sqrt x / Real.log x * lll x := by
  filter_upwards [lll_eventually_ge_one, eventually_gt_atTop 1] with x hlll hx
  exact mul_nonneg (div_nonneg (Real.sqrt_nonneg x) (Real.log_pos hx).le)
    (le_trans zero_le_one hlll)

/-- log x ≤ x^δ for x sufficiently large (any δ > 0).
From isLittleO_log_rpow_atTop: log = o(x^δ) at ∞. -/
theorem log_le_rpow_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x in atTop, Real.log x ≤ x ^ δ := by
  have h := (isLittleO_log_rpow_atTop hδ).bound one_pos
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx_ge
  simp only [Real.norm_eq_abs, one_mul] at hx
  calc Real.log x ≤ |Real.log x| := le_abs_self _
    _ ≤ |x ^ δ| := hx
    _ = x ^ δ := abs_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) δ)

/-- lll x ≤ x^δ for x sufficiently large (any δ > 0).
From log x ≤ x^δ applied 3 times (composing). -/
theorem lll_le_rpow_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x in atTop, lll x ≤ x ^ δ := by
  -- lll x = log(log(log x)). We use: log u ≤ u^δ for large u, and u = log(log x) etc.
  -- For large x: log(log(log x)) ≤ (log(log x))^δ ≤ (log x)^{δ²} ≤ x^{δ³}
  -- But we want lll x ≤ x^δ, so we use δ' = δ^{1/3} at each step.
  -- Simpler: lll x ≤ log(log x) ≤ log x ≤ x^δ for large enough x.
  -- Since lll x = log(log(log x)) ≤ log(log x) (for log(log x) ≥ e) ≤ log x ≤ x^δ.
  filter_upwards [log_le_rpow_eventually δ hδ,
    eventually_ge_atTop (Real.exp (Real.exp (Real.exp 1)))] with x hlog hx
  unfold lll
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlogx_ge : Real.exp (Real.exp 1) ≤ Real.log x := by
    rwa [← Real.log_exp (Real.exp (Real.exp 1)), Real.log_le_log_iff (Real.exp_pos _) hx_pos]
  have hlogx_pos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hlogx_ge
  have hloglogx_ge : Real.exp 1 ≤ Real.log (Real.log x) := by
    rwa [← Real.log_exp (Real.exp 1), Real.log_le_log_iff (Real.exp_pos _) hlogx_pos]
  have hloglogx_pos : 0 < Real.log (Real.log x) := lt_of_lt_of_le (Real.exp_pos _) hloglogx_ge
  -- log(log(log x)) ≤ log(log x) (since log is increasing and log(log x) ≥ e ≥ log(log(log x)) needs...)
  -- Actually use: for u ≥ e, log u ≤ u, so log(log(log x)) ≤ log(log x) ≤ log x ≤ x^δ
  -- Key fact: log u ≤ u for u > 0 (from exp(log u) = u ≥ 1 + log u)
  have log_le_self : ∀ u : ℝ, 0 < u → Real.log u ≤ u := by
    intro u hu
    have h1 : Real.log u + 1 ≤ Real.exp (Real.log u) := Real.add_one_le_exp (Real.log u)
    rw [Real.exp_log hu] at h1; linarith
  calc Real.log (Real.log (Real.log x))
      ≤ Real.log (Real.log x) := log_le_self _ hloglogx_pos
    _ ≤ Real.log x := log_le_self _ hlogx_pos
    _ ≤ x ^ δ := hlog

/-- √x · lll x ≤ x^α eventually, for any α > 1/2.
Key domination lemma: x^{1/2} · lll x ≤ x^{1/2} · x^{δ} = x^{1/2+δ} ≤ x^α
where δ = α - 1/2 > 0. -/
theorem sqrt_mul_lll_le_rpow (α : ℝ) (hα : 1/2 < α) :
    ∀ᶠ x in atTop, Real.sqrt x * lll x ≤ x ^ α := by
  have hδ : 0 < α - 1/2 := by linarith
  filter_upwards [lll_le_rpow_eventually (α - 1/2) hδ,
    eventually_ge_atTop (1 : ℝ)] with x hlll hx
  have hx_pos : 0 < x := lt_of_lt_of_le one_pos hx
  calc Real.sqrt x * lll x
      ≤ Real.sqrt x * x ^ (α - 1/2) := by
        apply mul_le_mul_of_nonneg_left hlll (Real.sqrt_nonneg x)
    _ = x ^ (1/2 : ℝ) * x ^ (α - 1/2) := by
        rw [Real.sqrt_eq_rpow x]
    _ = x ^ α := by
        rw [← Real.rpow_add hx_pos]
        congr 1; ring

/-- √x/log x · lll x ≤ x^α eventually, for any α > 1/2.
Follows from √x/log x ≤ √x (for log x ≥ 1) and √x · lll x ≤ x^α. -/
theorem sqrt_div_log_mul_lll_le_rpow (α : ℝ) (hα : 1/2 < α) :
    ∀ᶠ x in atTop, Real.sqrt x / Real.log x * lll x ≤ x ^ α := by
  filter_upwards [sqrt_mul_lll_le_rpow α hα, lll_eventually_ge_one,
    eventually_ge_atTop (Real.exp 1)] with x h_main hlll hx
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hlog_ge : 1 ≤ Real.log x := by
    rwa [← Real.log_exp 1, Real.log_le_log_iff (Real.exp_pos 1) hx_pos]
  calc Real.sqrt x / Real.log x * lll x
      ≤ Real.sqrt x * lll x := by
        exact mul_le_mul_of_nonneg_right
          (div_le_self (Real.sqrt_nonneg x) hlog_ge) (le_trans zero_le_one hlll)
    _ ≤ x ^ α := h_main

end GrowthDomination
