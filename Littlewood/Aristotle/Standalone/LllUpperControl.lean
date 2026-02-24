import Littlewood.CoreLemmas.GrowthDomination

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.LllUpperControl

open Real
open GrowthDomination

/-- Exact value of `lll` on a triple exponential. -/
theorem lll_exp_exp_exp (t : ℝ) :
    lll (Real.exp (Real.exp (Real.exp t))) = t := by
  unfold lll
  simp

/-- If `x` is sandwiched between `exp(exp(exp 1))` and `exp(exp(exp t))`, then
`lll x ≤ t`. -/
theorem lll_le_of_le_exp_exp_exp
    {x t : ℝ}
    (hx_lower : Real.exp (Real.exp (Real.exp 1)) ≤ x)
    (hx_upper : x ≤ Real.exp (Real.exp (Real.exp t))) :
    lll x ≤ t := by
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx_lower
  have hlogx_lower : Real.exp (Real.exp 1) ≤ Real.log x := by
    have hleft :
        Real.log (Real.exp (Real.exp (Real.exp 1))) ≤ Real.log x :=
      Real.log_le_log (Real.exp_pos _) hx_lower
    simpa [Real.log_exp] using hleft
  have hlogx_pos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hlogx_lower
  have hloglogx_lower : Real.exp 1 ≤ Real.log (Real.log x) := by
    have hleft :
        Real.log (Real.exp (Real.exp 1)) ≤ Real.log (Real.log x) :=
      Real.log_le_log (Real.exp_pos _) hlogx_lower
    simpa [Real.log_exp] using hleft
  have hloglogx_pos : 0 < Real.log (Real.log x) :=
    lt_of_lt_of_le (Real.exp_pos _) hloglogx_lower
  have hlogx_upper : Real.log x ≤ Real.exp (Real.exp t) := by
    have hleft :
        Real.log x ≤ Real.log (Real.exp (Real.exp (Real.exp t))) :=
      Real.log_le_log hx_pos hx_upper
    simpa [Real.log_exp] using hleft
  have hloglogx_upper : Real.log (Real.log x) ≤ Real.exp t := by
    have hleft :
        Real.log (Real.log x) ≤ Real.log (Real.exp (Real.exp t)) :=
      Real.log_le_log hlogx_pos hlogx_upper
    simpa [Real.log_exp] using hleft
  have hlogloglogx_upper : Real.log (Real.log (Real.log x)) ≤ t := by
    have hleft :
        Real.log (Real.log (Real.log x)) ≤ Real.log (Real.exp t) :=
      Real.log_le_log hloglogx_pos hloglogx_upper
    simpa [Real.log_exp] using hleft
  simpa [lll] using hlogloglogx_upper

/-- Converse direction: for sufficiently large `x`, `lll x ≤ t` forces
`x ≤ exp(exp(exp t))`. -/
theorem le_exp_exp_exp_of_lll_le
    {x t : ℝ}
    (hx_lower : Real.exp (Real.exp (Real.exp 1)) ≤ x)
    (hlll : lll x ≤ t) :
    x ≤ Real.exp (Real.exp (Real.exp t)) := by
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx_lower
  have hlogx_lower : Real.exp (Real.exp 1) ≤ Real.log x := by
    have hleft :
        Real.log (Real.exp (Real.exp (Real.exp 1))) ≤ Real.log x :=
      Real.log_le_log (Real.exp_pos _) hx_lower
    simpa [Real.log_exp] using hleft
  have hlogx_pos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hlogx_lower
  have hloglogx_lower : Real.exp 1 ≤ Real.log (Real.log x) := by
    have hleft :
        Real.log (Real.exp (Real.exp 1)) ≤ Real.log (Real.log x) :=
      Real.log_le_log (Real.exp_pos _) hlogx_lower
    simpa [Real.log_exp] using hleft
  have hloglogx_pos : 0 < Real.log (Real.log x) :=
    lt_of_lt_of_le (Real.exp_pos _) hloglogx_lower
  have hloglogx_upper : Real.log (Real.log x) ≤ Real.exp t := by
    have hexp := Real.exp_le_exp.mpr hlll
    simpa [lll, Real.exp_log hloglogx_pos] using hexp
  have hlogx_upper : Real.log x ≤ Real.exp (Real.exp t) := by
    have hexp := Real.exp_le_exp.mpr hloglogx_upper
    simpa [Real.exp_log hlogx_pos] using hexp
  have hx_upper : x ≤ Real.exp (Real.exp (Real.exp t)) := by
    have hexp := Real.exp_le_exp.mpr hlogx_upper
    simpa [Real.exp_log hx_pos] using hexp
  exact hx_upper

/-- A convenient corollary in the exact shape needed for coefficient estimates. -/
theorem two_mul_lll_le_two_mul_of_le_exp_exp_exp
    {x t : ℝ}
    (hx_lower : Real.exp (Real.exp (Real.exp 1)) ≤ x)
    (hx_upper : x ≤ Real.exp (Real.exp (Real.exp t))) :
    2 * lll x ≤ 2 * t := by
  exact mul_le_mul_of_nonneg_left
    (lll_le_of_le_exp_exp_exp hx_lower hx_upper) (by positivity)

/-- Specialization with a half-parameter: if `x ≤ exp(exp(exp (c/2)))`, then
`2 * lll x ≤ c`. -/
theorem two_mul_lll_le_of_le_exp_exp_exp_half
    {x c : ℝ}
    (hx_lower : Real.exp (Real.exp (Real.exp 1)) ≤ x)
    (hx_upper : x ≤ Real.exp (Real.exp (Real.exp (c / 2)))) :
    2 * lll x ≤ c := by
  have h2 : 2 * lll x ≤ 2 * (c / 2) :=
    two_mul_lll_le_two_mul_of_le_exp_exp_exp hx_lower hx_upper
  nlinarith

/-- Converse half-parameter form:
if `2 * lll x ≤ c`, then (for sufficiently large `x`) one gets the exact tower
upper bound `x ≤ exp(exp(exp (c/2)))`. -/
theorem le_exp_exp_exp_half_of_two_mul_lll_le
    {x c : ℝ}
    (hx_lower : Real.exp (Real.exp (Real.exp 1)) ≤ x)
    (hcoeff : 2 * lll x ≤ c) :
    x ≤ Real.exp (Real.exp (Real.exp (c / 2))) := by
  have hlll : lll x ≤ c / 2 := by nlinarith [hcoeff]
  exact le_exp_exp_exp_of_lll_le hx_lower hlll

end Aristotle.Standalone.LllUpperControl
