/-
Abel summation infrastructure: ψ-level explicit formula → π-level explicit formula.

This file provides sorry-free analytic lemmas needed to close the `pi_approx`
sorry in `PerronExplicitFormulaProvider.lean`. These are pure-Mathlib results
about asymptotics and real analysis — no Littlewood-specific imports needed.

## Key results

1. `log_sq_isLittleO_sqrt`: (logx)² = o(√x)
2. `log_cube_isLittleO_sqrt`: (logx)³ = o(√x)
3. `log_sq_eventually_le_eps_sqrt`: ∀ε>0, ∀ᶠ x, (logx)² ≤ ε·√x
4. `logT_sq_div_sqrtT_tendsto_zero`: (logT)²/√T → 0
5. `exists_T_perron_error_small`: ∀ C ε > 0, ∃ T₀ ≥ 2, C·(logT₀)²/√T₀ < ε
6. `log_eventually_le_eps_sqrt_div_log`: ∀ε>0, ∀ᶠ x, logx ≤ ε·(√x/logx)
7. `remainder_bound_div_log_eventually_small`: If ∀ᶠ x, |R(x)| ≤ C·(logx)²,
   then ∀ᶠ x, |R(x)|/logx ≤ ε·(√x/logx).
8. `exists_T_and_eventually_small`: For any C₂ > 0, ε > 0, there exists T₀ ≥ 2
   such that eventually C₂·(√x·(logT₀)²/√T₀ + (logx)²)/logx ≤ ε·(√x/logx).

## Proof path context

The `pi_approx` sorry (PerronExplicitFormulaProvider.lean:1704) needs:
- ψ-level bound: |ψ(x) - x + Σ Re(x^ρ/ρ)| ≤ C₂·(√x·(logT)²/√T + (logx)²)
  from `general_explicit_formula_from_perron`
- Division by logx and Abel summation ψ → π
- Choosing T to make (logT)²/√T small, then x large

This file provides the asymptotic domination lemmas for the final steps.
The main workhorse is `exists_T_and_eventually_small`, which gives the
"choose T then choose x₀" argument in one package.

SORRY COUNT: 0

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.BigOperators
import Mathlib.Topology.Algebra.Order.LiminfLimsup

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace AbelSummationPsiPi

open Real Filter Asymptotics

/-! ## Part 1: Basic asymptotic domination

These reproduce results from PerronAssumptionsBridge in a standalone,
cycle-free context that can be imported by PerronExplicitFormulaProvider. -/

/-- `(log x)² = o(√x)` as x → ∞.
    Proof: `log x = o(x^{1/4})` from Mathlib, squared gives `log² x = o(x^{1/2}) = o(√x)`. -/
theorem log_sq_isLittleO_sqrt :
    (fun x : ℝ => (Real.log x) ^ 2) =o[atTop] (fun x => Real.sqrt x) := by
  have h1 : (fun x : ℝ => Real.log x) =o[atTop] (fun x => x ^ ((1 : ℝ) / 4)) :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  exact ((by simp_rw [sq]; exact h1.mul h1 :
    (fun x : ℝ => (Real.log x) ^ 2) =o[atTop]
      (fun x => x ^ ((1 : ℝ) / 4) * x ^ ((1 : ℝ) / 4)))).trans_isBigO (by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [one_mul, ← rpow_add hx,
        show (1 : ℝ) / 4 + 1 / 4 = 1 / 2 from by norm_num, ← sqrt_eq_rpow])

/-- `(log x)³ = o(√x)` as x → ∞.
    This directly gives `(logx)²/(√x/logx) = (logx)³/√x → 0`, needed for
    the Abel summation step in `pi_approx`. -/
theorem log_cube_isLittleO_sqrt :
    (fun x : ℝ => (Real.log x) ^ 3) =o[atTop] (fun x => Real.sqrt x) := by
  have h1 : (fun x : ℝ => Real.log x) =o[atTop] (fun x => x ^ ((1 : ℝ) / 6)) :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)
  have hlog_o : (fun x : ℝ => (Real.log x) ^ 3) =o[atTop]
      (fun x => x ^ ((1 : ℝ) / 6) * (x ^ ((1 : ℝ) / 6) * x ^ ((1 : ℝ) / 6))) := by
    have : (fun x : ℝ => (Real.log x) ^ 3) = (fun x => Real.log x * (Real.log x * Real.log x)) :=
      funext (fun x => by ring)
    rw [this]; exact h1.mul (h1.mul h1)
  exact hlog_o.trans_isBigO (by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [one_mul, ← rpow_add hx, ← rpow_add hx,
        show (1 : ℝ) / 6 + ((1 : ℝ) / 6 + 1 / 6) = 1 / 2 from by norm_num,
        ← sqrt_eq_rpow])

/-- `(logT)²/√T → 0` as T → ∞. -/
theorem logT_sq_div_sqrtT_tendsto_zero :
    Tendsto (fun T : ℝ => (Real.log T) ^ 2 / Real.sqrt T)
      atTop (nhds 0) :=
  IsLittleO.tendsto_div_nhds_zero log_sq_isLittleO_sqrt

/-- For any ε > 0, eventually `(logx)² ≤ ε·√x`. -/
theorem log_sq_eventually_le_eps_sqrt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop, (Real.log x) ^ 2 ≤ ε * Real.sqrt x := by
  filter_upwards [log_sq_isLittleO_sqrt.def hε, eventually_ge_atTop (0 : ℝ)]
    with x hx _
  calc (Real.log x) ^ 2 = ‖(Real.log x) ^ 2‖ := by
        rw [norm_of_nonneg (sq_nonneg _)]
    _ ≤ ε * ‖Real.sqrt x‖ := hx
    _ = ε * Real.sqrt x := by rw [norm_of_nonneg (sqrt_nonneg _)]

/-- For any C > 0 and ε > 0, there exists T₀ ≥ 2 such that
    `C · (logT₀)² / √T₀ < ε`. -/
theorem exists_T_perron_error_small (C_coeff : ℝ) (hC : 0 < C_coeff) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ C_coeff * ((Real.log T₀) ^ 2 / Real.sqrt T₀) < ε := by
  have h_tend := logT_sq_div_sqrtT_tendsto_zero
  rw [Metric.tendsto_nhds] at h_tend
  obtain ⟨S, hS⟩ := eventually_atTop.1 (h_tend (ε / C_coeff) (div_pos hε hC))
  set T₀ := max S 2
  refine ⟨T₀, le_max_right _ _, ?_⟩
  have h_close := hS T₀ (le_max_left _ _)
  rw [Real.dist_eq] at h_close
  simp only [sub_zero, abs_of_nonneg (div_nonneg (sq_nonneg _) (sqrt_nonneg _))] at h_close
  calc C_coeff * ((Real.log T₀) ^ 2 / Real.sqrt T₀)
      < C_coeff * (ε / C_coeff) := mul_lt_mul_of_pos_left h_close hC
    _ = ε := by field_simp

/-! ## Part 2: Eventually-domination at the √x/logx scale -/

/-- Eventually `Real.log x > 0`. -/
theorem log_eventually_pos : ∀ᶠ x in atTop, (0 : ℝ) < Real.log x := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact Real.log_pos hx

/-- Eventually `Real.sqrt x > 0`. -/
theorem sqrt_eventually_pos : ∀ᶠ x in atTop, (0 : ℝ) < Real.sqrt x := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact Real.sqrt_pos.mpr hx

/-- Eventually `0 < √x / logx`. -/
theorem sqrt_div_log_eventually_pos : ∀ᶠ x in atTop, (0 : ℝ) < Real.sqrt x / Real.log x := by
  filter_upwards [sqrt_eventually_pos, log_eventually_pos] with x hsx hlx
  exact div_pos hsx hlx

/-- For any ε > 0, eventually `logx ≤ ε · (√x / logx)`.
    Equivalent to `(logx)² ≤ ε · √x`, the key fact that
    `C·logx = o(√x/logx)`. -/
theorem log_eventually_le_eps_sqrt_div_log (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop, Real.log x ≤ ε * (Real.sqrt x / Real.log x) := by
  filter_upwards [log_sq_eventually_le_eps_sqrt ε hε, log_eventually_pos] with x hx hlx
  have key : Real.log x * Real.log x ≤ ε * Real.sqrt x := by nlinarith [sq (Real.log x)]
  calc Real.log x
      = Real.log x * Real.log x / Real.log x := by rw [mul_div_cancel_right₀ _ (ne_of_gt hlx)]
    _ ≤ ε * Real.sqrt x / Real.log x := div_le_div_of_nonneg_right key hlx.le
    _ = ε * (Real.sqrt x / Real.log x) := by rw [mul_div_assoc']

/-! ## Part 3: Remainder-over-log bounds at the √x/logx scale

These lemmas handle the key algebraic step: if `|R(x)| ≤ C·(logx)²`,
then dividing by `logx` gives `|R(x)/logx| ≤ C·logx`,
and eventually `C·logx ≤ ε·(√x/logx)`. -/

/-- If `|R(x)| ≤ C · (logx)²` eventually, then eventually
    `|R(x)| / logx ≤ ε · (√x / logx)`.

    Proof: |R(x)|/logx ≤ C·logx, and eventually C·logx ≤ ε·√x/logx
    since (logx)² = o(√x). -/
theorem remainder_bound_div_log_eventually_small
    (C_bound : ℝ) (hC : 0 < C_bound)
    (R : ℝ → ℝ)
    (hR : ∀ᶠ x in atTop, |R x| ≤ C_bound * (Real.log x) ^ 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop, |R x| / Real.log x ≤ ε * (Real.sqrt x / Real.log x) := by
  filter_upwards [hR, log_sq_eventually_le_eps_sqrt (ε / C_bound) (div_pos hε hC),
                  log_eventually_pos] with x hRx hlog hlx
  have hlog' : Real.log x * Real.log x ≤ (ε / C_bound) * Real.sqrt x := by
    nlinarith [sq (Real.log x)]
  calc |R x| / Real.log x
      ≤ (C_bound * (Real.log x) ^ 2) / Real.log x :=
        div_le_div_of_nonneg_right hRx hlx.le
    _ = C_bound * Real.log x := by field_simp
    _ = C_bound * (Real.log x * Real.log x / Real.log x) := by
        rw [mul_div_cancel_right₀ _ (ne_of_gt hlx)]
    _ ≤ C_bound * ((ε / C_bound) * Real.sqrt x / Real.log x) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog' hlx.le) hC.le
    _ = ε * (Real.sqrt x / Real.log x) := by field_simp

/-! ## Part 4: The main workhorse for pi_approx

This packages the "choose T first, then choose x₀" argument. -/

/-- For any C₂ > 0, ε > 0, there exist T₀ ≥ 2 and eventually:
    C₂ · (√x · (logT₀)²/√T₀ + (logx)²) / logx ≤ ε · (√x/logx).

    This is the main workhorse for `pi_approx`. The proof:
    1. Choose T₀ so C₂·(logT₀)²/√T₀ < ε/2
    2. For x large enough: C₂·logx ≤ (ε/2)·(√x/logx)
    3. Sum the two pieces. -/
theorem exists_T_and_eventually_small
    (C₂ : ℝ) (hC₂ : 0 < C₂) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧
      ∀ᶠ x in atTop,
        C₂ * (Real.sqrt x * (Real.log T₀) ^ 2 / Real.sqrt T₀ + (Real.log x) ^ 2)
          / Real.log x ≤ ε * (Real.sqrt x / Real.log x) := by
  -- Step 1: Choose T₀ so that C₂·(logT₀)²/√T₀ < ε/2
  obtain ⟨T₀, hT₀_ge, hT₀_small⟩ :=
    exists_T_perron_error_small C₂ hC₂ (ε / 2) (by linarith)
  refine ⟨T₀, hT₀_ge, ?_⟩
  -- Step 2: For x large enough, the two pieces are each ≤ (ε/2)·√x/logx
  filter_upwards [log_eventually_le_eps_sqrt_div_log (ε / (2 * C₂)) (by positivity),
                  log_eventually_pos, sqrt_eventually_pos] with x hlogx hlx hsx
  -- Split the LHS into piece1 + piece2
  have h_expand : C₂ * (Real.sqrt x * (Real.log T₀) ^ 2 / Real.sqrt T₀ + (Real.log x) ^ 2)
      / Real.log x =
      C₂ * (Real.sqrt x * (Real.log T₀) ^ 2 / Real.sqrt T₀) / Real.log x +
        C₂ * (Real.log x) ^ 2 / Real.log x := by ring
  rw [h_expand]
  -- Piece 1: = C₂·(logT₀)²/√T₀ · √x/logx < (ε/2)·√x/logx
  have h_piece1 : C₂ * (Real.sqrt x * (Real.log T₀) ^ 2 / Real.sqrt T₀) / Real.log x
      = C₂ * ((Real.log T₀) ^ 2 / Real.sqrt T₀) * (Real.sqrt x / Real.log x) := by ring
  -- Piece 2: = C₂·logx
  have h_piece2 : C₂ * (Real.log x) ^ 2 / Real.log x = C₂ * Real.log x := by field_simp
  rw [h_piece1, h_piece2]
  have h1 : C₂ * ((Real.log T₀) ^ 2 / Real.sqrt T₀) * (Real.sqrt x / Real.log x)
      < (ε / 2) * (Real.sqrt x / Real.log x) :=
    mul_lt_mul_of_pos_right hT₀_small (div_pos hsx hlx)
  have h2 : C₂ * Real.log x ≤ (ε / 2) * (Real.sqrt x / Real.log x) := by
    calc C₂ * Real.log x
        ≤ C₂ * ((ε / (2 * C₂)) * (Real.sqrt x / Real.log x)) :=
          mul_le_mul_of_nonneg_left hlogx hC₂.le
      _ = (ε / 2) * (Real.sqrt x / Real.log x) := by field_simp
  linarith

/-! ## Part 5: Utility lemmas -/

/-- Absolute value through division by a positive number. -/
theorem abs_div_of_pos (a b : ℝ) (hb : 0 < b) : |a / b| = |a| / b := by
  rw [abs_div, abs_of_pos hb]

/-- Eventually x ≥ 2. -/
theorem eventually_ge_two : ∀ᶠ x in atTop, (2 : ℝ) ≤ x := eventually_ge_atTop 2

/-! ## Part 6: Asymptotic domination for Abel bridge corrections

These lemmas connect ψ-level explicit formulas to π-level by providing
the asymptotic absorption needed for the Abel summation step:
  π(x) - li(x) = (ψ(x) - x)/logx + O(√x/(logx)²)
The O(√x/(logx)²) correction is o(√x/logx), so it can be absorbed. -/

/-- 1/logx → 0 as x → ∞. Key building block for all correction-absorption lemmas. -/
theorem inv_log_tendsto_zero :
    Tendsto (fun x : ℝ => 1 / Real.log x) atTop (nhds 0) := by
  have : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (nhds 0) :=
    Filter.Tendsto.inv_tendsto_atTop Real.tendsto_log_atTop
  simp only [one_div]; exact this

/-- Eventually log x ≥ 1 (equivalently x ≥ e). -/
theorem log_eventually_ge_one : ∀ᶠ x in atTop, (1 : ℝ) ≤ Real.log x := by
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  rwa [← Real.log_exp 1, Real.log_le_log_iff (Real.exp_pos 1)
       (lt_of_lt_of_le (Real.exp_pos 1) hx)]

/-- Eventually 0 < √x ∧ 0 < logx (joint positivity). -/
theorem sqrt_and_log_eventually_pos : ∀ᶠ x in atTop,
    0 < Real.sqrt x ∧ 0 < Real.log x := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx1
  exact ⟨Real.sqrt_pos.mpr (lt_trans one_pos hx1), Real.log_pos hx1⟩

/-- Algebraic helper: a/b² ≤ c·(a/b) when 1/b ≤ c, a ≥ 0, b > 0. -/
theorem div_sq_le_mul_div_of_inv_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (h : 1 / b ≤ c) : a / b ^ 2 ≤ c * (a / b) := by
  have hrw : a / b ^ 2 = (1 / b) * (a / b) := by field_simp
  rw [hrw]
  exact mul_le_mul_of_nonneg_right h (div_nonneg ha hb.le)

/-! ## Part 7: √x/(logx)² = o(√x/logx) — prime power correction absorption

The classical Abel summation from ψ(x) to π(x) introduces a correction of
order O(√x/(logx)²). This section proves that correction is negligible
compared to the √x/logx oscillation scale. -/

/-- √x/(logx)² = o(√x/logx): the ratio 1/logx → 0.
    This is the key asymptotic for absorbing the O(√x/(logx)²) prime power
    correction when going from ψ(x)-x to π(x)-li(x) via Abel summation. -/
theorem sqrt_div_log_sq_isLittleO_sqrt_div_log :
    (fun x : ℝ => Real.sqrt x / (Real.log x) ^ 2) =o[atTop]
      (fun x => Real.sqrt x / Real.log x) := by
  rw [isLittleO_iff]
  intro c hc
  have h_tend := inv_log_tendsto_zero
  rw [Metric.tendsto_nhds] at h_tend
  filter_upwards [h_tend c hc, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  rw [Real.dist_eq, sub_zero] at hx
  have hlog_pos : 0 < Real.log x := Real.log_pos hx1
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := sqrt_nonneg x
  have h_inv_bound : 1 / Real.log x ≤ c := le_of_lt (lt_of_abs_lt hx)
  rw [norm_of_nonneg (div_nonneg hsqrt_nonneg (sq_nonneg _)),
      norm_of_nonneg (div_nonneg hsqrt_nonneg hlog_pos.le)]
  exact div_sq_le_mul_div_of_inv_le hsqrt_nonneg hlog_pos h_inv_bound

/-- For any ε > 0, eventually √x/(logx)² ≤ ε · √x/logx. -/
theorem sqrt_div_log_sq_eventually_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop, Real.sqrt x / (Real.log x) ^ 2 ≤ ε * (Real.sqrt x / Real.log x) := by
  have h := sqrt_div_log_sq_isLittleO_sqrt_div_log.def hε
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hlog_pos : 0 < Real.log x := Real.log_pos hx1
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := sqrt_nonneg x
  calc Real.sqrt x / (Real.log x) ^ 2
      = ‖Real.sqrt x / (Real.log x) ^ 2‖ := by
        rw [norm_of_nonneg (div_nonneg hsqrt_nonneg (sq_nonneg _))]
    _ ≤ ε * ‖Real.sqrt x / Real.log x‖ := hx
    _ = ε * (Real.sqrt x / Real.log x) := by
        rw [norm_of_nonneg (div_nonneg hsqrt_nonneg hlog_pos.le)]

/-- √x/(logx)² ≤ √x/logx pointwise for x ≥ e. -/
theorem sqrt_div_log_sq_le_sqrt_div_log_eventually :
    ∀ᶠ x in atTop, Real.sqrt x / (Real.log x) ^ 2 ≤ Real.sqrt x / Real.log x := by
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  have hx_pos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hlog_ge : 1 ≤ Real.log x := by
    rwa [← Real.log_exp 1, Real.log_le_log_iff (Real.exp_pos 1) hx_pos]
  have hlog_pos : 0 < Real.log x := lt_of_lt_of_le one_pos hlog_ge
  apply div_le_div_of_nonneg_left (Real.sqrt_pos.mpr hx_pos).le hlog_pos
  calc Real.log x = Real.log x * 1 := (mul_one _).symm
    _ ≤ Real.log x * Real.log x := mul_le_mul_of_nonneg_left hlog_ge hlog_pos.le
    _ = (Real.log x) ^ 2 := by ring

/-! ## Part 8: x/(logx)² = o(x/logx) — li(x) approximation correction

The standard approximation li(x) = x/logx + O(x/(logx)²) introduces a
correction at the x/(logx)² scale. This section proves it is negligible
compared to x/logx. -/

/-- x/(logx)² = o(x/logx): the li approximation correction is absorbed.
    Proof: ratio = 1/logx → 0, same pattern as the √x case. -/
theorem x_div_log_sq_isLittleO_x_div_log :
    (fun x : ℝ => x / (Real.log x) ^ 2) =o[atTop] (fun x => x / Real.log x) := by
  rw [isLittleO_iff]
  intro c hc
  have h_tend := inv_log_tendsto_zero
  rw [Metric.tendsto_nhds] at h_tend
  filter_upwards [h_tend c hc, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  rw [Real.dist_eq, sub_zero] at hx
  have hlog_pos : 0 < Real.log x := Real.log_pos hx1
  have hx_nonneg : 0 ≤ x := le_of_lt (lt_trans one_pos hx1)
  have h_inv_bound : 1 / Real.log x ≤ c := le_of_lt (lt_of_abs_lt hx)
  rw [norm_of_nonneg (div_nonneg hx_nonneg (sq_nonneg _)),
      norm_of_nonneg (div_nonneg hx_nonneg hlog_pos.le)]
  exact div_sq_le_mul_div_of_inv_le hx_nonneg hlog_pos h_inv_bound

/-- For any ε > 0, eventually x/(logx)² ≤ ε · x/logx. -/
theorem x_div_log_sq_eventually_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop, x / (Real.log x) ^ 2 ≤ ε * (x / Real.log x) := by
  have h := x_div_log_sq_isLittleO_x_div_log.def hε
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hlog_pos : 0 < Real.log x := Real.log_pos hx1
  have hx_nonneg : 0 ≤ x := le_of_lt (lt_trans one_pos hx1)
  calc x / (Real.log x) ^ 2
      = ‖x / (Real.log x) ^ 2‖ := by
        rw [norm_of_nonneg (div_nonneg hx_nonneg (sq_nonneg _))]
    _ ≤ ε * ‖x / Real.log x‖ := hx
    _ = ε * (x / Real.log x) := by
        rw [norm_of_nonneg (div_nonneg hx_nonneg hlog_pos.le)]

/-! ## Part 9: Abel bridge combinators — triangle inequality + absorption

These combinators package the full Abel summation bridge argument:
1. Triangle inequality: |f + S| ≤ |f - g| + |g + S|
2. Absorption: D·√x/(logx)² ≤ (ε/2)·√x/logx for large x
3. Combined: if correction is O(√x/(logx)²) and ψ-level bound is o(√x/logx),
   then π-level bound is o(√x/logx). -/

/-- Triangle inequality for the Abel bridge.
    If |π(x)-li(x) - (ψ(x)-x)/logx| ≤ correction(x)
    and |(ψ(x)-x)/logx + Σ/logx| ≤ main_err(x),
    then |π(x)-li(x) + Σ/logx| ≤ correction(x) + main_err(x). -/
theorem abel_bridge_triangle
    (f g S_val correction main_err : ℝ → ℝ)
    (h_corr : ∀ᶠ x in atTop, |f x - g x| ≤ correction x)
    (h_main : ∀ᶠ x in atTop, |g x + S_val x| ≤ main_err x) :
    ∀ᶠ x in atTop, |f x + S_val x| ≤ correction x + main_err x := by
  filter_upwards [h_corr, h_main] with x hc hm
  calc |f x + S_val x|
      = |(f x - g x) + (g x + S_val x)| := by ring_nf
    _ ≤ |f x - g x| + |g x + S_val x| := abs_add_le _ _
    _ ≤ correction x + main_err x := add_le_add hc hm

/-- Dividing a ψ-level bound by logx preserves the inequality. -/
theorem div_log_preserves_bound
    (f B : ℝ → ℝ)
    (hB : ∀ᶠ x in atTop, |f x| ≤ B x)
    (hB_nn : ∀ᶠ x in atTop, 0 ≤ B x) :
    ∀ᶠ x in atTop, |f x / Real.log x| ≤ B x / Real.log x := by
  filter_upwards [hB, hB_nn, eventually_gt_atTop (1 : ℝ)] with x hfx _hBx hx1
  have hlog_pos : 0 < Real.log x := Real.log_pos hx1
  rw [abs_div, abs_of_pos hlog_pos]
  exact div_le_div_of_nonneg_right hfx hlog_pos.le

/-- D · √x/(logx)² is eventually ≤ (ε/2) · √x/logx, for any D, ε > 0.
    Used to absorb the Abel summation correction into the ε budget. -/
theorem correction_eventually_absorbed (D : ℝ) (hD : 0 < D) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      D * (Real.sqrt x / (Real.log x) ^ 2) ≤ (ε / 2) * (Real.sqrt x / Real.log x) := by
  have h_tend := inv_log_tendsto_zero
  rw [Metric.tendsto_nhds] at h_tend
  filter_upwards [h_tend (ε / (2 * D)) (by positivity), eventually_gt_atTop (1 : ℝ)]
    with x hx hx1
  rw [Real.dist_eq, sub_zero] at hx
  have hlog_pos : 0 < Real.log x := Real.log_pos hx1
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := sqrt_nonneg x
  have h_inv : 1 / Real.log x ≤ ε / (2 * D) := le_of_lt (lt_of_abs_lt hx)
  calc D * (Real.sqrt x / (Real.log x) ^ 2)
      = D * ((1 / Real.log x) * (Real.sqrt x / Real.log x)) := by congr 1; field_simp
    _ ≤ D * ((ε / (2 * D)) * (Real.sqrt x / Real.log x)) := by
        apply mul_le_mul_of_nonneg_left _ hD.le
        exact mul_le_mul_of_nonneg_right h_inv (div_nonneg hsqrt_nonneg hlog_pos.le)
    _ = (ε / 2) * (Real.sqrt x / Real.log x) := by field_simp

/-- Full Abel bridge with adjustable ε.
    If |f(x) - g(x)| ≤ D·√x/(logx)² (correction from Abel summation ψ→π)
    and for every δ > 0, eventually |g(x) + S(x)| ≤ δ·√x/logx (ψ-level bound),
    then for every ε > 0, eventually |f(x) + S(x)| ≤ ε·√x/logx.

    This is the main structure needed to close `pi_approx`:
    f = π(x)-li(x), g = (ψ(x)-x)/logx, S = Σ Re(x^ρ/ρ)/logx. -/
theorem abel_bridge_adjustable
    (f g S_val : ℝ → ℝ)
    (D : ℝ) (hD : 0 < D) (ε : ℝ) (hε : 0 < ε)
    (h_corr : ∀ᶠ x in atTop, |f x - g x| ≤ D * (Real.sqrt x / (Real.log x) ^ 2))
    (h_main : ∀ (δ : ℝ), 0 < δ → ∀ᶠ x in atTop,
      |g x + S_val x| ≤ δ * (Real.sqrt x / Real.log x)) :
    ∀ᶠ x in atTop,
      |f x + S_val x| ≤ ε * (Real.sqrt x / Real.log x) := by
  have h_corr_abs := correction_eventually_absorbed D hD ε hε
  have h_main_half := h_main (ε / 2) (by linarith)
  filter_upwards [h_corr, h_corr_abs, h_main_half] with x hc hca hm
  calc |f x + S_val x|
      = |(f x - g x) + (g x + S_val x)| := by ring_nf
    _ ≤ |f x - g x| + |g x + S_val x| := abs_add_le _ _
    _ ≤ D * (Real.sqrt x / (Real.log x) ^ 2) + (ε / 2) * (Real.sqrt x / Real.log x) :=
        add_le_add hc hm
    _ ≤ (ε / 2) * (Real.sqrt x / Real.log x) + (ε / 2) * (Real.sqrt x / Real.log x) :=
        add_le_add_left hca _
    _ = ε * (Real.sqrt x / Real.log x) := by ring

/-! ## Part 10: Convenience wrappers -/

/-- If f = o(√x/logx), then |f x| ≤ ε·√x/logx eventually.
    Convenience for unwrapping isLittleO into an eventually bound. -/
theorem isLittleO_sqrt_div_log_eventually
    (f : ℝ → ℝ) (hf : f =o[atTop] (fun x => Real.sqrt x / Real.log x))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop, |f x| ≤ ε * (Real.sqrt x / Real.log x) := by
  have h := hf.def hε
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hlog_pos : 0 < Real.log x := Real.log_pos hx1
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := sqrt_nonneg x
  calc |f x| = ‖f x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ε * ‖Real.sqrt x / Real.log x‖ := hx
    _ = ε * (Real.sqrt x / Real.log x) := by
        rw [norm_of_nonneg (div_nonneg hsqrt_nonneg hlog_pos.le)]

/-- Monotonic scaling: upgrade bounds via monotonicity of the comparison function. -/
theorem eventually_abs_le_scale_mono
    (f g h : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hfg : ∀ᶠ x in atTop, |f x| ≤ C * g x)
    (hgh : ∀ᶠ x in atTop, g x ≤ h x) :
    ∀ᶠ x in atTop, |f x| ≤ C * h x := by
  filter_upwards [hfg, hgh] with x hfx hgx
  exact le_trans hfx (mul_le_mul_of_nonneg_left hgx hC)

/-! ## Part 11: ψ-level explicit formula → π-level via division by logx

The ψ-level explicit formula gives:
  |ψ(x) - x + Σ Re(x^ρ/ρ)| ≤ C₂·(√x·(logT)²/√T + (logx)²)

Dividing both sides by logx:
  |(ψ(x)-x)/logx + (Σ Re(x^ρ/ρ))/logx| ≤ C₂·(√x·(logT)²/√T + (logx)²)/logx

The RHS = C₂·(√x·(logT)²/(√T·logx) + logx), which for fixed T and large x
is eventually ≤ ε·(√x/logx) by `exists_T_and_eventually_small`.

These lemmas formalize the division-by-logx step, independent of any
project-specific definitions. -/

/-- Dividing a bound by a positive quantity preserves it.
    If |a| ≤ B and B ≥ 0 and d > 0, then |a/d| ≤ B/d. -/
theorem abs_div_le_div_of_pos {a B d : ℝ} (hab : |a| ≤ B)
    (hd : 0 < d) : |a / d| ≤ B / d := by
  rw [abs_div, abs_of_pos hd]
  exact div_le_div_of_nonneg_right hab hd.le

/-- If |f(x) + g(x)| ≤ B(x) eventually, and logx > 0 eventually,
    then |f(x)/logx + g(x)/logx| ≤ B(x)/logx eventually.

    This is the core algebraic step for converting ψ-level bounds to
    π-level bounds by dividing through by logx. -/
theorem sum_div_log_bound
    (f g B : ℝ → ℝ)
    (hB : ∀ᶠ x in atTop, |f x + g x| ≤ B x) :
    ∀ᶠ x in atTop, |f x / Real.log x + g x / Real.log x| ≤ B x / Real.log x := by
  filter_upwards [hB, log_eventually_pos] with x hfg hlx
  have : f x / Real.log x + g x / Real.log x = (f x + g x) / Real.log x := by
    rw [add_div]
  rw [this]
  exact abs_div_le_div_of_pos hfg hlx

/-- The complete π-level combinator using exists_T_and_eventually_small.

    Given:
    - A ψ-level explicit formula: for all x, T ≥ 2,
        |R(x,T)| ≤ C₂·(√x·(logT)²/√T + (logx)²)
    - Any ε > 0

    Produces: ∃ T₀ ≥ 2 such that eventually
        |R(x,T₀)| / logx ≤ ε · (√x / logx)

    This packages the "choose T then choose x₀" argument at the divided level. -/
theorem psi_bound_div_log_eventually_small
    (R : ℝ → ℝ → ℝ)
    (C₂ : ℝ) (hC₂ : 0 < C₂)
    (hR : ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |R x T| ≤ C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧
      ∀ᶠ x in atTop, |R x T₀| / Real.log x ≤ ε * (Real.sqrt x / Real.log x) := by
  obtain ⟨T₀, hT₀, hev⟩ := exists_T_and_eventually_small C₂ hC₂ ε hε
  refine ⟨T₀, hT₀, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (2 : ℝ), log_eventually_pos] with x hx hx2 hlx
  have hR_bound := hR x T₀ hx2 hT₀
  calc |R x T₀| / Real.log x
      ≤ (C₂ * (Real.sqrt x * (Real.log T₀) ^ 2 / Real.sqrt T₀ + (Real.log x) ^ 2))
          / Real.log x := div_le_div_of_nonneg_right hR_bound hlx.le
    _ = C₂ * (Real.sqrt x * (Real.log T₀) ^ 2 / Real.sqrt T₀ + (Real.log x) ^ 2)
          / Real.log x := by ring_nf
    _ ≤ ε * (Real.sqrt x / Real.log x) := hx

/-- Variant of `psi_bound_div_log_eventually_small` that directly produces the
    "for all ε, eventually" form needed by `PiApproxFromExplicitFormulaHyp`.

    Given a ψ-level bound parameterized by a finset S (with the S-dependence
    abstracted away), and an Abel correction bound, produces the π-level
    eventually-small statement. -/
theorem pi_level_from_psi_level_and_correction
    (piErr psiDivLog sumDivLog correction : ℝ → ℝ)
    (D : ℝ) (hD : 0 < D)
    -- Abel correction: |π(x)-li(x) - (ψ(x)-x)/logx| ≤ D·√x/(logx)²
    (h_abel : ∀ᶠ x in atTop,
      |piErr x - psiDivLog x| ≤ D * (Real.sqrt x / (Real.log x) ^ 2))
    -- ψ-level explicit formula divided by logx: for all δ > 0, eventually
    -- |(ψ(x)-x)/logx + Σ/logx| ≤ δ·√x/logx
    (h_psi : ∀ δ : ℝ, 0 < δ → ∀ᶠ x in atTop,
      |psiDivLog x + sumDivLog x| ≤ δ * (Real.sqrt x / Real.log x))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      |piErr x + sumDivLog x| ≤ ε * (Real.sqrt x / Real.log x) :=
  abel_bridge_adjustable piErr psiDivLog sumDivLog D hD ε hε h_abel h_psi

/-! ## Part 12: Full explicit formula assembly for the π-level

The final theorem packages all pieces together:
1. ψ-level bound → divide by logx → for all δ eventually small
2. Abel correction → O(√x/(logx)²) → o(√x/logx)
3. Triangle inequality → π-level bound at ε·√x/logx scale

This is what PerronExplicitFormulaProvider needs to close `pi_approx_bound`. -/

/-- The ψ-level "for all δ eventually" statement from a fixed-T bound.

    If for all x,T ≥ 2: |R(x,T)| ≤ C₂·(√x·(logT)²/√T + (logx)²),
    and f(x) = R(x,T₀)/logx for some T₀,
    then for all δ > 0: eventually |f(x)| ≤ δ·√x/logx.

    This converts the "∃ T₀, eventually" form to the "∀ δ, eventually" form
    needed by `abel_bridge_adjustable`. -/
theorem psi_div_log_forall_delta_eventually
    (R : ℝ → ℝ → ℝ)
    (C₂ : ℝ) (hC₂ : 0 < C₂)
    (hR : ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |R x T| ≤ C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧
      ∀ᶠ x in atTop, |R x T₀| / Real.log x ≤ δ * (Real.sqrt x / Real.log x) :=
  psi_bound_div_log_eventually_small R C₂ hC₂ hR δ hδ

/-- Key algebraic identity: for any a, b, L with L > 0,
    a/L + b/L = (a + b)/L. Used to merge ψ-error/logx with sum/logx. -/
theorem add_div_eq_div (a b L : ℝ) (hL : L ≠ 0) :
    a / L + b / L = (a + b) / L := (add_div a b L).symm

/-- Scaling an eventually-bound by a positive factor.
    If |f(x)| ≤ B(x) eventually, then C·|f(x)| ≤ C·B(x) eventually. -/
theorem eventually_mul_le_mul_of_nonneg
    (f B : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hfB : ∀ᶠ x in atTop, |f x| ≤ B x) :
    ∀ᶠ x in atTop, C * |f x| ≤ C * B x := by
  filter_upwards [hfB] with x hx
  exact mul_le_mul_of_nonneg_left hx hC

/-- If two eventually-bounds hold, their sum holds eventually. -/
theorem eventually_add_le_add
    (f₁ f₂ B₁ B₂ : ℝ → ℝ)
    (h₁ : ∀ᶠ x in atTop, f₁ x ≤ B₁ x)
    (h₂ : ∀ᶠ x in atTop, f₂ x ≤ B₂ x) :
    ∀ᶠ x in atTop, f₁ x + f₂ x ≤ B₁ x + B₂ x := by
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  exact add_le_add hx₁ hx₂

/-- Half-ε absorption: if D·√x/(logx)² ≤ (ε/2)·√x/logx and
    δ·√x/logx ≤ (ε/2)·√x/logx (with δ = ε/2),
    then D·√x/(logx)² + δ·√x/logx ≤ ε·√x/logx.
    This is the final combination for the Abel bridge. -/
theorem half_eps_combination (D ε : ℝ) (hD : 0 < D) (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      D * (Real.sqrt x / (Real.log x) ^ 2) + (ε / 2) * (Real.sqrt x / Real.log x) ≤
        ε * (Real.sqrt x / Real.log x) := by
  filter_upwards [correction_eventually_absorbed D hD ε hε] with x hx
  linarith

/-! ## Part 13: Infrastructure for PsiExplicitFormulaFinsetHyp (Ralph C51)

The ψ-level explicit formula for finite zero sets: for any δ > 0,
  |(ψ(x) - x + Σ_{ρ∈S} x^ρ/ρ) / logx| ≤ δ · √x/logx

The key mechanism is choosing T large enough that
C·(logT)²/√T ≤ δ, then the Perron error divided by logx is δ-small. -/

/-- **Finset sum difference via sdiff**: for S ⊆ S',
    S'.sum f - S.sum f = (S' \ S).sum f.
    PROVED: Finset.sum_sdiff. -/
theorem finset_sum_sub_eq_sdiff {ι : Type*} [DecidableEq ι]
    (S S' : Finset ι) (f : ι → ℝ) (hSS' : S ⊆ S') :
    S'.sum f - S.sum f = (S' \ S).sum f := by
  rw [← Finset.sum_sdiff hSS']; ring

/-- **Eventually logx > 0**: for large x, log(x) > 0.
    PROVED: from Real.log_pos. -/
theorem log_pos_eventually :
    ∀ᶠ x in atTop, (0 : ℝ) < Real.log x := by
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
  exact Real.log_pos (by linarith)

/-- **Eventually √x/logx > 0**: for large x, √x/logx > 0.
    PROVED: positivity of sqrt and log. -/
theorem sqrt_div_log_pos_eventually :
    ∀ᶠ x in atTop, (0 : ℝ) < Real.sqrt x / Real.log x := by
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
  exact div_pos (Real.sqrt_pos_of_pos (by linarith))
    (Real.log_pos (by linarith))

/-- **Scaling by constant preserves eventually**: if ∀ᶠ x, f(x) ≤ g(x),
    then for C ≥ 0, ∀ᶠ x, C · f(x) ≤ C · g(x).
    PROVED: filter_upwards + mul_le_mul. -/
theorem eventually_scale_le (f g : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ᶠ x in atTop, f x ≤ g x) :
    ∀ᶠ x in atTop, C * f x ≤ C * g x := by
  filter_upwards [h] with x hx
  exact mul_le_mul_of_nonneg_left hx hC

/-- **Division distributes over eventually**: if ∀ᶠ x, |f(x)| ≤ B(x),
    and logx > 0 eventually, then ∀ᶠ x, |f(x)|/logx ≤ B(x)/logx.
    PROVED: division preserves order for positive divisor. -/
theorem eventually_div_log_le (f B : ℝ → ℝ)
    (h : ∀ᶠ x in atTop, |f x| ≤ B x) :
    ∀ᶠ x in atTop,
      |f x| / Real.log x ≤ B x / Real.log x := by
  filter_upwards [h, log_pos_eventually] with x hx hlx
  exact div_le_div_of_nonneg_right hx hlx.le

/-- **abs of quotient**: |f(x)/logx| = |f(x)|/logx when logx > 0.
    PROVED: abs_div + abs_of_pos. -/
theorem abs_div_log_eq (f : ℝ → ℝ) (x : ℝ) (hx : 0 < Real.log x) :
    |f x / Real.log x| = |f x| / Real.log x := by
  rw [abs_div, abs_of_pos hx]

end AbelSummationPsiPi

-- Appended atomically by Ralph C62-C70

namespace AbelSummationPsiPi_Leibniz

open Real Filter Asymptotics

/-! ## Leibniz alternating series bound (Ralph C62-C70)

Full Leibniz test: |∑_{k<n} (-1)^k a(k)| ≤ a(0) for antitone nonneg a. -/

/-- Step-2 recurrence for alternating sums. -/
theorem alternating_sum_step2 (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 2), (-1 : ℝ) ^ i * a i =
    (∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * a i) +
      (-1 : ℝ) ^ n * (a n - a (n + 1)) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have : (-1 : ℝ) ^ (n + 1) = -((-1 : ℝ) ^ n) := by ring
  rw [this]; ring

/-- Even alternating sum = paired differences. -/
theorem even_alternating_eq_paired (a : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k), (-1 : ℝ) ^ i * a i =
    ∑ j ∈ Finset.range k, (a (2 * j) - a (2 * j + 1)) := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 from by omega, alternating_sum_step2]
    rw [ih, Finset.sum_range_succ]; congr 1
    rw [Even.neg_one_pow (⟨m, by omega⟩ : Even (2 * m)), one_mul]

/-- Even partial sum nonneg for antitone sequences. -/
theorem alternating_even_sum_nonneg (a : ℕ → ℝ) (ha_anti : Antitone a) (n : ℕ) :
    0 ≤ ∑ k ∈ Finset.range (2 * n), (-1 : ℝ) ^ k * a k := by
  rw [even_alternating_eq_paired]
  exact Finset.sum_nonneg (fun j _ =>
    sub_nonneg.mpr (ha_anti (show 2 * j ≤ 2 * j + 1 from Nat.le_succ _)))

/-- Odd alternating sum = a₀ minus paired differences. -/
theorem odd_alternating_eq_sub_paired (a : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ i * a i =
    a 0 - ∑ j ∈ Finset.range k, (a (2 * j + 1) - a (2 * j + 2)) := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 from by omega, alternating_sum_step2]
    rw [ih, Finset.sum_range_succ]
    rw [Odd.neg_one_pow (⟨m, by omega⟩ : Odd (2 * m + 1))]; ring

/-- Odd partial sum ≤ a₀ for antitone sequences. -/
theorem alternating_odd_sum_le_first (a : ℕ → ℝ) (ha_anti : Antitone a) (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1), (-1 : ℝ) ^ k * a k ≤ a 0 := by
  rw [odd_alternating_eq_sub_paired]
  linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.range n) =>
    sub_nonneg.mpr (ha_anti (show 2 * j + 1 ≤ 2 * j + 2 from by omega)))]

/-- **Full Leibniz bound**: |∑_{k<n} (-1)^k a(k)| ≤ a(0) for antitone nonneg a. -/
theorem leibniz_alternating_bound (a : ℕ → ℝ) (ha_anti : Antitone a)
    (ha_nn : ∀ k, 0 ≤ a k) (n : ℕ) :
    |∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * a k| ≤ a 0 := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [show n = 2 * m from by omega, abs_le]; constructor
    · linarith [alternating_even_sum_nonneg a ha_anti m, ha_nn 0]
    · rcases m with _ | m2
      · simp [ha_nn 0]
      · rw [show 2 * (m2 + 1) = (2 * m2 + 1) + 1 from by omega, Finset.sum_range_succ]
        rw [Odd.neg_one_pow (⟨m2, by omega⟩ : Odd (2 * m2 + 1)), neg_one_mul]
        linarith [alternating_odd_sum_le_first a ha_anti m2, ha_nn (2 * m2 + 1)]
  · rw [hm, abs_le]; constructor
    · rw [Finset.sum_range_succ, Even.neg_one_pow (⟨m, by omega⟩ : Even (2 * m)), one_mul]
      linarith [alternating_even_sum_nonneg a ha_anti m, ha_nn (2 * m), ha_nn 0]
    · exact alternating_odd_sum_le_first a ha_anti m

/-- Leibniz for shifted sequence. -/
theorem leibniz_shifted (a : ℕ → ℝ) (ha_anti : Antitone a)
    (ha_nn : ∀ k, 0 ≤ a k) (j n : ℕ) :
    |∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * a (k + j)| ≤ a j := by
  have h := leibniz_alternating_bound (fun k => a (k + j))
    (fun _ _ hab => ha_anti (Nat.add_le_add_right hab j))
    (fun k => ha_nn (k + j)) n
  simpa using h

end AbelSummationPsiPi_Leibniz

-- ============================================================
-- Part 16: Supplementary asymptotic lemmas (Ralph C63-C70)
-- ============================================================

namespace AbelSummationPsiPi_Asymptotics

open Real Filter Asymptotics

noncomputable section

/-- (logx)² = o(x). -/
theorem log_sq_isLittleO_id :
    (fun x : ℝ => (Real.log x) ^ 2) =o[atTop] (fun x => x) := by
  have h1 : (fun x : ℝ => Real.log x) =o[atTop] (fun x => x ^ ((1 : ℝ) / 2)) :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  have hlog2 : (fun x : ℝ => (Real.log x) ^ 2) =o[atTop]
      (fun x => x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2)) := by
    simp_rw [sq]; exact h1.mul h1
  exact hlog2.trans_isBigO (by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [one_mul, ← rpow_add hx,
        show (1 : ℝ) / 2 + 1 / 2 = 1 from by norm_num, rpow_one])

/-- (logx)²/x → 0. -/
theorem log_sq_div_id_tendsto_zero :
    Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x) atTop (nhds 0) :=
  log_sq_isLittleO_id.tendsto_div_nhds_zero

/-- For C, δ > 0, eventually C·(logx)²/x ≤ δ. -/
theorem log_sq_div_x_eventually_small (C : ℝ) (hC : 0 < C) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x in atTop, C * (Real.log x) ^ 2 / x ≤ δ := by
  have h_tend := log_sq_div_id_tendsto_zero
  rw [Metric.tendsto_nhds] at h_tend
  filter_upwards [h_tend (δ / C) (div_pos hδ hC), eventually_gt_atTop (0 : ℝ)] with x hx hx_pos
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (sq_nonneg _) (le_of_lt hx_pos))] at hx
  have h1 : C * ((Real.log x) ^ 2 / x) < C * (δ / C) := mul_lt_mul_of_pos_left hx hC
  have h2 : C * (δ / C) = δ := mul_div_cancel₀ δ (ne_of_gt hC)
  have h3 : C * (Real.log x) ^ 2 / x = C * ((Real.log x) ^ 2 / x) := by ring
  linarith

/-- logx/x → 0. -/
theorem log_div_id_tendsto_zero :
    Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
  have h := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 from by norm_num)
  simp only [rpow_one] at h
  exact h.tendsto_div_nhds_zero

/-- logx = o(x^ε) for ε > 0. -/
theorem log_isLittleO_rpow (ε : ℝ) (hε : 0 < ε) :
    (fun x : ℝ => Real.log x) =o[atTop] (fun x => x ^ ε) :=
  isLittleO_log_rpow_atTop hε

/-- Eventually logx ≤ C·x^ε for C, ε > 0. -/
theorem log_eventually_le_rpow (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop, Real.log x ≤ C * x ^ ε := by
  have h := (log_isLittleO_rpow ε hε).def hC
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hx hx_pos
  calc Real.log x ≤ |Real.log x| := le_abs_self _
    _ = ‖Real.log x‖ := (Real.norm_eq_abs _).symm
    _ ≤ C * ‖x ^ ε‖ := hx
    _ = C * x ^ ε := by rw [norm_of_nonneg (rpow_nonneg (le_of_lt hx_pos) _)]

/-- (logx)³ = o(x). -/
theorem log_cube_isLittleO_id :
    (fun x : ℝ => (Real.log x) ^ 3) =o[atTop] (fun x => x) := by
  have h1 : (fun x : ℝ => Real.log x) =o[atTop] (fun x => x ^ ((1 : ℝ) / 3)) :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)
  have hlog3 : (fun x : ℝ => (Real.log x) ^ 3) =o[atTop]
      (fun x => x ^ ((1 : ℝ) / 3) * (x ^ ((1 : ℝ) / 3) * x ^ ((1 : ℝ) / 3))) := by
    have : (fun x : ℝ => (Real.log x) ^ 3) = (fun x => Real.log x * (Real.log x * Real.log x)) :=
      funext (fun x => by ring)
    rw [this]; exact h1.mul (h1.mul h1)
  exact hlog3.trans_isBigO (by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [one_mul, ← rpow_add hx, ← rpow_add hx,
        show (1 : ℝ) / 3 + ((1 : ℝ) / 3 + 1 / 3) = 1 from by norm_num, rpow_one])

/-- Eventually (logx)³ ≤ ε·x for any ε > 0. -/
theorem log_cube_eventually_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop, (Real.log x) ^ 3 ≤ ε * x := by
  have h := log_cube_isLittleO_id.def hε
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hx hx_pos
  calc (Real.log x) ^ 3 ≤ |(Real.log x) ^ 3| := le_abs_self _
    _ = ‖(Real.log x) ^ 3‖ := (Real.norm_eq_abs _).symm
    _ ≤ ε * ‖x‖ := hx
    _ = ε * x := by rw [norm_of_nonneg (le_of_lt hx_pos)]

/-- logx/√x → 0: log is negligible compared to square root. -/
theorem log_div_sqrt_tendsto_zero :
    Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (nhds 0) := by
  have h := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 from by norm_num)
  have h2 : (fun x : ℝ => Real.log x / Real.sqrt x) =
      (fun x => Real.log x / x ^ ((1 : ℝ) / 2)) := by
    ext x; rw [Real.sqrt_eq_rpow]
  rw [h2]; exact h.tendsto_div_nhds_zero

/-- For any C, δ > 0, eventually C·logx ≤ δ·√x.
    From logx = o(√x) via isLittleO_log_rpow_atTop. -/
theorem C_log_le_delta_sqrt (C : ℝ) (hC : 0 < C) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x in atTop, C * Real.log x ≤ δ * Real.sqrt x := by
  have h_o := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 from by norm_num)
  have h_eq : (fun x : ℝ => x ^ ((1:ℝ)/2)) = (fun x => Real.sqrt x) := by
    ext x; exact (Real.sqrt_eq_rpow x).symm
  rw [h_eq] at h_o
  have h_ev := h_o.def (show (0:ℝ) < δ / C from div_pos hδ hC)
  filter_upwards [h_ev, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hlog_eq : ‖Real.log x‖ = Real.log x := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.log_pos hx1)]
  have hsqrt_eq : ‖Real.sqrt x‖ = Real.sqrt x := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos_of_pos (by linarith))]
  calc C * Real.log x
      = C * ‖Real.log x‖ := by rw [hlog_eq]
    _ ≤ C * ((δ / C) * ‖Real.sqrt x‖) :=
        mul_le_mul_of_nonneg_left hx hC.le
    _ = δ * ‖Real.sqrt x‖ := by field_simp
    _ = δ * Real.sqrt x := by rw [hsqrt_eq]

end

end AbelSummationPsiPi_Asymptotics

-- ============================================================
-- Part 17: Harmonic-log sum estimates for VdC mode summation
-- ============================================================

namespace AbelSummationPsiPi_HarmonicLog

open Real Filter Asymptotics Finset

noncomputable section

/-! ## Harmonic-log sum bounds: Σ_{n=2}^{N} 1/log(n) ≤ C·N/log(N)

The VdC first-derivative test bounds each mode's oscillatory integral by
O(1/log(n+1)). Summing over modes n ≤ N requires bounding Σ 1/log(n+1).

By comparison with the integral ∫₂ᴺ dx/logx = li(N) - li(2), the partial
sum satisfies Σ_{n=2}^{N} 1/log(n) ≤ C·N/log(N) for large N. We prove a
cruder but sufficient bound: each term 1/log(n+1) ≤ 1/log(2) for n ≥ 1,
giving Σ ≤ N/log(2). The weighted sum Σ n^{-1/2}/log(n+1) ≤ C·√N/log(2)
then follows from the Cauchy-Schwarz / integral comparison.

These feed into the main term integral bound in HardyZFirstMomentIBP.lean. -/

/-- 1/log(n+1) ≤ 1/log(2) for all n ≥ 1 : ℕ. -/
theorem inv_log_le_inv_log2 (n : ℕ) (hn : 1 ≤ n) :
    1 / Real.log ((n : ℝ) + 1) ≤ 1 / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : (2 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hn
  have hlog_n1 : Real.log 2 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by norm_num) hn1
  exact div_le_div_of_nonneg_left (by norm_num) hlog2 hlog_n1

/-- Crude partial sum: Σ_{n∈range N, n≥1} 1/log(n+1) ≤ N/log(2). -/
theorem inv_log_partial_sum_le (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / Real.log ((n : ℝ) + 1 + 1) ≤
      (N : ℝ) / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  calc ∑ n ∈ Finset.range N, 1 / Real.log ((n : ℝ) + 1 + 1)
      ≤ ∑ _n ∈ Finset.range N, (1 / Real.log 2) := by
        apply Finset.sum_le_sum
        intro n _hn
        have : (2 : ℝ) ≤ (n : ℝ) + 1 + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
        have hlog_ge : Real.log 2 ≤ Real.log ((n : ℝ) + 1 + 1) :=
          Real.log_le_log (by norm_num) this
        exact div_le_div_of_nonneg_left (by norm_num) hlog2 hlog_ge
    _ = (N : ℝ) * (1 / Real.log 2) := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (N : ℝ) / Real.log 2 := by ring

/-- Weighted sum: Σ_{n=0}^{N-1} (n+1)^{-1/2}/log(n+2) ≤ √N / log(2).

    Each term (n+1)^{-1/2}/log(n+2) ≤ 1/log(2) (since (n+1)^{-1/2} ≤ 1).
    Sum of N such terms ≤ N/log(2).
    Sharper: Σ (n+1)^{-1/2} ≤ 2√N (integral comparison), and 1/log(n+2) ≤ 1/log(2),
    so Σ ≤ 2√N/log(2). We prove the cruder N/log(2) here. -/
theorem weighted_inv_log_sum_le (N : ℕ) :
    ∑ n ∈ Finset.range N,
      ((n : ℝ) + 1) ^ (-(1 : ℝ)/2) / Real.log ((n : ℝ) + 2) ≤
      (N : ℝ) / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  calc ∑ n ∈ Finset.range N,
        ((n : ℝ) + 1) ^ (-(1 : ℝ)/2) / Real.log ((n : ℝ) + 2)
      ≤ ∑ _n ∈ Finset.range N, (1 / Real.log 2) := by
        apply Finset.sum_le_sum
        intro n _hn
        have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hn1_ge : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
        have hn2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
        have hlog_ge : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
          Real.log_le_log (by norm_num) hn2
        have h_coef : ((n : ℝ) + 1) ^ (-(1 : ℝ)/2) ≤ 1 := by
          calc ((n : ℝ) + 1) ^ (-(1 : ℝ)/2)
              ≤ ((n : ℝ) + 1) ^ (0 : ℝ) :=
                rpow_le_rpow_of_exponent_le hn1_ge (by norm_num)
            _ = 1 := rpow_zero _
        calc ((n : ℝ) + 1) ^ (-(1 : ℝ)/2) / Real.log ((n : ℝ) + 2)
            ≤ 1 / Real.log ((n : ℝ) + 2) := by
              apply div_le_div_of_nonneg_right h_coef
              exact le_of_lt (Real.log_pos (by linarith))
          _ ≤ 1 / Real.log 2 :=
              div_le_div_of_nonneg_left (by norm_num) hlog2 hlog_ge
    _ = (N : ℝ) * (1 / Real.log 2) := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (N : ℝ) / Real.log 2 := by ring

/-- N/log(2) ≤ C·√T/log(T) when N ~ √(T/2π) and T is large enough.

    More precisely: if N ≤ √T then N/log(2) ≤ √T/log(2).
    And √T/log(2) ≤ C·√T/log(T) when log(T) ≤ C·log(2), which fails.
    So the correct bound is: N/log(2) ≤ (1/log 2)·√T = O(√T).

    For the first moment, O(√T) suffices (it's within the C·√T target). -/
theorem mode_sum_le_sqrt (N : ℕ) (T : ℝ) (hT : 2 ≤ T)
    (hN : (N : ℝ) ≤ Real.sqrt T) :
    (N : ℝ) / Real.log 2 ≤ (1 / Real.log 2) * Real.sqrt T := by
  rw [one_div, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right hN (le_of_lt (Real.log_pos (by norm_num)))

/-- Assembly: the total weighted mode sum Σ_{n<N} (n+1)^{-1/2}/log(n+2)
    is O(√T) when N ≤ √T.

    This is the key estimate for the main term contribution to the
    first moment |∫₁ᵀ Z(t) dt|. Each mode contributes O(1/log(n+2))
    from VdC, the amplitude is (n+1)^{-1/2}, and there are N ~ √T modes. -/
theorem vdc_mode_sum_bound (N : ℕ) (T : ℝ) (hT : 2 ≤ T)
    (hN : (N : ℝ) ≤ Real.sqrt T) :
    ∑ n ∈ Finset.range N,
      ((n : ℝ) + 1) ^ (-(1 : ℝ)/2) / Real.log ((n : ℝ) + 2) ≤
      (1 / Real.log 2) * Real.sqrt T :=
  le_trans (weighted_inv_log_sum_le N) (mode_sum_le_sqrt N T hT hN)

/-- The O(√T) mode sum bound is O(C·T^{1/2}) for an explicit constant. -/
theorem vdc_mode_sum_le_C_sqrt (N : ℕ) (T : ℝ) (hT : 2 ≤ T)
    (hN : (N : ℝ) ≤ Real.sqrt T) :
    ∑ n ∈ Finset.range N,
      ((n : ℝ) + 1) ^ (-(1 : ℝ)/2) / Real.log ((n : ℝ) + 2) ≤
      (1 / Real.log 2) * T ^ ((1 : ℝ)/2) := by
  have hT_pos : (0 : ℝ) < T := by linarith
  rw [show T ^ ((1 : ℝ)/2) = Real.sqrt T from (Real.sqrt_eq_rpow T).symm]
  exact vdc_mode_sum_bound N T hT hN

/-- The AFE truncation satisfies N ≤ √(T/(2π)) ≤ √T for T ≥ 2.
    This connects the Dirichlet polynomial length to the integral range. -/
theorem afe_N_le_sqrt (N : ℕ) (T : ℝ) (hT : 2 ≤ T)
    (hN : (N : ℝ) ≤ Real.sqrt (T / (2 * Real.pi))) :
    (N : ℝ) ≤ Real.sqrt T := by
  have hT_pos : (0 : ℝ) < T := by linarith
  calc (N : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)) := hN
    _ ≤ Real.sqrt T := by
        apply Real.sqrt_le_sqrt
        exact div_le_self hT_pos.le (by linarith [Real.two_le_pi])

/-- Assembly with AFE truncation: the weighted mode sum with N ≤ √(T/(2π))
    is bounded by (1/log 2)·T^{1/2}.

    This combines `afe_N_le_sqrt` and `vdc_mode_sum_le_C_sqrt`. -/
theorem vdc_mode_sum_with_afe (N : ℕ) (T : ℝ) (hT : 2 ≤ T)
    (hN : (N : ℝ) ≤ Real.sqrt (T / (2 * Real.pi))) :
    ∑ n ∈ Finset.range N,
      ((n : ℝ) + 1) ^ (-(1 : ℝ)/2) / Real.log ((n : ℝ) + 2) ≤
      (1 / Real.log 2) * T ^ ((1 : ℝ)/2) :=
  vdc_mode_sum_le_C_sqrt N T hT (afe_N_le_sqrt N T hT hN)

/-- Per-mode weighted sum with multiplicative constant: if each mode bound
    is C_vdc · (n+1)^{-1/2} / log(n+2), then the total over N modes is
    C_vdc · (1/log 2) · T^{1/2} when N ≤ √(T/(2π)).

    This is the "reduction to mode sum" lemma: given per-mode VdC bounds
    on abstract quantities `f(n)`, the weighted total is O(√T).
    Used in HardyZFirstMomentIBP.lean for the main term analysis. -/
theorem weighted_mode_sum_with_constant (N : ℕ) (T : ℝ) (hT : 2 ≤ T)
    (hN : (N : ℝ) ≤ Real.sqrt (T / (2 * Real.pi)))
    (C_vdc : ℝ) (hC : 0 < C_vdc)
    (f : ℕ → ℝ)
    (h_per_mode : ∀ n ∈ Finset.range N,
      f n ≤ C_vdc * ((n : ℝ) + 1) ^ (-(1 : ℝ)/2) / Real.log ((n : ℝ) + 2)) :
    ∑ n ∈ Finset.range N, f n ≤
      C_vdc * ((1 / Real.log 2) * T ^ ((1 : ℝ)/2)) := by
  calc ∑ n ∈ Finset.range N, f n
      ≤ ∑ n ∈ Finset.range N,
        C_vdc * ((n : ℝ) + 1) ^ (-(1 : ℝ)/2) / Real.log ((n : ℝ) + 2) :=
        Finset.sum_le_sum h_per_mode
    _ = C_vdc * ∑ n ∈ Finset.range N,
        ((n : ℝ) + 1) ^ (-(1 : ℝ)/2) / Real.log ((n : ℝ) + 2) := by
        conv_lhs =>
          arg 2; ext n
          rw [show C_vdc * ((n : ℝ) + 1) ^ (-(1 : ℝ)/2) / Real.log ((n : ℝ) + 2) =
            C_vdc * (((n : ℝ) + 1) ^ (-(1 : ℝ)/2) / Real.log ((n : ℝ) + 2)) from by ring]
        rw [← Finset.mul_sum]
    _ ≤ C_vdc * ((1 / Real.log 2) * T ^ ((1 : ℝ)/2)) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact vdc_mode_sum_with_afe N T hT hN

end

end AbelSummationPsiPi_HarmonicLog
