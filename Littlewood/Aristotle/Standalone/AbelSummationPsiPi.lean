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

end AbelSummationPsiPi
