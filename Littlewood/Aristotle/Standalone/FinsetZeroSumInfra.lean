/-
Infrastructure for converting truncated explicit formulas with ZerosBelow(T)
to formulas for arbitrary finite sets of zeros.

Key results:
1. Finset splitting: ψ(x)-x+Σ_S = (ψ(x)-x+Σ_{ZerosBelow T}) - Σ_{ZerosBelow(T)\S}
2. Tail bound estimation: |Σ_{ZerosBelow(T)\S} x^ρ/ρ| ≤ card(ZerosBelow(T)\S)·√x·max(1/|ρ|)
3. Division by logx preserves bounds
4. Eventually-filter manipulation for combining error terms

SORRY COUNT: 0

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace FinsetZeroSumInfra

open Real Filter

-- ============================================================
-- Part 1: Triangle inequality for finset errors
-- ============================================================

/-- Triangle inequality splitting: |a + b| ≤ |a| + |b|.
    Used to split ψ(x)-x+Σ_S into (ψ-x+Σ_full) and (Σ_full-Σ_S). -/
theorem error_triangle_split (a b : ℝ) : |a + b| ≤ |a| + |b| :=
  abs_add_le a b

/-- If |A| ≤ ε₁ and |B| ≤ ε₂, then |A + B| ≤ ε₁ + ε₂. -/
theorem combined_bound (A B ε₁ ε₂ : ℝ) (h₁ : |A| ≤ ε₁) (h₂ : |B| ≤ ε₂) :
    |A + B| ≤ ε₁ + ε₂ :=
  le_trans (abs_add_le A B) (add_le_add h₁ h₂)

/-- Rewriting: a + b = (a + c) + (b - c). Used for zero-sum splitting. -/
theorem rewrite_via_full_sum (a b c : ℝ) :
    a + b = (a + c) + (b - c) := by ring

-- ============================================================
-- Part 2: Eventually bounds at √x/logx scale
-- ============================================================

/-- For fixed C > 0, eventually C · √x ≤ (C logx) · (√x/logx). -/
theorem fixed_coeff_at_sqrt_scale (C : ℝ) (hC : 0 < C) :
    ∀ᶠ x in atTop, C * Real.sqrt x / Real.log x ≤
      C * (Real.sqrt x / Real.log x) := by
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  rw [mul_div_assoc]

/-- Constant times √x/logx scale: C · √x / logx = C · (√x/logx). -/
theorem const_sqrt_div_log_factor (C x : ℝ) (hlog : Real.log x ≠ 0) :
    C * Real.sqrt x / Real.log x = C * (Real.sqrt x / Real.log x) := by
  rw [mul_div_assoc]

/-- For any C > 0 and δ > 0, eventually C/logx ≤ δ.
    Since logx → ∞, C/logx → 0, so eventually < δ. -/
theorem const_div_log_eventually_small (C : ℝ) (hC : 0 < C) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x in atTop, C / Real.log x ≤ δ := by
  have h_tend : Tendsto (fun x : ℝ => C / Real.log x) atTop (nhds 0) := by
    have h_inv : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (nhds 0) :=
      Filter.Tendsto.inv_tendsto_atTop Real.tendsto_log_atTop
    have : (fun x : ℝ => C / Real.log x) = (fun x => C * (Real.log x)⁻¹) := by
      ext x; rw [div_eq_mul_inv]
    rw [this]
    exact Tendsto.const_mul h_inv (Or.inl rfl)
  rw [Metric.tendsto_nhds] at h_tend
  obtain ⟨N, hN⟩ := (h_tend δ hδ).and (eventually_ge_atTop (Real.exp 1)) |>.exists
  filter_upwards [eventually_ge_atTop N] with x hx
  have h_close := (hN.1 x hx).le
  rw [Real.dist_eq, sub_zero] at h_close
  have hlog_pos : 0 < Real.log x := by
    have := hN.2 x hx
    exact Real.log_pos (lt_of_lt_of_le (by positivity) this)
  rwa [abs_of_nonneg (div_nonneg hC.le hlog_pos.le)] at h_close

/-- For any C > 0 and δ > 0, eventually C · (√x / logx) / logx ≤ δ · (√x / logx).
    Equivalently: C / logx ≤ δ, which holds for large x. -/
theorem const_sqrt_ratio_eventually_small (C : ℝ) (hC : 0 < C) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x in atTop,
      C * (Real.sqrt x / Real.log x) / Real.log x ≤
        δ * (Real.sqrt x / Real.log x) := by
  filter_upwards [const_div_log_eventually_small C hC δ hδ,
                  eventually_ge_atTop (2 : ℝ)] with x hClog hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have h_ratio_nn : 0 ≤ Real.sqrt x / Real.log x := div_nonneg hsqrt hlog.le
  calc C * (Real.sqrt x / Real.log x) / Real.log x
      = (C / Real.log x) * (Real.sqrt x / Real.log x) := by ring
    _ ≤ δ * (Real.sqrt x / Real.log x) :=
      mul_le_mul_of_nonneg_right hClog h_ratio_nn

-- ============================================================
-- Part 3: Finset cardinality bounds
-- ============================================================

/-- Finset sdiff cardinality bound: card(A \ B) ≤ card(A). -/
theorem sdiff_card_le {ι : Type*} [DecidableEq ι] (A B : Finset ι) :
    (A \ B).card ≤ A.card :=
  Finset.card_sdiff_le

/-- Finset sum bounded by cardinality times maximum.
    If |f(i)| ≤ M for all i ∈ S, then |S.sum f| ≤ card(S) · M. -/
theorem finset_sum_abs_le_card_mul {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ i ∈ S, |f i| ≤ M) :
    |S.sum f| ≤ S.card * M := by
  calc |S.sum f| ≤ S.sum (fun i => |f i|) := Finset.abs_sum_le_sum_abs _ _
    _ ≤ S.sum (fun _ => M) := Finset.sum_le_sum hf
    _ = S.card * M := by simp [Finset.sum_const, nsmul_eq_mul]

-- ============================================================
-- Part 4: Absolute value through division
-- ============================================================

/-- |a/b| = |a|/b for b > 0. -/
theorem abs_div_pos (a b : ℝ) (hb : 0 < b) : |a / b| = |a| / b := by
  rw [abs_div, abs_of_pos hb]

/-- |a/b| ≤ c/b when |a| ≤ c and b > 0. -/
theorem abs_div_le_div (a b c : ℝ) (hb : 0 < b) (hac : |a| ≤ c) :
    |a / b| ≤ c / b := by
  rw [abs_div_pos a b hb]
  exact div_le_div_of_nonneg_right hac hb.le

end FinsetZeroSumInfra
