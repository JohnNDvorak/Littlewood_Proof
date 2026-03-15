/-
Infrastructure for converting truncated explicit formulas.
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

/-- If |A| ≤ ε₁ and |B| ≤ ε₂, then |A + B| ≤ ε₁ + ε₂. -/
theorem combined_bound (A B ε₁ ε₂ : ℝ) (h₁ : |A| ≤ ε₁) (h₂ : |B| ≤ ε₂) :
    |A + B| ≤ ε₁ + ε₂ :=
  le_trans (abs_add_le A B) (add_le_add h₁ h₂)

/-- Rewriting: a + b = (a + c) + (b - c). -/
theorem rewrite_via_full_sum (a b c : ℝ) :
    a + b = (a + c) + (b - c) := by ring

/-- C · √x / logx = C · (√x/logx). -/
theorem const_sqrt_div_log_factor (C x : ℝ) (_hlog : Real.log x ≠ 0) :
    C * Real.sqrt x / Real.log x = C * (Real.sqrt x / Real.log x) := by
  rw [mul_div_assoc]

/-- For any C > 0 and δ > 0, eventually C/logx ≤ δ. -/
theorem const_div_log_eventually_small (C : ℝ) (hC : 0 < C) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x in atTop, C / Real.log x ≤ δ := by
  -- logx → ∞, so 1/logx → 0, so C/logx → 0 < δ
  filter_upwards [eventually_ge_atTop (Real.exp (C / δ + 1))] with x hx
  have hlog_pos : 0 < Real.log x := by
    calc 0 < C / δ + 1 := by positivity
      _ ≤ Real.log (Real.exp (C / δ + 1)) := by rw [Real.log_exp]
      _ ≤ Real.log x := by
          apply Real.log_le_log (Real.exp_pos _) hx
  rw [div_le_iff₀ hlog_pos]
  calc C = δ * (C / δ) := by field_simp
    _ ≤ δ * Real.log x := by
        apply mul_le_mul_of_nonneg_left _ hδ.le
        calc C / δ ≤ C / δ + 1 := by linarith
          _ ≤ Real.log (Real.exp (C / δ + 1)) := by rw [Real.log_exp]
          _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hx

/-- For C > 0 and δ > 0, eventually C·(√x/logx)/logx ≤ δ·(√x/logx). -/
theorem const_sqrt_ratio_eventually_small (C : ℝ) (hC : 0 < C) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x in atTop,
      C * (Real.sqrt x / Real.log x) / Real.log x ≤
        δ * (Real.sqrt x / Real.log x) := by
  filter_upwards [const_div_log_eventually_small C hC δ hδ,
                  eventually_ge_atTop (2 : ℝ)] with x hClog hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have h_ratio_nn : 0 ≤ Real.sqrt x / Real.log x :=
    div_nonneg (Real.sqrt_nonneg x) hlog.le
  calc C * (Real.sqrt x / Real.log x) / Real.log x
      = (C / Real.log x) * (Real.sqrt x / Real.log x) := by ring
    _ ≤ δ * (Real.sqrt x / Real.log x) :=
      mul_le_mul_of_nonneg_right hClog h_ratio_nn

/-- |S.sum f| ≤ card(S) · M when ∀ i ∈ S, |f i| ≤ M. -/
theorem finset_sum_abs_le_card_mul {ι : Type*}
    (S : Finset ι) (f : ι → ℝ) (M : ℝ) (_hM : 0 ≤ M)
    (hf : ∀ i ∈ S, |f i| ≤ M) :
    |S.sum f| ≤ S.card * M := by
  calc |S.sum f| ≤ S.sum (fun i => |f i|) := Finset.abs_sum_le_sum_abs _ _
    _ ≤ S.sum (fun _ => M) := Finset.sum_le_sum hf
    _ = S.card * M := by simp [Finset.sum_const, nsmul_eq_mul]

/-- |a/b| ≤ c/b when |a| ≤ c and b > 0. -/
theorem abs_div_le_div (a b c : ℝ) (hb : 0 < b) (hac : |a| ≤ c) :
    |a / b| ≤ c / b := by
  rw [abs_div, abs_of_pos hb]
  exact div_le_div_of_nonneg_right hac hb.le

/-- Scaling bound: if ∀ᶠ x, |f x| ≤ g x, then ∀ᶠ x, |f x|/L ≤ g x/L for L > 0. -/
theorem eventually_abs_div_le (f g : ℝ → ℝ)
    (h : ∀ᶠ x in atTop, |f x| ≤ g x) :
    ∀ᶠ x in atTop, ∀ L : ℝ, 0 < L → |f x / L| ≤ g x / L := by
  filter_upwards [h] with x hx L hL
  rw [abs_div, abs_of_pos hL]
  exact div_le_div_of_nonneg_right hx hL.le

end FinsetZeroSumInfra
