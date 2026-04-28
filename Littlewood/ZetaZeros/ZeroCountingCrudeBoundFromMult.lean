/-
# ZeroCountingCrudeBoundHyp from ZeroCountingMultRvmExplicitHyp

REPLACEMENT for ZeroCountingCrudeBoundFromMult.lean.

Provides `ZeroCountingCrudeBoundHyp` (N(T) ≤ C·T·log T) directly from
`ZeroCountingMultRvmExplicitHyp` (PROVED) using N(T) ≤ Nmult(T).

Bypasses the circular NmultNGapBoundHyp dependency.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.ZetaZeros.ZeroCountingMultiplicity

set_option maxHeartbeats 800000

noncomputable section

namespace ZetaZeros

open Real

/-- The RvM main term g(T) = (T/2π)·log(T/2π) - T/2π is bounded by T·log T for T ≥ 1. -/
private lemma rvm_main_term_le_T_logT {T : ℝ} (hT : 1 ≤ T) :
    (T / (2 * π)) * log (T / (2 * π)) - T / (2 * π) ≤ T * log T := by
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hT_pos : (0 : ℝ) < T := by linarith
  have hTdiv : T / (2 * π) ≤ T := div_le_self hT_pos.le (by linarith [pi_gt_three])
  have hTdiv_pos : 0 < T / (2 * π) := div_pos hT_pos h2pi
  by_cases hge1 : 1 ≤ T / (2 * π)
  · -- Case: T/(2π) ≥ 1, so log(T/(2π)) ≥ 0
    have hlog_nn : 0 ≤ log (T / (2 * π)) := log_nonneg hge1
    have hlog_le : log (T / (2 * π)) ≤ log T := log_le_log hTdiv_pos hTdiv
    have h1 : (T / (2 * π)) * log (T / (2 * π)) ≤ T * log T :=
      mul_le_mul hTdiv hlog_le hlog_nn hT_pos.le
    linarith [div_nonneg hT_pos.le h2pi.le]
  · -- Case: T/(2π) < 1, so log(T/(2π)) < 0 and the whole term is ≤ 0
    push_neg at hge1
    have hlog_neg : log (T / (2 * π)) ≤ 0 := log_nonpos hTdiv_pos.le (le_of_lt hge1)
    have h1 : (T / (2 * π)) * log (T / (2 * π)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hTdiv_pos.le hlog_neg
    have h2 : 0 ≤ T * log T := mul_nonneg hT_pos.le (log_nonneg hT)
    linarith [div_nonneg hT_pos.le h2pi.le]

/-- N(T) ≤ C·T·log T from the mult RvM, bypassing NmultNGapBoundHyp. -/
instance (priority := 300) zeroCountingCrudeBoundHyp_of_multRvm
    [ZeroCountingMultRvmExplicitHyp] :
    ZeroCountingCrudeBoundHyp where
  crude_bound := by
    rcases ZeroCountingMultRvmExplicitHyp.bound with ⟨C₁, T₀, hMult⟩
    set M := max T₀ 4
    set NM := (N M : ℝ)
    set C := max (|C₁| + 1) (NM + 1)
    refine ⟨C, fun {T} hT4 => ?_⟩
    have hT_pos : (0 : ℝ) < T := by linarith
    have hlogT : 0 < log T := log_pos (by linarith)
    have hN_le : (N T : ℝ) ≤ (Nmult T : ℝ) := zeroCountingFunction_le_zeroCountingFunctionMult_real T
    have hC_pos : 0 < C := by positivity
    by_cases hTM : M ≤ T
    · -- Large T ≥ M ≥ T₀: use RvM
      have hT0 : T₀ ≤ T := le_trans (le_max_left _ _) hTM
      have hRvM := hMult T hT0
      -- From |Nmult - g + correction| ≤ C₁·log T:
      have hNmult_le : (Nmult T : ℝ) ≤
          (T / (2 * π)) * log (T / (2 * π)) - T / (2 * π) + C₁ * log T := by
        have := (abs_le.mp hRvM).2; linarith
      have hg_le := rvm_main_term_le_T_logT (by linarith : (1 : ℝ) ≤ T)
      have h_abs : C₁ * log T ≤ |C₁| * log T :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hlogT.le
      have h_absT : |C₁| * log T ≤ |C₁| * (T * log T) := by
        gcongr; exact le_mul_of_one_le_left hlogT.le (by linarith)
      calc (N T : ℝ) ≤ (Nmult T : ℝ) := hN_le
        _ ≤ T * log T + C₁ * log T := by linarith
        _ ≤ T * log T + |C₁| * (T * log T) := by linarith
        _ = (|C₁| + 1) * (T * log T) := by ring
        _ ≤ C * (T * log T) := by gcongr; exact le_max_left _ _
        _ = C * T * log T := by ring
    · -- Small T < M: N(T) ≤ N(M) = NM
      push_neg at hTM
      have hN_mono : N T ≤ N M := zeroCountingFunction_mono (le_of_lt hTM)
      have hTlogT : 1 ≤ T * log T := by
        have hexp_le : exp 1 ≤ T := by
          linarith [Real.exp_one_lt_d9]
        have h1 : (1 : ℝ) ≤ log T := by
          rw [show (1 : ℝ) = log (exp 1) from (log_exp 1).symm]
          exact log_le_log (exp_pos 1) hexp_le
        nlinarith
      calc (N T : ℝ) ≤ (N M : ℝ) := by exact_mod_cast hN_mono
        _ ≤ NM + 1 := by simp [NM]
        _ ≤ C := le_max_right _ _
        _ = C * 1 := (mul_one _).symm
        _ ≤ C * (T * log T) := by gcongr
        _ = C * T * log T := by ring

end ZetaZeros
