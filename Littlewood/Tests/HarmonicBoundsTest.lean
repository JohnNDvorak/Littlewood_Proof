/-
Test harmonic sum bounds for DiagonalIntegralBound.
-/
import Mathlib

set_option maxHeartbeats 800000

open Finset Real in
/-- Lower bound: ∑_{k=1}^n 1/k ≥ log(n+1). -/
lemma harmonic_Icc_lower (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, (1 / (k : ℝ)) ≥ Real.log (n + 1) := by
  rw [ge_iff_le, Real.log_le_iff_le_exp (by positivity : (0 : ℝ) < ↑n + 1)]
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [one_div] at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), Real.exp_add]
    have hpos : (0 : ℝ) < ↑n + 1 := by positivity
    have h_exp := Real.add_one_le_exp ((↑n + 1 : ℝ)⁻¹)
    have h_inv := mul_inv_cancel₀ (ne_of_gt hpos)
    have h_mul := mul_le_mul ih h_exp (by positivity) (Real.exp_nonneg _)
    have h_lhs : (↑n + 1 : ℝ) * ((↑n + 1 : ℝ)⁻¹ + 1) = ↑n + 2 := by
      rw [mul_add, h_inv]; ring
    show (↑(n + 1) : ℝ) + 1 ≤ _
    push_cast
    linarith

open Finset Real in
/-- Upper bound: ∑_{k=1}^n 1/k ≤ log(n) + 1 for n ≥ 1. -/
lemma harmonic_Icc_upper (n : ℕ) (hn : n ≥ 1) : ∑ k ∈ Finset.Icc 1 n, (1 / (k : ℝ)) ≤ Real.log n + 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn1 : n = 0
    · subst hn1; simp [Finset.Icc_self]
    · rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have ihn := ih (by omega)
      have hpos_n : (0 : ℝ) < ↑n := by positivity
      have hpos_n1 : (0 : ℝ) < ↑n + 1 := by positivity
      -- Key: exp(x)(1-x) ≤ 1 via add_one_le_exp(-x)
      have h_sub := Real.add_one_le_exp (-(1 / (↑n + 1 : ℝ)))
      have h_prod : Real.exp (1 / (↑n + 1 : ℝ)) * (1 - 1 / (↑n + 1 : ℝ)) ≤ 1 := by
        calc Real.exp (1 / (↑n + 1 : ℝ)) * (1 - 1 / (↑n + 1 : ℝ))
            ≤ Real.exp (1 / (↑n + 1 : ℝ)) * Real.exp (-(1 / (↑n + 1 : ℝ))) := by
              gcongr; linarith
          _ = Real.exp (1 / (↑n + 1 : ℝ) + -(1 / (↑n + 1 : ℝ))) := (Real.exp_add _ _).symm
          _ = 1 := by simp
      -- exp(1/(n+1)) * n ≤ n+1
      have h_factor : (1 - 1 / (↑n + 1 : ℝ)) * (↑n + 1) = ↑n := by field_simp; ring
      have h_exp_n : Real.exp (1 / (↑n + 1 : ℝ)) * ↑n ≤ ↑n + 1 := by
        calc Real.exp (1 / (↑n + 1 : ℝ)) * ↑n
            = Real.exp (1 / (↑n + 1 : ℝ)) * (1 - 1 / (↑n + 1 : ℝ)) * (↑n + 1) := by
              rw [mul_assoc, h_factor]
          _ ≤ 1 * (↑n + 1) := by gcongr
          _ = ↑n + 1 := one_mul _
      -- exp(1/(n+1)) ≤ (n+1)/n
      have h_exp_bound : Real.exp (1 / (↑n + 1 : ℝ)) ≤ (↑n + 1) / ↑n := by
        rwa [le_div_iff₀ hpos_n]
      -- Take log: 1/(n+1) ≤ log(n+1) - log(n)
      have h_log := Real.log_le_log (Real.exp_pos (1 / (↑n + 1 : ℝ))) h_exp_bound
      rw [Real.log_exp, Real.log_div (ne_of_gt hpos_n1) (ne_of_gt hpos_n)] at h_log
      push_cast at ihn h_log ⊢
      linarith
