/-
# Perron Kernel Atomics

Concrete Mathlib computations for the Perron kernel: norm bounds on
y^s/s, differentiability of cpow, and related estimates.

Co-authored-by: Claude (Anthropic)
-/
import Mathlib

open Complex Real MeasureTheory Filter

noncomputable section

namespace PerronKernelAtomics

-- 7. For x > 0: ‖x^(σ+it)‖ = x^σ  (stated first as dependency for lemma 1)
theorem norm_cpow_real_exponent (x σ t : ℝ) (hx : 0 < x) :
    ‖(x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I)‖ = x ^ σ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero]
  ring

-- 6. ‖σ + T*I‖ ≥ |T| for any σ, T  (stated early as dependency for lemma 1)
theorem norm_add_mul_I_ge (σ T : ℝ) : |T| ≤ ‖(σ : ℂ) + (T : ℂ) * I‖ := by
  rw [show |T| = Real.sqrt (T ^ 2) from by rw [Real.sqrt_sq_eq_abs]]
  apply Real.le_sqrt_of_sq_le
  rw [Real.sq_sqrt (sq_nonneg T), Complex.normSq_add_mul_I]
  nlinarith [sq_nonneg σ]

-- 1. |y^(-U+it)/(-U+it)| ≤ y^(-U)/U for y > 0, U > 0
theorem left_edge_norm_bound (y U t : ℝ) (hy : 0 < y) (hU : 0 < U) :
    ‖(y : ℂ) ^ ((-U : ℝ) + (t : ℝ) * I) / ((-U : ℝ) + (t : ℝ) * I)‖ ≤
    y ^ (-U) / U := by
  rw [norm_div, norm_cpow_real_exponent y (-U) t hy]
  have hU_le : U ≤ ‖((-U : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I‖ := by
    have : |(-U : ℝ)| ≤ ‖((-U : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I‖ := by
      rw [show |(-U : ℝ)| = Real.sqrt ((-U) ^ 2) from by rw [Real.sqrt_sq_eq_abs]]
      apply Real.le_sqrt_of_sq_le
      rw [Real.sq_sqrt (sq_nonneg (-U)), Complex.normSq_add_mul_I]
      nlinarith [sq_nonneg t]
    rwa [abs_neg, abs_of_pos hU] at this
  exact div_le_div_of_nonneg_left (rpow_pos_of_pos hy (-U)).le hU hU_le

-- 2. ∫_{-T}^{T} |y^(-U+it)/(-U+it)| ≤ 2T · y^(-U)/U
theorem left_edge_integral_bound (y T U : ℝ) (hy : 0 < y) (hT : 0 < T) (hU : 0 < U) :
    ‖∫ t in (-T)..T, (y : ℂ) ^ ((-U : ℝ) + (t : ℝ) * I) /
      ((-U : ℝ) + (t : ℝ) * I)‖ ≤ 2 * T * y ^ (-U) / U := by
  have hbound : ∀ t, t ∈ Set.uIoc (-T) T →
      ‖(y : ℂ) ^ ((-U : ℝ) + (t : ℝ) * I) / ((-U : ℝ) + (t : ℝ) * I)‖ ≤
      y ^ (-U) / U :=
    fun t _ => left_edge_norm_bound y U t hy hU
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  calc ‖∫ t in (-T)..T, (y : ℂ) ^ ((-U : ℝ) + (t : ℝ) * I) /
        ((-U : ℝ) + (t : ℝ) * I)‖
      ≤ y ^ (-U) / U * |T - -T| := h
    _ = y ^ (-U) / U * (2 * T) := by
        rw [show T - -T = 2 * T from by ring,
            abs_of_nonneg (by linarith)]
    _ = 2 * T * y ^ (-U) / U := by ring

-- 3. 2T · y^(-U)/U → 0 as U → ∞ for y > 1
theorem left_edge_tendsto_zero (y T : ℝ) (hy : 1 < y) (_hT : 0 < T) :
    Filter.Tendsto (fun U => 2 * T * y ^ (-U) / U) Filter.atTop (nhds 0) := by
  have hy_pos : 0 < y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy
  -- First show y^(-U) → 0
  have h_rpow_zero : Tendsto (fun U : ℝ => y ^ (-U)) atTop (nhds 0) := by
    have h_eq : (fun U : ℝ => y ^ (-U)) = (fun U => Real.exp (-U * Real.log y)) := by
      ext U; rw [Real.rpow_def_of_pos hy_pos]; ring_nf
    rw [h_eq]
    have h_bot : Tendsto (fun U : ℝ => -U * Real.log y) atTop atBot := by
      have h1 : Tendsto (fun U : ℝ => Real.log y * U) atTop atTop :=
        Tendsto.const_mul_atTop hlog tendsto_id
      exact (tendsto_neg_atTop_atBot.comp h1).congr (fun U => by simp [mul_comm])
    exact Real.tendsto_exp_atBot.comp h_bot
  -- 2T * y^(-U) → 0
  have h_mul_zero : Tendsto (fun U : ℝ => 2 * T * y ^ (-U)) atTop (nhds 0) := by
    have := h_rpow_zero.const_mul (2 * T)
    simp only [mul_zero] at this
    exact this
  -- 2T * y^(-U) / U → 0 since numerator → 0 and denominator → ∞
  exact h_mul_zero.div_atTop tendsto_id

-- 4. For x > 0, s ↦ x^s is differentiable everywhere
theorem differentiable_cpow_ofReal (x : ℝ) (hx : 0 < x) :
    Differentiable ℂ (fun (s : ℂ) => (x : ℂ) ^ s) := by
  intro s
  apply DifferentiableAt.const_cpow differentiableAt_id
  left
  exact_mod_cast hx.ne'

-- 5. For x > 0, s ↦ x^s/s is differentiable at any s ≠ 0
theorem differentiableAt_cpow_div (x : ℝ) (hx : 0 < x) (s : ℂ) (hs : s ≠ 0) :
    DifferentiableAt ℂ (fun (s : ℂ) => (x : ℂ) ^ s / s) s := by
  apply DifferentiableAt.div
  · exact (differentiable_cpow_ofReal x hx).differentiableAt
  · exact differentiableAt_id
  · exact hs

end PerronKernelAtomics
