/-
Proof of `zero_sum_neg_frequently` for the π-chain.

For any ρ₀ on the critical line with Im(ρ₀) ≠ 0,
there exist arbitrarily large x where Re(x^ρ₀/ρ₀)/log(x) ≤ -c·√x/log(x).

Strategy: Choose x = exp(t) where cos(Im(ρ₀)·t) = -1.
Then x^ρ₀ = -√x, so Re(x^ρ₀/ρ₀) = -√x · Re(ρ₀)/‖ρ₀‖².

SORRY COUNT: 0

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ZeroSumNegFrequently

open Complex Real Finset Filter

/-! ### Sub-lemmas -/

/-- cos((2k+1)π) = -1 for any integer k. -/
private theorem cos_odd_mul_pi (k : ℤ) : Real.cos ((2 * ↑k + 1) * π) = -1 := by
  rw [show (2 * ↑k + 1) * π = π + ↑k * (2 * π) from by ring]
  rw [Real.cos_add_int_mul_two_pi]
  exact Real.cos_pi

/-- For γ ≠ 0, there exist arbitrarily large t with cos(γ·t) = -1. -/
private theorem exists_large_cos_neg_one (γ : ℝ) (hγ : γ ≠ 0) (B : ℝ) :
    ∃ t > B, Real.cos (γ * t) = -1 := by
  by_cases hγ_pos : 0 < γ
  · obtain ⟨n, hn⟩ := exists_nat_gt (B * γ / π)
    refine ⟨(2 * (n : ℝ) + 1) * π / γ, ?_, ?_⟩
    · rw [gt_iff_lt, lt_div_iff₀ hγ_pos]
      have h1 : B * γ < ↑n * π := (div_lt_iff₀ pi_pos).mp hn
      nlinarith [pi_pos, Nat.cast_nonneg' (α := ℝ) n]
    · have : γ * ((2 * ↑n + 1) * π / γ) = (2 * ↑n + 1) * π := by
        field_simp
      rw [this]
      exact cos_odd_mul_pi ↑n
  · push_neg at hγ_pos
    have hγ_neg : γ < 0 := lt_of_le_of_ne hγ_pos hγ
    obtain ⟨n, hn⟩ := exists_nat_gt (-B * γ / π)
    refine ⟨-(2 * (n : ℝ) + 1) * π / γ, ?_, ?_⟩
    · rw [gt_iff_lt]
      rw [show -(2 * (n : ℝ) + 1) * π / γ = (2 * (n : ℝ) + 1) * π / (-γ) from by ring]
      rw [lt_div_iff₀ (neg_pos.mpr hγ_neg)]
      have h1 : -B * γ < ↑n * π := (div_lt_iff₀ pi_pos).mp hn
      nlinarith [pi_pos, Nat.cast_nonneg' (α := ℝ) n]
    · have : γ * (-(2 * ↑n + 1) * π / γ) = (2 * ↑(-(↑n : ℤ) - 1) + 1) * π := by
        push_cast; field_simp; ring
      rw [this]
      exact cos_odd_mul_pi _

/-- exp(I·θ) = -1 when cos(θ) = -1. -/
private theorem exp_I_of_cos_neg_one (θ : ℝ) (hcos : Real.cos θ = -1) :
    Complex.exp (I * ↑θ) = -1 := by
  have hsin : Real.sin θ = 0 := by
    have := Real.sin_sq_add_cos_sq θ
    rw [hcos] at this; nlinarith [sq_nonneg (Real.sin θ)]
  rw [show I * (↑θ : ℂ) = ↑θ * I from mul_comm _ _]
  rw [exp_mul_I]
  rw [show Complex.cos ↑θ = ↑(Real.cos θ) from (Complex.ofReal_cos θ).symm]
  rw [show Complex.sin ↑θ = ↑(Real.sin θ) from (Complex.ofReal_sin θ).symm]
  rw [hcos, hsin]
  push_cast
  ring

/-- Complex.log of a positive real equals the real log coerced. -/
private theorem clog_ofReal_pos (x : ℝ) (hx : 0 < x) :
    Complex.log (↑x : ℂ) = ↑(Real.log x) := by
  apply Complex.ext
  · simp [Complex.log_re, abs_of_pos hx]
  · simp [Complex.log_im, Complex.arg_ofReal_of_nonneg hx.le]

/-- exp(t/2) = √(exp(t)). -/
private theorem exp_half_eq_sqrt_exp (t : ℝ) :
    Real.exp (t / 2) = Real.sqrt (Real.exp t) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (exp_pos t), Real.log_exp]
  ring_nf

/-! ### Main theorem -/

/-- For ρ₀ with Re = 1/2 and Im ≠ 0, there exist arbitrarily large x > 1 where
    Re(x^ρ₀/ρ₀)/log(x) ≤ -c·√x/log(x) for c = Re(ρ₀)/‖ρ₀‖². -/
theorem zero_sum_neg_frequently_core
    (ρ₀ : ℂ) (hre : ρ₀.re = 1 / 2) (him : ρ₀.im ≠ 0) :
    ∃ c > 0, ∀ X : ℝ, ∃ x > X,
      1 < x ∧
        ((∑ ρ ∈ ({ρ₀} : Finset ℂ), ((x : ℂ) ^ ρ / ρ)).re) / Real.log x
          ≤ -(c * (Real.sqrt x / Real.log x)) := by
  have hρ₀_ne : ρ₀ ≠ 0 := by intro h; simp [h] at hre
  refine ⟨ρ₀.re / Complex.normSq ρ₀,
    div_pos (by rw [hre]; norm_num) (Complex.normSq_pos.mpr hρ₀_ne), ?_⟩
  intro X
  set γ := ρ₀.im with hγ_def
  set B := max (Real.log (max X 2)) 1 with hB_def
  -- Find t > B with cos(γ·t) = -1
  obtain ⟨t, ht_gt_B, hcos⟩ := exists_large_cos_neg_one γ him B
  have ht_pos : 0 < t := lt_of_lt_of_le (by linarith [le_max_right (Real.log (max X 2)) 1]) ht_gt_B.le
  -- Set x = exp(t)
  set x := Real.exp t with hx_def
  have hx_pos : 0 < x := exp_pos t
  have hlog : Real.log x = t := Real.log_exp t
  -- x > X and x > 1
  have hx_gt_X : x > X := by
    have ht_log : t > Real.log (max X 2) := by
      linarith [le_max_left (Real.log (max X 2)) 1]
    have h2 : max X 2 > 0 := by linarith [le_max_right X 2]
    calc X ≤ max X 2 := le_max_left X 2
      _ = Real.exp (Real.log (max X 2)) := (Real.exp_log h2).symm
      _ < Real.exp t := Real.exp_lt_exp.mpr ht_log
      _ = x := rfl
  have hx_gt_1 : 1 < x := by
    calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
      _ < Real.exp t := Real.exp_lt_exp.mpr ht_pos
      _ = x := rfl
  refine ⟨x, hx_gt_X, hx_gt_1, ?_⟩
  -- Simplify Finset.sum over singleton
  simp only [sum_singleton]
  -- sin(γ·t) = 0 from cos = -1
  have hsin : Real.sin (γ * t) = 0 := by
    have := Real.sin_sq_add_cos_sq (γ * t)
    rw [hcos] at this; nlinarith [sq_nonneg (Real.sin (γ * t))]
  -- Key: (↑x)^ρ₀ = -↑(√x)
  have hcpow : (↑x : ℂ) ^ ρ₀ = -(↑(Real.sqrt x) : ℂ) := by
    have hx_ne : (↑x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx_pos)
    rw [cpow_def_of_ne_zero hx_ne]
    -- Complex.log(↑x) = ↑t
    have hclog : Complex.log (↑x : ℂ) = ↑t := by
      rw [clog_ofReal_pos x hx_pos, hlog]
    rw [hclog]
    -- ↑t * ρ₀ = ↑(t/2) + I * ↑(γ*t)
    have hsplit : ↑t * ρ₀ = ↑(t / 2) + I * ↑(γ * t) := by
      apply Complex.ext
      · simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hre]; ring
      · simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
    rw [hsplit, Complex.exp_add]
    -- exp(↑(t/2)) = ↑(exp(t/2)) = ↑(√x)
    rw [← Complex.ofReal_exp, exp_half_eq_sqrt_exp]
    -- exp(I * ↑(γ*t)) = -1
    rw [exp_I_of_cos_neg_one _ hcos]
    ring
  -- Now compute Re(x^ρ₀/ρ₀) / log x
  rw [hcpow]
  -- Re(-↑(√x) / ρ₀) / log x = -(re/normSq · √x/log x)
  rw [neg_div, Complex.neg_re, Complex.div_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  rw [hlog]
  -- Both sides are -(re(ρ₀) * √x / (normSq(ρ₀) * t))
  ring_nf
  rfl

end Aristotle.Standalone.ZeroSumNegFrequently
