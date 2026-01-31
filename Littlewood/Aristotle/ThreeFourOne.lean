/-
3-4-1 inequality and zero-free region foundations - proved by Aristotle.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

noncomputable section

open Complex Real Topology Filter
open scoped BigOperators Real Nat Classical

/-- The fundamental 3-4-1 inequality: 3 + 4cos(θ) + cos(2θ) ≥ 0

This is the KEY inequality for proving the zero-free region.
Proof: cos(2θ) = 2cos²(θ) - 1, so
  3 + 4cos(θ) + cos(2θ) = 3 + 4cos(θ) + 2cos²(θ) - 1
                        = 2 + 4cos(θ) + 2cos²(θ)
                        = 2(1 + 2cos(θ) + cos²(θ))
                        = 2(1 + cos(θ))²
                        ≥ 0
-/
lemma three_four_one_inequality (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]
  -- cos(2θ) = 2cos²(θ) - 1
  -- 3 + 4cos(θ) + 2cos²(θ) - 1 = 2 + 4cos(θ) + 2cos²(θ) = 2(1 + cos(θ))²
  have h : 3 + 4 * Real.cos θ + (2 * Real.cos θ ^ 2 - 1) = 2 * (1 + Real.cos θ)^2 := by ring
  linarith [sq_nonneg (1 + Real.cos θ)]

/-- Alternative form: (1 + cos θ)² ≥ 0 implies the 3-4-1 inequality -/
lemma three_four_one_from_square (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ)^2 := by
  rw [Real.cos_two_mul]
  ring

/-- The 3-4-1 inequality is tight: equality holds when cos(θ) = -1, i.e., θ = π -/
lemma three_four_one_tight : 3 + 4 * Real.cos Real.pi + Real.cos (2 * Real.pi) = 0 := by
  rw [Real.cos_pi, Real.cos_two_pi]
  norm_num

/-- Re(-log(1-z)) = Σ_{n≥1} Re(z^n)/n for |z| < 1 -/
lemma neg_log_one_sub_re_eq_tsum (z : ℂ) (hz : ‖z‖ < 1) :
    (-Complex.log (1 - z)).re = ∑' n : ℕ, (z ^ (n + 1)).re / (n + 1) := by
  -- Step 1: -log(1-z) = Σ z^n/n (power series, n=0 term is 0)
  have h := hasSum_taylorSeries_neg_log hz
  -- Step 2: Shift index to start from n+1 (n=0 term z^0/0 = 0)
  have h1 : HasSum (fun n : ℕ => z ^ (n + 1) / (↑(n + 1) : ℂ)) (-Complex.log (1 - z)) :=
    (hasSum_nat_add_iff (f := fun n => z ^ n / (↑n : ℂ)) 1).mpr
      (by simp only [Finset.sum_range_one, pow_zero, Nat.cast_zero, div_zero, add_zero]; exact h)
  -- Step 3: Map through Re (continuous linear map preserves HasSum)
  have h2 := h1.mapL reCLM
  -- Step 4: Pointwise rewrite (z^(n+1)/↑(n+1)).re = (z^(n+1)).re/(n+1)
  have h3 : (fun n : ℕ => reCLM (z ^ (n + 1) / (↑(n + 1) : ℂ))) =
      fun n : ℕ => (z ^ (n + 1)).re / ((n : ℝ) + 1) := by
    ext n; simp only [reCLM_apply]
    rw [show (↑(n + 1) : ℂ) = ↑((n : ℝ) + 1) from by push_cast; ring]
    exact div_ofReal_re _ _
  rw [h3] at h2
  exact h2.tsum_eq.symm

/-- For z = r·e^{iθ} with 0 ≤ r < 1:
    Re(-log(1 - r·e^{iθ})) = Σ_{n≥1} r^n cos(nθ) / n -/
lemma real_part_log_series (r θ : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    (-Complex.log (1 - ↑r * Complex.exp (↑θ * Complex.I))).re =
    ∑' n : ℕ, r ^ (n + 1) / (n + 1) * Real.cos ((n + 1) * θ) := by
  have hz : ‖(↑r : ℂ) * exp (↑θ * I)‖ < 1 := by
    simp only [norm_mul, norm_exp_ofReal_mul_I, mul_one]
    rwa [Complex.norm_of_nonneg hr]
  rw [neg_log_one_sub_re_eq_tsum _ hz]
  congr 1; ext n
  -- Goal: ((↑r * exp(↑θ * I))^(n+1)).re / (↑n+1) = r^(n+1) / (↑n+1) * cos((n+1)*θ)
  have h_re : ((↑r * exp (↑θ * I)) ^ (n + 1)).re = r ^ (n + 1) * Real.cos ((n + 1) * θ) := by
    rw [mul_pow, ← Complex.exp_nat_mul,
        show (↑(n + 1) : ℂ) * (↑θ * I) = ↑(((n : ℝ) + 1) * θ) * I from by push_cast; ring,
        exp_mul_I, ← ofReal_pow]
    simp only [mul_re, add_re, ofReal_re, ofReal_im, cos_ofReal_re,
               sin_ofReal_re, sin_ofReal_im, mul_re, I_re, I_im]
    ring
  rw [h_re]; ring

/-- Summability of r^(n+1)/(n+1) · cos(k(n+1)θ) series for |r| < 1 -/
lemma summable_r_pow_div_mul_cos (r θ k : ℝ) (hr : |r| < 1) :
    Summable (fun n : ℕ => r ^ (n + 1) / (n + 1) * Real.cos (k * (n + 1) * θ)) := by
  -- Bounding series: |r|^(n+1) is summable (shifted geometric series)
  have h_shifted : Summable (fun n : ℕ => |r| ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_abs_lt_one (by rw [abs_abs]; exact hr))
  apply Summable.of_norm_bounded h_shifted
  intro i
  simp only [Real.norm_eq_abs, abs_mul, abs_div, abs_pow]
  have h_pos : (0 : ℝ) < (↑i : ℝ) + 1 := by positivity
  rw [abs_of_pos h_pos]
  calc |r| ^ (i + 1) / ((↑i : ℝ) + 1) * |Real.cos (k * ((↑i : ℝ) + 1) * θ)|
      ≤ |r| ^ (i + 1) / ((↑i : ℝ) + 1) * 1 := by
        gcongr; exact Real.abs_cos_le_one _
    _ ≤ |r| ^ (i + 1) := by
        rw [mul_one]
        exact div_le_self (pow_nonneg (abs_nonneg r) _)
          (le_add_of_nonneg_left (Nat.cast_nonneg i))

/-- Linear combination of log terms for 3-4-1 -/
lemma log_combination_eq_sum (r θ : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    3 * (-Complex.log (1 - r)).re +
    4 * (-Complex.log (1 - ↑r * Complex.exp (↑θ * Complex.I))).re +
    (-Complex.log (1 - ↑r * Complex.exp (2 * ↑θ * Complex.I))).re =
    ∑' n : ℕ, (r ^ (n + 1) / (n + 1)) * (3 + 4 * Real.cos ((n + 1) * θ) + Real.cos (2 * (n + 1) * θ)) := by
  -- Rewrite each log term as a power series using real_part_log_series
  have h0 : (-Complex.log (1 - (↑r : ℂ))).re =
      ∑' n : ℕ, r ^ (n + 1) / (↑n + 1) := by
    have := real_part_log_series r 0 hr hr1
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
               Real.cos_zero] at this
    exact this
  have hθ := real_part_log_series r θ hr hr1
  have h2θ : (-Complex.log (1 - ↑r * Complex.exp (2 * ↑θ * Complex.I))).re =
      ∑' n : ℕ, r ^ (n + 1) / (↑n + 1) * Real.cos ((↑n + 1) * (2 * θ)) := by
    have := real_part_log_series r (2 * θ) hr hr1
    rw [show (↑(2 * θ) : ℂ) * Complex.I = 2 * ↑θ * Complex.I from by push_cast; ring] at this
    exact this
  rw [h0, hθ, h2θ]
  -- Summability
  have hr_abs : |r| < 1 := by rwa [abs_of_nonneg hr]
  have hs1 : Summable (fun n : ℕ => r ^ (n + 1) / (↑n + 1)) := by
    have := summable_r_pow_div_mul_cos r θ 0 hr_abs
    simp only [zero_mul, Real.cos_zero, mul_one] at this
    exact this
  have hs2 : Summable (fun n : ℕ => r ^ (n + 1) / (↑n + 1) * Real.cos ((↑n + 1) * θ)) := by
    have := summable_r_pow_div_mul_cos r θ 1 hr_abs
    simp only [one_mul] at this
    exact this
  have hs3 : Summable (fun n : ℕ => r ^ (n + 1) / (↑n + 1) * Real.cos ((↑n + 1) * (2 * θ))) := by
    have := summable_r_pow_div_mul_cos r (2 * θ) 1 hr_abs
    simp only [one_mul] at this
    exact this
  -- Combine: 3*∑f + 4*∑g + ∑h = ∑(3f + 4g + h)
  simp only [← tsum_mul_left]
  rw [← (hs1.mul_left 3).tsum_add (hs2.mul_left 4),
      ← ((hs1.mul_left 3).add (hs2.mul_left 4)).tsum_add hs3]
  congr 1; ext n
  have : (↑n + 1) * (2 * θ) = 2 * (↑n + 1) * θ := by ring
  rw [this]; ring

/-- KEY THEOREM: For 0 ≤ r < 1, the 3-4-1 combination of log terms is non-negative.

This is used to prove the zero-free region: taking r = p^{-σ} for a prime p,
the inequality becomes:
  3·log|ζ(σ)| + 4·log|ζ(σ+it)| + log|ζ(σ+2it)| ≥ 0
which prevents ζ(σ+it) = 0 near Re(s) = 1. -/
theorem real_part_log_euler_product_term_ge_zero (r θ : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    0 ≤ 3 * (-Complex.log (1 - r)).re +
        4 * (-Complex.log (1 - ↑r * Complex.exp (↑θ * Complex.I))).re +
        (-Complex.log (1 - ↑r * Complex.exp (2 * ↑θ * Complex.I))).re := by
  rw [log_combination_eq_sum r θ hr hr1]
  apply tsum_nonneg
  intro n
  apply mul_nonneg
  · exact div_nonneg (pow_nonneg hr _) (by positivity)
  · have := three_four_one_inequality ((↑n + 1) * θ)
    rwa [show 2 * ((↑n + 1) * θ) = 2 * (↑n + 1) * θ from by ring] at this

/-- log‖ζ(s)‖ as sum over primes (Euler product) -/
lemma log_norm_zeta_eq_sum_re_log (s : ℂ) (hs : 1 < s.re) :
    Real.log ‖riemannZeta s‖ = ∑' p : Nat.Primes, (-Complex.log (1 - (p : ℂ) ^ (-s))).re := by
  have h_prod := riemannZeta_eulerProduct_exp_log hs
  rw [← h_prod, norm_exp, Real.log_exp]
  have h_summ : Summable (fun p : Nat.Primes => -log (1 - (p : ℂ) ^ (-s))) := by
    have h := DirichletCharacter.summable_neg_log_one_sub_mul_prime_cpow
      (1 : DirichletCharacter ℂ 1) hs
    simp only [MulChar.one_apply (isUnit_of_subsingleton _), one_mul] at h
    exact h
  exact reCLM.map_tsum h_summ

/-- The de la Vallée Poussin zero-free region follows from 3-4-1:
    |ζ(σ)³ ζ(σ+it)⁴ ζ(σ+2it)| ≥ 1 for σ > 1
    This prevents zeros near Re(s) = 1. -/
theorem zeta_product_ge_one (σ : ℝ) (t : ℝ) (hσ : 1 < σ) :
    1 ≤ ‖riemannZeta σ‖^3 * ‖riemannZeta (σ + t * I)‖^4 * ‖riemannZeta (σ + 2 * t * I)‖ := by
  have hx : 0 < σ - 1 := by linarith
  have h := DirichletCharacter.norm_LFunction_product_ge_one (1 : DirichletCharacter ℂ 1) hx t
  simp only [DirichletCharacter.LFunction_modOne_eq, one_pow] at h
  rw [show (1 : ℂ) + ↑(σ - 1) = (σ : ℂ) from by push_cast; ring] at h
  rw [norm_mul, norm_mul, norm_pow, norm_pow] at h
  -- Convert I * t to t * I (commutativity)
  rw [show (↑σ : ℂ) + I * ↑t = ↑σ + ↑t * I from by ring] at h
  rw [show (↑σ : ℂ) + 2 * I * ↑t = ↑σ + 2 * ↑t * I from by ring] at h
  exact h

end
