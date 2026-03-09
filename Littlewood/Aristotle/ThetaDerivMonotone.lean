/-
Proves that thetaDeriv is strictly increasing on (0, ∞).

The key identity: thetaDeriv'(t) = (t/4) · Σ_{n≥0} (n+1/4)/|1/4+it/2+n|⁴ > 0 for t > 0.

This uses the trigamma series ψ'(s) = Σ_{n≥0} 1/(s+n)², obtained by differentiating the
Gauss series ψ(s) - log(s) = Σ gaussTerm(s+n) via hasDerivAt_tsum.

## Main results

- `thetaDeriv_strictMonoOn`: thetaDeriv is strictly monotone on (0, ∞)

## Architecture

1. HasDerivAt for gaussTerm composed with s(t) = 1/4 + it/2
2. Uniform norm bound on derivatives → hasDerivAt_tsum
3. Partial fractions + telescoping → trigamma series
4. Sign of Im(1/(s+n)²) → thetaDeriv' > 0

Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.ThetaDerivAsymptotic
import Littlewood.Aristotle.GammaHalfPlane
import Littlewood.Aristotle.GammaSeqLocallyUniform
import Littlewood.Aristotle.DigammaBinetBound

set_option maxHeartbeats 800000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace ThetaDerivMonotone

open Complex Filter Asymptotics MeasureTheory Set Topology
open ThetaDerivAsymptotic GammaSeqLocalUniform
open GammaHalfPlane

-- ==============================================================
-- Section 0: Setup — the critical-line point s(t) = 1/4 + it/2
-- ==============================================================

/-- The standard critical-line point s(t) = 1/4 + I·t/2. -/
abbrev sOfT (t : ℝ) : ℂ := 1/4 + I * (↑t / 2)

lemma sOfT_re (t : ℝ) : (sOfT t).re = 1/4 := by
  show ((1 : ℂ) / 4 + I * (↑t / 2)).re = 1/4
  have : ((1 : ℂ) / 4).re = 1/4 := by norm_num [Complex.ofReal_re, Complex.div_ofNat]
  have him : (I * (↑t / 2)).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.div_ofNat]
  simp [Complex.add_re, this, him]

lemma sOfT_re_pos (t : ℝ) : 0 < (sOfT t).re := by
  rw [sOfT_re]; norm_num

lemma sOfT_add_nat_ne_zero (t : ℝ) (n : ℕ) : sOfT t + (n : ℂ) ≠ 0 := by
  intro h
  have hre : (sOfT t + (n : ℂ)).re = 0 := by rw [h]; simp
  have : (sOfT t).re + (n : ℝ) = 0 := by
    simpa [Complex.add_re, Complex.natCast_re] using hre
  rw [sOfT_re] at this
  linarith [Nat.cast_nonneg (α := ℝ) n]

lemma sOfT_add_nat_succ_ne_zero (t : ℝ) (n : ℕ) : sOfT t + (n : ℂ) + 1 ≠ 0 := by
  intro h
  have hre : (sOfT t + (n : ℂ) + 1).re = 0 := by rw [h]; simp
  have : (sOfT t + (n : ℂ) + 1).re = (sOfT t).re + (n : ℝ) + 1 := by
    simp [Complex.add_re, Complex.natCast_re, Complex.one_re]
  rw [this, sOfT_re] at hre
  linarith [Nat.cast_nonneg (α := ℝ) n]

lemma sOfT_add_nat_re_pos (t : ℝ) (n : ℕ) : 0 < (sOfT t + (n : ℂ)).re := by
  have : (sOfT t + (n : ℂ)).re = (sOfT t).re + (n : ℝ) := by
    simp [Complex.add_re, Complex.natCast_re]
  rw [this, sOfT_re]
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- s(t) has derivative i/2 in t. -/
lemma hasDerivAt_sOfT (t : ℝ) : HasDerivAt sOfT (I / 2 : ℂ) t := by
  show HasDerivAt (fun t : ℝ => (1 : ℂ) / 4 + I * ((↑t : ℂ) / 2)) (I / 2) t
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) / 2) (1 / 2 : ℂ) t := by
    have := h1.div_const (2 : ℂ)
    simp only [one_div] at this ⊢
    convert this using 1
  have h3 : HasDerivAt (fun t : ℝ => I * ((t : ℂ) / 2)) (I * (1 / 2)) t :=
    h2.const_mul I
  have h4 := (hasDerivAt_const t (1 / 4 : ℂ)).add h3
  simp only [zero_add] at h4
  convert h4 using 1; ring

-- ==============================================================
-- Section 1: HasDerivAt for gaussTerm composed with s(t) + n
-- ==============================================================

/-- The derivative of gaussTerm at w (for Re(w) > 0) is 1/(w²(w+1)).
    gaussTerm w = log(1+1/w) - 1/w
    d/dw = (1/(1+1/w))·(-1/w²) + 1/w² = -1/(w(w+1)) + 1/w² = 1/(w²(w+1)). -/
theorem hasDerivAt_gaussTerm_at_w (w : ℂ) (hw_re : 0 < w.re) :
    HasDerivAt (fun z => gaussTerm z) (1 / (w ^ 2 * (w + 1))) w := by
  -- gaussTerm w = log(1 + 1/w) - 1/w
  -- d/dw = [derivative of log(1+1/w)] - [derivative of 1/w]
  -- = (1/(1+1/w))·(-1/w²) - (-1/w²) = -1/(w(w+1)) + 1/w² = 1/(w²(w+1))
  have hw_ne : w ≠ 0 := by intro h; rw [h] at hw_re; simp at hw_re
  have hw1_ne : w + 1 ≠ 0 := by
    intro h
    have : (w + 1).re = 0 := by rw [h]; simp
    simp [Complex.add_re] at this
    linarith
  -- 1+1/w is in slitPlane since Re(1+1/w) = 1 + Re(w)/|w|² > 0
  have h_slitPlane : 1 + 1 / w ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have : (1 + 1 / w).re = 1 + w.re / Complex.normSq w := by
      simp [Complex.add_re, Complex.div_re, Complex.one_re, Complex.one_im]
    rw [this]
    have := Complex.normSq_pos.mpr hw_ne
    positivity
  -- HasDerivAt for 1/w: derivative of id⁻¹ is -1/w²
  have h_inv : HasDerivAt (fun z => 1 / z) (-(1 / w ^ 2)) w := by
    have h := (hasDerivAt_id w).inv hw_ne
    -- h : HasDerivAt (fun z => z⁻¹) (-1 / w ^ 2) w
    -- Convert 1/z = z⁻¹ and -(1/w²) = -1/w²
    have : (fun z : ℂ => 1 / z) = (fun z => z⁻¹) := by ext z; simp [one_div]
    rw [this, show -(1 / w ^ 2) = -1 / w ^ 2 from by ring]
    exact h
  -- HasDerivAt for 1 + 1/w
  have h_sum : HasDerivAt (fun z => 1 + 1 / z) (-(1 / w ^ 2)) w := by
    have := (hasDerivAt_const w (1 : ℂ)).add h_inv
    simp only [zero_add] at this; exact this
  -- HasDerivAt for log(1 + 1/w) via chain rule
  have h_log : HasDerivAt (fun z => Complex.log (1 + 1 / z))
      (-(1 / w ^ 2) / (1 + 1 / w)) w :=
    h_sum.clog h_slitPlane
  -- Combine: gaussTerm = log(1+1/w) - 1/w
  have h_gauss : HasDerivAt (fun z => gaussTerm z)
      (-(1 / w ^ 2) / (1 + 1 / w) - (-(1 / w ^ 2))) w := by
    show HasDerivAt (fun z => Complex.log (1 + 1 / z) - 1 / z) _ w
    exact h_log.sub h_inv
  -- Simplify the derivative expression
  convert h_gauss using 1
  field_simp
  ring

/-- Chain rule: d/dt[gaussTerm(s(t)+n)] = (I/2) · gaussTerm'(s(t)+n). -/
theorem hasDerivAt_gaussTerm_comp_sOfT (n : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => gaussTerm (sOfT t + (n : ℂ)))
      (I / 2 * (1 / ((sOfT t + ↑n) ^ 2 * (sOfT t + ↑n + 1)))) t := by
  set w := sOfT t + (↑n : ℂ) with hw_def
  -- Inner derivative: d/dt[sOfT t + n] = I/2
  have h_inner : HasDerivAt (fun t : ℝ => sOfT t + (↑n : ℂ)) (I / 2) t := by
    exact (hasDerivAt_sOfT t).add (hasDerivAt_const t (↑n : ℂ)) |>.congr_deriv (by simp)
  -- Outer derivative: d/dw[gaussTerm w] = 1/(w²(w+1))
  have h_outer : HasDerivAt (fun z => gaussTerm z) (1 / (w ^ 2 * (w + 1))) w :=
    hasDerivAt_gaussTerm_at_w w (sOfT_add_nat_re_pos t n)
  -- Chain rule: (1/(w²(w+1))) * (I/2) = I/2 * (1/(w²(w+1)))
  have h_comp := h_outer.comp t h_inner
  convert h_comp using 1; ring

-- ==============================================================
-- Section 2: Uniform norm bounds
-- ==============================================================

/-- ‖s(t)+n‖ ≥ n + 1/4. -/
lemma norm_sOfT_add_nat_ge (t : ℝ) (n : ℕ) :
    (↑n + 1/4 : ℝ) ≤ ‖sOfT t + (↑n : ℂ)‖ := by
  have hre : (sOfT t + (↑n : ℂ)).re = ↑n + 1/4 := by
    have : (sOfT t + (↑n : ℂ)).re = (sOfT t).re + (n : ℝ) := by
      simp [Complex.add_re, Complex.natCast_re]
    rw [this, sOfT_re]; ring
  have hnn : (0 : ℝ) ≤ ↑n + 1/4 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  calc (↑n + 1/4 : ℝ) = |(sOfT t + (↑n : ℂ)).re| := by rw [hre, abs_of_nonneg hnn]
    _ ≤ ‖sOfT t + (↑n : ℂ)‖ := abs_re_le_norm _

/-- ‖s(t)+n+1‖ ≥ n + 5/4. -/
lemma norm_sOfT_add_nat_succ_ge (t : ℝ) (n : ℕ) :
    (↑n + 5/4 : ℝ) ≤ ‖sOfT t + (↑n : ℂ) + 1‖ := by
  have hre : (sOfT t + (↑n : ℂ) + 1).re = ↑n + 5/4 := by
    have : (sOfT t + (↑n : ℂ) + 1).re = (sOfT t).re + (n : ℝ) + 1 := by
      simp [Complex.add_re, Complex.natCast_re, Complex.one_re]
    rw [this, sOfT_re]; ring
  have hnn : (0 : ℝ) ≤ ↑n + 5/4 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  calc (↑n + 5/4 : ℝ) = |(sOfT t + (↑n : ℂ) + 1).re| := by rw [hre, abs_of_nonneg hnn]
    _ ≤ ‖sOfT t + (↑n : ℂ) + 1‖ := abs_re_le_norm _

/-- Uniform bound on the derivative: ‖(I/2)/(w²(w+1))‖ ≤ 1/(2(n+1/4)²(n+5/4)). -/
lemma norm_gaussTerm_deriv_comp_le (n : ℕ) (t : ℝ) :
    ‖I / 2 * (1 / ((sOfT t + ↑n) ^ 2 * (sOfT t + ↑n + 1)))‖
      ≤ 1 / (2 * ((↑n : ℝ) + 1/4) ^ 2 * ((↑n : ℝ) + 5/4)) := by
  set w := sOfT t + (↑n : ℂ) with hw_def
  have h14 := norm_sOfT_add_nat_ge t n
  have h54 := norm_sOfT_add_nat_succ_ge t n
  have h14_pos : (0 : ℝ) < ↑n + 1/4 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have h54_pos : (0 : ℝ) < ↑n + 5/4 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hw_ne : w ≠ 0 := sOfT_add_nat_ne_zero t n
  have hw1_ne : w + 1 ≠ 0 := sOfT_add_nat_succ_ne_zero t n
  -- ‖I/2 * (1/(w²(w+1)))‖ = (1/2) * 1/(‖w‖²·‖w+1‖)
  have h_norm : ‖I / 2 * (1 / (w ^ 2 * (w + 1)))‖ =
      1 / (2 * ‖w‖ ^ 2 * ‖w + 1‖) := by
    rw [norm_mul, norm_div, norm_div, norm_mul, norm_pow, norm_one, Complex.norm_I]
    rw [show ‖(2 : ℂ)‖ = 2 from by norm_num]
    have : (0 : ℝ) < ‖w‖ ^ 2 * ‖w + 1‖ := by positivity
    field_simp
  rw [h_norm]
  -- Now: 1/(2·‖w‖²·‖w+1‖) ≤ 1/(2·(n+1/4)²·(n+5/4))
  apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
  -- Goal: 2*(n+1/4)²*(n+5/4) ≤ 2*‖w‖²*‖w+1‖
  apply mul_le_mul
  · apply mul_le_mul (le_refl _)
      (sq_le_sq' (by linarith [norm_nonneg w]) h14) (by positivity) (by norm_num)
  · exact h54
  · exact h54_pos.le
  · apply mul_nonneg (by norm_num)
    apply sq_nonneg

/-- Shifted cubic p-series is summable. -/
private lemma summable_inv_add_one_cube :
    Summable (fun n : ℕ => 1 / ((↑n : ℝ) + 1) ^ 3) := by
  have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (↑n : ℝ) ^ 3) 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3))
  simp only [Nat.cast_add, Nat.cast_one] at h
  exact h

/-- The bound sequence is summable (comparison with C/n³). -/
lemma summable_gaussTerm_deriv_bound :
    Summable (fun n : ℕ => 1 / (2 * ((↑n : ℝ) + 1/4) ^ 2 * ((↑n : ℝ) + 5/4))) := by
  -- Compare: 1/(2(n+1/4)²(n+5/4)) ≤ 8/(n+1)³
  -- because (n+1/4) ≥ (n+1)/4 so (n+1/4)² ≥ (n+1)²/16
  -- and (n+5/4) ≥ (n+1), so denom ≥ 2·(n+1)²/16·(n+1) = (n+1)³/8
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ (summable_inv_add_one_cube.mul_left 8)
  intro n
  have hn : (0 : ℝ) ≤ ↑n := Nat.cast_nonneg n
  have h14 : (0 : ℝ) < ↑n + 1/4 := by linarith
  have h54 : (0 : ℝ) < ↑n + 5/4 := by linarith
  have h1 : (0 : ℝ) < ↑n + 1 := by linarith
  rw [show (8 : ℝ) * (1 / ((↑n + 1) ^ 3)) = 8 / ((↑n + 1) ^ 3) from by ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- Need: (n+1)³ ≤ 8 * (2 * (n+1/4)² * (n+5/4)) = 16 * (n+1/4)² * (n+5/4)
  -- (n+1/4) ≥ (n+1)/4 so (n+1/4)² ≥ (n+1)²/16
  have hge : (↑n : ℝ) + 1/4 ≥ (↑n + 1)/4 := by linarith
  have hge2 : (↑n : ℝ) + 5/4 ≥ ↑n + 1 := by linarith
  have hsq : (↑n + 1/4 : ℝ) ^ 2 ≥ ((↑n + 1) / 4) ^ 2 :=
    sq_le_sq' (by linarith) hge
  -- 16 * (n+1/4)² * (n+5/4) ≥ 16 * (n+1)²/16 * (n+1) = (n+1)³
  nlinarith [sq_nonneg ((↑n : ℝ) + 1)]

-- ==============================================================
-- Section 2b: p-series infrastructure
-- ==============================================================

/-- Shifted quadratic p-series is summable. -/
private lemma summable_inv_add_one_sq :
    Summable (fun n : ℕ => 1 / ((↑n : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (↑n : ℝ) ^ 2) 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  simp only [Nat.cast_add, Nat.cast_one] at h
  exact h

/-- Summability of 16/(n+1)². -/
private lemma summable_sixteen_div_sq :
    Summable (fun n : ℕ => 16 / ((↑n : ℝ) + 1) ^ 2) :=
  (summable_inv_add_one_sq.mul_left 16).congr (fun n => by ring)

-- ==============================================================
-- Section 3: Summability of gaussTerm at s(t)
-- ==============================================================

/-- The Gauss series Σ gaussTerm(s(t)+n) is summable for all t. -/
lemma summable_gaussTerm_sOfT (t : ℝ) :
    Summable (fun n : ℕ => gaussTerm (sOfT t + (↑n : ℂ))) := by
  -- For n ≥ 2, ‖sOfT t + n‖ ≥ n + 1/4 ≥ 2, so gauss_term_bound gives ‖·‖ ≤ 1/‖·‖²
  -- The tail (n ≥ 2) is summable by comparison; first 2 terms are finite
  rw [show (fun n : ℕ => gaussTerm (sOfT t + (↑n : ℂ)))
      = (fun n : ℕ => Complex.log (1 + 1 / (sOfT t + (↑n : ℂ))) - 1 / (sOfT t + (↑n : ℂ)))
    from rfl]
  have hshift : Summable (fun n : ℕ =>
      Complex.log (1 + 1 / (sOfT t + ((↑n + 2 : ℕ) : ℂ))) -
        1 / (sOfT t + ((↑n + 2 : ℕ) : ℂ))) := by
    -- For n ≥ 0: ‖sOfT t + (n+2)‖ ≥ (n+2)+1/4 ≥ 2
    -- gauss_term_bound gives ‖gaussTerm(w)‖ ≤ 1/‖w‖² for ‖w‖ ≥ 2
    -- 1/‖w‖² ≤ 1/(n+2+1/4)² ≤ 16/(n+1)² (since n+2+1/4 ≥ (n+1)/1)
    -- And Σ 16/(n+1)² converges
    apply Summable.of_norm_bounded_eventually_nat summable_sixteen_div_sq
    filter_upwards [Filter.eventually_ge_atTop 0] with n _
    have hge : (2 : ℝ) ≤ ‖sOfT t + ((↑n + 2 : ℕ) : ℂ)‖ := by
      have : (↑(n + 2) : ℝ) + 1/4 ≥ 2 := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
      linarith [norm_sOfT_add_nat_ge t (n + 2)]
    calc ‖Complex.log (1 + 1 / (sOfT t + ((↑n + 2 : ℕ) : ℂ))) -
            1 / (sOfT t + ((↑n + 2 : ℕ) : ℂ))‖
        ≤ 1 / ‖sOfT t + ((↑n + 2 : ℕ) : ℂ)‖ ^ 2 :=
          Aristotle.DigammaBinetBound.gauss_term_bound _ hge
      _ ≤ 16 / ((↑n : ℝ) + 1) ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          -- 1 * (n+1)² ≤ 16 * ‖w‖²
          -- ‖w‖ ≥ n+2+1/4 so ‖w‖² ≥ (n+2+1/4)² ≥ (n+1)²
          have hlow := norm_sOfT_add_nat_ge t (n + 2)
          have hlow_sq : ((↑n : ℝ) + 1) ^ 2 ≤ ‖sOfT t + ((↑(n + 2) : ℕ) : ℂ)‖ ^ 2 := by
            have h1 : (↑n : ℝ) + 1 ≤ (↑(n + 2) : ℝ) + 1/4 := by
              push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
            have h2 : (0 : ℝ) ≤ (↑n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
            calc ((↑n : ℝ) + 1) ^ 2 ≤ ((↑(n + 2) : ℝ) + 1/4) ^ 2 :=
                    sq_le_sq' (by linarith [norm_nonneg (sOfT t + ((↑(n + 2) : ℕ) : ℂ))]) h1
              _ ≤ ‖sOfT t + ((↑(n + 2) : ℕ) : ℂ)‖ ^ 2 :=
                    sq_le_sq' (by linarith [norm_nonneg (sOfT t + ((↑(n + 2) : ℕ) : ℂ))]) hlow
          nlinarith
  exact (summable_nat_add_iff 2).1 hshift

-- ==============================================================
-- Section 4: hasDerivAt_tsum application
-- ==============================================================

/-- The Gauss series is differentiable in t, with derivative the derivative series. -/
theorem hasDerivAt_gauss_series (t : ℝ) :
    HasDerivAt (fun t : ℝ => ∑' n : ℕ, gaussTerm (sOfT t + (↑n : ℂ)))
      (∑' n : ℕ, I / 2 * (1 / ((sOfT t + ↑n) ^ 2 * (sOfT t + ↑n + 1)))) t :=
  hasDerivAt_tsum summable_gaussTerm_deriv_bound
    (fun n t => hasDerivAt_gaussTerm_comp_sOfT n t)
    (fun n t => norm_gaussTerm_deriv_comp_le n t)
    (summable_gaussTerm_sOfT 0) t

-- ==============================================================
-- Section 4b: Summability of 1/(s+n)² (needed for Section 5)
-- ==============================================================

/-- The summands 1/(s+n)² are summable (for norm bound on trigamma). -/
lemma summable_inv_sq_sOfT (t : ℝ) :
    Summable (fun n : ℕ => 1 / (sOfT t + (↑n : ℂ)) ^ 2) :=
  Summable.of_norm_bounded summable_sixteen_div_sq (fun n => by
    have hn14 := norm_sOfT_add_nat_ge t n
    have h14 : (0 : ℝ) < ↑n + 1/4 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have h1 : (0 : ℝ) < ↑n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hstep1 : ‖(1 : ℂ) / (sOfT t + (↑n : ℂ)) ^ 2‖ ≤ 1 / ((↑n : ℝ) + 1/4) ^ 2 := by
      rw [one_div, norm_inv, norm_pow, one_div]
      apply inv_anti₀ (by positivity : (0 : ℝ) < ((↑n : ℝ) + 1/4) ^ 2)
      exact sq_le_sq' (by linarith [norm_nonneg (sOfT t + (↑n : ℂ))]) hn14
    have hstep2 : 1 / ((↑n : ℝ) + 1/4) ^ 2 ≤ 16 / ((↑n : ℝ) + 1) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    linarith)

-- ==============================================================
-- Section 5: Partial fractions and trigamma reduction
-- ==============================================================

/-- Partial fractions: 1/(w²(w+1)) = 1/w² - 1/w + 1/(w+1). -/
lemma partial_fractions (w : ℂ) (hw : w ≠ 0) (hw1 : w + 1 ≠ 0) :
    1 / (w ^ 2 * (w + 1)) = 1 / w ^ 2 - 1 / w + 1 / (w + 1) := by
  field_simp; ring

/-- The derivative series reduces to the trigamma series minus 1/s.

    Using partial fractions + telescoping:
    Σ 1/((s+n)²(s+n+1)) = (Σ 1/(s+n)²) - 1/s

    In our application, the factor I/2 goes along for the ride:
    Σ (I/2)/((s+n)²(s+n+1)) = (I/2) · (Σ 1/(s+n)² - 1/s) -/
theorem derivative_series_eq_trigamma (t : ℝ) :
    (∑' n : ℕ, I / 2 * (1 / ((sOfT t + ↑n) ^ 2 * (sOfT t + ↑n + 1))))
    = I / 2 * ((∑' n : ℕ, 1 / (sOfT t + ↑n) ^ 2) - 1 / sOfT t) := by
  -- Factor out I/2
  rw [tsum_mul_left]
  congr 1
  -- Need: ∑' n, 1/((s+n)²(s+n+1)) = ∑' n, 1/(s+n)² - 1/s
  set s := sOfT t with hs_def
  -- Summability of the telescoping terms
  have h_summ_tel : Summable (fun n : ℕ => 1 / (s + ↑(n + 1)) - 1 / (s + ↑n)) := by
    apply Summable.of_norm_bounded summable_sixteen_div_sq
    intro n
    have hw : s + ↑n ≠ 0 := sOfT_add_nat_ne_zero t n
    have hw1 : s + ↑n + 1 ≠ 0 := sOfT_add_nat_succ_ne_zero t n
    have h14 := norm_sOfT_add_nat_ge t n
    have h54 := norm_sOfT_add_nat_succ_ge t n
    have h54_pos : (0 : ℝ) < ↑n + 5/4 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have h_eq : s + (↑(n + 1) : ℂ) = s + ↑n + 1 := by push_cast; ring
    rw [h_eq]
    have hd : 1 / (s + ↑n + 1) - 1 / (s + ↑n) = -1 / ((s + ↑n) * (s + ↑n + 1)) := by
      field_simp
      ring
    rw [hd, norm_div, norm_neg, norm_one, norm_mul, one_div]
    calc (‖s + ↑n‖ * ‖s + ↑n + 1‖)⁻¹
        ≤ ((↑n + 1/4) * (↑n + 5/4))⁻¹ := by
          apply inv_anti₀ (by positivity)
          exact mul_le_mul h14 h54 h54_pos.le (by linarith [norm_nonneg (s + ↑n)])
      _ ≤ 16 / ((↑n : ℝ) + 1) ^ 2 := by
          rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have h_summ_sq := summable_inv_sq_sOfT t
  -- The telescope: ∑' n, (1/(s+n+1) - 1/(s+n)) = -1/s
  have h_tel : ∑' n : ℕ, (1 / (s + ↑(n + 1)) - 1 / (s + ↑n)) = -1 / s := by
    apply HasSum.tsum_eq
    -- Partial sums telescope: ∑_{k<N} (f(k+1)-f(k)) = f(N) - f(0)
    have h_partial : ∀ N : ℕ,
        ∑ i ∈ Finset.range N, (1 / (s + (↑(i + 1) : ℂ)) - 1 / (s + (↑i : ℂ)))
          = 1 / (s + ↑N) - 1 / s := by
      intro N
      have htel := Finset.sum_range_sub (fun n : ℕ => 1 / (s + (↑n : ℂ))) N
      simp only [Nat.cast_zero, add_zero] at htel
      rw [htel]
    -- 1/(s+N) → 0
    have h_inv_tend : Filter.Tendsto (fun N : ℕ => 1 / (s + (↑N : ℂ))) Filter.atTop (nhds 0) := by
      apply squeeze_zero_norm
      · intro N
        have h14 := norm_sOfT_add_nat_ge t N
        have h14_pos : (0 : ℝ) < ↑N + 1/4 := by linarith [Nat.cast_nonneg (α := ℝ) N]
        calc ‖1 / (s + (↑N : ℂ))‖ = 1 / ‖s + (↑N : ℂ)‖ := by
              rw [norm_div, norm_one]
          _ ≤ 1 / (↑N + 1/4) := by
              exact div_le_div_of_nonneg_left zero_le_one h14_pos h14
      · have : Filter.Tendsto (fun N : ℕ => (↑N : ℝ) + 1/4) Filter.atTop Filter.atTop :=
          Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
        have h1 := tendsto_inv_atTop_zero.comp this
        refine h1.congr (fun N => ?_)
        rw [Function.comp_apply, inv_eq_one_div]
    -- Partial sums → 0 - 1/s = -1/s
    rw [hasSum_iff_tendsto_nat_of_summable_norm (h_summ_tel.norm)]
    simp_rw [h_partial]
    have : Filter.Tendsto (fun N : ℕ => 1 / (s + ↑N) - 1 / s) Filter.atTop
        (nhds (0 - 1 / s)) :=
      h_inv_tend.sub tendsto_const_nhds
    rwa [show (-1 : ℂ) / s = 0 - 1 / s from by ring]
  -- Main identity: rewrite each term, split, and use telescope
  have h_pf : (fun n : ℕ => 1 / ((s + ↑n) ^ 2 * (s + ↑n + 1)))
      = (fun n : ℕ => 1 / (s + ↑n) ^ 2 + (1 / (s + ↑(n + 1)) - 1 / (s + ↑n))) := by
    ext n
    have hw : s + ↑n ≠ 0 := sOfT_add_nat_ne_zero t n
    have hw1 : s + ↑n + 1 ≠ 0 := sOfT_add_nat_succ_ne_zero t n
    have h_eq : s + (↑(n + 1) : ℂ) = s + ↑n + 1 := by push_cast; ring
    rw [h_eq]
    have hpf := partial_fractions _ hw hw1
    -- hpf : 1/(w²(w+1)) = 1/w² - 1/w + 1/(w+1)  where w = s + ↑n
    -- Need: 1/(w²(w+1)) = 1/w² + (1/(w+1) - 1/w)
    -- i.e., 1/w² - 1/w + 1/(w+1) = 1/w² + (1/(w+1) - 1/w)
    linear_combination hpf
  rw [h_pf, h_summ_sq.tsum_add h_summ_tel, h_tel]
  ring

-- ==============================================================
-- Section 6: Connection to thetaDeriv
-- ==============================================================

/-- The derivative of thetaDeriv at t equals -(1/4)·Im(Σ 1/(s+n)²).

    Proof sketch:
    thetaDeriv(t) = (1/2) · Re(ψ(s(t))) - (1/2) · log(π)
    d/dt = (1/2) · Re(ψ'(s) · s'(t)) = (1/2) · Re((i/2) · ψ'(s))
         = -(1/4) · Im(ψ'(s))
         = -(1/4) · Im(Σ 1/(s+n)²)    [trigamma series] -/
theorem thetaDeriv_hasDerivAt (t : ℝ) :
    HasDerivAt thetaDeriv
      (-(1 / 4) * (∑' n : ℕ, 1 / (sOfT t + (↑n : ℂ)) ^ 2).im) t := by
  -- Step 0: Key hypotheses
  have hs_re : 0 < (sOfT t).re := sOfT_re_pos t
  have hΓ : Complex.Gamma (sOfT t) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hs_re
  have hsumm := summable_gaussTerm_sOfT t
  -- Step 1: Show thetaDeriv = (1/2) * Re(log(sOfT ·) + Σ gaussTerm(sOfT · + n)) - (1/2)*log π
  have h_eq : thetaDeriv = fun u =>
      (1/2) * (Complex.log (sOfT u) + ∑' n : ℕ, gaussTerm (sOfT u + (↑n : ℂ))).re
      - (1/2) * Real.log Real.pi := by
    ext u
    show ThetaDerivAsymptotic.thetaDeriv u = _
    simp only [ThetaDerivAsymptotic.thetaDeriv]
    congr 1; congr 1
    have hu_re : 0 < (sOfT u).re := sOfT_re_pos u
    have hΓu : Complex.Gamma (sOfT u) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos hu_re
    have hsummu := summable_gaussTerm_sOfT u
    have hgu := gauss_series_identity (sOfT u) hu_re hΓu hsummu
    -- hgu : deriv Γ s / Γ s - log s = Σ gaussTerm(s+n)
    -- So deriv Γ s / Γ s = log s + Σ gaussTerm(s+n)
    have h_eq_c : deriv Complex.Gamma (sOfT u) / Complex.Gamma (sOfT u) =
        Complex.log (sOfT u) + ∑' n : ℕ, gaussTerm (sOfT u + (↑n : ℂ)) := by
      linear_combination hgu
    exact congrArg Complex.re h_eq_c
  -- Step 2: Differentiate the composed function.
  -- HasDerivAt of Complex.log (sOfT t) via scomp:
  have h_sOfT_slitPlane : sOfT t ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; exact hs_re
  have h_log_deriv : HasDerivAt (fun t : ℝ => Complex.log (sOfT t))
      ((sOfT t)⁻¹ * (I / 2)) t := by
    have h := (Complex.hasDerivAt_log h_sOfT_slitPlane).scomp t (hasDerivAt_sOfT t)
    -- h : HasDerivAt (log ∘ sOfT) ((I/2) • (sOfT t)⁻¹) t
    have h2 := h.congr_deriv (show (I / 2) • (sOfT t)⁻¹ = (sOfT t)⁻¹ * (I / 2) from by
      rw [smul_eq_mul]; ring)
    exact h2
  -- HasDerivAt of the Gauss series (from Section 4):
  have h_series_deriv := hasDerivAt_gauss_series t
  -- HasDerivAt of log + series:
  have h_sum_deriv : HasDerivAt (fun t : ℝ =>
      Complex.log (sOfT t) + ∑' n : ℕ, gaussTerm (sOfT t + (↑n : ℂ)))
      ((sOfT t)⁻¹ * (I / 2) +
       ∑' n : ℕ, I / 2 * (1 / ((sOfT t + ↑n) ^ 2 * (sOfT t + ↑n + 1)))) t :=
    h_log_deriv.add h_series_deriv
  -- Step 3: Extract real part via reCLM.hasFDerivAt
  have h_re_deriv : HasDerivAt (fun t : ℝ =>
      (Complex.log (sOfT t) + ∑' n : ℕ, gaussTerm (sOfT t + (↑n : ℂ))).re)
      ((sOfT t)⁻¹ * (I / 2) +
       ∑' n : ℕ, I / 2 * (1 / ((sOfT t + ↑n) ^ 2 * (sOfT t + ↑n + 1)))).re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h_sum_deriv |>.congr_deriv (by
      simp [ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply])
  -- Step 4: Scale by 1/2 and subtract constant
  set D := ((sOfT t)⁻¹ * (I / 2) +
       ∑' n : ℕ, I / 2 * (1 / ((sOfT t + ↑n) ^ 2 * (sOfT t + ↑n + 1)))).re with hD_def
  have h_scaled : HasDerivAt (fun t : ℝ =>
      (1/2 : ℝ) * (Complex.log (sOfT t) + ∑' n : ℕ, gaussTerm (sOfT t + (↑n : ℂ))).re
      - (1/2) * Real.log Real.pi)
      ((1/2 : ℝ) * D) t := by
    exact (h_re_deriv.const_mul (1/2 : ℝ)).sub (hasDerivAt_const t _)
      |>.congr_deriv (by simp [sub_zero])
  -- Step 5: Rewrite using h_eq and show derivative values match.
  rw [h_eq]
  refine h_scaled.congr_deriv ?_
  -- Simplify the derivative expression.
  rw [hD_def]
  have h_trigamma := derivative_series_eq_trigamma t
  rw [h_trigamma]
  -- Cancel 1/s terms:
  have h_cancel : (sOfT t)⁻¹ * (I / 2) +
      I / 2 * ((∑' n : ℕ, 1 / (sOfT t + (↑n : ℂ)) ^ 2) - 1 / sOfT t) =
      I / 2 * (∑' n : ℕ, 1 / (sOfT t + (↑n : ℂ)) ^ 2) := by ring
  rw [h_cancel]
  -- Re(I/2 * z) = -(1/2) * Im(z)
  have h_re_I : (I / 2 * (∑' n : ℕ, 1 / (sOfT t + (↑n : ℂ)) ^ 2)).re =
      -(1/2) * (∑' n : ℕ, 1 / (sOfT t + (↑n : ℂ)) ^ 2).im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [h_re_I]; ring

-- ==============================================================
-- Section 7: Sign of Im(Σ 1/(s+n)²)
-- ==============================================================

/-- For w with Re(w) > 0 and Im(w) > 0:
    Im(1/w²) = -2·Re(w)·Im(w)/|w|⁴ < 0.

    Proof: w² = (Re² - Im²) + 2i·Re·Im, so
    1/w² = conj(w²)/|w|⁴ has Im = -2·Re·Im/|w|⁴. -/
lemma im_inv_sq_neg_of_re_pos_im_pos (w : ℂ) (hw_re : 0 < w.re) (hw_im : 0 < w.im) :
    (1 / w ^ 2).im < 0 := by
  have hw_ne : w ≠ 0 := by intro h; rw [h] at hw_re; simp at hw_re
  rw [one_div, Complex.inv_im]
  -- Goal: -(w^2).im / normSq(w^2) < 0
  have h_sq_im : (w ^ 2).im = 2 * w.re * w.im := by
    rw [sq]; simp only [Complex.mul_im]; ring
  rw [h_sq_im]
  apply div_neg_of_neg_of_pos
  · nlinarith  -- -(2·re·im) < 0
  · exact Complex.normSq_pos.mpr (pow_ne_zero 2 hw_ne)

/-- For s = 1/4 + it/2 with t > 0, each term Im(1/(s+n)²) < 0. -/
lemma im_inv_sq_sOfT_neg (t : ℝ) (ht : 0 < t) (n : ℕ) :
    (1 / (sOfT t + (↑n : ℂ)) ^ 2).im < 0 := by
  apply im_inv_sq_neg_of_re_pos_im_pos
  · exact sOfT_add_nat_re_pos t n
  · -- Im(s(t) + n) = t/2 > 0
    show 0 < (sOfT t + (↑n : ℂ)).im
    have : (sOfT t + (↑n : ℂ)).im = (sOfT t).im := by
      simp [Complex.add_im, Complex.natCast_im]
    rw [this]
    show 0 < ((1 : ℂ) / 4 + I * (↑t / 2)).im
    have : ((1 : ℂ) / 4).im = 0 := by
      norm_num [Complex.ofReal_im, Complex.div_ofNat]
    have him : (I * (↑t / 2)).im = t / 2 := by
      simp [Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.div_ofNat, Complex.ofReal_re, Complex.ofReal_im]
    simp only [Complex.add_im]; rw [‹((1 : ℂ) / 4).im = 0›, ‹(I * (↑t / 2)).im = t / 2›]
    linarith

/-- The trigamma series has negative imaginary part for t > 0. -/
theorem im_trigamma_series_neg (t : ℝ) (ht : 0 < t) :
    (∑' n : ℕ, 1 / (sOfT t + (↑n : ℂ)) ^ 2).im < 0 := by
  have hsumm := summable_inv_sq_sOfT t
  rw [Complex.im_tsum hsumm]
  have hsumm_im : Summable (fun n : ℕ => (1 / (sOfT t + (↑n : ℂ)) ^ 2).im) :=
    hsumm.mapL Complex.imCLM
  -- Split: tsum = f(0) + tsum_{n≥1} f(n)
  rw [hsumm_im.tsum_eq_zero_add]
  -- f(0) < 0 and each f(n+1) ≤ 0, so tail ≤ 0
  have h0 : (1 / (sOfT t + (↑(0 : ℕ) : ℂ)) ^ 2).im < 0 := im_inv_sq_sOfT_neg t ht 0
  have htail_neg : ∀ n : ℕ, (1 / (sOfT t + (↑(n + 1) : ℂ)) ^ 2).im ≤ 0 :=
    fun n => le_of_lt (im_inv_sq_sOfT_neg t ht (n + 1))
  have htail_nonneg : ∀ n : ℕ, 0 ≤ -(1 / (sOfT t + (↑(n + 1) : ℂ)) ^ 2).im :=
    fun n => neg_nonneg.mpr (htail_neg n)
  have htail_le : ∑' n : ℕ, (1 / (sOfT t + (↑(n + 1) : ℂ)) ^ 2).im ≤ 0 :=
    nonpos_of_neg_nonneg (by rw [← tsum_neg]; exact tsum_nonneg htail_nonneg)
  linarith

-- ==============================================================
-- Section 8: Main results
-- ==============================================================

/-- **Key theorem**: thetaDeriv'(t) > 0 for all t > 0. -/
theorem thetaDeriv_deriv_pos (t : ℝ) (ht : 0 < t) :
    ∃ d : ℝ, HasDerivAt thetaDeriv d t ∧ 0 < d := by
  refine ⟨-(1/4) * (∑' n : ℕ, 1 / (sOfT t + (↑n : ℂ)) ^ 2).im,
         thetaDeriv_hasDerivAt t, ?_⟩
  have him := im_trigamma_series_neg t ht
  nlinarith

/-- thetaDeriv is strictly increasing on (0, ∞). -/
theorem thetaDeriv_strictMonoOn : StrictMonoOn thetaDeriv (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ))
  · -- ContinuousOn: thetaDeriv has a derivative at every point, hence differentiable, hence continuous
    apply ContinuousOn.mono (fun x _ => (thetaDeriv_hasDerivAt x).continuousAt.continuousWithinAt)
    exact Set.subset_univ _
  · -- 0 < deriv thetaDeriv x for x ∈ interior (Ioi 0) = Ioi 0
    intro x hx
    rw [interior_Ioi] at hx
    have ⟨d, hd, hd_pos⟩ := thetaDeriv_deriv_pos x hx
    rw [hd.deriv]
    exact hd_pos

end ThetaDerivMonotone
