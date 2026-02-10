/-
Properties of Γ(1/4 + it/2) needed for Hardy's theta function analysis.

KEY RESULTS:
  gamma_quarter_ne_zero: Γ(1/4 + it/2) ≠ 0 for all t : ℝ
  gamma_quarter_re_pos: Re(1/4 + I*t/2) = 1/4 > 0
  gamma_quarter_not_neg_int: 1/4 + I*t/2 ≠ -↑m for all m : ℕ
  differentiableAt_gamma_quarter: Γ is ℂ-differentiable at 1/4+it/2
  hasDerivAt_gamma_quarter: t ↦ Γ(1/4+it/2) has ℝ→ℂ derivative
  gamma_quarter_zero_in_slitPlane: Γ(1/4) ∈ slitPlane (positive real)

These are prerequisites for computing θ'(t) via Mathlib's chain rule:
  differentiableAt_Gamma requires s ≠ -m for all m
  HasDerivAt.clog requires f(x) ∈ slitPlane

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GammaHalfPlane

open Complex

/-- The real part of 1/4 + it/2 is always 1/4. -/
lemma re_quarter_plus_it_half (t : ℝ) :
    (1/4 + I * (t/2) : ℂ).re = 1/4 := by
  simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im]

/-- 1/4 + it/2 has positive real part. -/
lemma re_quarter_plus_it_half_pos (t : ℝ) :
    (0 : ℝ) < (1/4 + I * (t/2) : ℂ).re := by
  rw [re_quarter_plus_it_half]
  norm_num

/-- 1/4 + it/2 is never a non-positive integer. -/
lemma quarter_plus_it_half_ne_neg_nat (t : ℝ) (m : ℕ) :
    (1/4 + I * (t/2) : ℂ) ≠ -(m : ℂ) := by
  intro h
  have h1 := re_quarter_plus_it_half_pos t
  rw [h] at h1
  simp at h1
  linarith [Nat.cast_nonneg (α := ℝ) m]

/-- Γ(1/4 + it/2) is never zero. -/
theorem gamma_quarter_ne_zero (t : ℝ) :
    Gamma (1/4 + I * (t/2) : ℂ) ≠ 0 :=
  Gamma_ne_zero_of_re_pos (re_quarter_plus_it_half_pos t)

/-- Γ is ℂ-differentiable at 1/4 + it/2. -/
theorem differentiableAt_gamma_quarter (t : ℝ) :
    DifferentiableAt ℂ Gamma (1/4 + I * (t/2) : ℂ) :=
  differentiableAt_Gamma _ (fun m => quarter_plus_it_half_ne_neg_nat t m)

/-- The affine function t ↦ 1/4 + it/2 from ℝ to ℂ. -/
private lemma hasDerivAt_quarter_affine (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1/4 + I * ((t : ℂ)/2) : ℂ)) (I / 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => (I * ((t : ℂ) / 2) : ℂ)) (I / 2) t := by
    have h3 : HasDerivAt (fun t : ℝ => ((t : ℂ) / 2 : ℂ)) (1 / 2 : ℂ) t := by
      convert h1.div_const (2 : ℂ) using 1
    convert h3.const_mul I using 1; ring
  convert (hasDerivAt_const t (1/4 : ℂ)).add h2 using 1; ring

/-- The function t ↦ Γ(1/4 + it/2) has a derivative as a function ℝ → ℂ.
    Derivative = Γ'(1/4+it/2) · (i/2) by the chain rule. -/
theorem hasDerivAt_gamma_quarter (t : ℝ) :
    HasDerivAt (fun t : ℝ => Gamma (1/4 + I * ((t : ℂ)/2)))
      ((I / 2) • deriv Gamma (1/4 + I * (t/2) : ℂ))
      t :=
  (differentiableAt_gamma_quarter t).hasDerivAt.scomp t (hasDerivAt_quarter_affine t)

/-- ‖Γ(1/4 + it/2)‖ > 0 for all t. -/
lemma norm_gamma_quarter_pos (t : ℝ) :
    (0 : ℝ) < ‖Gamma (1/4 + I * (t/2) : ℂ)‖ :=
  norm_pos_iff.mpr (gamma_quarter_ne_zero t)

/-- Γ(1/4) is a positive real number. -/
lemma gamma_quarter_pos : (0 : ℝ) < Real.Gamma (1/4) :=
  Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1/4)

/-- At t = 0, Γ(1/4 + it/2) = Γ(1/4) > 0, hence in slitPlane. -/
theorem gamma_quarter_zero_in_slitPlane :
    Gamma (1/4 + I * ((0 : ℝ)/2) : ℂ) ∈ slitPlane := by
  simp only [ofReal_zero, zero_div, mul_zero, add_zero]
  have : (1/4 : ℂ) = ((1/4 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.Gamma_ofReal]
  exact Complex.ofReal_mem_slitPlane.mpr gamma_quarter_pos

end GammaHalfPlane
