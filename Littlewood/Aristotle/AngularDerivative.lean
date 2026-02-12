/-
Elementary derivative infrastructure for normalized complex-valued functions.

This file provides a robust quotient-rule based derivative formula for
`z(t) / ‖z(t)‖` when `z(t) ≠ 0`. It avoids branch-cut arguments and is
intended as reusable calculus wiring for Hardy-phase derivatives.
-/

import Mathlib

set_option linter.mathlibStandardSet false

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.AngularDerivative

open Complex

/-- Real inner product on `ℂ` as the real part of `conj z * w`. -/
private lemma inner_eq_star_mul_re (z w : ℂ) :
    inner ℝ z w = ((star z) * w).re := by
  simp [Complex.mul_re]
  ring

/-- Algebraic identity used to simplify the quotient-rule derivative of normalization. -/
private lemma raw_normalize_deriv_eq_angular (z z' : ℂ) (hz : z ≠ 0) :
    ((z' * (‖z‖ : ℂ) - z *
      (((2 * inner ℝ z z') / (2 * Real.sqrt (‖z‖ ^ 2)) : ℝ) : ℂ))
      / ((‖z‖ : ℂ) ^ 2))
    = (Complex.I * ↑(Complex.im (z' / z))) • (z / (‖z‖ : ℂ)) := by
  have hnormR : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hz
  have hsqrt : Real.sqrt (‖z‖ ^ 2) = ‖z‖ := by simp
  simp [hsqrt, smul_eq_mul]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.normSq_eq_norm_sq, Complex.ofReal_re, Complex.ofReal_im]
    field_simp [hnormR]
    have hre : (((‖z‖ : ℂ) ^ 2).re) = ‖z‖ ^ 2 := by simp [pow_two]
    have him : (((‖z‖ : ℂ) ^ 2).im) = 0 := by simp [pow_two]
    rw [hre, him]
    have hsqr : ‖z‖ ^ 2 - z.re ^ 2 = z.im ^ 2 := Complex.sq_norm_sub_sq_re z
    have hnormsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by nlinarith
    rw [hnormsq]
    ring
  · simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.normSq_eq_norm_sq, Complex.ofReal_re, Complex.ofReal_im]
    field_simp [hnormR]
    have hre : (((‖z‖ : ℂ) ^ 2).re) = ‖z‖ ^ 2 := by simp [pow_two]
    have him : (((‖z‖ : ℂ) ^ 2).im) = 0 := by simp [pow_two]
    rw [hre, him]
    have hsqi : ‖z‖ ^ 2 - z.im ^ 2 = z.re ^ 2 := Complex.sq_norm_sub_sq_im z
    have hnormsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by nlinarith
    rw [hnormsq]
    ring

/-- Derivative of the real norm of a complex-valued differentiable function,
written via `HasDerivAt.norm_sq` and `HasDerivAt.sqrt`. -/
theorem hasDerivAt_norm_of_hasDerivAt {z : ℝ → ℂ} {z' : ℂ} {t : ℝ}
    (hz : z t ≠ 0) (hd : HasDerivAt z z' t) :
    HasDerivAt (fun x => ‖z x‖)
      ((2 * inner ℝ (z t) z') / (2 * Real.sqrt (‖z t‖ ^ 2))) t := by
  have hsq : HasDerivAt (fun x => ‖z x‖ ^ 2) (2 * inner ℝ (z t) z') t := hd.norm_sq
  have hsqrt : HasDerivAt (fun x => Real.sqrt (‖z x‖ ^ 2))
      ((2 * inner ℝ (z t) z') / (2 * Real.sqrt (‖z t‖ ^ 2))) t := by
    exact hsq.sqrt (by
      have hnorm : ‖z t‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      exact pow_ne_zero 2 hnorm)
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt

/-- Complex-valued version of `hasDerivAt_norm_of_hasDerivAt` via `Complex.ofRealCLM`. -/
theorem hasDerivAt_norm_coe_of_hasDerivAt {z : ℝ → ℂ} {z' : ℂ} {t : ℝ}
    (hz : z t ≠ 0) (hd : HasDerivAt z z' t) :
    HasDerivAt (fun x => (‖z x‖ : ℂ))
      (((2 * inner ℝ (z t) z') / (2 * Real.sqrt (‖z t‖ ^ 2)) : ℝ) : ℂ) t := by
  have hcomp : HasDerivAt
      (fun x => Complex.ofRealCLM (‖z x‖))
      (((2 * inner ℝ (z t) z') / (2 * Real.sqrt (‖z t‖ ^ 2)) : ℝ) : ℂ) t := by
    simpa using
      (Complex.ofRealCLM.hasFDerivAt.comp t
        (hasDerivAt_norm_of_hasDerivAt hz hd).hasFDerivAt).hasDerivAt
  simpa using hcomp

/-- Quotient-rule derivative for complex normalization `z / ‖z‖`. -/
theorem hasDerivAt_normalize_aux {z : ℝ → ℂ} {z' : ℂ} {t : ℝ}
    (hz : z t ≠ 0) (hd : HasDerivAt z z' t) :
    HasDerivAt (fun x => z x / (‖z x‖ : ℂ))
      ((z' * (‖z t‖ : ℂ) - z t *
        (((2 * inner ℝ (z t) z') / (2 * Real.sqrt (‖z t‖ ^ 2)) : ℝ) : ℂ))
        / ((‖z t‖ : ℂ) ^ 2)) t := by
  have hnorm : HasDerivAt (fun x => (‖z x‖ : ℂ))
      (((2 * inner ℝ (z t) z') / (2 * Real.sqrt (‖z t‖ ^ 2)) : ℝ) : ℂ) t :=
    hasDerivAt_norm_coe_of_hasDerivAt hz hd
  have hnorm_ne : ((‖z t‖ : ℂ) ≠ 0) :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  simpa using hd.div hnorm hnorm_ne

/-- Simplified angular derivative for complex normalization. -/
theorem hasDerivAt_normalize {z : ℝ → ℂ} {z' : ℂ} {t : ℝ}
    (hz : z t ≠ 0) (hd : HasDerivAt z z' t) :
    HasDerivAt (fun x => z x / (‖z x‖ : ℂ))
      (Complex.I * ↑(Complex.im (z' / z t)) * (z t / (‖z t‖ : ℂ))) t := by
  have haux := hasDerivAt_normalize_aux (z := z) (z' := z') (t := t) hz hd
  have hEq : ((z' * (‖z t‖ : ℂ) - z t *
      (((2 * inner ℝ (z t) z') / (2 * Real.sqrt (‖z t‖ ^ 2)) : ℝ) : ℂ))
      / ((‖z t‖ : ℂ) ^ 2))
      = (Complex.I * ↑(Complex.im (z' / z t))) • (z t / (‖z t‖ : ℂ)) :=
    raw_normalize_deriv_eq_angular (z := z t) (z' := z') hz
  have haux' : HasDerivAt (fun x => z x / (‖z x‖ : ℂ))
      ((z' * (‖z t‖ : ℂ) -
        z t * (2 * ((z' * star (z t)).re) / (2 * ‖z t‖)))
        / ((‖z t‖ : ℂ) ^ 2)) t := by
    simpa [inner_eq_star_mul_re] using haux
  have hEq' :
      ((z' * (‖z t‖ : ℂ) -
        z t * (2 * ((z' * star (z t)).re) / (2 * ‖z t‖)))
        / ((‖z t‖ : ℂ) ^ 2))
      = (Complex.I * ↑(Complex.im (z' / z t))) • (z t / (‖z t‖ : ℂ)) := by
    simpa [inner_eq_star_mul_re, mul_comm] using hEq
  have hEq'' :
      ((z' * (‖z t‖ : ℂ) -
        z t * (2 * ((z' * star (z t)).re) / (2 * ‖z t‖)))
        / ((‖z t‖ : ℂ) ^ 2))
      = (Complex.I * ↑(Complex.im (z' / z t))) * (z t / (‖z t‖ : ℂ)) := by
    simpa [smul_eq_mul] using hEq'
  have hfinal : HasDerivAt (fun x => z x / (‖z x‖ : ℂ))
      ((Complex.I * ↑(Complex.im (z' / z t))) * (z t / (‖z t‖ : ℂ))) t :=
    hEq'' ▸ haux'
  exact hfinal

end Aristotle.AngularDerivative
