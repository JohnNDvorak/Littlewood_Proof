/-
Angular-velocity form of the derivative of `HardyCosSmooth.hardyCosExp`.

This file packages the product-rule derivative from `HardyCosExpDeriv` into the
single-coefficient form

  d/dt hardyCosExp(n,t) = i * (thetaDeriv(t) - log(n+1)) * hardyCosExp(n,t).
-/

import Mathlib
import Littlewood.Aristotle.HardyCosExpDeriv
import Littlewood.Aristotle.ThetaDerivAsymptotic

set_option linter.mathlibStandardSet false

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.HardyCosExpOmega

open Complex
open ThetaDerivAsymptotic

private lemma half_log_pi_mul_sq (n : ℕ) :
    (1 / 2 : ℝ) * Real.log (Real.pi * (↑n + 1) ^ 2)
      = (1 / 2 : ℝ) * Real.log Real.pi + Real.log (↑n + 1) := by
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hn_pos : (0 : ℝ) < (↑n + 1) := by positivity
  have hn_ne : (↑n + 1 : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hsq : ((↑n + 1 : ℝ) ^ 2) = (↑n + 1) * (↑n + 1) := by ring
  calc
    (1 / 2 : ℝ) * Real.log (Real.pi * (↑n + 1) ^ 2)
        = (1 / 2 : ℝ) * (Real.log Real.pi + Real.log ((↑n + 1 : ℝ) ^ 2)) := by
            rw [Real.log_mul hpi_ne (pow_ne_zero 2 hn_ne)]
    _ = (1 / 2 : ℝ) * Real.log Real.pi + (1 / 2 : ℝ) * Real.log ((↑n + 1 : ℝ) ^ 2) := by ring
    _ = (1 / 2 : ℝ) * Real.log Real.pi
          + (1 / 2 : ℝ) * (Real.log (↑n + 1) + Real.log (↑n + 1)) := by
            rw [hsq, Real.log_mul hn_ne hn_ne]
    _ = (1 / 2 : ℝ) * Real.log Real.pi + Real.log (↑n + 1) := by ring

private lemma coeff_eq_thetaDeriv_sub_log (n : ℕ) (t : ℝ) :
    ((Complex.I / 2) • deriv Gamma (1/4 + Complex.I * (↑t / 2 : ℂ)) /
        Aristotle.HardyCosExpDeriv.gammaQuarter t).im
    - (1 / 2 : ℝ) * Real.log (Real.pi * (↑n + 1) ^ 2)
    = ThetaDerivAsymptotic.thetaDeriv t - Real.log (↑n + 1) := by
  have h_im :
      (((Complex.I / 2) • deriv Gamma (1/4 + Complex.I * (↑t / 2 : ℂ)) /
          Aristotle.HardyCosExpDeriv.gammaQuarter t).im)
      = (1 / 2 : ℝ) *
          (deriv Gamma (1/4 + Complex.I * (↑t / 2 : ℂ)) /
            Aristotle.HardyCosExpDeriv.gammaQuarter t).re := by
    rw [show (((Complex.I / 2) • deriv Gamma (1/4 + Complex.I * (↑t / 2 : ℂ))) /
          Aristotle.HardyCosExpDeriv.gammaQuarter t)
          = ((Complex.I / 2 : ℂ) *
            (deriv Gamma (1/4 + Complex.I * (↑t / 2 : ℂ)) /
              Aristotle.HardyCosExpDeriv.gammaQuarter t)) by
          simp [smul_eq_mul, div_eq_mul_inv, mul_assoc]]
    simp [Complex.mul_im]
  have h_theta : ThetaDerivAsymptotic.thetaDeriv t
      = (1 / 2 : ℝ) *
          (deriv Gamma (1/4 + Complex.I * (↑t / 2 : ℂ)) /
            Aristotle.HardyCosExpDeriv.gammaQuarter t).re
        - (1 / 2 : ℝ) * Real.log Real.pi := by
    simp [ThetaDerivAsymptotic.thetaDeriv, Aristotle.HardyCosExpDeriv.gammaQuarter]
  rw [h_im, half_log_pi_mul_sq]
  linarith [h_theta]

private lemma pack_coeff (a b : ℝ) (G E : ℂ) :
    Complex.I * (a : ℂ) * G * E + G * (E * (-Complex.I * (b : ℂ)))
      = Complex.I * ((a - b : ℝ) : ℂ) * (G * E) := by
  calc
    Complex.I * (a : ℂ) * G * E + G * (E * (-Complex.I * (b : ℂ)))
        = G * (E * (Complex.I * (a : ℂ))) - G * (E * (Complex.I * (b : ℂ))) := by
            simp [sub_eq_add_neg, mul_left_comm, mul_comm]
    _ = G * (E * (Complex.I * (a : ℂ)) - E * (Complex.I * (b : ℂ))) := by
          rw [← mul_sub]
    _ = G * (E * (Complex.I * (((a - b : ℝ) : ℂ)))) := by
          congr 1
          calc
            E * (Complex.I * (a : ℂ)) - E * (Complex.I * (b : ℂ))
                = (E * Complex.I) * ((a : ℂ) - (b : ℂ)) := by
                    rw [mul_sub]
                    simp [mul_assoc]
            _ = E * (Complex.I * (((a - b : ℝ) : ℂ))) := by
                    simp [mul_assoc]
    _ = Complex.I * ((a - b : ℝ) : ℂ) * (G * E) := by
          simp [mul_assoc, mul_left_comm, mul_comm]

/--
Single-coefficient angular-velocity derivative for `hardyCosExp`.
-/
theorem hardyCosExp_angular_velocity (n : ℕ) (t : ℝ) :
    HasDerivAt (fun x => HardyCosSmooth.hardyCosExp n x)
      (Complex.I * ↑(ThetaDerivAsymptotic.thetaDeriv t - Real.log (↑(n + 1)))
        * HardyCosSmooth.hardyCosExp n t) t := by
  have h := Aristotle.HardyCosExpDeriv.hasDerivAt_hardyCosExp_clean n t
  set Dold : ℂ :=
      Complex.I * ↑((Complex.I / 2) • deriv Gamma (1/4 + Complex.I * (↑t / 2 : ℂ)) /
          Aristotle.HardyCosExpDeriv.gammaQuarter t).im
        * Aristotle.HardyCosExpDeriv.gammaQuarterNormalized t *
          Complex.exp (Aristotle.HardyCosExpDeriv.phaseArg n t)
      + Aristotle.HardyCosExpDeriv.gammaQuarterNormalized t *
          (Complex.exp (Aristotle.HardyCosExpDeriv.phaseArg n t) *
            (-Complex.I * (((1 / 2) * Real.log (Real.pi * (↑n + 1) ^ 2) : ℝ) : ℂ))) with hDold
  have hD : HasDerivAt (fun x => HardyCosSmooth.hardyCosExp n x) Dold t := by
    simpa [hDold] using h
  have hcoef := coeff_eq_thetaDeriv_sub_log n t
  have hHardy :
      HardyCosSmooth.hardyCosExp n t =
        Aristotle.HardyCosExpDeriv.gammaQuarterNormalized t *
          Complex.exp (Aristotle.HardyCosExpDeriv.phaseArg n t) := by
    simpa [Aristotle.HardyCosExpDeriv.hardyCosExpAux,
      Aristotle.HardyCosExpDeriv.hardyCosExpAux_eq] using
      (Aristotle.HardyCosExpDeriv.hardyCosExpAux_eq n t).symm
  have hrewrite :
      Dold = Complex.I * ↑(ThetaDerivAsymptotic.thetaDeriv t - Real.log (↑(n + 1)))
        * HardyCosSmooth.hardyCosExp n t := by
    rw [hDold, hHardy]
    calc
      Complex.I *
            ↑((Complex.I / 2) • deriv Gamma (1 / 4 + Complex.I * (↑t / 2 : ℂ)) /
                Aristotle.HardyCosExpDeriv.gammaQuarter t).im *
            Aristotle.HardyCosExpDeriv.gammaQuarterNormalized t *
          Complex.exp (Aristotle.HardyCosExpDeriv.phaseArg n t) +
          Aristotle.HardyCosExpDeriv.gammaQuarterNormalized t *
            (Complex.exp (Aristotle.HardyCosExpDeriv.phaseArg n t) *
              (-Complex.I * ↑(1 / 2 * Real.log (Real.pi * (↑n + 1) ^ 2))))
          = Complex.I *
              (((Complex.I / 2) • deriv Gamma (1 / 4 + Complex.I * (↑t / 2 : ℂ)) /
                    Aristotle.HardyCosExpDeriv.gammaQuarter t).im
                  - ((1 / 2 : ℝ) * Real.log (Real.pi * (↑n + 1) ^ 2) : ℝ) : ℂ) *
              (Aristotle.HardyCosExpDeriv.gammaQuarterNormalized t *
                Complex.exp (Aristotle.HardyCosExpDeriv.phaseArg n t)) := by
              simpa using pack_coeff
                (((Complex.I / 2) • deriv Gamma (1/4 + Complex.I * (↑t / 2 : ℂ)) /
                  Aristotle.HardyCosExpDeriv.gammaQuarter t).im)
                ((1 / 2 : ℝ) * Real.log (Real.pi * (↑n + 1) ^ 2))
                (Aristotle.HardyCosExpDeriv.gammaQuarterNormalized t)
                (Complex.exp (Aristotle.HardyCosExpDeriv.phaseArg n t))
      _ = Complex.I * ↑(ThetaDerivAsymptotic.thetaDeriv t - Real.log (↑(n + 1))) *
            (Aristotle.HardyCosExpDeriv.gammaQuarterNormalized t *
              Complex.exp (Aristotle.HardyCosExpDeriv.phaseArg n t)) := by
            congr 2
            exact_mod_cast hcoef
  exact hrewrite ▸ hD

end Aristotle.HardyCosExpOmega
