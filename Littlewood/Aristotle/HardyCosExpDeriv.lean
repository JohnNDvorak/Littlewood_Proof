/-
Derivative infrastructure for `HardyCosSmooth.hardyCosExp`.

This file builds a fully explicit `HasDerivAt` formula for `hardyCosExp`
using:
- Gamma-quarter derivative from `GammaHalfPlane`
- Normalization derivative from `Aristotle.AngularDerivative`
- Product/chain rules for the exponential phase factor
-/

import Mathlib
import Littlewood.Aristotle.AngularDerivative
import Littlewood.Aristotle.GammaHalfPlane
import Littlewood.Aristotle.HardyCosSmooth

set_option linter.mathlibStandardSet false

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.HardyCosExpDeriv

open Complex

/-- `Γ(1/4 + it/2)` as a real-parameterized complex function. -/
def gammaQuarter (t : ℝ) : ℂ :=
  Gamma (1/4 + I * (↑t / 2) : ℂ)

/-- Derivative of `gammaQuarter`. -/
theorem hasDerivAt_gammaQuarter (t : ℝ) :
    HasDerivAt gammaQuarter
      ((I / 2) • deriv Gamma (1/4 + I * (↑t / 2) : ℂ)) t := by
  change HasDerivAt (fun t : ℝ => Gamma (1/4 + I * (↑t / 2) : ℂ))
    ((I / 2) • deriv Gamma (1/4 + I * (↑t / 2) : ℂ)) t
  simpa [smul_eq_mul] using (GammaHalfPlane.hasDerivAt_gamma_quarter t)

/-- Non-vanishing of `gammaQuarter`. -/
theorem gammaQuarter_ne_zero (t : ℝ) : gammaQuarter t ≠ 0 := by
  simpa [gammaQuarter] using GammaHalfPlane.gamma_quarter_ne_zero t

/-- Normalized quarter-gamma phase factor. -/
def gammaQuarterNormalized (t : ℝ) : ℂ :=
  gammaQuarter t / (‖gammaQuarter t‖ : ℂ)

/-- The exponential phase argument in complex form. -/
def phaseArg (n : ℕ) (t : ℝ) : ℂ :=
  -(I * (((t : ℂ) / 2) * (Real.log (Real.pi * (↑n + 1) ^ 2) : ℂ)))

/-- A local expression equal to `HardyCosSmooth.hardyCosExp`. -/
def hardyCosExpAux (n : ℕ) (t : ℝ) : ℂ :=
  gammaQuarterNormalized t * Complex.exp (phaseArg n t)

/-- `hardyCosExpAux` is definitionally equal to `HardyCosSmooth.hardyCosExp`. -/
theorem hardyCosExpAux_eq (n : ℕ) (t : ℝ) :
    hardyCosExpAux n t = HardyCosSmooth.hardyCosExp n t := by
  simp [hardyCosExpAux, gammaQuarterNormalized, gammaQuarter, phaseArg,
    HardyCosSmooth.hardyCosExp]

/-- Derivative of the normalized quarter-gamma factor. -/
theorem hasDerivAt_gammaQuarterNormalized (t : ℝ) :
    HasDerivAt gammaQuarterNormalized
      ((((I / 2) • deriv Gamma (1/4 + I * (↑t / 2) : ℂ)) * (‖gammaQuarter t‖ : ℂ)
        - gammaQuarter t *
          (((2 * inner ℝ (gammaQuarter t)
              ((I / 2) • deriv Gamma (1/4 + I * (↑t / 2) : ℂ))) /
            (2 * Real.sqrt (‖gammaQuarter t‖ ^ 2)) : ℝ) : ℂ)) /
        ((‖gammaQuarter t‖ : ℂ) ^ 2)) t := by
  simpa [gammaQuarterNormalized] using
    (Aristotle.AngularDerivative.hasDerivAt_normalize_aux (z := gammaQuarter)
      (z' := ((I / 2) • deriv Gamma (1/4 + I * (↑t / 2) : ℂ)))
      (t := t) (gammaQuarter_ne_zero t) (hasDerivAt_gammaQuarter t))

/-- Angular-velocity form for `gammaQuarterNormalized`. -/
theorem hasDerivAt_gammaQuarterNormalized_clean (t : ℝ) :
    HasDerivAt gammaQuarterNormalized
      (Complex.I * ↑(Complex.im
        (((I / 2) • deriv Gamma (1/4 + I * (↑t / 2) : ℂ)) / gammaQuarter t))
        * gammaQuarterNormalized t) t := by
  simpa [gammaQuarterNormalized] using
    (Aristotle.AngularDerivative.hasDerivAt_normalize
      (z := gammaQuarter)
      (z' := ((I / 2) • deriv Gamma (1/4 + I * (↑t / 2) : ℂ)))
      (t := t)
      (gammaQuarter_ne_zero t)
      (hasDerivAt_gammaQuarter t))

/-- Derivative of `phaseArg`. -/
theorem hasDerivAt_phaseArg (n : ℕ) (t : ℝ) :
    HasDerivAt (phaseArg n)
      (-I * (((1 / 2) * Real.log (Real.pi * (↑n + 1) ^ 2) : ℝ) : ℂ)) t := by
  have hcast : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t))
  have hmul : HasDerivAt
      (fun x : ℝ => (((x : ℂ) / 2) * (Real.log (Real.pi * (↑n + 1) ^ 2) : ℂ)))
      (((1 : ℂ) / 2) * (Real.log (Real.pi * (↑n + 1) ^ 2) : ℂ)) t := by
    exact (hcast.div_const (2 : ℂ)).mul_const _
  have h := (HasDerivAt.const_mul (I : ℂ) hmul).neg
  simpa [phaseArg, mul_assoc, mul_left_comm, mul_comm] using h

/-- Derivative of the exponential phase factor. -/
theorem hasDerivAt_phaseExp (n : ℕ) (t : ℝ) :
    HasDerivAt (fun x => Complex.exp (phaseArg n x))
      (Complex.exp (phaseArg n t) *
        (-I * (((1 / 2) * Real.log (Real.pi * (↑n + 1) ^ 2) : ℝ) : ℂ))) t := by
  simpa using (hasDerivAt_phaseArg n t).cexp

/-- Product-rule derivative for the auxiliary Hardy phase expression. -/
theorem hasDerivAt_hardyCosExp_aux (n : ℕ) (t : ℝ) :
    HasDerivAt (fun x => hardyCosExpAux n x)
      ((((I / 2) • deriv Gamma (1/4 + I * (↑t / 2) : ℂ)) * (‖gammaQuarter t‖ : ℂ)
        - gammaQuarter t *
          (((2 * inner ℝ (gammaQuarter t)
              ((I / 2) • deriv Gamma (1/4 + I * (↑t / 2) : ℂ))) /
            (2 * Real.sqrt (‖gammaQuarter t‖ ^ 2)) : ℝ) : ℂ)) /
        ((‖gammaQuarter t‖ : ℂ) ^ 2) * Complex.exp (phaseArg n t)
      + gammaQuarterNormalized t *
        (Complex.exp (phaseArg n t) *
          (-I * (((1 / 2) * Real.log (Real.pi * (↑n + 1) ^ 2) : ℝ) : ℂ)))) t := by
  unfold hardyCosExpAux
  exact (hasDerivAt_gammaQuarterNormalized t).mul (hasDerivAt_phaseExp n t)

/-- Explicit derivative formula for `HardyCosSmooth.hardyCosExp`. -/
theorem hasDerivAt_hardyCosExp (n : ℕ) (t : ℝ) :
    HasDerivAt (fun x => HardyCosSmooth.hardyCosExp n x)
      ((((I / 2) • deriv Gamma (1/4 + I * (↑t / 2) : ℂ)) * (‖gammaQuarter t‖ : ℂ)
        - gammaQuarter t *
          (((2 * inner ℝ (gammaQuarter t)
              ((I / 2) • deriv Gamma (1/4 + I * (↑t / 2) : ℂ))) /
            (2 * Real.sqrt (‖gammaQuarter t‖ ^ 2)) : ℝ) : ℂ)) /
        ((‖gammaQuarter t‖ : ℂ) ^ 2) * Complex.exp (phaseArg n t)
      + gammaQuarterNormalized t *
        (Complex.exp (phaseArg n t) *
          (-I * (((1 / 2) * Real.log (Real.pi * (↑n + 1) ^ 2) : ℝ) : ℂ)))) t := by
  simpa [hardyCosExpAux_eq] using hasDerivAt_hardyCosExp_aux n t

/-- Cleaner product-rule form: normalized-Gamma angular term plus explicit phase term. -/
theorem hasDerivAt_hardyCosExp_clean (n : ℕ) (t : ℝ) :
    HasDerivAt (fun x => HardyCosSmooth.hardyCosExp n x)
      (Complex.I * ↑(Complex.im
          (((I / 2) • deriv Gamma (1/4 + I * (↑t / 2) : ℂ)) / gammaQuarter t))
          * gammaQuarterNormalized t * Complex.exp (phaseArg n t)
        + gammaQuarterNormalized t *
          (Complex.exp (phaseArg n t) *
            (-Complex.I * (((1 / 2) * Real.log (Real.pi * (↑n + 1) ^ 2) : ℝ) : ℂ)))) t := by
  have hA := hasDerivAt_gammaQuarterNormalized_clean t
  have hB := hasDerivAt_phaseExp n t
  have hAux : HasDerivAt (fun x => hardyCosExpAux n x)
      (Complex.I * ↑(Complex.im
          (((I / 2) • deriv Gamma (1/4 + I * (↑t / 2) : ℂ)) / gammaQuarter t))
          * gammaQuarterNormalized t * Complex.exp (phaseArg n t)
        + gammaQuarterNormalized t *
          (Complex.exp (phaseArg n t) *
            (-Complex.I * (((1 / 2) * Real.log (Real.pi * (↑n + 1) ^ 2) : ℝ) : ℂ)))) t := by
    simpa [hardyCosExpAux] using hA.mul hB
  simpa [hardyCosExpAux_eq] using hAux

end Aristotle.HardyCosExpDeriv
