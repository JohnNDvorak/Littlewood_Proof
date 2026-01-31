/- 
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib

/-!
# Perron's Formula (Minimal Core)

This file provides the basic integrand and truncated Perron kernel definitions
needed for downstream work. The full analytic Perron formula remains to be
developed.

Perron's formula relates Dirichlet series coefficients to contour integrals:
  ∑_{n≤x} a_n = (1/2πi) ∫_{c-i∞}^{c+i∞} F(s) x^s/s ds
-/

namespace Littlewood.ExplicitFormulas.PerronFormula

open Complex MeasureTheory

/-- The Perron integrand x^(c+it)/(c+it). -/
noncomputable def perronIntegrand (x c t : ℝ) : ℂ :=
  (x : ℂ) ^ (c + t * I) / (c + t * I)

/-- Truncated Perron kernel over [-T, T]. -/
noncomputable def perronKernelTrunc (x c T : ℝ) : ℂ :=
  (1 / (2 * π)) * ∫ t in Set.Icc (-T) T, perronIntegrand x c t

/-- Perron kernel at T = 0. -/
noncomputable def perronKernel (x c : ℝ) : ℂ :=
  perronKernelTrunc x c 0

@[simp] theorem perronKernel_def (x c : ℝ) :
    perronKernel x c = perronKernelTrunc x c 0 := rfl

@[simp] theorem perronKernelTrunc_def (x c T : ℝ) :
    perronKernelTrunc x c T =
      (1 / (2 * π)) * ∫ t in Set.Icc (-T) T, perronIntegrand x c t := rfl

end Littlewood.ExplicitFormulas.PerronFormula
