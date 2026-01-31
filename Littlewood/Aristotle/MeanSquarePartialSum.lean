/-
Integrated from Aristotle output 0e362e66-33af-4975-b36c-2dd58c94066d.
Definitions for partial sums and mean squares of the Riemann zeta function.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

KEY DEFINITIONS:
- zetaPartialSum: partial sum of the Dirichlet series for zeta at s = 1/2 + it
- M: truncation point ⌊√(t/2π)⌋ for the approximate functional equation
- meanSquarePartialSum: ∫₁ᵀ ‖Σₙ≤M(t) n^{-1/2-it}‖² dt
- meanSquareZeta: ∫₁ᵀ ‖ζ(1/2+it)‖² dt
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace MeanSquarePartialSum

/-
The partial sum of the Dirichlet series for the Riemann zeta function at s = 1/2 + it:
  Σ_{n=1}^{N} n^{-1/2 - it}
-/
noncomputable def zetaPartialSum (t : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-(1/2 : ℂ) - Complex.I * t)

/-
The upper bound of the summation in the approximate functional equation,
defined as the integer part of √(t / 2π).
-/
noncomputable def M (t : ℝ) : ℕ := Nat.sqrt ⌊t / (2 * Real.pi)⌋₊

/-
The mean square of the partial sum of the zeta function up to T:
  ∫₁ᵀ ‖Σ_{n≤M(t)} n^{-1/2-it}‖² dt
-/
noncomputable def meanSquarePartialSum (T : ℝ) : ℝ :=
  ∫ t in Set.Ioc 1 T, ‖zetaPartialSum t (M t)‖^2

/-
The mean square of the Riemann zeta function on the critical line up to T:
  ∫₁ᵀ ‖ζ(1/2 + it)‖² dt
-/
noncomputable def meanSquareZeta (T : ℝ) : ℝ :=
  ∫ t in Set.Ioc 1 T, ‖riemannZeta (1/2 + Complex.I * t)‖^2

end MeanSquarePartialSum
