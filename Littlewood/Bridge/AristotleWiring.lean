/-
Master wiring file connecting Aristotle proofs to sorries.
This file imports proved results and re-exports them with names
matching what other files expect.

Key theorems available:

From ZeroCountingXi (namespace ZeroCountingXi):
- xi : ℂ → ℂ                    -- s * (s - 1) * completedRiemannZeta₀ s + 1
- xi_entire : Differentiable ℂ xi
- xi_Mathlib_differentiable     -- alias for xi_entire
- zetaZeroCount_via_argument    -- zero counting via argument principle

From NZerosStirling (namespace NZerosStirling):
- S_bound                       -- |S(T)| ≤ C * log T
- N_from_S_and_Stirling         -- N(T) from S and Stirling

From StirlingArgGamma (root level):
- stirling_arg_gamma            -- |arg Γ - approx| ≤ C/T for T ≥ 2
- stirling_formula_exp          -- Γ(s) = exp(stirling_term s) * (1 + ε)
- im_stirling_term_approx       -- Im(stirling_term) - approx is O(1/T)
- stirling_approx               -- (T/2) * log(T/2) - T/2 - π/8
- stirling_term                 -- (s - 1/2) * log s - s + (1/2) * log(2π)

From TruncatedExplicitFormula (namespace TruncatedExplicitFormula):
- chebyshevPsi                  -- local definition
- zetaZerosInBox                -- zeros with |Im ρ| ≤ T
- psi_as_trig_sum               -- ψ(x) - x as sum over zeros + error

From ZetaBoundsNorm (root level):
- zeta_bound_two_line           -- |ζ(2+it)| < 2
- norm_zeta_zero_line_eq        -- |ζ(it)| relation via functional equation

From HardyZConjugation (namespace HardyZConjugation):
- hardyTheta                    -- Hardy θ function
- hardyZ                        -- Hardy Z function
- completedRiemannZeta_conj     -- Λ(s̄) = Λ(s)̄
- completedRiemannZeta_critical_line_real -- Im Λ(1/2 + it) = 0

From RiemannVonMangoldt (namespace RiemannVonMangoldtModule):
- N                             -- zero counting function
- S                             -- error term function
- N_expansion                   -- N(T) = (T/2π) log(T/2πe) + 1 + S(T)

From IntegralLogSqrtAsymp (namespace IntegralLogSqrtModule):
- integral_log_sqrt_quarter_asymp -- ∫₁ᵀ log√(1/4 + t²) = Θ(T log T)
-/

import Littlewood.Aristotle.ZeroCountingXi
import Littlewood.Aristotle.NZerosStirling
import Littlewood.Aristotle.StirlingArgGamma
import Littlewood.Aristotle.TruncatedExplicitFormula
import Littlewood.Aristotle.RiemannVonMangoldt
import Littlewood.Aristotle.ZetaBoundsNorm
import Littlewood.Aristotle.HardyZConjugation
import Littlewood.Aristotle.IntegralLogSqrtAsymp

-- Make key theorems available at module level for easier wiring

namespace AristotleWiring

-- From ZeroCountingXi
open ZeroCountingXi in
theorem xi_is_entire : Differentiable ℂ ZeroCountingXi.xi := xi_entire

-- From NZerosStirling: S(T) bound
open NZerosStirling in
theorem S_is_bounded (T : ℝ) (hT : 2 ≤ T) : ∃ C, |NZerosStirling.S T| ≤ C * Real.log T :=
  S_bound T hT

-- From StirlingArgGamma: Stirling's approximation (pointwise form)
theorem stirling_pointwise (T : ℝ) (hT : 2 ≤ T) :
    ∃ C, |Complex.arg (Complex.Gamma (1/4 + Complex.I * T/2)) -
     ((T/2) * Real.log (T/2) - T/2 - Real.pi/8)| ≤ C / T :=
  stirling_arg_gamma T hT

-- From StirlingArgGamma: asymptotic form
theorem stirling_asymptotic :
    (fun (T : ℝ) => (stirling_term (1/4 + Complex.I * T/2)).im - stirling_approx T)
    =O[Filter.atTop] (fun (T : ℝ) => 1/T) :=
  im_stirling_term_approx

-- From ZetaBoundsNorm: zeta bound on Re(s) = 2
theorem zeta_bounded_on_two_line (t : ℝ) :
    ‖riemannZeta (2 + Complex.I * t)‖ ≤ ‖riemannZeta 2‖ ∧ ‖riemannZeta 2‖ < 2 :=
  zeta_bound_two_line t

-- From HardyZConjugation: completed zeta is real on critical line
open HardyZConjugation in
theorem completed_zeta_real_critical_line (t : ℝ) :
    (completedRiemannZeta (1 / 2 + Complex.I * t)).im = 0 :=
  completedRiemannZeta_critical_line_real t

-- From IntegralLogSqrtAsymp: integral asymptotic (different from MeanSquare's version)
theorem log_sqrt_quarter_integral_asymp :
    (fun T => ∫ t in (1:ℝ)..T, Real.log (Real.sqrt (1/4 + t^2)))
    =Θ[Filter.atTop] (fun T => T * Real.log T) :=
  IntegralLogSqrtModule.integral_log_sqrt_quarter_asymp

-- From TruncatedExplicitFormula: explicit formula
open TruncatedExplicitFormula in
theorem psi_explicit_formula (x : ℝ) (hx : 2 < x) (T : ℝ) (hT : 2 ≤ T) :
    ∃ (error_term : ℝ) (C : ℝ),
      TruncatedExplicitFormula.chebyshevPsi x - x =
      -2 * ∑ ρ ∈ TruncatedExplicitFormula.zetaZerosInBox T,
        (x^ρ.re / ‖ρ‖) * Real.cos (ρ.im * Real.log x + ρ.arg)
      + error_term ∧
      |error_term| ≤ C * x * (Real.log x)^2 / T :=
  psi_as_trig_sum x hx T hT

end AristotleWiring
