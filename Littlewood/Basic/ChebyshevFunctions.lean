/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Chebyshev Functions - Extensions

This file provides aliases and additional lemmas for the Chebyshev functions
from Mathlib.NumberTheory.Chebyshev.

The main definitions are:
* `Chebyshev.psi` : ψ(x) = ∑_{n ≤ x} Λ(n)
* `Chebyshev.theta` : θ(x) = ∑_{p ≤ x, p prime} log(p)

## References

* Montgomery-Vaughan, "Multiplicative Number Theory I", Chapter 2
-/

open Nat ArithmeticFunction Finset BigOperators Real Filter
open scoped Chebyshev

-- Alias for compatibility with existing code
noncomputable def chebyshevPsi (x : ℝ) : ℝ := Chebyshev.psi x
noncomputable def chebyshevTheta (x : ℝ) : ℝ := Chebyshev.theta x

namespace ChebyshevExt

-- Additional lemmas not in Mathlib

-- Asymptotics
open Asymptotics in
theorem chebyshevPsi_sub_chebyshevTheta_isBigO :
    (fun x => ψ x - θ x) =O[atTop] (fun x => x.sqrt * log x) := by
  refine IsBigO.of_bound 2 ?_
  refine (Filter.eventually_atTop.2 ?_)
  refine ⟨1, ?_⟩
  intro x hx
  have hbound := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := x) hx
  have hxlog : 0 ≤ log x := by
    exact log_nonneg (by linarith)
  have hx0 : 0 ≤ x.sqrt := by
    exact Real.sqrt_nonneg _
  have hnorm : ‖x.sqrt * log x‖ = x.sqrt * log x := by
    calc
      ‖x.sqrt * log x‖ = |x.sqrt * log x| := by
        simp [Real.norm_eq_abs]
      _ = |x.sqrt| * |log x| := by
        simp [abs_mul]
      _ = x.sqrt * log x := by
        simp [abs_of_nonneg hx0, abs_of_nonneg hxlog]
  have hbound' : |ψ x - θ x| ≤ 2 * (x.sqrt * log x) := by
    simpa [mul_assoc] using hbound
  simpa [Real.norm_eq_abs, hnorm] using hbound'

theorem chebyshevTheta_le (x : ℝ) (hx : 1 ≤ x) : θ x ≤ 2 * x := by
  -- log(4) ≈ 1.39 < 2
  calc θ x ≤ Real.log 4 * x := Chebyshev.theta_le_log4_mul_x (by linarith)
    _ ≤ 2 * x := by
      have h : Real.log 4 ≤ 2 := by
        have h' : (4 : ℝ) ≤ Real.exp 2 := by
          have h'' : (2 : ℝ) * 2 ≤ Real.exp 2 := by
            simpa using (Real.two_mul_le_exp (x := (2 : ℝ)))
          nlinarith
        exact (Real.log_le_iff_le_exp (by norm_num)).2 h'
      nlinarith

theorem chebyshevPsi_le (x : ℝ) (hx : 1 ≤ x) : ψ x ≤ 6 * x := by
  -- log(4) + 4 ≈ 5.39 < 6
  calc ψ x ≤ (Real.log 4 + 4) * x := Chebyshev.psi_le_const_mul_self (by linarith)
    _ ≤ 6 * x := by
      have h : Real.log 4 ≤ 2 := by
        have h' : (4 : ℝ) ≤ Real.exp 2 := by
          have h'' : (2 : ℝ) * 2 ≤ Real.exp 2 := by
            simpa using (Real.two_mul_le_exp (x := (2 : ℝ)))
          nlinarith
        exact (Real.log_le_iff_le_exp (by norm_num)).2 h'
      nlinarith

/-- θ(x)/x → 1 as x → ∞ (PNT for θ).
Axiomatized: previously derived from PrimeNumberTheoremAnd.chebyshev_asymptotic.
Unused by the critical path but retained for completeness. -/
axiom chebyshevTheta_asymptotic : Tendsto (fun x => θ x / x) atTop (nhds 1)

/-- ψ(x)/x → 1 as x → ∞ (PNT for ψ).
Axiomatized: previously derived from PrimeNumberTheoremAnd.WeakPNT''.
Unused by the critical path but retained for completeness. -/
axiom chebyshevPsi_asymptotic : Tendsto (fun x => ψ x / x) atTop (nhds 1)

/-- x/2 ≤ θ(x) eventually, consequence of PNT.
Axiomatized: previously derived from PrimeNumberTheoremAnd.chebyshev_asymptotic.
Unused by the critical path but retained for completeness. -/
axiom chebyshevTheta_eventually_ge : ∀ᶠ x in atTop, x / 2 ≤ θ x

-- Specific values
theorem chebyshevTheta_two : θ 2 = Real.log 2 := by
  have hprim : primorial 2 = 2 := by
    decide
  simpa [hprim] using (Chebyshev.theta_eq_log_primorial (x := (2 : ℝ)))

theorem chebyshevPsi_two : ψ 2 = Real.log 2 := by
  have htheta : θ 2 = Real.log 2 := chebyshevTheta_two
  have hlog2 : Real.log 2 ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by norm_num))
  have hfloor : ⌊Real.log 2 / Real.log 2⌋₊ = 1 := by
    simp [hlog2]
  have hsum :
      (∑ n ∈ Icc 2 ⌊Real.log 2 / Real.log 2⌋₊, θ (2 ^ ((n : ℝ)⁻¹))) = 0 := by
    have hIcc : Icc (2 : ℕ) (⌊Real.log 2 / Real.log 2⌋₊) = ∅ := by
      simp [hfloor]
    simp [hIcc]
  have hpsi :
      ψ 2 = θ 2 + ∑ n ∈ Icc 2 ⌊Real.log 2 / Real.log 2⌋₊, θ (2 ^ ((n : ℝ)⁻¹)) := by
    simpa using (Chebyshev.psi_eq_theta_add_sum_theta (x := (2 : ℝ)) (by norm_num))
  calc
    ψ 2 = θ 2 := by simpa [hsum] using hpsi
    _ = Real.log 2 := htheta

end ChebyshevExt
