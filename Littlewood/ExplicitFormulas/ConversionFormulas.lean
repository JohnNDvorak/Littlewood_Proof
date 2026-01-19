/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Littlewood.Basic.OmegaNotation
import Littlewood.Basic.ChebyshevFunctions
import Littlewood.Basic.LogarithmicIntegral
import Littlewood.ZetaZeros.ZeroCountingFunction

/-!
# Conversion Formulas

This file proves the relationships between ψ, θ, π, and li, which are essential
for transferring oscillation results from ψ to π - li.

## Main Results

* `theta_psi_conversion` : θ(x) = ψ(x) - O(x^{1/2})
* `pi_li_theta_conversion` : π(x) - li(x) = (θ(x) - x)/log(x) + O(x^{1/2}/log²x)

## References

* Montgomery-Vaughan, "Multiplicative Number Theory I", Chapter 2
-/

open Real Filter Topology Asymptotics
open Chebyshev LogarithmicIntegral ZetaZeros

namespace Conversion

/-! ## ψ to θ Conversion -/

/-- θ(x) = ψ(x) - ψ(x^{1/2}) - ψ(x^{1/3}) - ... -/
theorem theta_from_psi (x : ℝ) (hx : 1 < x) :
    chebyshevTheta x = chebyshevPsi x -
      ∑ k ∈ Finset.Icc 2 (Nat.floor (Real.log x / Real.log 2)),
        chebyshevTheta (x ^ (1 / k : ℝ)) := by
  by_cases hx2 : 2 ≤ x
  · have h := Chebyshev.psi_eq_theta_add_sum_theta (x := x) hx2
    have h' :
        chebyshevTheta x +
          ∑ k ∈ Finset.Icc 2 (Nat.floor (Real.log x / Real.log 2)),
            chebyshevTheta (x ^ (1 / k : ℝ)) =
          chebyshevPsi x := by
      simpa [chebyshevTheta, chebyshevPsi] using h.symm
    exact (eq_sub_iff_add_eq).2 h'
  · have hxlt2 : x < 2 := lt_of_not_ge hx2
    have hpsi : chebyshevPsi x = 0 := by
      simpa [chebyshevPsi] using (Chebyshev.psi_eq_zero_of_lt_two (x := x) hxlt2)
    have htheta : chebyshevTheta x = 0 := by
      simpa [chebyshevTheta] using (Chebyshev.theta_eq_zero_of_lt_two (x := x) hxlt2)
    have hlog_le : Real.log x / Real.log 2 ≤ 1 := by
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hxpos : 0 < x := by linarith
      have hlog_le' : Real.log x ≤ Real.log 2 := by
        exact le_of_lt (Real.log_lt_log hxpos hxlt2)
      calc
        Real.log x / Real.log 2 ≤ Real.log 2 / Real.log 2 := by
          exact div_le_div_of_nonneg_right hlog_le' (le_of_lt hlog2pos)
        _ = 1 := by field_simp [hlog2pos.ne']
    have hfloor : Nat.floor (Real.log x / Real.log 2) ≤ 1 :=
      Nat.floor_le_one_of_le_one hlog_le
    have hIcc : Finset.Icc 2 (Nat.floor (Real.log x / Real.log 2)) = ∅ := by
      refine Finset.Icc_eq_empty_of_lt ?_
      exact lt_of_le_of_lt hfloor (by decide : (1 : ℕ) < 2)
    simp [htheta, hpsi, hIcc, one_div]

/-- θ(x) = ψ(x) - ψ(x^{1/2}) + O(x^{1/3}) -/
theorem theta_psi_first_correction (x : ℝ) (hx : 2 ≤ x) :
    ∃ E : ℝ, |E| ≤ x ^ (1/3 : ℝ) ∧
    chebyshevTheta x = chebyshevPsi x - chebyshevPsi (Real.sqrt x) + E := by
  sorry

/-- The simpler bound: θ(x) = ψ(x) + O(x^{1/2} log x) -/
theorem theta_psi_simple (x : ℝ) (hx : 2 ≤ x) :
    ∃ E : ℝ, |E| ≤ 2 * Real.sqrt x * Real.log x ∧
    chebyshevTheta x = chebyshevPsi x + E := by
  refine ⟨chebyshevTheta x - chebyshevPsi x, ?_, ?_⟩
  · have hx' : 1 ≤ x := by linarith
    have hbound := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := x) hx'
    simpa [chebyshevPsi, chebyshevTheta, abs_sub_comm] using hbound
  · linarith

/-- Under RH: θ(x) = ψ(x) - x^{1/2} + O(x^{1/3}) -/
theorem theta_psi_RH (hRH : ZetaZeros.RiemannHypothesis') (x : ℝ) (hx : 2 ≤ x) :
    ∃ E : ℝ, |E| ≤ x ^ (1/3 : ℝ) ∧
    chebyshevTheta x = chebyshevPsi x - Real.sqrt x + E := by
  sorry

/-! ## θ to π - li Conversion -/

/-- Partial summation: π(x) = θ(x)/log(x) + ∫₂ˣ θ(t)/(t log²t) dt -/
theorem pi_from_theta_summation (x : ℝ) (hx : 2 < x) :
    ∃ E : ℝ, |E| ≤ Real.sqrt x / (Real.log x)^2 ∧
    (Nat.primeCounting (Nat.floor x) : ℝ) =
      chebyshevTheta x / Real.log x +
      ∫ t in Set.Ioc 2 x, chebyshevTheta t / (t * (Real.log t)^2) + E := by
  sorry

/-- li(x) = x/log(x) + ∫₂ˣ 1/log²t dt -/
theorem li_expansion (x : ℝ) (hx : 2 < x) :
    ∃ E : ℝ, |E| ≤ x / (Real.log x)^2 ∧
    logarithmicIntegral x = x / Real.log x + ∫ t in Set.Ioc 2 x, 1 / (Real.log t)^2 + E := by
  sorry

/-- The key conversion: π(x) - li(x) = (θ(x) - x)/log(x) + O(x^{1/2}/log²x) -/
theorem pi_li_from_theta (x : ℝ) (hx : 2 < x) :
    ∃ E : ℝ, |E| ≤ Real.sqrt x / (Real.log x)^2 ∧
    (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x =
      (chebyshevTheta x - x) / Real.log x + E := by
  sorry

/-- Under RH: π(x) - li(x) = (ψ(x) - x)/log(x) - x^{1/2}/log(x) + O(x^{1/2}/log²x) -/
theorem pi_li_from_psi_RH (hRH : ZetaZeros.RiemannHypothesis') (x : ℝ) (hx : 2 < x) :
    ∃ E : ℝ, |E| ≤ Real.sqrt x / (Real.log x)^2 ∧
    (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x =
      (chebyshevPsi x - x) / Real.log x - Real.sqrt x / Real.log x + E := by
  sorry

/-! ## Omega Transfer -/

/-- If ψ - x = Ω±(f), then θ - x = Ω±(f) provided f dominates x^{1/2} -/
theorem omega_psi_to_theta (f : ℝ → ℝ) (hf : ∀ᶠ x in atTop, Real.sqrt x ≤ f x)
    (h : (fun x => chebyshevPsi x - x) =Ω±[f]) :
    (fun x => chebyshevTheta x - x) =Ω±[f] := by
  sorry

/-- If θ - x = Ω±(f), then π - li = Ω±(f/log) -/
theorem omega_theta_to_pi_li (f : ℝ → ℝ) (hf : ∀ᶠ x in atTop, Real.sqrt x ≤ f x)
    (h : (fun x => chebyshevTheta x - x) =Ω±[f]) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x)
    =Ω±[fun x => f x / Real.log x] := by
  sorry

/-- Combined: If ψ - x = Ω±(f) with f ≥ x^{1/2}, then π - li = Ω±(f/log) -/
theorem omega_psi_to_pi_li (f : ℝ → ℝ) (hf : ∀ᶠ x in atTop, Real.sqrt x ≤ f x)
    (h : (fun x => chebyshevPsi x - x) =Ω±[f]) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x)
    =Ω±[fun x => f x / Real.log x] := by
  exact omega_theta_to_pi_li f hf (omega_psi_to_theta f hf h)

end Conversion
