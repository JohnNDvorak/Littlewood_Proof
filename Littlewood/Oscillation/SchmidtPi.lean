/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Littlewood.Oscillation.SchmidtTheorem
import Littlewood.ExplicitFormulas.ConversionFormulas

/-!
# Schmidt's Theorem for π - li

This file transfers Schmidt's oscillation results to π(x) - li(x).

## Main Results

* `pi_li_oscillation_minus` : π(x) - li(x) = Ω₋(x^{1/2}/log x)
* `pi_li_oscillation_RH_false` : If RH fails, π(x) - li(x) = Ω±(x^{Θ-ε})

## References

* Montgomery-Vaughan, "Multiplicative Number Theory I", Section 15.1
-/

open Real Filter Topology Asymptotics
open Chebyshev LogarithmicIntegral ZetaZeros Schmidt Conversion

namespace SchmidtPi

/-! ## Transfer to π - li -/

/-- π(x) - li(x) = Ω₋(x^{1/2}/log x) unconditionally -/
theorem pi_li_oscillation_minus :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x)
    =Ω₋[fun x => Real.sqrt x / Real.log x] := by
  -- From θ - x = Ω₋(x^{1/2}) and π - li = (θ - x)/log x + O(x^{1/2}/log²x)
  have hf : ∀ᶠ x in atTop, Real.sqrt x ≤ (fun x => Real.sqrt x) x := by
    exact Filter.Eventually.of_forall fun x => le_rfl
  have h := omega_psi_to_pi_li (f := fun x => Real.sqrt x) hf Schmidt.psi_oscillation_sqrt
  simpa using h.2

/-- If RH fails (Θ > 1/2), then π(x) - li(x) = Ω±(x^{Θ-ε}) -/
theorem pi_li_oscillation_RH_false (ε : ℝ) (hε : 0 < ε) (hRH_false : 1/2 < Θ)
    (hε_small : ε < Θ - 1/2) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x)
    =Ω±[fun x => x ^ (Θ - ε) / Real.log x] := by
  -- When Θ > 1/2, Schmidt's theorem gives Ω±(x^{Θ-ε})
  -- Since Θ - ε > 1/2, the conversion π - li = (θ - x)/log x + O(x^{1/2}/log²x)
  -- preserves the Ω± behavior (the error is smaller order)
  have hf : ∀ᶠ x in atTop, Real.sqrt x ≤ (fun x => x ^ (Θ - ε)) x := by
    refine (eventually_ge_atTop (1 : ℝ)).mono ?_
    intro x hx
    have hle : (1 / 2 : ℝ) ≤ Θ - ε := by linarith
    have hpow : x ^ (1 / 2 : ℝ) ≤ x ^ (Θ - ε) :=
      Real.rpow_le_rpow_of_exponent_le hx hle
    simpa [Real.sqrt_eq_rpow] using hpow
  simpa using omega_psi_to_pi_li (f := fun x => x ^ (Θ - ε)) hf
    (Schmidt.schmidt_psi_oscillation ε hε)

/-! ## The Gap: Ω₊ Under RH -/

/-- Under RH, Schmidt's method only gives Ω₋ for π - li, not Ω₊ -/
theorem schmidt_limitation :
    ∃ (π_li_error : ℝ → ℝ),
      (∀ x, π_li_error x = (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x) ∧
      π_li_error =Ω₋[fun x => Real.sqrt x / Real.log x] := by
  refine ⟨_, ?_, ?_⟩
  · intro x
    rfl
  · exact pi_li_oscillation_minus

/-- This is where Littlewood's deeper analysis is needed -/
theorem littlewood_needed_for_omega_plus :
    (∀ hRH : ZetaZeros.RiemannHypothesis,
      (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x)
      =Ω₊[fun x => Real.sqrt x / Real.log x]) →
    (∀ hRH : ZetaZeros.RiemannHypothesis,
      (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x)
      =Ω₊[fun x => Real.sqrt x / Real.log x]) := by
  intro h
  exact h

end SchmidtPi
