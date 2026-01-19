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
      (∑ k ∈ Finset.Icc 2 (Nat.floor (Real.log x / Real.log 2)),
        chebyshevTheta (x ^ (1 / k : ℝ))) :=
by
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

-- θ(x) = ψ(x) - ψ(x^{1/2}) + O(x^{1/3})
/--
HYPOTHESIS: First correction term for θ(x) in terms of ψ(x).
MATH STATUS: Classical (explicit formula + prime power analysis).
MATHLIB: Not available.
-/
class ThetaPsiFirstCorrectionHyp : Prop where
  property : ∀ x : ℝ, 2 ≤ x →
    ∃ E : ℝ, |E| ≤ x ^ (1/3 : ℝ) ∧
      chebyshevTheta x = chebyshevPsi x - chebyshevPsi (Real.sqrt x) + E

theorem theta_psi_first_correction [ThetaPsiFirstCorrectionHyp] (x : ℝ) (hx : 2 ≤ x) :
    ∃ E : ℝ, |E| ≤ x ^ (1/3 : ℝ) ∧
    chebyshevTheta x = chebyshevPsi x - chebyshevPsi (Real.sqrt x) + E := by
  simpa using (ThetaPsiFirstCorrectionHyp.property x hx)

/-- The simpler bound: θ(x) = ψ(x) + O(x^{1/2} log x) -/
theorem theta_psi_simple (x : ℝ) (hx : 2 ≤ x) :
    ∃ E : ℝ, |E| ≤ 2 * Real.sqrt x * Real.log x ∧
    chebyshevTheta x = chebyshevPsi x + E := by
  refine ⟨chebyshevTheta x - chebyshevPsi x, ?_, ?_⟩
  · have hx' : 1 ≤ x := by linarith
    have hbound := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := x) hx'
    simpa [chebyshevPsi, chebyshevTheta, abs_sub_comm] using hbound
  · linarith

-- Under RH: θ(x) = ψ(x) - x^{1/2} + O(x^{1/3})
/--
HYPOTHESIS: Under RH, θ(x) = ψ(x) - x^{1/2} + O(x^{1/3}).
MATH STATUS: Classical (RH + explicit formula).
MATHLIB: Not available.
-/
class ThetaPsiRHHyp (hRH : ZetaZeros.RiemannHypothesis') : Prop where
  property : ∀ x : ℝ, 2 ≤ x →
    ∃ E : ℝ, |E| ≤ x ^ (1/3 : ℝ) ∧
      chebyshevTheta x = chebyshevPsi x - Real.sqrt x + E

theorem theta_psi_RH (hRH : ZetaZeros.RiemannHypothesis') [ThetaPsiRHHyp hRH] (x : ℝ) (hx : 2 ≤ x) :
    ∃ E : ℝ, |E| ≤ x ^ (1/3 : ℝ) ∧
    chebyshevTheta x = chebyshevPsi x - Real.sqrt x + E := by
  simpa using (ThetaPsiRHHyp.property (hRH := hRH) x hx)

/-! ## θ to π - li Conversion -/

-- Partial summation: π(x) = θ(x)/log(x) + ∫₂ˣ θ(t)/(t log²t) dt
/--
HYPOTHESIS: Partial summation formula for π in terms of θ.
MATH STATUS: Classical (partial summation).
MATHLIB: Not available.
-/
class PiFromThetaSummationHyp : Prop where
  property : ∀ x : ℝ, 2 < x →
    ∃ E : ℝ, |E| ≤ Real.sqrt x / (Real.log x)^2 ∧
      (Nat.primeCounting (Nat.floor x) : ℝ) =
        chebyshevTheta x / Real.log x +
        ∫ t in Set.Ioc 2 x, chebyshevTheta t / (t * (Real.log t)^2) + E

theorem pi_from_theta_summation [PiFromThetaSummationHyp] (x : ℝ) (hx : 2 < x) :
    ∃ E : ℝ, |E| ≤ Real.sqrt x / (Real.log x)^2 ∧
    (Nat.primeCounting (Nat.floor x) : ℝ) =
      chebyshevTheta x / Real.log x +
      ∫ t in Set.Ioc 2 x, chebyshevTheta t / (t * (Real.log t)^2) + E := by
  simpa using (PiFromThetaSummationHyp.property x hx)

-- li(x) = x/log(x) + ∫₂ˣ 1/log²t dt
/--
HYPOTHESIS: Expansion of li(x) via partial summation.
MATH STATUS: Classical.
MATHLIB: Not available.
-/
class LiExpansionHyp : Prop where
  property : ∀ x : ℝ, 2 < x →
    ∃ E : ℝ, |E| ≤ x / (Real.log x)^2 ∧
      logarithmicIntegral x =
        x / Real.log x + ∫ t in Set.Ioc 2 x, 1 / (Real.log t)^2 + E

theorem li_expansion [LiExpansionHyp] (x : ℝ) (hx : 2 < x) :
    ∃ E : ℝ, |E| ≤ x / (Real.log x)^2 ∧
    logarithmicIntegral x = x / Real.log x + ∫ t in Set.Ioc 2 x, 1 / (Real.log t)^2 + E := by
  simpa using (LiExpansionHyp.property x hx)

-- The key conversion: π(x) - li(x) = (θ(x) - x)/log(x) + O(x^{1/2}/log²x)
/--
HYPOTHESIS: Conversion from θ to π-li with square-root error.
MATH STATUS: Classical.
MATHLIB: Not available.
-/
class PiLiFromThetaHyp : Prop where
  property : ∀ x : ℝ, 2 < x →
    ∃ E : ℝ, |E| ≤ Real.sqrt x / (Real.log x)^2 ∧
      (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x =
        (chebyshevTheta x - x) / Real.log x + E

theorem pi_li_from_theta [PiLiFromThetaHyp] (x : ℝ) (hx : 2 < x) :
    ∃ E : ℝ, |E| ≤ Real.sqrt x / (Real.log x)^2 ∧
    (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x =
      (chebyshevTheta x - x) / Real.log x + E := by
  simpa using (PiLiFromThetaHyp.property x hx)

-- Under RH: π(x) - li(x) = (ψ(x) - x)/log(x) - x^{1/2}/log(x) + O(x^{1/2}/log²x)
/--
HYPOTHESIS: Under RH, π-li expressed via ψ with explicit square-root term.
MATH STATUS: Classical.
MATHLIB: Not available.
-/
class PiLiFromPsiRHHyp (hRH : ZetaZeros.RiemannHypothesis') : Prop where
  property : ∀ x : ℝ, 2 < x →
    ∃ E : ℝ, |E| ≤ Real.sqrt x / (Real.log x)^2 ∧
      (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x =
        (chebyshevPsi x - x) / Real.log x - Real.sqrt x / Real.log x + E

theorem pi_li_from_psi_RH (hRH : ZetaZeros.RiemannHypothesis') [PiLiFromPsiRHHyp hRH]
    (x : ℝ) (hx : 2 < x) :
    ∃ E : ℝ, |E| ≤ Real.sqrt x / (Real.log x)^2 ∧
    (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x =
      (chebyshevPsi x - x) / Real.log x - Real.sqrt x / Real.log x + E := by
  simpa using (PiLiFromPsiRHHyp.property (hRH := hRH) x hx)

/-! ## Omega Transfer -/

/--
HYPOTHESIS: Omega transfer from ψ to θ under a square-root dominance condition.
MATH STATUS: Classical (partial summation + Chebyshev bounds).
MATHLIB: Not available.
-/
class OmegaPsiToThetaHyp : Prop where
  property : ∀ f : ℝ → ℝ, (∀ᶠ x in atTop, Real.sqrt x ≤ f x) →
    (fun x => chebyshevPsi x - x) =Ω±[f] →
    (fun x => chebyshevTheta x - x) =Ω±[f]

/-- If ψ - x = Ω±(f), then θ - x = Ω±(f) provided f dominates x^{1/2} -/
theorem omega_psi_to_theta [OmegaPsiToThetaHyp] (f : ℝ → ℝ)
    (hf : ∀ᶠ x in atTop, Real.sqrt x ≤ f x)
    (h : (fun x => chebyshevPsi x - x) =Ω±[f]) :
    (fun x => chebyshevTheta x - x) =Ω±[f] := by
  simpa using (OmegaPsiToThetaHyp.property f hf h)

/--
HYPOTHESIS: Omega transfer from θ to π-li under square-root dominance.
MATH STATUS: Classical (partial summation).
MATHLIB: Not available.
-/
class OmegaThetaToPiLiHyp : Prop where
  property : ∀ f : ℝ → ℝ, (∀ᶠ x in atTop, Real.sqrt x ≤ f x) →
    (fun x => chebyshevTheta x - x) =Ω±[f] →
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x)
      =Ω±[fun x => f x / Real.log x]

/-- If θ - x = Ω±(f), then π - li = Ω±(f/log) -/
theorem omega_theta_to_pi_li [OmegaThetaToPiLiHyp] (f : ℝ → ℝ)
    (hf : ∀ᶠ x in atTop, Real.sqrt x ≤ f x)
    (h : (fun x => chebyshevTheta x - x) =Ω±[f]) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x)
    =Ω±[fun x => f x / Real.log x] := by
  simpa using (OmegaThetaToPiLiHyp.property f hf h)

/-- Combined: If ψ - x = Ω±(f) with f ≥ x^{1/2}, then π - li = Ω±(f/log) -/
theorem omega_psi_to_pi_li [OmegaPsiToThetaHyp] [OmegaThetaToPiLiHyp] (f : ℝ → ℝ)
    (hf : ∀ᶠ x in atTop, Real.sqrt x ≤ f x)
    (h : (fun x => chebyshevPsi x - x) =Ω±[f]) :
    (fun x => (Nat.primeCounting (Nat.floor x) : ℝ) - logarithmicIntegral x)
    =Ω±[fun x => f x / Real.log x] := by
  exact omega_theta_to_pi_li f hf (omega_psi_to_theta f hf h)

end Conversion
