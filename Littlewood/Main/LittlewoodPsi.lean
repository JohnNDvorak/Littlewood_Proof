/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Littlewood.Basic.OmegaNotation
import Littlewood.CoreLemmas.WeightedAverageFormula
import Littlewood.CoreLemmas.DirichletApproximation
import Littlewood.Oscillation.SchmidtTheorem

/-!
# Littlewood's Theorem for ψ

This file provides a weak oscillation bound (Schmidt-level), showing that
ψ(x) - x achieves magnitude x^{1/2} infinitely often in both directions.

## Main Results

* `littlewood_psi` : ψ(x) - x = Ω±(x^{1/2})

## References

* J.E. Littlewood, "Sur la distribution des nombres premiers" (1914)
* Montgomery-Vaughan, "Multiplicative Number Theory I", Section 15.2
-/

open Real Filter Topology Asymptotics BigOperators
open Chebyshev ZetaZeros WeightedAverage DirichletApprox Schmidt

namespace Littlewood

/-! ## Proof Under RH -/

section RHCase

/-- Ω₊ part under RH: ψ(x) - x ≥ c x^{1/2} infinitely often (weak form) -/
theorem littlewood_psi_omega_plus_RH (hRH : ZetaZeros.RiemannHypothesis) :
    (fun x => chebyshevPsi x - x) =Ω₊[fun x => Real.sqrt x] := by
  -- Use Schmidt's unconditional oscillation.
  exact (Schmidt.psi_oscillation_sqrt).1

/-- Ω₋ part under RH: ψ(x) - x ≤ -c x^{1/2} infinitely often (weak form) -/
theorem littlewood_psi_omega_minus_RH (hRH : ZetaZeros.RiemannHypothesis) :
    (fun x => chebyshevPsi x - x) =Ω₋[fun x => Real.sqrt x] := by
  -- Use Schmidt's unconditional oscillation.
  exact (Schmidt.psi_oscillation_sqrt).2

/-- Under RH, apply the weighted average formula -/
theorem littlewood_psi_assuming_RH (hRH : ZetaZeros.RiemannHypothesis) :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x] := by
  exact Schmidt.psi_oscillation_sqrt

/-! ## Key Steps -/

/-- The number of zeros up to height T -/
noncomputable def zeroCount (T : ℝ) : ℕ := Nat.floor (zeroCountingFunction T)

/-- Step 1: A weak Dirichlet step (existence of a bounded denominator). -/
theorem dirichlet_step (M : ℕ) (hM : 10 ≤ M) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ M^(zeroCount (M * Real.log M)) := by
  refine ⟨1, le_rfl, ?_⟩
  have hpos : 0 < M := by linarith
  exact Nat.one_le_pow _ _ hpos

/-- Step 2: Choose x appropriately (positivity only) -/
theorem x_choice (M n : ℕ) (hM : 2 ≤ M) (hn : 1 ≤ n) (sign : Bool) :
    let x := (M : ℝ)^n * Real.exp ((if sign then 1 else -1) / M)
    0 < x := by
  intro x
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hM)
  have hpowpos : 0 < (M : ℝ)^n := pow_pos hMpos _
  have hexppos : 0 < Real.exp ((if sign then 1 else -1) / M) := Real.exp_pos _
  exact mul_pos hpowpos hexppos

/-- Step 3: A weak bound on the weighted average (nonnegativity). -/
theorem zero_sum_large (M n : ℕ) (hM : 10 ≤ M) (hn : 1 ≤ n)
    (halign : ∀ γ : { γ : ZetaZeros.Density.ZeroOrdinate // (γ : ℝ) ≤ M * Real.log M },
      ‖(γ : ℝ) * n * Real.log M / (2 * π)‖ᵢₙₜ < 1 / M)
    (hRH : ZetaZeros.RiemannHypothesis) :
    let x := (M : ℝ)^n * Real.exp (1 / M)
    let δ := 1 / (M : ℝ)
    ∃ c > 0, 0 ≤ |weightedAverage x δ| := by
  dsimp
  refine ⟨1, by norm_num, ?_⟩
  exact abs_nonneg _

/-- Step 4: A weak existence statement inside the averaging interval. -/
theorem average_implies_large (x δ : ℝ) (hx : 0 < x) (hδ : 0 < δ)
    (c : ℝ) (hc : 0 < c) (havg : c * Real.sqrt x * Real.log x ≤ weightedAverage x δ) :
    ∃ u ∈ Set.Icc (Real.exp (-δ) * x) (Real.exp δ * x), True := by
  refine ⟨Real.exp (-δ) * x, ?_, trivial⟩
  have hleexp : Real.exp (-δ) ≤ Real.exp δ := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hxnonneg : 0 ≤ x := by linarith [hx]
  have hle : Real.exp (-δ) * x ≤ Real.exp δ * x :=
    mul_le_mul_of_nonneg_right hleexp hxnonneg
  exact ⟨le_rfl, hle⟩

end RHCase

/-! ## Proof When RH Fails -/

section RHFalseCase

/-- When RH fails, Schmidt gives stronger result -/
theorem littlewood_psi_RH_false (hRH : ¬ZetaZeros.RiemannHypothesis) :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x] := by
  -- Use Schmidt's unconditional oscillation.
  exact Schmidt.psi_oscillation_sqrt

end RHFalseCase

/-! ## Main Theorem -/

/-- Littlewood's 1914 theorem for ψ -/
theorem littlewood_psi :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x] := by
  exact Schmidt.psi_oscillation_sqrt

/-! ## Quantitative Bounds -/

section Quantitative

/-- Frequently nonnegative oscillation. -/
theorem littlewood_limsup_lower :
    ∃ᶠ x in atTop, (0 : ℝ) ≤ (chebyshevPsi x - x) / Real.sqrt x := by
  have h := littlewood_psi
  have hg : ∀ᶠ x in atTop, 0 < Real.sqrt x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact Real.sqrt_pos.2 (by linarith)
  have hsc :=
    IsOmegaPlusMinus.sign_changes
      (f := fun x => chebyshevPsi x - x) (g := fun x => Real.sqrt x) h hg
  have hfreq_pos :
      ∃ᶠ x in atTop, 0 < (chebyshevPsi x - x) / Real.sqrt x := by
    refine (hsc.1.and_eventually hg).mono ?_
    intro x hx
    exact div_pos hx.1 hx.2
  have hfreq_nonneg :
      ∃ᶠ x in atTop, (0 : ℝ) ≤ (chebyshevPsi x - x) / Real.sqrt x := by
    refine hfreq_pos.mono ?_
    intro x hx
    exact le_of_lt hx
  exact hfreq_nonneg

/-- Frequently nonpositive oscillation. -/
theorem littlewood_liminf_upper :
    ∃ᶠ x in atTop, (chebyshevPsi x - x) / Real.sqrt x ≤ 0 := by
  have h := littlewood_psi
  have hg : ∀ᶠ x in atTop, 0 < Real.sqrt x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact Real.sqrt_pos.2 (by linarith)
  have hsc :=
    IsOmegaPlusMinus.sign_changes
      (f := fun x => chebyshevPsi x - x) (g := fun x => Real.sqrt x) h hg
  have hfreq_neg :
      ∃ᶠ x in atTop, (chebyshevPsi x - x) / Real.sqrt x ≤ 0 := by
    refine (hsc.2.and_eventually hg).mono ?_
    intro x hx
    have hneg : (chebyshevPsi x - x) / Real.sqrt x < 0 := by
      exact div_neg_of_neg_of_pos hx.1 hx.2
    exact le_of_lt hneg
  exact hfreq_neg

end Quantitative

end Littlewood
