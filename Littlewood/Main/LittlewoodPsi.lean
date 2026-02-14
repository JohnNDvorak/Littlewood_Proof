/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Your Name]
-/
import Littlewood.Basic.OmegaNotation
import Littlewood.CoreLemmas.WeightedAverageFormula
import Littlewood.CoreLemmas.DirichletApproximation
import Littlewood.CoreLemmas.GrowthDomination
import Littlewood.Oscillation.SchmidtTheorem
import Littlewood.CriticalAssumptions
import Littlewood.Aristotle.DeepSorries

/-!
# Littlewood's Theorem for ψ

Full-strength Littlewood 1914: ψ(x) - x = Ω±(√x · log log log x).

The full-strength result is extracted from the consolidated deep mathematical
results in `Aristotle.DeepSorries.psi_full_strength_oscillation`, which bundles
Hardy's theorem, the Landau contradictions, and the full-strength oscillation
into a single atomic sorry.

## Main Results

* `littlewood_psi` : ψ(x) - x = Ω±(√x · log log log x)
* `littlewood_psi_sqrt` : ψ(x) - x = Ω±(√x)  (backward-compatible corollary)

## References

* J.E. Littlewood, "Sur la distribution des nombres premiers" (1914)
* Montgomery-Vaughan, "Multiplicative Number Theory I", Section 15.2
-/

open Real Filter Topology Asymptotics BigOperators
open Chebyshev ZetaZeros WeightedAverage DirichletApprox Schmidt GrowthDomination

namespace Littlewood

/-! ## Full-Strength Main Theorem -/

/-- **Littlewood's 1914 theorem for ψ** (full strength):
ψ(x) - x = Ω±(√x · log log log x).

Extracted from the consolidated deep mathematical results with no direct sorry. -/
theorem littlewood_psi :
    (fun x => chebyshevPsi x - x)
    =Ω±[fun x => Real.sqrt x * lll x] :=
  Aristotle.DeepSorries.psi_full_strength_oscillation

/-- Backward-compatible corollary: ψ(x) - x = Ω±(√x).
Follows from the full-strength result since √x ≤ √x · lll x eventually. -/
theorem littlewood_psi_sqrt :
    (fun x => chebyshevPsi x - x)
    =Ω±[fun x => Real.sqrt x] := by
  exact littlewood_psi.of_eventually_ge
    sqrt_eventually_le_sqrt_mul_lll
    (Eventually.mono (eventually_ge_atTop 0) (fun x hx => Real.sqrt_nonneg x))

/-! ## Quantitative Bounds -/

section Quantitative

/-- Frequently nonnegative oscillation. -/
theorem littlewood_limsup_lower :
    ∃ᶠ x in atTop, (0 : ℝ) ≤ (chebyshevPsi x - x) / Real.sqrt x := by
  have h := littlewood_psi_sqrt
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
  exact hfreq_pos.mono (fun x hx => le_of_lt hx)

/-- Frequently nonpositive oscillation. -/
theorem littlewood_liminf_upper :
    ∃ᶠ x in atTop, (chebyshevPsi x - x) / Real.sqrt x ≤ 0 := by
  have h := littlewood_psi_sqrt
  have hg : ∀ᶠ x in atTop, 0 < Real.sqrt x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact Real.sqrt_pos.2 (by linarith)
  have hsc :=
    IsOmegaPlusMinus.sign_changes
      (f := fun x => chebyshevPsi x - x) (g := fun x => Real.sqrt x) h hg
  refine (hsc.2.and_eventually hg).mono ?_
  intro x hx
  exact le_of_lt (div_neg_of_neg_of_pos hx.1 hx.2)

end Quantitative

/-! ## Legacy API -/

section RHCase

/-- Ω₊ part under RH: ψ(x) - x ≥ c x^{1/2} infinitely often (weak form) -/
theorem littlewood_psi_omega_plus_RH (_hRH : ZetaZeros.RiemannHypothesis) :
    (fun x => chebyshevPsi x - x) =Ω₊[fun x => Real.sqrt x] :=
  littlewood_psi_sqrt.1

/-- Ω₋ part under RH: ψ(x) - x ≤ -c x^{1/2} infinitely often (weak form) -/
theorem littlewood_psi_omega_minus_RH (_hRH : ZetaZeros.RiemannHypothesis) :
    (fun x => chebyshevPsi x - x) =Ω₋[fun x => Real.sqrt x] :=
  littlewood_psi_sqrt.2

/-- Under RH, apply the weighted average formula -/
theorem littlewood_psi_assuming_RH (_hRH : ZetaZeros.RiemannHypothesis) :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x] :=
  littlewood_psi_sqrt

end RHCase

section RHFalseCase

/-- When RH fails, Schmidt gives stronger result -/
theorem littlewood_psi_RH_false (_hRH : ¬ZetaZeros.RiemannHypothesis) :
    (fun x => chebyshevPsi x - x) =Ω±[fun x => Real.sqrt x] :=
  littlewood_psi_sqrt

end RHFalseCase

/-! ## Legacy helpers (kept for backward compatibility) -/

/-- The number of zeros up to height T -/
noncomputable def zeroCount (T : ℝ) : ℕ := Nat.floor (zeroCountingFunction T)

/-- Step 1: A weak Dirichlet step (existence of a bounded denominator). -/
theorem dirichlet_step (M : ℕ) (hM : 10 ≤ M) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ M^(zeroCount (M * Real.log M)) := by
  refine ⟨1, le_rfl, ?_⟩
  have hpos : 0 < M := by linarith
  exact Nat.one_le_pow _ _ hpos

end Littlewood
