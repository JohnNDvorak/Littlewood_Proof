import Littlewood.Basic.ChebyshevFunctions
import Littlewood.Basic.LogarithmicIntegral
import Littlewood.CoreLemmas.GrowthDomination
import Littlewood.ZetaZeros.SupremumRealPart

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.RHFrequentWitnessConstruction

open Filter
open GrowthDomination

/-- RH-side witness construction for the positive `ψ-x` branch.

This is the exact cofinal witness shape consumed by
`RHCaseOscillation.rh_psi_oscillation_from_frequent`.

Input data:
1. Eventual truncated explicit-formula control at `√x * lll x` scale.
2. Cofinal Dirichlet-aligned main-term negativity with `2 * √x * lll x` margin. -/
theorem rh_psi_frequent_plus_from_explicit_formula_and_alignment
    (_hRH : ZetaZeros.RiemannHypothesis)
    (psiMain : ℝ → ℝ)
    (h_error : ∀ᶠ x in atTop,
      |(chebyshevPsi x - x) + psiMain x| ≤ Real.sqrt x * lll x)
    (h_main : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      psiMain x ≤ -(2 * (Real.sqrt x * lll x))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      chebyshevPsi x - x ≥ Real.sqrt x * lll x := by
  intro X
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp h_error
  obtain ⟨x, hxgt, hmainx⟩ := h_main (max X M)
  have hX : X < x := lt_of_le_of_lt (le_max_left X M) hxgt
  have hMle : M ≤ x := le_trans (le_max_right X M) (le_of_lt hxgt)
  have herr := hM x hMle
  have hlow : -(Real.sqrt x * lll x) ≤ (chebyshevPsi x - x) + psiMain x :=
    (abs_le.mp herr).1
  refine ⟨x, hX, ?_⟩
  nlinarith

/-- RH-side witness construction for the negative `ψ-x` branch.

Exact cofinal witness shape consumed by
`RHCaseOscillation.rh_psi_oscillation_from_frequent`. -/
theorem rh_psi_frequent_minus_from_explicit_formula_and_alignment
    (_hRH : ZetaZeros.RiemannHypothesis)
    (psiMain : ℝ → ℝ)
    (h_error : ∀ᶠ x in atTop,
      |(chebyshevPsi x - x) + psiMain x| ≤ Real.sqrt x * lll x)
    (h_main : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      2 * (Real.sqrt x * lll x) ≤ psiMain x) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      chebyshevPsi x - x ≤ -(Real.sqrt x * lll x) := by
  intro X
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp h_error
  obtain ⟨x, hxgt, hmainx⟩ := h_main (max X M)
  have hX : X < x := lt_of_le_of_lt (le_max_left X M) hxgt
  have hMle : M ≤ x := le_trans (le_max_right X M) (le_of_lt hxgt)
  have herr := hM x hMle
  have hupp : (chebyshevPsi x - x) + psiMain x ≤ Real.sqrt x * lll x :=
    (abs_le.mp herr).2
  refine ⟨x, hX, ?_⟩
  nlinarith

/-- RH-side witness construction for the positive `π-li` branch.

Exact cofinal witness shape consumed by
`RHCaseOscillation.rh_pi_li_oscillation_from_frequent`. -/
theorem rh_pi_li_frequent_plus_from_explicit_formula_and_alignment
    (_hRH : ZetaZeros.RiemannHypothesis)
    (piMain : ℝ → ℝ)
    (h_error : ∀ᶠ x in atTop,
      |((Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x) + piMain x|
        ≤ Real.sqrt x / Real.log x * lll x)
    (h_main : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      piMain x ≤ -(2 * (Real.sqrt x / Real.log x * lll x))) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      (Nat.primeCounting (Nat.floor x) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x ≥
        Real.sqrt x / Real.log x * lll x := by
  intro X
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp h_error
  obtain ⟨x, hxgt, hmainx⟩ := h_main (max X M)
  have hX : X < x := lt_of_le_of_lt (le_max_left X M) hxgt
  have hMle : M ≤ x := le_trans (le_max_right X M) (le_of_lt hxgt)
  have herr := hM x hMle
  have hlow : -(Real.sqrt x / Real.log x * lll x) ≤
      ((Nat.primeCounting (Nat.floor x) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x) + piMain x :=
    (abs_le.mp herr).1
  refine ⟨x, hX, ?_⟩
  nlinarith

/-- RH-side witness construction for the negative `π-li` branch.

Exact cofinal witness shape consumed by
`RHCaseOscillation.rh_pi_li_oscillation_from_frequent`. -/
theorem rh_pi_li_frequent_minus_from_explicit_formula_and_alignment
    (_hRH : ZetaZeros.RiemannHypothesis)
    (piMain : ℝ → ℝ)
    (h_error : ∀ᶠ x in atTop,
      |((Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x) + piMain x|
        ≤ Real.sqrt x / Real.log x * lll x)
    (h_main : ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      2 * (Real.sqrt x / Real.log x * lll x) ≤ piMain x) :
    ∀ X : ℝ, ∃ x : ℝ, X < x ∧
      (Nat.primeCounting (Nat.floor x) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x ≤
        -(Real.sqrt x / Real.log x * lll x) := by
  intro X
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp h_error
  obtain ⟨x, hxgt, hmainx⟩ := h_main (max X M)
  have hX : X < x := lt_of_le_of_lt (le_max_left X M) hxgt
  have hMle : M ≤ x := le_trans (le_max_right X M) (le_of_lt hxgt)
  have herr := hM x hMle
  have hupp :
      ((Nat.primeCounting (Nat.floor x) : ℝ) -
        LogarithmicIntegral.logarithmicIntegral x) + piMain x
        ≤ Real.sqrt x / Real.log x * lll x :=
    (abs_le.mp herr).2
  refine ⟨x, hX, ?_⟩
  nlinarith

end Aristotle.RHFrequentWitnessConstruction
