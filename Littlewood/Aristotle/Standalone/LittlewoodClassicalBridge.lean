/-
Bridge from the classical Littlewood Key Lemma to the existing proof assembly.

Given the two Key Lemmas and the corrected PL strip bounds, produces
`RhPsiWitnessData` — the RH-branch ψ oscillation witness used by
`CombinedAtomsFromDeepBlockers.psi_omega_from_blockers`.

This makes the classical route a DROP-IN REPLACEMENT for the Ingham variant,
without needing `PhaseAlignmentToTargetHyp`.

The bridge works by converting the two classical contradictions
  ¬(∀ δ > 0, ψ(x)-x < δ·√x·lll x eventually)
and
  ¬(∀ δ > 0, -(ψ(x)-x) < δ·√x·lll x eventually)
into the Ω₊ and Ω₋ directions via standard order-of-growth reasoning.
-/

import Littlewood.Aristotle.Standalone.LittlewoodKeyLemma
import Littlewood.Aristotle.Standalone.CombinedAtomsFromDeepBlockers
import Littlewood.Aristotle.LittlewoodRHTrue

set_option maxHeartbeats 400000
set_option autoImplicit false

noncomputable section

open Real Filter Topology Asymptotics
open scoped Real BigOperators

namespace Littlewood.Classical.Bridge

open Littlewood.Classical
open Aristotle.Standalone.CombinedAtomsFromDeepBlockers

/-! ## From contradiction to Ω±

The corrected classical contradictions say:

* under RH, it is not the case that `ψ(x)-x < δ·√x·lll(x)` eventually for all `δ > 0`;
* under RH, it is not the case that `-(ψ(x)-x) < δ·√x·lll(x)` eventually for all `δ > 0`.

These imply the `Ω₊` and `Ω₋` directions because `lll(x) → ∞`. -/

/-- The classical key-lemma + PL package directly yields the full-strength RH
Littlewood conclusion `ψ(x) - x = Ω±(√x · lll x)`. This is the canonical RH
`ψ` output; weaker square-root witnesses should be derived from it as
compatibility corollaries. -/
theorem psiOscillationLLLRHHyp_of_classical
    [LittlewoodKeyLemmaHyp] [LittlewoodPLBridgeHyp]
    [LittlewoodKeyLemmaMinusHyp] [PhragmenLindelofAbelStripBoundHyp] :
    Aristotle.LittlewoodRHTrue.PsiOscillationLLLRHHyp := by
  refine ⟨?_⟩
  intro hRH
  have hRH' : ZetaZeros.RiemannHypothesis' := hRH
  constructor
  · have hcontra := littlewood_classical_contradiction hRH'
    push_neg at hcontra
    obtain ⟨δ, hδ_pos, hfreq⟩ := hcontra
    refine ⟨δ, hδ_pos, ?_⟩
    exact hfreq.mono (fun x hx => by
      simpa [ge_iff_le, GrowthDomination.lll, mul_assoc, mul_left_comm, mul_comm] using hx)
  · have hcontra := littlewood_classical_contradiction_minus hRH'
    push_neg at hcontra
    obtain ⟨δ, hδ_pos, hfreq⟩ := hcontra
    refine ⟨δ, hδ_pos, ?_⟩
    exact hfreq.mono (fun x hx => by
      have hx' : δ * (Real.sqrt x * GrowthDomination.lll x) ≤ -(chebyshevPsi x - x) := by
        simpa [GrowthDomination.lll, mul_assoc, mul_left_comm, mul_comm] using hx
      linarith)

/-- The classical route produces `RhPsiWitnessData` when both the Key Lemma
and PL Bridge are instantiated. This replaces the Ingham-style proof path
without needing `PhaseAlignmentToTargetHyp`. -/
theorem rhPsiWitnessData_of_classical
    [LittlewoodKeyLemmaHyp] [LittlewoodPLBridgeHyp]
    [LittlewoodKeyLemmaMinusHyp] [PhragmenLindelofAbelStripBoundHyp] :
    RhPsiWitnessData := by
  intro hRH
  -- Convert RiemannHypothesis to RiemannHypothesis' (same definition)
  have hRH' : ZetaZeros.RiemannHypothesis' := hRH
  -- Ω₊ direction: from classical contradiction
  constructor
  · -- littlewood_classical_contradiction gives ¬(∀ δ > 0, eventually f < δ·√x·lll x)
    -- Convert to Ω₊(√x) via: ∃ δ₀, frequently f ≥ δ₀·√x·lll x ≥ δ₀·√x
    have hcontra := littlewood_classical_contradiction hRH'
    push_neg at hcontra
    obtain ⟨δ, hδ_pos, hfreq⟩ := hcontra
    refine ⟨δ, hδ_pos, ?_⟩
    have hlll_large : ∀ᶠ x in atTop,
        1 ≤ Real.log (Real.log (Real.log x)) := by
      filter_upwards [Filter.eventually_ge_atTop (Real.exp (Real.exp (Real.exp 1)))] with x hx
      have h1 : Real.exp (Real.exp 1) ≤ Real.log x := by
        rw [← Real.log_exp (Real.exp (Real.exp 1))]
        exact Real.log_le_log (by positivity) hx
      have h2 : Real.exp 1 ≤ Real.log (Real.log x) := by
        rw [← Real.log_exp (Real.exp 1)]
        exact Real.log_le_log (by positivity) h1
      rw [← Real.log_exp 1]
      exact Real.log_le_log (by positivity) h2
    exact (hfreq.and_eventually hlll_large).mono (fun x ⟨hfx, hlll⟩ => by
      calc δ * Real.sqrt x ≤ δ * Real.sqrt x * Real.log (Real.log (Real.log x)) :=
            le_mul_of_one_le_right (by positivity) hlll
        _ ≤ chebyshevPsi x - x := hfx)
  · -- Ω₋ direction: symmetric (use contradiction_minus)
    have hcontra := littlewood_classical_contradiction_minus hRH'
    push_neg at hcontra
    obtain ⟨δ, hδ_pos, hfreq⟩ := hcontra
    refine ⟨δ, hδ_pos, ?_⟩
    have hlll_large : ∀ᶠ x in atTop,
        1 ≤ Real.log (Real.log (Real.log x)) := by
      filter_upwards [Filter.eventually_ge_atTop (Real.exp (Real.exp (Real.exp 1)))] with x hx
      have h1 : Real.exp (Real.exp 1) ≤ Real.log x := by
        rw [← Real.log_exp (Real.exp (Real.exp 1))]
        exact Real.log_le_log (by positivity) hx
      have h2 : Real.exp 1 ≤ Real.log (Real.log x) := by
        rw [← Real.log_exp (Real.exp 1)]
        exact Real.log_le_log (by positivity) h1
      rw [← Real.log_exp 1]
      exact Real.log_le_log (by positivity) h2
    exact (hfreq.and_eventually hlll_large).mono (fun x ⟨hfx, hlll⟩ => by
      -- hfx : δ * √x * lll x ≤ -(ψ x - x), i.e., ψ x - x ≤ -δ*√x*lll x
      -- hlll : 1 ≤ lll x
      -- Need: ψ x - x ≤ -(δ * √x)
      have h1 : chebyshevPsi x - x ≤ -(δ * Real.sqrt x * Real.log (Real.log (Real.log x))) := by
        linarith
      have h2 : -(δ * Real.sqrt x * Real.log (Real.log (Real.log x))) ≤ -(δ * Real.sqrt x) := by
        exact neg_le_neg (le_mul_of_one_le_right (by positivity) hlll)
      linarith)

end Littlewood.Classical.Bridge
