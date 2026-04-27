/-
Landau-Mellin contradiction: the final wiring for the Landau oscillation argument.

This file now re-exports the Landau contradiction consequences from
`SmoothedExplicitFormula` with the same signatures.

## Proof Structure

Given: h_inf (∞ critical zeros), σ = ±1, h_side (one-sided o₊(√x) bound)

Step 1: Transfer h_side to smoothed domain → σ·g(u) ≤ 0 eventually
Step 2: Cesàro explicit formula → g Cesàro ≈ finite trig sum
Step 3: From one-sided + mean → 0: L² mean → 0  (one_sided_zero_l2_mean)
Step 4: But Parseval: L² mean → ∑|cₖ|² > 0  (parseval_finite_trig_sum)
Step 5: Contradiction: 0 = ∑|cₖ|² > 0

## Status

Sorry-free forwarding layer over `SmoothedExplicitFormula`.

REFERENCES:
  - Landau, "Über einen Satz von Tschebyschef" (1905)
  - Montgomery-Vaughan, "Multiplicative Number Theory I", §15.1
-/

import Littlewood.Aristotle.SmoothedExplicitFormula

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace Aristotle.LandauMellinContradiction

open Filter Topology
open ZetaZeros
open Aristotle.SmoothedExplicitFormula

variable [Aristotle.Standalone.PsiZeroSumOscillationFromIngham.CriticalZeroSumDivergesHyp]
variable [Aristotle.DirichletPhaseAlignment.PhaseAlignmentToTargetHyp]
variable [Aristotle.Standalone.AtkinsonFormula.AtkinsonShiftedInversePhaseCellPrefixBoundHyp]
variable [Aristotle.Standalone.SiegelSaddleExpansionHyp.SiegelSaddleExpansionHyp]
variable [Aristotle.Standalone.GabckePhaseCouplingHyp.GabckePhaseCouplingHyp]
variable [Littlewood.Development.ShiftedRemainderInterface.ShiftedRemainderSegmentBoundLargeTHyp]
variable [Littlewood.Development.HadamardProductZeta.SmallTPerronBoundHyp]
variable [PiLiDirectOscillationBridge.TruncatedExplicitFormulaPiHyp]
variable [Aristotle.Standalone.PerronExplicitFormulaProvider.PerronPiApproxCompatibilityHyp]
variable [Aristotle.Standalone.PerronExplicitFormulaProvider.InhomogeneousPhaseFitAbovePerronThresholdHyp]
variable [Aristotle.Standalone.RHPiCorrectedCanonicalWitnessClasses.TargetTowerPhaseCouplingFamilyHyp_corrected]
variable [Aristotle.Standalone.RHPiCorrectedCanonicalWitnessClasses.AntiTargetTowerPhaseCouplingFamilyHyp_corrected]

/-- **Landau ψ-contradiction proof**: one-sided o₊(√x) bound on σ·(ψ-x)
plus infinitely many critical-line zeros of ζ → False.

This is the core of Landau's oscillation method (1905), modernized via
the Cesàro-averaged explicit formula approach.

PROOF OUTLINE:
1. h_side ⟹ σ·smoothedPsiError(u) ≤ 0 for u ≥ u₀ (smoothed_psi_eventually_nonpos)
2. cesaro_psi_approx_trig_sum gives: Cesàro mean of g ≈ finite trig sum with
   n > 0 terms, distinct nonzero frequencies γₖ, and some cₖ ≠ 0
3. smoothedPsiError_bounded gives: |g(u)| ≤ B
4. The Cesàro mean of the trig sum → 0 (from cesaro_exp_norm_tendsto_zero)
5. Combined: (1/T)∫₀ᵀ g du → 0
6. By one_sided_zero_l2_mean: (1/T)∫₀ᵀ g² du → 0
7. But the trig sum's L² mean → ∑|cₖ|² by parseval_finite_trig_sum
8. Since some cₖ ≠ 0: ∑|cₖ|² > 0, but L² mean → 0. Contradiction. -/
theorem landau_psi_contradiction_proof
    (h_inf : Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 })
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (h_side : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop, σ * (chebyshevPsi x - x) < c * Real.sqrt x) :
    False :=
  Aristotle.SmoothedExplicitFormula.psi_signed_contradiction h_inf σ hσ h_side

/-- **Landau π-li contradiction proof**: one-sided o₊(√x/log x) bound on
σ·(π(x)-li(x)) plus infinitely many critical-line zeros of ζ → False.

Same proof structure as `landau_psi_contradiction_proof`. -/
theorem landau_pi_li_contradiction_proof
    (h_inf : Set.Infinite { ρ ∈ zetaNontrivialZeros | ρ.re = 1 / 2 })
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (h_side : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop, σ * DeepSorries.piLiError x <
        c * (Real.sqrt x / Real.log x)) :
    False := by
  have h_side' : ∀ c : ℝ, c > 0 →
      ∀ᶠ x in atTop, σ * Aristotle.SmoothedExplicitFormula.piLiError x <
        c * (Real.sqrt x / Real.log x) := by
    intro c hc
    simpa [Aristotle.SmoothedExplicitFormula.piLiError] using h_side c hc
  exact Aristotle.SmoothedExplicitFormula.pi_li_signed_contradiction h_inf σ hσ h_side'

end Aristotle.LandauMellinContradiction
