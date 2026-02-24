import Littlewood.Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
import Littlewood.Aristotle.Standalone.RHPiInhomogeneousApproxObstruction

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiExactSeedObstructionBridge

open Complex ZetaZeros
open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiArgApproxFromPerronThreshold
open Aristotle.Standalone.RHPiTargetPhaseArgReduction
open Aristotle.Standalone.RHPiInhomogeneousApproxObstruction

/-!
Bridge the exact-seed-above-threshold payloads to the inhomogeneous obstruction
criteria already available for the arg-approximation layer.

This file is intentionally standalone and sorry-free.
-/

/-- Positive exact-seed payload implies the positive arg-approximation family. -/
theorem targetArgApproxFamily_of_exactSeed
    [TruncatedExplicitFormulaPiHyp]
    (hSeed : TargetTowerExactSeedAbovePerronThreshold) :
    TargetTowerArgApproxFamily :=
  targetTowerArgApproxFamily_of_above_threshold
    (target_argAboveThreshold_of_exactSeedFamily hSeed)

/-- Negative exact-seed payload implies the negative arg-approximation family. -/
theorem antiTargetArgApproxFamily_of_exactSeed
    [TruncatedExplicitFormulaPiHyp]
    (hSeed : AntiTargetTowerExactSeedAbovePerronThreshold) :
    AntiTargetTowerArgApproxFamily :=
  antiTargetTowerArgApproxFamily_of_above_threshold
    (antiTarget_argAboveThreshold_of_exactSeedFamily hSeed)

/-- Under a uniform relation-gap obstruction, the positive exact-seed payload
cannot exist. -/
theorem not_targetExactSeed_of_uniform_relation_gap
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (hObs :
      ∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            (∑ i, |(m i : ℝ)|)
              < ‖(∑ i, (m i : ℝ) * Complex.arg i.1) + (k : ℝ) * (2 * Real.pi)‖)) :
    ¬ TargetTowerExactSeedAbovePerronThreshold := by
  intro hSeed
  have hArg : TargetTowerArgApproxFamily :=
    targetArgApproxFamily_of_exactSeed hSeed
  exact (not_targetTowerArgApproxFamily_of_uniform_relation_gap hRH hObs) hArg

/-- Under a uniform relation-gap obstruction, the anti-target exact-seed
payload cannot exist. -/
theorem not_antiTargetExactSeed_of_uniform_relation_gap
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (hObs :
      ∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            (∑ i, |(m i : ℝ)|)
              <
                ‖(∑ i, (m i : ℝ) * (Complex.arg i.1 + Real.pi)) +
                    (k : ℝ) * (2 * Real.pi)‖)) :
    ¬ AntiTargetTowerExactSeedAbovePerronThreshold := by
  intro hSeed
  have hArg : AntiTargetTowerArgApproxFamily :=
    antiTargetArgApproxFamily_of_exactSeed hSeed
  exact (not_antiTargetTowerArgApproxFamily_of_uniform_relation_gap hRH hObs) hArg

/-- Typeclass form of `not_targetExactSeed_of_uniform_relation_gap`. -/
theorem not_targetExactSeedHyp_of_uniform_relation_gap
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (hObs :
      ∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            (∑ i, |(m i : ℝ)|)
              < ‖(∑ i, (m i : ℝ) * Complex.arg i.1) + (k : ℝ) * (2 * Real.pi)‖)) :
    ¬ TargetTowerExactSeedAbovePerronThresholdHyp := by
  intro hHyp
  exact not_targetExactSeed_of_uniform_relation_gap hRH hObs hHyp.witness

/-- Typeclass form of `not_antiTargetExactSeed_of_uniform_relation_gap`. -/
theorem not_antiTargetExactSeedHyp_of_uniform_relation_gap
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (hObs :
      ∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            (∑ i, |(m i : ℝ)|)
              <
                ‖(∑ i, (m i : ℝ) * (Complex.arg i.1 + Real.pi)) +
                    (k : ℝ) * (2 * Real.pi)‖)) :
    ¬ AntiTargetTowerExactSeedAbovePerronThresholdHyp := by
  intro hHyp
  exact not_antiTargetExactSeed_of_uniform_relation_gap hRH hObs hHyp.witness

end Aristotle.Standalone.RHPiExactSeedObstructionBridge

