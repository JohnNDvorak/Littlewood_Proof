import Littlewood.Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
import Littlewood.Aristotle.Standalone.RHPiInhomogeneousApproxObstruction
import Littlewood.Aristotle.Standalone.RHPiDeepCoeffControlWitnesses

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
open Aristotle.Standalone.RHPiDeepCoeffControlWitnesses

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

/-- Under a uniform `π/2`-scaled relation-gap obstruction, the positive
exact-seed payload cannot exist (via the Blocker-7 coeff-control boundary). -/
theorem not_targetExactSeed_of_uniform_relation_gap_piOverTwo
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (hObs :
      ∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            ((Real.pi / 2) * (∑ i, |(m i : ℝ)|))
              < ‖(∑ i, (m i : ℝ) * Complex.arg i.1) + (k : ℝ) * (2 * Real.pi)‖)) :
    ¬ TargetTowerExactSeedAbovePerronThreshold := by
  intro hSeed
  have hCoeff :
      Aristotle.Standalone.RHPiWitnessFromExplicitFormula.RhPiTargetHeightCoeffControlHyp :=
    target_height_coeff_control_of_exactSeedAboveThreshold
      (hTruncated := (inferInstance : TruncatedExplicitFormulaPiHyp))
      (hTarget := hSeed)
  exact
    (not_RhPiTargetHeightCoeffControlHyp_of_uniform_relation_gap_piOverTwo hRH hObs)
      hCoeff

/-- Under a uniform `π/2`-scaled relation-gap obstruction, the anti-target
exact-seed payload cannot exist (via the Blocker-7 coeff-control boundary). -/
theorem not_antiTargetExactSeed_of_uniform_relation_gap_piOverTwo
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (hObs :
      ∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            ((Real.pi / 2) * (∑ i, |(m i : ℝ)|))
              <
                ‖(∑ i, (m i : ℝ) * (Complex.arg i.1 + Real.pi)) +
                    (k : ℝ) * (2 * Real.pi)‖)) :
    ¬ AntiTargetTowerExactSeedAbovePerronThreshold := by
  intro hSeed
  have hCoeff :
      Aristotle.Standalone.RHPiWitnessFromExplicitFormula.RhPiAntiTargetHeightCoeffControlHyp :=
    antitarget_height_coeff_control_of_exactSeedAboveThreshold
      (hTruncated := (inferInstance : TruncatedExplicitFormulaPiHyp))
      (hAntiTarget := hSeed)
  exact
    (not_RhPiAntiTargetHeightCoeffControlHyp_of_uniform_relation_gap_piOverTwo hRH hObs)
      hCoeff

/-- Typeclass form of `not_targetExactSeed_of_uniform_relation_gap_piOverTwo`. -/
theorem not_targetExactSeedHyp_of_uniform_relation_gap_piOverTwo
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (hObs :
      ∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            ((Real.pi / 2) * (∑ i, |(m i : ℝ)|))
              < ‖(∑ i, (m i : ℝ) * Complex.arg i.1) + (k : ℝ) * (2 * Real.pi)‖)) :
    ¬ TargetTowerExactSeedAbovePerronThresholdHyp := by
  intro hHyp
  exact not_targetExactSeed_of_uniform_relation_gap_piOverTwo hRH hObs hHyp.witness

/-- Typeclass form of `not_antiTargetExactSeed_of_uniform_relation_gap_piOverTwo`. -/
theorem not_antiTargetExactSeedHyp_of_uniform_relation_gap_piOverTwo
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (hObs :
      ∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            ((Real.pi / 2) * (∑ i, |(m i : ℝ)|))
              <
                ‖(∑ i, (m i : ℝ) * (Complex.arg i.1 + Real.pi)) +
                    (k : ℝ) * (2 * Real.pi)‖)) :
    ¬ AntiTargetTowerExactSeedAbovePerronThresholdHyp := by
  intro hHyp
  exact not_antiTargetExactSeed_of_uniform_relation_gap_piOverTwo hRH hObs hHyp.witness

/-- Forward form: any positive exact-seed payload excludes a uniform
`π/2`-scaled positive relation-gap obstruction. -/
theorem no_uniform_relation_gap_piOverTwo_of_targetExactSeed
    [TruncatedExplicitFormulaPiHyp]
    (hSeed : TargetTowerExactSeedAbovePerronThreshold)
    (hRH : ZetaZeros.RiemannHypothesis) :
    ¬ (∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            ((Real.pi / 2) * (∑ i, |(m i : ℝ)|))
              < ‖(∑ i, (m i : ℝ) * Complex.arg i.1) + (k : ℝ) * (2 * Real.pi)‖)) := by
  intro hObs
  exact (not_targetExactSeed_of_uniform_relation_gap_piOverTwo hRH hObs) hSeed

/-- Forward form: any anti-target exact-seed payload excludes a uniform
`π/2`-scaled anti-target relation-gap obstruction. -/
theorem no_uniform_relation_gap_piOverTwo_of_antiTargetExactSeed
    [TruncatedExplicitFormulaPiHyp]
    (hSeed : AntiTargetTowerExactSeedAbovePerronThreshold)
    (hRH : ZetaZeros.RiemannHypothesis) :
    ¬ (∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            ((Real.pi / 2) * (∑ i, |(m i : ℝ)|))
              <
                ‖(∑ i, (m i : ℝ) * (Complex.arg i.1 + Real.pi)) +
                    (k : ℝ) * (2 * Real.pi)‖)) := by
  intro hObs
  exact (not_antiTargetExactSeed_of_uniform_relation_gap_piOverTwo hRH hObs) hSeed

/-- Typeclass forward form for positive exact seeds. -/
theorem no_uniform_relation_gap_piOverTwo_of_targetExactSeedHyp
    [TruncatedExplicitFormulaPiHyp]
    [TargetTowerExactSeedAbovePerronThresholdHyp]
    (hRH : ZetaZeros.RiemannHypothesis) :
    ¬ (∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            ((Real.pi / 2) * (∑ i, |(m i : ℝ)|))
              < ‖(∑ i, (m i : ℝ) * Complex.arg i.1) + (k : ℝ) * (2 * Real.pi)‖)) := by
  exact
    no_uniform_relation_gap_piOverTwo_of_targetExactSeed
      (hSeed := TargetTowerExactSeedAbovePerronThresholdHyp.witness) hRH

/-- Typeclass forward form for anti-target exact seeds. -/
theorem no_uniform_relation_gap_piOverTwo_of_antiTargetExactSeedHyp
    [TruncatedExplicitFormulaPiHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdHyp]
    (hRH : ZetaZeros.RiemannHypothesis) :
    ¬ (∀ T : ℝ,
        ∃ m : {ρ // ρ ∈ ((finite_zeros_le T).toFinset)} → ℤ,
          (∑ i, (m i : ℝ) * i.1.im = 0) ∧
          (∀ k : ℤ,
            ((Real.pi / 2) * (∑ i, |(m i : ℝ)|))
              <
                ‖(∑ i, (m i : ℝ) * (Complex.arg i.1 + Real.pi)) +
                    (k : ℝ) * (2 * Real.pi)‖)) := by
  exact
    no_uniform_relation_gap_piOverTwo_of_antiTargetExactSeed
      (hSeed := AntiTargetTowerExactSeedAbovePerronThresholdHyp.witness) hRH

end Aristotle.Standalone.RHPiExactSeedObstructionBridge
