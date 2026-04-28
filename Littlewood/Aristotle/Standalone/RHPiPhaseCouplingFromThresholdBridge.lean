import Littlewood.Aristotle.Standalone.RHPi7a7cFromPerronPhase
import Littlewood.Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiPhaseCouplingFromThresholdBridge

open Filter Complex ZetaZeros
open GrowthDomination
open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiPerronTowerWitness
open Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase
open Aristotle.Standalone.RHPiPerronFromTruncatedPiBridge
open Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold
open Aristotle.Standalone.RHPi7a7cFromPerronPhase

/-- Positive above-threshold payload implies the positive phase-coupling payload
used by the RH-π 7a/7c endpoint. -/
instance
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [TargetTowerPhaseAbovePerronThresholdHyp] :
    TargetTowerPhaseCouplingFamilyHyp where
  witness :=
    target_tower_sqrt_witness_of_phase_above_threshold
      TargetTowerPhaseAbovePerronThresholdHyp.witness

/-- Negative above-threshold payload implies the negative phase-coupling payload
used by the RH-π 7a/7c endpoint. -/
instance
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [AntiTargetTowerPhaseAbovePerronThresholdHyp] :
    AntiTargetTowerPhaseCouplingFamilyHyp where
  witness :=
    antitarget_tower_sqrt_witness_of_phase_above_threshold
      AntiTargetTowerPhaseAbovePerronThresholdHyp.witness

/-- 7a/7c endpoint from fixed-height Perron error + above-threshold phase/tower
payload classes. -/
theorem rh_pi_7a_7c_pair_from_threshold_hyp
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [TargetTowerPhaseAbovePerronThresholdHyp]
    [AntiTargetTowerPhaseAbovePerronThresholdHyp]
    (hRH : ZetaZeros.RiemannHypothesis) :
    (∃ piMain : ℝ → ℝ,
      (∀ᶠ x in atTop,
        |((Nat.primeCounting (Nat.floor x) : ℝ) -
            LogarithmicIntegral.logarithmicIntegral x) + piMain x|
          ≤ Real.sqrt x / Real.log x * lll x))
    ∧
    ((∀ X : ℝ, ∃ x : ℝ, X < x ∧
      ((Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x)
        ≤ -(3 * (Real.sqrt x / Real.log x * lll x)))
    ∧
    (∀ X : ℝ, ∃ x : ℝ, X < x ∧
      3 * (Real.sqrt x / Real.log x * lll x) ≤
        ((Nat.primeCounting (Nat.floor x) : ℝ) -
          LogarithmicIntegral.logarithmicIntegral x))) := by
  exact rh_pi_7a_7c_pair_from_perron_phase_hyp hRH

end Aristotle.Standalone.RHPiPhaseCouplingFromThresholdBridge
