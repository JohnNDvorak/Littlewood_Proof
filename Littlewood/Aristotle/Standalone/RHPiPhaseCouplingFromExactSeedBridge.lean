import Littlewood.Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
import Littlewood.Aristotle.Standalone.RHPi7a7cFromPerronPhase
import Littlewood.Aristotle.Standalone.RHPiPhaseCouplingConstructiveFamilies

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge

open Filter Complex ZetaZeros
open GrowthDomination
open PiLiDirectOscillationBridge
open Aristotle.Standalone.CombinedAtomsFromDeepBlockers
open Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPi7a7cFromPerronPhase
open Aristotle.Standalone.RHPiPhaseCouplingConstructiveFamilies

/-!
Direct bridge from exact-seed-above-threshold payload classes to the final
phase-coupling payload classes used by the RH-`pi` chain.

All heavy mathematics still lives in the exact-seed constructors; this file
provides deterministic class-level wiring and import-friendly endpoints.
-/

/-- Positive phase-coupling payload is available directly from the positive
exact-seed-above-threshold class with the legacy truncated-π input. -/
instance (priority := 100)
    [TruncatedExplicitFormulaPiHyp]
    [TargetTowerExactSeedAbovePerronThresholdHyp] :
    TargetTowerPhaseCouplingFamilyHyp := by
  infer_instance

/-- Negative phase-coupling payload is available directly from the negative
exact-seed-above-threshold class with the legacy truncated-π input. -/
instance (priority := 100)
    [TruncatedExplicitFormulaPiHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdHyp] :
    AntiTargetTowerPhaseCouplingFamilyHyp := by
  infer_instance

/-- Convenience endpoint: exact-seed-above-threshold classes imply full RH-`pi`
witness data through the phase-coupling endpoint. -/
theorem rhPiWitnessData_of_exactSeedAboveThreshold_hyp
    [TruncatedExplicitFormulaPiHyp]
    [TargetTowerExactSeedAbovePerronThresholdHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdHyp] :
    RhPiWitnessData := by
  exact rhPiWitnessData_of_phaseCouplingHyp

/-- Convenience endpoint: exact-seed-above-threshold classes imply the RH 7a/7c
pair through the phase-coupling endpoint. -/
theorem rh_pi_7a_7c_pair_of_exactSeedAboveThreshold_hyp
    [TruncatedExplicitFormulaPiHyp]
    [TargetTowerExactSeedAbovePerronThresholdHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdHyp]
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
  exact rh_pi_7a_7c_pair_of_phaseCouplingHyp hRH

end Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge
