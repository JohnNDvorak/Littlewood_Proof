import Littlewood.Aristotle.Standalone.RHPiPhaseCouplingConstructiveFamilies
import Littlewood.Aristotle.Standalone.RHPiCorrectedCanonicalWitnessClasses
import Littlewood.Aristotle.Standalone.RHPiTargetPhaseArgReduction
import Littlewood.Aristotle.Standalone.RHPiCorrectedToLegacyPhaseCouplingBridge

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiFinalPayloadInstancesUnconditional

open Filter Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.CombinedAtomsFromDeepBlockers
open Aristotle.Standalone.RHPiCorrectedCanonicalWitnessClasses
open Aristotle.Standalone.RHPiTargetPhaseArgReduction
open Aristotle.Standalone.RHPiPhaseCouplingConstructiveFamilies
open Aristotle.Standalone.RHPiCorrectedToLegacyPhaseCouplingBridge

/-- Build corrected canonical payload instances directly from explicit positive
and negative argument-approximation witness families. -/
theorem corrected_payload_instances_of_arg_families
    (hTargetArg : TargetTowerArgApproxFamily)
    (hAntiTargetArg : AntiTargetTowerArgApproxFamily) :
    TargetTowerPhaseCouplingFamilyHyp_corrected ∧
      AntiTargetTowerPhaseCouplingFamilyHyp_corrected := by
  refine ⟨?_, ?_⟩
  · exact targetPhaseCouplingFamilyHyp_corrected_of_argApprox hTargetArg
  · exact antiTargetPhaseCouplingFamilyHyp_corrected_of_argApprox hAntiTargetArg

/-- Full RH-`pi` witness payload from explicit target/anti-target
argument-approximation families. -/
theorem rhPiWitnessData_of_arg_families
    (hTargetArg : TargetTowerArgApproxFamily)
    (hAntiTargetArg : AntiTargetTowerArgApproxFamily) :
    RhPiWitnessData := by
  letI : TargetTowerPhaseCouplingFamilyHyp_corrected :=
    targetPhaseCouplingFamilyHyp_corrected_of_argApprox hTargetArg
  letI : AntiTargetTowerPhaseCouplingFamilyHyp_corrected :=
    antiTargetPhaseCouplingFamilyHyp_corrected_of_argApprox hAntiTargetArg
  exact rhPiWitnessData_of_correctedPhaseCouplingHyp

/-- 7a/7c pair from explicit target/anti-target argument-approximation
families, via corrected canonical payload classes. -/
theorem rh_pi_7a_7c_pair_of_arg_families
    (hTargetArg : TargetTowerArgApproxFamily)
    (hAntiTargetArg : AntiTargetTowerArgApproxFamily)
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
  letI : TargetTowerPhaseCouplingFamilyHyp_corrected :=
    targetPhaseCouplingFamilyHyp_corrected_of_argApprox hTargetArg
  letI : AntiTargetTowerPhaseCouplingFamilyHyp_corrected :=
    antiTargetPhaseCouplingFamilyHyp_corrected_of_argApprox hAntiTargetArg
  exact rh_pi_7a_7c_pair_of_correctedHyp hRH

end Aristotle.Standalone.RHPiFinalPayloadInstancesUnconditional
