import Littlewood.Aristotle.Standalone.RHPiWitnessFromExplicitFormula
import Littlewood.Aristotle.Standalone.RHPiPhaseCouplingConstructiveFamilies
import Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedExistence

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiDeepCoeffControlWitnesses

open Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.RHPiWitnessFromExplicitFormula
open Aristotle.Standalone.RHPiPhaseCouplingConstructiveFamilies
open Aristotle.Standalone.RHPiUnconditionalExactSeedExistence

/-!
Deep constructive closure targets for Blocker 7 coefficient-control payloads.

These are the mathematically hard leaves behind B7a/B7b:
construct unconditional positive/negative RH `pi` coefficient-control witness
families in the exact shape consumed by `RHPiWitnessFromExplicitFormula`.
-/

/-- Unconditional positive B7 coeff-control payload. -/
theorem target_height_coeff_control_unconditional :
    RhPiTargetHeightCoeffControlHyp := by
  exact coeffControlClasses_unconditional.1

/-- Unconditional negative B7 coeff-control payload. -/
theorem antitarget_height_coeff_control_unconditional :
    RhPiAntiTargetHeightCoeffControlHyp := by
  exact coeffControlClasses_unconditional.2

/-- Typeclass endpoint for the unconditional positive coeff-control payload. -/
instance (priority := 100) : RhPiTargetHeightCoeffControlHyp :=
  target_height_coeff_control_unconditional

/-- Typeclass endpoint for the unconditional negative coeff-control payload. -/
instance (priority := 100) : RhPiAntiTargetHeightCoeffControlHyp :=
  antitarget_height_coeff_control_unconditional

end Aristotle.Standalone.RHPiDeepCoeffControlWitnesses
