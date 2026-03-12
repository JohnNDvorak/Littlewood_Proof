import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTPNT5StrongRefactor
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedRefactor
import Littlewood.Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors
import Littlewood.Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.StrongPNTGlobalRefactorBundle

open PiLiDirectOscillationBridge
open Aristotle.Standalone.ExplicitFormulaPsiSkeleton
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra
open Aristotle.Standalone.ExternalPort.StrongPNTPNT5StrongRefactor
open Aristotle.Standalone.ExternalPort.StrongPNTRHPiExactSeedRefactor
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadAutoInstances
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalPayloadConcreteLane
open Aristotle.Standalone.ExternalPort.StrongPNTGlobalRootConstructors

/-- Lean-4.27 refactor surface bundling the two external lanes used by the
active B5a/B7 closure path:
1. `PNT5_Strong`-style B5a contour witness package
2. RH-`pi` exact-seed witness package. -/
structure StrongPNTGlobalRefactorPayload : Type where
  pnt5 : PNT5StrongRefactorBundle
  rhpi : RHPiExactSeedRefactorBundle

/-- Convert a bundled refactor payload into the canonical global StrongPNT
payload class term. -/
def toGlobalPayload
    (hBundle : StrongPNTGlobalRefactorPayload) :
    StrongPNTGlobalPayload :=
  strongpnt_global_payload_of_pnt5_refactor_bundle
    hBundle.pnt5
    (toStrongPNTBundle hBundle.rhpi)

/-- Endpoint: recover the canonical B5a shifted-remainder bound and all three
RH-`pi` exact-seed obligations from one bundled refactor payload. -/
theorem b5a_and_rhpi_endpoints_of_refactored_global_bundle
    (hBundle : StrongPNTGlobalRefactorPayload) :
    (∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤
        C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2)) ∧
      TruncatedExplicitFormulaPiHyp ∧
      (letI : TruncatedExplicitFormulaPiHyp := hBundle.rhpi.truncatedPiFormula
       TargetTowerExactSeedAbovePerronThreshold ∧
       AntiTargetTowerExactSeedAbovePerronThreshold) := by
  exact
    b5a_and_rhpi_endpoints_of_pnt5_refactor_bundle
      hBundle.pnt5
      (toStrongPNTBundle hBundle.rhpi)

/-- Endpoint: recover all three constructor roots
(`ExplicitFormulaPsiHyp`, `ExplicitFormulaPsiGeneralHyp`,
`RHPiUnconditionalExactSeedRootPayload`) from one bundled refactor payload. -/
theorem root_constructor_bundle_of_refactored_global_bundle
    (hBundle : StrongPNTGlobalRefactorPayload) :
    ∃ _ : Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp,
      Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries.ExplicitFormulaPsiGeneralHyp ∧
      RHPiUnconditionalExactSeedRootPayload := by
  letI : StrongPNTGlobalPayload := toGlobalPayload hBundle
  exact root_constructor_bundle_of_strongpnt_global_payload

end Aristotle.Standalone.ExternalPort.StrongPNTGlobalRefactorBundle
