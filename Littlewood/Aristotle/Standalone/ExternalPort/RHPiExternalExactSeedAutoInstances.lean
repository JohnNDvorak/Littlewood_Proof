import Littlewood.Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedAutoInstances

open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedPayload
open Aristotle.Standalone.RHPiUnconditionalExactSeedRootEndpoint

/-- Auto-wire the truncated explicit-formula RH-`pi` class from the external
exact-seed payload class. -/
instance (priority := 100)
    [ExternalExactSeedPayload] :
    TruncatedExplicitFormulaPiHyp :=
  truncatedExplicitFormulaPi_unconditional_from_rootPayload

/-- Auto-wire the target exact-seed class from the external exact-seed payload
class. -/
instance (priority := 100)
    [ExternalExactSeedPayload] :
    TargetTowerExactSeedAbovePerronThreshold :=
  targetTowerExactSeedAbovePerronThreshold_unconditional_from_rootPayload

/-- Auto-wire the anti-target exact-seed class from the external exact-seed
payload class. -/
instance (priority := 100)
    [ExternalExactSeedPayload] :
    AntiTargetTowerExactSeedAbovePerronThreshold :=
  antiTargetTowerExactSeedAbovePerronThreshold_unconditional_from_rootPayload

/-- Endpoint triple through auto-wired external exact-seed payload classes. -/
theorem exactSeedUnconditionalTriple_of_externalPayload_auto
    [ExternalExactSeedPayload] :
    TruncatedExplicitFormulaPiHyp ∧
      TargetTowerExactSeedAbovePerronThreshold ∧
      AntiTargetTowerExactSeedAbovePerronThreshold := by
  refine ⟨truncatedExplicitFormulaPi_unconditional_from_rootPayload, ?_, ?_⟩
  · exact targetTowerExactSeedAbovePerronThreshold_unconditional_from_rootPayload
  · exact antiTargetTowerExactSeedAbovePerronThreshold_unconditional_from_rootPayload

end Aristotle.Standalone.ExternalPort.RHPiExternalExactSeedAutoInstances
