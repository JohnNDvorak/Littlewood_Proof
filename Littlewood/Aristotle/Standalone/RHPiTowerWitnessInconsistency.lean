import Littlewood.Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiTowerWitnessInconsistency

open ZetaZeros
open Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase

/--
Post-refactor consistency bridge:
the target-phase/tower payload already carries the Perron `sqrt/log` error term,
so the Perron payload follows by projection.
-/
theorem perron_of_target
    (hTarget : TargetTowerPhaseCouplingFamily) :
    PerronSqrtErrorThresholdFamily :=
  perron_family_of_target_tower_phase hTarget

/-- If target payload is available, `(Perron ∧ Target)` is immediately inhabited. -/
theorem perron_and_target_of_target
    (hTarget : TargetTowerPhaseCouplingFamily) :
    PerronSqrtErrorThresholdFamily ∧ TargetTowerPhaseCouplingFamily := by
  exact ⟨perron_of_target hTarget, hTarget⟩

/-- If target and anti-target payloads are both available, then
`(Perron ∧ AntiTarget)` is also inhabited (Perron projected from target). -/
theorem perron_and_antitarget_of_target_and_antitarget
    (hTarget : TargetTowerPhaseCouplingFamily)
    (hAntiTarget : AntiTargetTowerPhaseCouplingFamily) :
    PerronSqrtErrorThresholdFamily ∧ AntiTargetTowerPhaseCouplingFamily := by
  exact ⟨perron_of_target hTarget, hAntiTarget⟩

end Aristotle.Standalone.RHPiTowerWitnessInconsistency
