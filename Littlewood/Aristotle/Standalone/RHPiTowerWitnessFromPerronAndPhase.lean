import Littlewood.Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase

open Complex ZetaZeros
open GrowthDomination
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge
open Aristotle.Standalone.RHPiPerronTowerWitness
open Aristotle.Standalone.RHPiPerronTruncatedWitness

/-- RH Perron/truncated explicit-formula error payload at baseline `sqrt/log`
scale. This is the direct finite-zero witness family:
`∀ X, ∃ x > X, ∃ T, error(x,T)`. -/
abbrev PerronSqrtErrorThresholdFamily : Prop :=
  PerronSqrtErrorFamily

/-- Positive RH branch payload:
for each RH branch, provide the full target-phase/tower witness family already
containing the Perron `sqrt/log` error bound. -/
abbrev TargetTowerPhaseCouplingFamily : Prop :=
  ∀ _hRH : ZetaZeros.RiemannHypothesis, TargetHeightTowerSqrtWitness

/-- Negative RH branch payload:
for each RH branch, provide the full anti-target-phase/tower witness family
already containing the Perron `sqrt/log` error bound. -/
abbrev AntiTargetTowerPhaseCouplingFamily : Prop :=
  ∀ _hRH : ZetaZeros.RiemannHypothesis, AntiTargetHeightTowerSqrtWitness

/-- Any target-phase/tower witness payload trivially induces the Perron
`sqrt/log` witness payload by forgetting phase/tower data. -/
theorem perron_family_of_target_tower_phase
    (hTargetPhase : TargetTowerPhaseCouplingFamily) :
    PerronSqrtErrorThresholdFamily := by
  intro hRH X
  rcases hTargetPhase hRH X with
    ⟨x, hXx, T, hT4, hx1, herr, ε, hεpos, hεlt, hphase, hxUpper⟩
  exact ⟨x, hXx, T, hT4, hx1, herr⟩

/-- Construct the positive `TargetHeightTowerSqrtWitness` payload by coupling:
1. Perron/truncated explicit-formula witness payload and
2. target-phase/tower witness payload.

The target payload already contains the required `sqrt/log` Perron bound. -/
theorem positive_target_tower_sqrt_witness_of_perron_and_phase
    (hTargetPhase : TargetTowerPhaseCouplingFamily) :
    ∀ _hRH : ZetaZeros.RiemannHypothesis,
      TargetHeightTowerSqrtWitness := by
  intro hRH
  exact hTargetPhase hRH

/-- Construct the negative `AntiTargetHeightTowerSqrtWitness` payload by
coupling Perron/truncated explicit-formula payload with anti-target
phase/tower witnesses.

The anti-target payload already contains the required `sqrt/log` Perron bound. -/
theorem antitarget_tower_sqrt_witness_of_perron_and_phase
    (hAntiTargetPhase : AntiTargetTowerPhaseCouplingFamily) :
    ∀ _hRH : ZetaZeros.RiemannHypothesis,
      AntiTargetHeightTowerSqrtWitness := by
  intro hRH
  exact hAntiTargetPhase hRH

/-- Full RH-π witness data from the two phase/tower families plus the Perron
threshold family. This is a sorry-free assembly path to Blocker 7 once the
three deep payload families are proved. -/
theorem rhPiWitnessData_of_perron_and_phase_payloads
    (hTargetPhase : TargetTowerPhaseCouplingFamily)
    (hAntiTargetPhase : AntiTargetTowerPhaseCouplingFamily) :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData := by
  exact
    Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt.rhPiWitness_proved_of_target_tower_sqrt_via_coeff
      (positive_target_tower_sqrt_witness_of_perron_and_phase hTargetPhase)
      (antitarget_tower_sqrt_witness_of_perron_and_phase hAntiTargetPhase)

/-- Typeclass packaging for the three deep RH-π payload families. -/
class PerronSqrtErrorThresholdFamilyHyp : Prop where
  witness : PerronSqrtErrorThresholdFamily

class TargetTowerPhaseCouplingFamilyHyp : Prop where
  witness : TargetTowerPhaseCouplingFamily

class AntiTargetTowerPhaseCouplingFamilyHyp : Prop where
  witness : AntiTargetTowerPhaseCouplingFamily

/-- Auxiliary typeclass bridge: target-phase payload implies Perron witness
payload (by forgetting phase/tower data). -/
instance [TargetTowerPhaseCouplingFamilyHyp] : PerronSqrtErrorThresholdFamilyHyp where
  witness :=
    perron_family_of_target_tower_phase
      TargetTowerPhaseCouplingFamilyHyp.witness

/-- Manual bridge (non-instance): any available target tower-sqrt payload class
can be repackaged as `TargetTowerPhaseCouplingFamilyHyp`. -/
theorem targetPhaseHyp_of_targetTowerSqrtHyp
    [Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt.RhPiTargetTowerSqrtWitnessHyp] :
    TargetTowerPhaseCouplingFamilyHyp := by
  exact ⟨Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt.RhPiTargetTowerSqrtWitnessHyp.witness⟩

/-- Manual bridge (non-instance): any available anti-target tower-sqrt payload
class can be repackaged as `AntiTargetTowerPhaseCouplingFamilyHyp`. -/
theorem antiTargetPhaseHyp_of_antiTargetTowerSqrtHyp
    [Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt.RhPiAntiTargetTowerSqrtWitnessHyp] :
    AntiTargetTowerPhaseCouplingFamilyHyp := by
  exact ⟨Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt.RhPiAntiTargetTowerSqrtWitnessHyp.witness⟩

/-- Instance form of `targetPhaseHyp_of_targetTowerSqrtHyp`, kept low-priority
to avoid interfering with the primary forward assembly path. -/
instance (priority := 100)
    [Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt.RhPiTargetTowerSqrtWitnessHyp] :
    TargetTowerPhaseCouplingFamilyHyp :=
  targetPhaseHyp_of_targetTowerSqrtHyp

/-- Instance form of `antiTargetPhaseHyp_of_antiTargetTowerSqrtHyp`, kept
low-priority to avoid interfering with the primary forward assembly path. -/
instance (priority := 100)
    [Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt.RhPiAntiTargetTowerSqrtWitnessHyp] :
    AntiTargetTowerPhaseCouplingFamilyHyp :=
  antiTargetPhaseHyp_of_antiTargetTowerSqrtHyp

/-- Typeclass bridge: target-phase payloads directly produce the positive
tower-sqrt witness class consumed by `RHPiCoeffControlFromTargetTowerSqrt`. -/
instance
    [TargetTowerPhaseCouplingFamilyHyp] :
    Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt.RhPiTargetTowerSqrtWitnessHyp where
  witness :=
    positive_target_tower_sqrt_witness_of_perron_and_phase
      TargetTowerPhaseCouplingFamilyHyp.witness

/-- Typeclass bridge: anti-target-phase payloads directly produce the negative
tower-sqrt witness class consumed by `RHPiCoeffControlFromTargetTowerSqrt`. -/
instance
    [AntiTargetTowerPhaseCouplingFamilyHyp] :
    Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt.RhPiAntiTargetTowerSqrtWitnessHyp where
  witness :=
    antitarget_tower_sqrt_witness_of_perron_and_phase
      AntiTargetTowerPhaseCouplingFamilyHyp.witness

/-- Typeclass endpoint: once the two deep phase/tower payload classes are
instantiated, `RhPiWitnessData` follows without additional assembly work.
`PerronSqrtErrorThresholdFamilyHyp` is derivable automatically from target-phase
payload by projection (`perron_family_of_target_tower_phase`). -/
theorem rhPiWitnessData_of_hyp
    [TargetTowerPhaseCouplingFamilyHyp]
    [AntiTargetTowerPhaseCouplingFamilyHyp] :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData := by
  exact rhPiWitnessData_of_perron_and_phase_payloads
    TargetTowerPhaseCouplingFamilyHyp.witness
    AntiTargetTowerPhaseCouplingFamilyHyp.witness

end Aristotle.Standalone.RHPiTowerWitnessFromPerronAndPhase
