import Littlewood.Aristotle.Standalone.RHPiPerronFromTruncatedPiBridge
import Littlewood.Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt
import Littlewood.Bridge.PiLiDirectOscillation

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold

open Filter Complex ZetaZeros
open GrowthDomination
open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiZeroSumAlignmentBridge
open Aristotle.Standalone.RHPiPerronTowerWitness
open Aristotle.Standalone.RHPiPerronFromTruncatedPiBridge
open Aristotle.Standalone.RHPiCoeffControlFromTargetTowerSqrt

/--
Chosen eventual threshold for the fixed-height Perron error statement.

For each `hRH` and fixed zero cutoff `T`, this is a concrete `B` such that every
`x ≥ B` satisfies the `sqrt/log` explicit-formula error bound.
-/
noncomputable def perronThreshold
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (T : ℝ) : ℝ :=
  Classical.choose <| Filter.eventually_atTop.1
    (perron_sqrt_error_eventually_at_height_of_truncatedPiBridge hRH T)

/-- Specification of `perronThreshold`. -/
theorem perronThreshold_spec
    [TruncatedExplicitFormulaPiHyp]
    (hRH : ZetaZeros.RiemannHypothesis)
    (T : ℝ) :
    ∀ x : ℝ, perronThreshold hRH T ≤ x →
      1 < x ∧
      |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x|
        ≤ Real.sqrt x / Real.log x := by
  let hEvent :
      ∀ᶠ x in atTop,
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x|
          ≤ Real.sqrt x / Real.log x :=
    perron_sqrt_error_eventually_at_height_of_truncatedPiBridge hRH T
  have hChosen :
      ∀ x : ℝ, Classical.choose (Filter.eventually_atTop.1 hEvent) ≤ x →
        1 < x ∧
        |piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x|
          ≤ Real.sqrt x / Real.log x :=
    Classical.choose_spec (Filter.eventually_atTop.1 hEvent)
  simpa [perronThreshold, hEvent] using hChosen

/--
Positive RH payload reduced to phase+tower data above the Perron threshold.

The Perron error term is recovered deterministically from `perronThreshold_spec`.
-/
abbrev TargetTowerPhaseAbovePerronThreshold [TruncatedExplicitFormulaPiHyp] : Prop :=
  ∀ _hRH : ZetaZeros.RiemannHypothesis, ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
    4 ≤ T ∧
    perronThreshold _hRH T ≤ x ∧
    (∃ ε : ℝ,
      0 < ε ∧ ε < 1 ∧
      (∀ ρ ∈ (finite_zeros_le T).toFinset,
        ‖(x : ℂ) ^ (Complex.I * ρ.im) - ρ / ‖ρ‖‖ ≤ ε) ∧
      x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2))))

/--
Negative RH payload reduced to anti-phase+tower data above the Perron threshold.

The Perron error term is recovered deterministically from `perronThreshold_spec`.
-/
abbrev AntiTargetTowerPhaseAbovePerronThreshold [TruncatedExplicitFormulaPiHyp] : Prop :=
  ∀ _hRH : ZetaZeros.RiemannHypothesis, ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
    4 ≤ T ∧
    perronThreshold _hRH T ≤ x ∧
    (∃ ε : ℝ,
      0 < ε ∧ ε < 1 ∧
      (∀ ρ ∈ (finite_zeros_le T).toFinset,
        ‖(x : ℂ) ^ (Complex.I * ρ.im) - (-(ρ / ‖ρ‖))‖ ≤ ε) ∧
      x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2))))

/-- Construct the positive target tower witness from phase+tower data above the
Perron threshold. -/
theorem target_tower_sqrt_witness_of_phase_above_threshold
    [TruncatedExplicitFormulaPiHyp]
    (hTarget : TargetTowerPhaseAbovePerronThreshold) :
    ∀ _hRH : ZetaZeros.RiemannHypothesis, TargetHeightTowerSqrtWitness := by
  intro hRH X
  rcases hTarget hRH X with
    ⟨x, hXx, T, hT4, hThreshold, ε, hεpos, hεlt, hphase, hxUpper⟩
  have hperron := perronThreshold_spec hRH T x hThreshold
  exact ⟨x, hXx, T, hT4, hperron.1, hperron.2, ε, hεpos, hεlt, hphase, hxUpper⟩

/-- Construct the negative anti-target tower witness from anti-phase+tower data
above the Perron threshold. -/
theorem antitarget_tower_sqrt_witness_of_phase_above_threshold
    [TruncatedExplicitFormulaPiHyp]
    (hAntiTarget : AntiTargetTowerPhaseAbovePerronThreshold) :
    ∀ _hRH : ZetaZeros.RiemannHypothesis, AntiTargetHeightTowerSqrtWitness := by
  intro hRH X
  rcases hAntiTarget hRH X with
    ⟨x, hXx, T, hT4, hThreshold, ε, hεpos, hεlt, hphase, hxUpper⟩
  have hperron := perronThreshold_spec hRH T x hThreshold
  exact ⟨x, hXx, T, hT4, hperron.1, hperron.2, ε, hεpos, hεlt, hphase, hxUpper⟩

/-- Typeclass wrapper for positive phase+tower-above-threshold payload. -/
class TargetTowerPhaseAbovePerronThresholdHyp
    [TruncatedExplicitFormulaPiHyp] : Prop where
  witness : TargetTowerPhaseAbovePerronThreshold

/-- Typeclass wrapper for negative anti-phase+tower-above-threshold payload. -/
class AntiTargetTowerPhaseAbovePerronThresholdHyp
    [TruncatedExplicitFormulaPiHyp] : Prop where
  witness : AntiTargetTowerPhaseAbovePerronThreshold

/-- Positive bridge instance to the existing RH-π tower witness class. -/
instance
    [TruncatedExplicitFormulaPiHyp]
    [TargetTowerPhaseAbovePerronThresholdHyp] :
    RhPiTargetTowerSqrtWitnessHyp where
  witness := target_tower_sqrt_witness_of_phase_above_threshold
    TargetTowerPhaseAbovePerronThresholdHyp.witness

/-- Negative bridge instance to the existing RH-π tower witness class. -/
instance
    [TruncatedExplicitFormulaPiHyp]
    [AntiTargetTowerPhaseAbovePerronThresholdHyp] :
    RhPiAntiTargetTowerSqrtWitnessHyp where
  witness := antitarget_tower_sqrt_witness_of_phase_above_threshold
    AntiTargetTowerPhaseAbovePerronThresholdHyp.witness

/-- Endpoint: once the two above-threshold phase payload classes are provided
and truncated π explicit formula is available, Blocker 7 follows via the
existing tower-to-coefficient chain. -/
theorem rhPiWitness_proved_of_phase_above_threshold_hyp
    [TruncatedExplicitFormulaPiHyp]
    [TargetTowerPhaseAbovePerronThresholdHyp]
    [AntiTargetTowerPhaseAbovePerronThresholdHyp] :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData := by
  exact rhPiWitness_proved_of_target_tower_sqrt_hyp

end Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold
