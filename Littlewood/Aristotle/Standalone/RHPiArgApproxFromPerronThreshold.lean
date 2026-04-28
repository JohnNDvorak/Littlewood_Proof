import Littlewood.Aristotle.Standalone.RHPiTargetPhaseArgReduction
import Littlewood.Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiArgApproxFromPerronThreshold

open Complex ZetaZeros
open GrowthDomination
open PiLiDirectOscillationBridge
open Aristotle.Standalone.RHPiPerronFromTruncatedPiBridge
open Aristotle.Standalone.RHPiTargetPhaseArgReduction
open Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold

/-- Positive arg-approx payload reduced to phase/height data above Perron's
threshold. The explicit-formula error and `1 < x` side conditions are recovered
from `perronThreshold_spec`. -/
abbrev TargetTowerArgApproxAbovePerronThreshold
    [PerronSqrtErrorEventuallyAtHeightHyp] : Prop :=
  ∀ _hRH : ZetaZeros.RiemannHypothesis, ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
    4 ≤ T ∧
    perronThreshold _hRH T ≤ x ∧
    (∃ ε : ℝ,
      0 < ε ∧ ε < 1 ∧
      (∀ ρ ∈ (finite_zeros_le T).toFinset,
        ∃ k : ℤ,
          ‖Real.log x * ρ.im - Complex.arg ρ - k • (2 * Real.pi)‖ ≤ ε) ∧
      x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2))))

/-- Negative arg-approx payload reduced to anti-phase/height data above
Perron's threshold. -/
abbrev AntiTargetTowerArgApproxAbovePerronThreshold
    [PerronSqrtErrorEventuallyAtHeightHyp] : Prop :=
  ∀ _hRH : ZetaZeros.RiemannHypothesis, ∀ X : ℝ, ∃ x : ℝ, X < x ∧ ∃ T : ℝ,
    4 ≤ T ∧
    perronThreshold _hRH T ≤ x ∧
    (∃ ε : ℝ,
      0 < ε ∧ ε < 1 ∧
      (∀ ρ ∈ (finite_zeros_le T).toFinset,
        ∃ k : ℤ,
          ‖Real.log x * ρ.im - (Complex.arg ρ + Real.pi) - k • (2 * Real.pi)‖ ≤ ε) ∧
      x ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2))))

/-- Build the full positive arg-approx family from the above-threshold payload.
All missing side conditions are supplied by `perronThreshold_spec`. -/
theorem targetTowerArgApproxFamily_of_above_threshold
    [PerronSqrtErrorEventuallyAtHeightHyp]
    (hTarget : TargetTowerArgApproxAbovePerronThreshold) :
    TargetTowerArgApproxFamily := by
  intro hRH X
  rcases hTarget hRH X with
    ⟨x, hXx, T, hT4, hThreshold, ε, hεpos, hεlt, harg, hxUpper⟩
  have hperron := perronThreshold_spec hRH T x hThreshold
  exact ⟨x, hXx, T, hT4, hperron.1, hperron.2, ε, hεpos, hεlt, harg, hxUpper⟩

/-- Build the full negative arg-approx family from the above-threshold
payload. -/
theorem antiTargetTowerArgApproxFamily_of_above_threshold
    [PerronSqrtErrorEventuallyAtHeightHyp]
    (hAntiTarget : AntiTargetTowerArgApproxAbovePerronThreshold) :
    AntiTargetTowerArgApproxFamily := by
  intro hRH X
  rcases hAntiTarget hRH X with
    ⟨x, hXx, T, hT4, hThreshold, ε, hεpos, hεlt, harg, hxUpper⟩
  have hperron := perronThreshold_spec hRH T x hThreshold
  exact ⟨x, hXx, T, hT4, hperron.1, hperron.2, ε, hεpos, hεlt, harg, hxUpper⟩

/-- Build the positive phase-above-threshold payload from the positive
arg-above-threshold payload. -/
theorem targetTowerPhaseAbovePerronThreshold_of_argAbove
    [PerronSqrtErrorEventuallyAtHeightHyp]
    (hTarget : TargetTowerArgApproxAbovePerronThreshold) :
    TargetTowerPhaseAbovePerronThreshold := by
  intro hRH X
  rcases hTarget hRH X with
    ⟨x, hXx, T, hT4, hThreshold, ε, hεpos, hεlt, harg, hxUpper⟩
  have hperron := perronThreshold_spec hRH T x hThreshold
  have hx_pos : 0 < x := lt_trans zero_lt_one hperron.1
  refine ⟨x, hXx, T, hT4, hThreshold, ε, hεpos, hεlt, ?_, hxUpper⟩
  intro ρ hρ
  rcases harg ρ hρ with ⟨k, hk⟩
  have hρz : ρ ∈ zetaNontrivialZeros := by
    have hz : ρ ∈ zerosUpTo T := by simpa using hρ
    have hz' : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
      simpa [zerosUpTo] using hz
    exact (mem_zetaNontrivialZerosPos.1 hz'.1).1
  have hρne : ρ ≠ 0 := by
    intro h0
    have hre_pos : 0 < ρ.re := hρz.2.1
    have : (0 : ℝ) < 0 := by simpa [h0] using hre_pos
    exact (lt_irrefl 0) this
  exact target_phase_close_of_log_arg_approx hx_pos hρne hk

/-- Build the negative phase-above-threshold payload from the negative
arg-above-threshold payload. -/
theorem antiTargetTowerPhaseAbovePerronThreshold_of_argAbove
    [PerronSqrtErrorEventuallyAtHeightHyp]
    (hAntiTarget : AntiTargetTowerArgApproxAbovePerronThreshold) :
    AntiTargetTowerPhaseAbovePerronThreshold := by
  intro hRH X
  rcases hAntiTarget hRH X with
    ⟨x, hXx, T, hT4, hThreshold, ε, hεpos, hεlt, harg, hxUpper⟩
  have hperron := perronThreshold_spec hRH T x hThreshold
  have hx_pos : 0 < x := lt_trans zero_lt_one hperron.1
  refine ⟨x, hXx, T, hT4, hThreshold, ε, hεpos, hεlt, ?_, hxUpper⟩
  intro ρ hρ
  rcases harg ρ hρ with ⟨k, hk⟩
  have hρz : ρ ∈ zetaNontrivialZeros := by
    have hz : ρ ∈ zerosUpTo T := by simpa using hρ
    have hz' : ρ ∈ zetaNontrivialZerosPos ∧ ρ.im ≤ T := by
      simpa [zerosUpTo] using hz
    exact (mem_zetaNontrivialZerosPos.1 hz'.1).1
  have hρne : ρ ≠ 0 := by
    intro h0
    have hre_pos : 0 < ρ.re := hρz.2.1
    have : (0 : ℝ) < 0 := by simpa [h0] using hre_pos
    exact (lt_irrefl 0) this
  exact antitarget_phase_close_of_log_arg_approx hx_pos hρne hk

/-- Positive payload class at the above-threshold interface. -/
class TargetTowerArgApproxAbovePerronThresholdHyp
    [PerronSqrtErrorEventuallyAtHeightHyp] : Prop where
  witness : TargetTowerArgApproxAbovePerronThreshold

/-- Negative payload class at the above-threshold interface. -/
class AntiTargetTowerArgApproxAbovePerronThresholdHyp
    [PerronSqrtErrorEventuallyAtHeightHyp] : Prop where
  witness : AntiTargetTowerArgApproxAbovePerronThreshold

/-- Instance bridge: positive above-threshold arg payload gives the full
positive arg-approximation family. -/
instance
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [TargetTowerArgApproxAbovePerronThresholdHyp] :
    TargetTowerArgApproxFamilyHyp where
  witness :=
    targetTowerArgApproxFamily_of_above_threshold
      TargetTowerArgApproxAbovePerronThresholdHyp.witness

/-- Instance bridge: negative above-threshold arg payload gives the full
negative arg-approximation family. -/
instance
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [AntiTargetTowerArgApproxAbovePerronThresholdHyp] :
    AntiTargetTowerArgApproxFamilyHyp where
  witness :=
    antiTargetTowerArgApproxFamily_of_above_threshold
      AntiTargetTowerArgApproxAbovePerronThresholdHyp.witness

/-- Positive arg-above-threshold payload also supplies the positive
phase-above-threshold payload. -/
instance
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [TargetTowerArgApproxAbovePerronThresholdHyp] :
    TargetTowerPhaseAbovePerronThresholdHyp where
  witness :=
    targetTowerPhaseAbovePerronThreshold_of_argAbove
      TargetTowerArgApproxAbovePerronThresholdHyp.witness

/-- Negative arg-above-threshold payload also supplies the negative
phase-above-threshold payload. -/
instance
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [AntiTargetTowerArgApproxAbovePerronThresholdHyp] :
    AntiTargetTowerPhaseAbovePerronThresholdHyp where
  witness :=
    antiTargetTowerPhaseAbovePerronThreshold_of_argAbove
      AntiTargetTowerArgApproxAbovePerronThresholdHyp.witness

/-- Fact-level endpoint for the positive family. -/
instance (priority := 100)
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [TargetTowerArgApproxAbovePerronThresholdHyp] :
    Fact TargetTowerArgApproxFamily :=
  ⟨TargetTowerArgApproxFamilyHyp.witness⟩

/-- Fact-level endpoint for the negative family. -/
instance (priority := 100)
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [AntiTargetTowerArgApproxAbovePerronThresholdHyp] :
    Fact AntiTargetTowerArgApproxFamily :=
  ⟨AntiTargetTowerArgApproxFamilyHyp.witness⟩

/-- End-to-end RH-`pi` witness endpoint:
above-threshold arg payload classes + fixed-height Perron error imply
`RhPiWitnessData`. -/
theorem rhPiWitnessData_of_arg_above_threshold_hyp
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [TargetTowerArgApproxAbovePerronThresholdHyp]
    [AntiTargetTowerArgApproxAbovePerronThresholdHyp] :
    Aristotle.Standalone.CombinedAtomsFromDeepBlockers.RhPiWitnessData := by
  exact rhPiWitnessData_of_argApproxHyp

end Aristotle.Standalone.RHPiArgApproxFromPerronThreshold
