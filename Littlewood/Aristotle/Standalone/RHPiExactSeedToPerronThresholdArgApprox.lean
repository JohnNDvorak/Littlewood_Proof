import Littlewood.Aristotle.Standalone.RHPiArgApproxFromPerronThreshold
import Littlewood.Aristotle.Standalone.RHPiPhaseCouplingConstructiveFamilies
import Littlewood.Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox

open Filter Complex ZetaZeros
open GrowthDomination
open PiLiDirectOscillationBridge
open Aristotle.Standalone.CombinedAtomsFromDeepBlockers
open Aristotle.Standalone.RHPiArgApproxFromPerronThreshold
open Aristotle.Standalone.RHPiPhaseCouplingConstructiveFamilies
open Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold

/-- Positive exact-seed payload at Perron-threshold/tower-cap level.

For each RH branch and each threshold `X`, this provides:
1. a cutoff height `T`,
2. a tolerance `ε ∈ (0,1)`,
3. a real seed time `t0`,
such that `x = exp t0` is above both `X` and the Perron threshold at `T`,
satisfies exact target congruences for all zeros up to `T`, and also satisfies
the required tower-height cap.

This is the exact constructive content that feeds
`TargetTowerArgApproxAbovePerronThreshold`.
-/
abbrev TargetTowerExactSeedAbovePerronThreshold
    [TruncatedExplicitFormulaPiHyp] : Prop :=
  ∀ _hRH : ZetaZeros.RiemannHypothesis, ∀ X : ℝ, ∃ t0 T ε : ℝ,
    4 ≤ T ∧
    0 < ε ∧ ε < 1 ∧
    X < Real.exp t0 ∧
    perronThreshold _hRH T ≤ Real.exp t0 ∧
    (∀ ρ ∈ (finite_zeros_le T).toFinset,
      ∃ m : ℤ, t0 * ρ.im - Complex.arg ρ - m • (2 * Real.pi) = 0) ∧
    Real.exp t0 ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2)))

/-- Anti-target exact-seed payload at Perron-threshold/tower-cap level. -/
abbrev AntiTargetTowerExactSeedAbovePerronThreshold
    [TruncatedExplicitFormulaPiHyp] : Prop :=
  ∀ _hRH : ZetaZeros.RiemannHypothesis, ∀ X : ℝ, ∃ t0 T ε : ℝ,
    4 ≤ T ∧
    0 < ε ∧ ε < 1 ∧
    X < Real.exp t0 ∧
    perronThreshold _hRH T ≤ Real.exp t0 ∧
    (∀ ρ ∈ (finite_zeros_le T).toFinset,
      ∃ m : ℤ, t0 * ρ.im - (Complex.arg ρ + Real.pi) - m • (2 * Real.pi) = 0) ∧
    Real.exp t0 ≤ Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2)))

/-- Positive exact seeds induce the positive arg-above-threshold payload. -/
theorem target_argAboveThreshold_of_exactSeedFamily
    [TruncatedExplicitFormulaPiHyp]
    (hSeed : TargetTowerExactSeedAbovePerronThreshold) :
    TargetTowerArgApproxAbovePerronThreshold := by
  intro hRH X
  rcases hSeed hRH X with
    ⟨t0, T, ε, hT4, hεpos, hεlt, hX, hThreshold, hseed, hUpper⟩
  let x : ℝ := Real.exp t0
  refine ⟨x, ?_, T, hT4, ?_, ε, hεpos, hεlt, ?_, ?_⟩
  · simpa [x] using hX
  · simpa [x] using hThreshold
  · intro ρ hρ
    rcases hseed ρ hρ with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hEq : Real.log x * ρ.im - Complex.arg ρ - m • (2 * Real.pi) = 0 := by
      simpa [x] using hm
    rw [hEq]
    simpa using (le_of_lt hεpos)
  · simpa [x] using hUpper

/-- Anti-target exact seeds induce the anti-target arg-above-threshold payload. -/
theorem antiTarget_argAboveThreshold_of_exactSeedFamily
    [TruncatedExplicitFormulaPiHyp]
    (hSeed : AntiTargetTowerExactSeedAbovePerronThreshold) :
    AntiTargetTowerArgApproxAbovePerronThreshold := by
  intro hRH X
  rcases hSeed hRH X with
    ⟨t0, T, ε, hT4, hεpos, hεlt, hX, hThreshold, hseed, hUpper⟩
  let x : ℝ := Real.exp t0
  refine ⟨x, ?_, T, hT4, ?_, ε, hεpos, hεlt, ?_, ?_⟩
  · simpa [x] using hX
  · simpa [x] using hThreshold
  · intro ρ hρ
    rcases hseed ρ hρ with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hEq :
        Real.log x * ρ.im - (Complex.arg ρ + Real.pi) - m • (2 * Real.pi) = 0 := by
      simpa [x] using hm
    rw [hEq]
    simpa using (le_of_lt hεpos)
  · simpa [x] using hUpper

/-- Typeclass wrapper for positive exact-seed families. -/
class TargetTowerExactSeedAbovePerronThresholdHyp
    [TruncatedExplicitFormulaPiHyp] : Prop where
  witness : TargetTowerExactSeedAbovePerronThreshold

/-- Typeclass wrapper for anti-target exact-seed families. -/
class AntiTargetTowerExactSeedAbovePerronThresholdHyp
    [TruncatedExplicitFormulaPiHyp] : Prop where
  witness : AntiTargetTowerExactSeedAbovePerronThreshold

/-- Positive instance bridge into the existing arg-above-threshold class. -/
instance
    [TruncatedExplicitFormulaPiHyp]
    [TargetTowerExactSeedAbovePerronThresholdHyp] :
    TargetTowerArgApproxAbovePerronThresholdHyp where
  witness :=
    target_argAboveThreshold_of_exactSeedFamily
      TargetTowerExactSeedAbovePerronThresholdHyp.witness

/-- Anti-target instance bridge into the existing arg-above-threshold class. -/
instance
    [TruncatedExplicitFormulaPiHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdHyp] :
    AntiTargetTowerArgApproxAbovePerronThresholdHyp where
  witness :=
    antiTarget_argAboveThreshold_of_exactSeedFamily
      AntiTargetTowerExactSeedAbovePerronThresholdHyp.witness

/-- Endpoint: exact-seed payload classes imply `RhPiWitnessData` through the
existing Perron-threshold arg/phase chain. -/
theorem rhPiWitnessData_of_exact_seed_above_threshold_hyp
    [TruncatedExplicitFormulaPiHyp]
    [TargetTowerExactSeedAbovePerronThresholdHyp]
    [AntiTargetTowerExactSeedAbovePerronThresholdHyp] :
    RhPiWitnessData := by
  exact rhPiWitnessData_of_arg_above_threshold_hyp

/-- 7a/7c endpoint from exact-seed payload classes. -/
theorem rh_pi_7a_7c_pair_of_exact_seed_above_threshold_hyp
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
  exact rh_pi_7a_7c_pair_of_thresholdPhaseHyp hRH

end Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
