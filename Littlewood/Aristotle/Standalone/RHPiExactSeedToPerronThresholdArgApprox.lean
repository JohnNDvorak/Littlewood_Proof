import Littlewood.Aristotle.Standalone.RHPiArgApproxFromPerronThreshold
import Littlewood.Aristotle.Standalone.RHPiPhaseCouplingConstructiveFamilies
import Littlewood.Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold
import Mathlib.Topology.Instances.AddCircle.Defs

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

/-- Single-frequency exact congruence is equivalent to equality in
`AddCircle (2π)`. -/
lemma exists_int_congruence_iff_addCircle_eq
    {t γ φ : ℝ} :
    (∃ m : ℤ, t * γ - φ - m • (2 * Real.pi) = 0) ↔
      (((t * γ : ℝ) : AddCircle (2 * Real.pi)) =
        (φ : AddCircle (2 * Real.pi))) := by
  constructor
  · intro h
    rcases h with ⟨m, hm⟩
    have hsub : t * γ - φ = m • (2 * Real.pi) := by linarith
    have hsub0 : (((t * γ - φ : ℝ) : ℝ) : AddCircle (2 * Real.pi)) = 0 := by
      exact (AddCircle.coe_eq_zero_iff (p := (2 * Real.pi))).2 ⟨m, hsub.symm⟩
    have hsub0' :
        ((t * γ : AddCircle (2 * Real.pi)) - (φ : AddCircle (2 * Real.pi))) = 0 := by
      simpa [AddCircle.coe_sub] using hsub0
    exact sub_eq_zero.mp hsub0'
  · intro hEq
    have hsub0 :
        ((t * γ : AddCircle (2 * Real.pi)) - (φ : AddCircle (2 * Real.pi))) = 0 := by
      simpa using sub_eq_zero.mpr hEq
    have hsub0' : (((t * γ - φ : ℝ) : ℝ) : AddCircle (2 * Real.pi)) = 0 := by
      simpa [AddCircle.coe_sub] using hsub0
    rcases (AddCircle.coe_eq_zero_iff (p := (2 * Real.pi))).1 hsub0' with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    linarith [hm]

/-- Target exact-seed payload rewritten in additive-circle form. -/
theorem targetTowerExactSeedAbovePerronThreshold_iff_addCircle
    [TruncatedExplicitFormulaPiHyp] :
    TargetTowerExactSeedAbovePerronThreshold ↔
      ∀ _hRH : ZetaZeros.RiemannHypothesis, ∀ X : ℝ, ∃ t0 T ε : ℝ,
        4 ≤ T ∧
        0 < ε ∧ ε < 1 ∧
        X < Real.exp t0 ∧
        perronThreshold _hRH T ≤ Real.exp t0 ∧
        (∀ ρ ∈ (finite_zeros_le T).toFinset,
          (((t0 * ρ.im : ℝ) : AddCircle (2 * Real.pi)) =
            (Complex.arg ρ : AddCircle (2 * Real.pi)))) ∧
        Real.exp t0 ≤
          Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2))) := by
  constructor
  · intro hSeed hRH X
    rcases hSeed hRH X with
      ⟨t0, T, ε, hT4, hεpos, hεlt, hX, hThreshold, hseed, hUpper⟩
    refine ⟨t0, T, ε, hT4, hεpos, hεlt, hX, hThreshold, ?_, hUpper⟩
    intro ρ hρ
    exact (exists_int_congruence_iff_addCircle_eq
      (t := t0) (γ := ρ.im) (φ := Complex.arg ρ)).1 (hseed ρ hρ)
  · intro hSeed hRH X
    rcases hSeed hRH X with
      ⟨t0, T, ε, hT4, hεpos, hεlt, hX, hThreshold, hseed, hUpper⟩
    refine ⟨t0, T, ε, hT4, hεpos, hεlt, hX, hThreshold, ?_, hUpper⟩
    intro ρ hρ
    exact (exists_int_congruence_iff_addCircle_eq
      (t := t0) (γ := ρ.im) (φ := Complex.arg ρ)).2 (hseed ρ hρ)

/-- Anti-target exact-seed payload rewritten in additive-circle form. -/
theorem antiTargetTowerExactSeedAbovePerronThreshold_iff_addCircle
    [TruncatedExplicitFormulaPiHyp] :
    AntiTargetTowerExactSeedAbovePerronThreshold ↔
      ∀ _hRH : ZetaZeros.RiemannHypothesis, ∀ X : ℝ, ∃ t0 T ε : ℝ,
        4 ≤ T ∧
        0 < ε ∧ ε < 1 ∧
        X < Real.exp t0 ∧
        perronThreshold _hRH T ≤ Real.exp t0 ∧
        (∀ ρ ∈ (finite_zeros_le T).toFinset,
          (((t0 * ρ.im : ℝ) : AddCircle (2 * Real.pi)) =
            ((Complex.arg ρ + Real.pi) : AddCircle (2 * Real.pi)))) ∧
        Real.exp t0 ≤
          Real.exp (Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2))) := by
  constructor
  · intro hSeed hRH X
    rcases hSeed hRH X with
      ⟨t0, T, ε, hT4, hεpos, hεlt, hX, hThreshold, hseed, hUpper⟩
    refine ⟨t0, T, ε, hT4, hεpos, hεlt, hX, hThreshold, ?_, hUpper⟩
    intro ρ hρ
    exact (exists_int_congruence_iff_addCircle_eq
      (t := t0) (γ := ρ.im) (φ := Complex.arg ρ + Real.pi)).1 (hseed ρ hρ)
  · intro hSeed hRH X
    rcases hSeed hRH X with
      ⟨t0, T, ε, hT4, hεpos, hεlt, hX, hThreshold, hseed, hUpper⟩
    refine ⟨t0, T, ε, hT4, hεpos, hεlt, hX, hThreshold, ?_, hUpper⟩
    intro ρ hρ
    exact (exists_int_congruence_iff_addCircle_eq
      (t := t0) (γ := ρ.im) (φ := Complex.arg ρ + Real.pi)).2 (hseed ρ hρ)

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
