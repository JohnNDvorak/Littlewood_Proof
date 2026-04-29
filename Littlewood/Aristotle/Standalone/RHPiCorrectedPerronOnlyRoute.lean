import Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider
import Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute

open Filter Complex ZetaZeros
open GrowthDomination
open PiLiDirectOscillationBridge
open Aristotle.Standalone.CombinedAtomsFromDeepBlockers
open Aristotle.Standalone.RHPiPerronFromTruncatedPiBridge
open Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold
open Aristotle.Standalone.PerronExplicitFormulaProvider
open Aristotle.Standalone.RHPiCorrectedCanonicalWitnessClasses
open Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox
open Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge

variable [Littlewood.Development.ShiftedRemainderInterface.ShiftedRemainderSegmentBoundLargeTHyp]
variable [Littlewood.Development.HadamardProductZeta.SmallTPerronBoundHyp]

/-!
Corrected Perron-only RH-`pi` packaging endpoint.

This file intentionally adds no analytic source axiom.  It packages the current
honest provider route from fixed-height Perron error, relation-compatible
finite-set Kronecker, paired zeta finite-zero compatibility, and paired
phase-radius tower geometry into the corrected witness endpoints.
-/

/-- Relation-compatible finite-set Kronecker plus paired zeta compatibility
supplies the paired target/anti finite-zero relative-density payload. -/
theorem targetAntiDensity_of_relationCompatibleKroneckerAndCompatibility
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp] :
    TargetAntiFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
  targetAntiFiniteZeroInhomogeneousPhaseRelativelyDense_of_relationCompatibleKronecker_hyp

private theorem target_exactSeedAboveThreshold_perron_from_targetPhaseFit_noTrunc
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [TargetPhaseFitAbovePerronThresholdPerronHyp] :
    TargetTowerExactSeedAbovePerronThresholdPerron := by
  intro hRH X
  rcases TargetPhaseFitAbovePerronThresholdPerronHyp.witness hRH X with
    ⟨x, hXx, T, hT4, hThreshold, ε, hεpos, hεlt, harg, hxUpper⟩
  have hperron := perronThreshold_spec hRH T x hThreshold
  have hx_pos : 0 < x := lt_trans zero_lt_one hperron.1
  refine ⟨Real.log x, T, ε, hT4, hεpos, hεlt, ?_, ?_, ?_, ?_⟩
  · rwa [Real.exp_log hx_pos]
  · rwa [Real.exp_log hx_pos]
  · intro ρ hρ
    rcases harg ρ hρ with ⟨m, hm⟩
    exact ⟨m, by simpa using hm⟩
  · rwa [Real.exp_log hx_pos]

private theorem antiTarget_exactSeedAboveThreshold_perron_from_targetPhaseFit_noTrunc
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [AntiTargetPhaseFitAbovePerronThresholdPerronHyp] :
    AntiTargetTowerExactSeedAbovePerronThresholdPerron := by
  intro hRH X
  rcases AntiTargetPhaseFitAbovePerronThresholdPerronHyp.witness hRH X with
    ⟨x, hXx, T, hT4, hThreshold, ε, hεpos, hεlt, harg, hxUpper⟩
  have hperron := perronThreshold_spec hRH T x hThreshold
  have hx_pos : 0 < x := lt_trans zero_lt_one hperron.1
  refine ⟨Real.log x, T, ε, hT4, hεpos, hεlt, ?_, ?_, ?_, ?_⟩
  · rwa [Real.exp_log hx_pos]
  · rwa [Real.exp_log hx_pos]
  · intro ρ hρ
    rcases harg ρ hρ with ⟨m, hm⟩
    exact ⟨m, by simpa using hm⟩
  · rwa [Real.exp_log hx_pos]

/-- The four honest corrected-route classes package both Perron-only exact-seed
classes. -/
theorem exactSeed_of_correctedPerronOnlyRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [TargetAntiPerronThresholdTowerGeometryForPhaseRadiiHyp] :
    TargetTowerExactSeedAbovePerronThresholdPerronHyp ∧
      AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp := by
  letI : TargetAntiFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
    targetAntiDensity_of_relationCompatibleKroneckerAndCompatibility
  letI : TargetFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
    targetFiniteZeroInhomogeneousPhaseRelativelyDense_of_paired_hyp
  letI : AntiTargetFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
    antiTargetFiniteZeroInhomogeneousPhaseRelativelyDense_of_paired_hyp
  letI : TargetPerronThresholdTowerGeometryForPhaseRadiusHyp :=
    targetPerronThresholdTowerGeometryForPhaseRadius_of_pairedGeometry_hyp
  letI : AntiTargetPerronThresholdTowerGeometryForPhaseRadiusHyp :=
    antiTargetPerronThresholdTowerGeometryForPhaseRadius_of_pairedGeometry_hyp
  letI : TargetPerronThresholdTowerWideDominationWithPhaseRadiusHyp :=
    targetPerronThresholdTowerWideDominationWithPhaseRadius_of_geometry_hyp
  letI : AntiTargetPerronThresholdTowerWideDominationWithPhaseRadiusHyp :=
    antiTargetPerronThresholdTowerWideDominationWithPhaseRadius_of_geometry_hyp
  letI : TargetPhaseFitAbovePerronThresholdPerronHyp :=
    targetPhaseFitAbovePerronThresholdPerron_of_realizedRadiusDomination_hyp
  letI : AntiTargetPhaseFitAbovePerronThresholdPerronHyp :=
    antiTargetPhaseFitAbovePerronThresholdPerron_of_realizedRadiusDomination_hyp
  exact
    ⟨{ witness := target_exactSeedAboveThreshold_perron_from_targetPhaseFit_noTrunc },
      { witness := antiTarget_exactSeedAboveThreshold_perron_from_targetPhaseFit_noTrunc }⟩

/-- Half-budget variant of the corrected route.

This exposes the current smallest tower geometry leaves below
`TargetAntiPerronThresholdTowerGeometryForPhaseRadiiHyp` while preserving the
same corrected Perron-only endpoint. -/
theorem exactSeed_of_correctedPerronOnlyHalfBudgetRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [PerronThresholdTowerLogHalfBudgetHyp]
    [TargetAntiFiniteZeroPhaseRadiusHalfBudgetAtPerronThresholdHyp] :
    TargetTowerExactSeedAbovePerronThresholdPerronHyp ∧
      AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp := by
  letI : TargetAntiFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
    targetAntiDensity_of_relationCompatibleKroneckerAndCompatibility
  letI : TargetFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
    targetFiniteZeroInhomogeneousPhaseRelativelyDense_of_paired_hyp
  letI : AntiTargetFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
    antiTargetFiniteZeroInhomogeneousPhaseRelativelyDense_of_paired_hyp
  letI : TargetAntiPerronThresholdTowerLogBudgetForPhaseRadiiHyp :=
    targetAntiPerronThresholdTowerLogBudgetForPhaseRadii_of_halfBudgets_hyp
  letI : TargetAntiPerronThresholdTowerLogGeometryForPhaseRadiiHyp :=
    targetAntiPerronThresholdTowerLogGeometryForPhaseRadii_of_budget_hyp
  letI : TargetAntiPerronThresholdTowerGeometryForPhaseRadiiHyp :=
    targetAntiPerronThresholdTowerGeometryForPhaseRadii_of_logGeometry_hyp
  exact exactSeed_of_correctedPerronOnlyRoute

/-- The four honest corrected-route classes package both corrected canonical
phase-coupling payload classes. -/
theorem correctedPhaseCoupling_of_correctedPerronOnlyRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [TargetAntiPerronThresholdTowerGeometryForPhaseRadiiHyp] :
    TargetTowerPhaseCouplingFamilyHyp_corrected ∧
      AntiTargetTowerPhaseCouplingFamilyHyp_corrected := by
  rcases exactSeed_of_correctedPerronOnlyRoute with ⟨hTarget, hAntiTarget⟩
  letI : TargetTowerExactSeedAbovePerronThresholdPerronHyp := hTarget
  letI : AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp := hAntiTarget
  exact correctedPhaseCoupling_of_exactSeedAboveThreshold_perron_hyp

/-- Half-budget corrected route to the corrected canonical phase-coupling
payload classes. -/
theorem correctedPhaseCoupling_of_correctedPerronOnlyHalfBudgetRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [PerronThresholdTowerLogHalfBudgetHyp]
    [TargetAntiFiniteZeroPhaseRadiusHalfBudgetAtPerronThresholdHyp] :
    TargetTowerPhaseCouplingFamilyHyp_corrected ∧
      AntiTargetTowerPhaseCouplingFamilyHyp_corrected := by
  rcases exactSeed_of_correctedPerronOnlyHalfBudgetRoute with
    ⟨hTarget, hAntiTarget⟩
  letI : TargetTowerExactSeedAbovePerronThresholdPerronHyp := hTarget
  letI : AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp := hAntiTarget
  exact correctedPhaseCoupling_of_exactSeedAboveThreshold_perron_hyp

/-- Corrected Perron-only route to the RH-side `pi` witness data. -/
theorem rhPiWitnessData_of_correctedPerronOnlyRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [TargetAntiPerronThresholdTowerGeometryForPhaseRadiiHyp] :
    RhPiWitnessData := by
  rcases exactSeed_of_correctedPerronOnlyRoute with ⟨hTarget, hAntiTarget⟩
  letI : TargetTowerExactSeedAbovePerronThresholdPerronHyp := hTarget
  letI : AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp := hAntiTarget
  exact rhPiWitnessData_of_exactSeedAboveThreshold_perron_corrected_hyp

/-- Half-budget corrected route to the RH-side `pi` witness data. -/
theorem rhPiWitnessData_of_correctedPerronOnlyHalfBudgetRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [PerronThresholdTowerLogHalfBudgetHyp]
    [TargetAntiFiniteZeroPhaseRadiusHalfBudgetAtPerronThresholdHyp] :
    RhPiWitnessData := by
  rcases exactSeed_of_correctedPerronOnlyHalfBudgetRoute with
    ⟨hTarget, hAntiTarget⟩
  letI : TargetTowerExactSeedAbovePerronThresholdPerronHyp := hTarget
  letI : AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp := hAntiTarget
  exact rhPiWitnessData_of_exactSeedAboveThreshold_perron_corrected_hyp

/-- Corrected Perron-only route from the explicit same-height growth sources
below the two half-budget leaves. -/
theorem rhPiWitnessData_of_correctedPerronOnlyGrowthBudgetRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [PerronThresholdTowerExpHalfBudgetGrowthHyp]
    [TargetAntiFiniteZeroPhaseRadiusHalfBudgetGrowthHyp] :
    RhPiWitnessData := by
  exact rhPiWitnessData_of_correctedPerronOnlyHalfBudgetRoute

/-- Corrected Perron-only route from the same-height majorant/tower splits
below the explicit growth-budget sources. -/
theorem rhPiWitnessData_of_correctedPerronOnlyMajorantBudgetRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [PerronThresholdTowerExpHalfBudgetMajorantHyp]
    [TargetAntiFiniteZeroPhaseRadiusHalfBudgetMajorantHyp] :
    RhPiWitnessData := by
  exact rhPiWitnessData_of_correctedPerronOnlyGrowthBudgetRoute

/-- Corrected Perron-only route from the canonical Perron max-majorant and the
same-height target/anti radius majorants. -/
theorem rhPiWitnessData_of_correctedPerronOnlyCanonicalRadiusMajorantRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [PerronThresholdTowerExpHalfBudgetCanonicalMajorantHyp]
    [TargetFiniteZeroPhaseRadiusHalfBudgetMajorantHyp]
    [AntiTargetFiniteZeroPhaseRadiusHalfBudgetMajorantHyp] :
    RhPiWitnessData := by
  exact rhPiWitnessData_of_correctedPerronOnlyMajorantBudgetRoute

/-- Corrected Perron-only route to the concrete RH 7a/7c pair. -/
theorem rh_pi_7a_7c_pair_of_correctedPerronOnlyRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [TargetAntiPerronThresholdTowerGeometryForPhaseRadiiHyp]
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
  rcases exactSeed_of_correctedPerronOnlyRoute with ⟨hTarget, hAntiTarget⟩
  letI : TargetTowerExactSeedAbovePerronThresholdPerronHyp := hTarget
  letI : AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp := hAntiTarget
  exact rh_pi_7a_7c_pair_of_exactSeedAboveThreshold_perron_hyp hRH

/-- Half-budget corrected route to the concrete RH 7a/7c pair. -/
theorem rh_pi_7a_7c_pair_of_correctedPerronOnlyHalfBudgetRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [PerronThresholdTowerLogHalfBudgetHyp]
    [TargetAntiFiniteZeroPhaseRadiusHalfBudgetAtPerronThresholdHyp]
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
  rcases exactSeed_of_correctedPerronOnlyHalfBudgetRoute with
    ⟨hTarget, hAntiTarget⟩
  letI : TargetTowerExactSeedAbovePerronThresholdPerronHyp := hTarget
  letI : AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp := hAntiTarget
  exact rh_pi_7a_7c_pair_of_exactSeedAboveThreshold_perron_hyp hRH

end Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute
