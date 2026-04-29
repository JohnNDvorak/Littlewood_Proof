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

/-- Budgeted-radius variant of the corrected route.

This route consumes an explicitly budgeted target/anti finite-zero
relative-density theorem, so it does not need to bound the old unconstrained
`Classical.choose` phase radii. -/
theorem exactSeed_of_correctedPerronOnlyBudgetedRadiusRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [PerronThresholdTowerLogHalfBudgetHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseBudgetedRelativelyDenseHyp] :
    TargetTowerExactSeedAbovePerronThresholdPerronHyp ∧
      AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp := by
  rcases
    targetAntiPerronThresholdTowerWideDominationWithPhaseRadius_of_logHalfBudget_budgetedRelativelyDense_hyp with
    ⟨hTargetDom, hAntiDom⟩
  letI : TargetPerronThresholdTowerWideDominationWithPhaseRadiusHyp := hTargetDom
  letI : AntiTargetPerronThresholdTowerWideDominationWithPhaseRadiusHyp := hAntiDom
  letI : TargetPhaseFitAbovePerronThresholdPerronHyp :=
    targetPhaseFitAbovePerronThresholdPerron_of_realizedRadiusDomination_hyp
  letI : AntiTargetPhaseFitAbovePerronThresholdPerronHyp :=
    antiTargetPhaseFitAbovePerronThresholdPerron_of_realizedRadiusDomination_hyp
  exact
    ⟨{ witness := target_exactSeedAboveThreshold_perron_from_targetPhaseFit_noTrunc },
      { witness := antiTarget_exactSeedAboveThreshold_perron_from_targetPhaseFit_noTrunc }⟩

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

/-- Budgeted-radius corrected route to the corrected canonical phase-coupling
payload classes. -/
theorem correctedPhaseCoupling_of_correctedPerronOnlyBudgetedRadiusRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [PerronThresholdTowerLogHalfBudgetHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseBudgetedRelativelyDenseHyp] :
    TargetTowerPhaseCouplingFamilyHyp_corrected ∧
      AntiTargetTowerPhaseCouplingFamilyHyp_corrected := by
  rcases exactSeed_of_correctedPerronOnlyBudgetedRadiusRoute with
    ⟨hTarget, hAntiTarget⟩
  letI : TargetTowerExactSeedAbovePerronThresholdPerronHyp := hTarget
  letI : AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp := hAntiTarget
  exact correctedPhaseCoupling_of_exactSeedAboveThreshold_perron_hyp

/-- Fixed-height Perron-error phase fit supplies the corrected phase-coupling
payloads without using the Perron-threshold exact-seed classes. -/
theorem correctedPhaseCoupling_of_correctedPerronOnlyFixedHeightErrorRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [InhomogeneousPhaseFitWithFixedHeightPerronErrorHyp] :
    TargetTowerPhaseCouplingFamilyHyp_corrected ∧
      AntiTargetTowerPhaseCouplingFamilyHyp_corrected := by
  exact correctedPhaseCoupling_of_exactSeedWithFixedHeightPerronError
    target_exact_seed_withFixedHeightPerronError_from_phase_fit
    antiTarget_exact_seed_withFixedHeightPerronError_from_phase_fit

/-- Relation-compatible target/anti finite-zero data plus the fixed-height
Perron-error wide-window source supply corrected phase-coupling without the
arbitrary-target phase-fit class. -/
theorem correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiFixedHeightErrorRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [FixedHeightPerronErrorPhaseWideWindowHyp] :
    TargetTowerPhaseCouplingFamilyHyp_corrected ∧
      AntiTargetTowerPhaseCouplingFamilyHyp_corrected := by
  rcases targetAntiFixedHeightPerronErrorPhaseFit_of_relationCompatibleAndWindow_hyp with
    ⟨hTarget, hAntiTarget⟩
  letI : TargetPhaseFitWithFixedHeightPerronErrorHyp := hTarget
  letI : AntiTargetPhaseFitWithFixedHeightPerronErrorHyp := hAntiTarget
  exact correctedPhaseCoupling_of_targetAntiFixedHeightPerronErrorPhaseFit_hyp

/-- Same-height Perron-threshold wide windows feed the target/anti
fixed-height route by one local `perronThreshold_spec` adapter. -/
theorem correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiThresholdWindowRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [PerronThresholdTowerPhaseWideWindowHyp] :
    TargetTowerPhaseCouplingFamilyHyp_corrected ∧
      AntiTargetTowerPhaseCouplingFamilyHyp_corrected := by
  letI : FixedHeightPerronErrorPhaseWideWindowHyp :=
    fixedHeightPerronErrorPhaseWideWindow_of_perronThresholdWideWindow_hyp
  exact correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiFixedHeightErrorRoute

/-- Target/anti fixed-height route with the residual reduced to same-height
arbitrary-radius tower domination. -/
theorem correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiWideDominationRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [PerronThresholdTowerWideDominationHyp] :
    TargetTowerPhaseCouplingFamilyHyp_corrected ∧
      AntiTargetTowerPhaseCouplingFamilyHyp_corrected := by
  letI : FixedHeightPerronErrorPhaseWideWindowHyp :=
    fixedHeightPerronErrorPhaseWideWindow_of_perronThresholdWideDomination_hyp
  exact correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiFixedHeightErrorRoute

/-- Target/anti fixed-height route from the log-level arbitrary-radius tower
domination source. -/
theorem correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiWideLogDominationRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [PerronThresholdTowerWideLogDominationHyp] :
    TargetTowerPhaseCouplingFamilyHyp_corrected ∧
      AntiTargetTowerPhaseCouplingFamilyHyp_corrected := by
  letI : PerronThresholdTowerWideDominationHyp :=
    perronThresholdTowerWideDomination_of_logDomination_hyp
  exact correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiWideDominationRoute

/-- Target/anti fixed-height route from the arbitrary-radius log half-budget
source. -/
theorem correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiWideLogBudgetRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [PerronThresholdTowerWideLogBudgetHyp] :
    TargetTowerPhaseCouplingFamilyHyp_corrected ∧
      AntiTargetTowerPhaseCouplingFamilyHyp_corrected := by
  letI : PerronThresholdTowerWideLogDominationHyp :=
    perronThresholdTowerWideLogDomination_of_logBudget_hyp
  exact correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiWideLogDominationRoute

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

/-- Fixed-height Perron-error phase fit supplies the corrected RH-`pi` witness
data without the opaque cross-height `perronThreshold` comparison. -/
theorem rhPiWitnessData_of_correctedPerronOnlyFixedHeightErrorRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [InhomogeneousPhaseFitWithFixedHeightPerronErrorHyp] :
    RhPiWitnessData := by
  exact rhPiWitnessData_of_fixedHeightPerronErrorPhaseFit_hyp

/-- Relation-compatible target/anti finite-zero data plus the fixed-height
Perron-error wide-window source supply the corrected RH-`pi` witness endpoint
without the arbitrary-target phase-fit class. -/
theorem rhPiWitnessData_of_correctedPerronOnlyTargetAntiFixedHeightErrorRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [FixedHeightPerronErrorPhaseWideWindowHyp] :
    RhPiWitnessData := by
  rcases correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiFixedHeightErrorRoute with
    ⟨hTarget, hAntiTarget⟩
  letI : TargetTowerPhaseCouplingFamilyHyp_corrected := hTarget
  letI : AntiTargetTowerPhaseCouplingFamilyHyp_corrected := hAntiTarget
  exact rhPiWitnessData_of_correctedHyp

/-- Corrected RH-`pi` witness endpoint from relation-compatible target/anti
data plus the same-height Perron-threshold wide-window source. -/
theorem rhPiWitnessData_of_correctedPerronOnlyTargetAntiThresholdWindowRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [PerronThresholdTowerPhaseWideWindowHyp] :
    RhPiWitnessData := by
  rcases correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiThresholdWindowRoute with
    ⟨hTarget, hAntiTarget⟩
  letI : TargetTowerPhaseCouplingFamilyHyp_corrected := hTarget
  letI : AntiTargetTowerPhaseCouplingFamilyHyp_corrected := hAntiTarget
  exact rhPiWitnessData_of_correctedHyp

/-- Corrected RH-`pi` endpoint from relation-compatible target/anti data plus
same-height arbitrary-radius tower domination. -/
theorem rhPiWitnessData_of_correctedPerronOnlyTargetAntiWideDominationRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [PerronThresholdTowerWideDominationHyp] :
    RhPiWitnessData := by
  rcases correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiWideDominationRoute with
    ⟨hTarget, hAntiTarget⟩
  letI : TargetTowerPhaseCouplingFamilyHyp_corrected := hTarget
  letI : AntiTargetTowerPhaseCouplingFamilyHyp_corrected := hAntiTarget
  exact rhPiWitnessData_of_correctedHyp

/-- Corrected RH-`pi` endpoint from the log-level arbitrary-radius tower
domination source. -/
theorem rhPiWitnessData_of_correctedPerronOnlyTargetAntiWideLogDominationRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [PerronThresholdTowerWideLogDominationHyp] :
    RhPiWitnessData := by
  rcases correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiWideLogDominationRoute with
    ⟨hTarget, hAntiTarget⟩
  letI : TargetTowerPhaseCouplingFamilyHyp_corrected := hTarget
  letI : AntiTargetTowerPhaseCouplingFamilyHyp_corrected := hAntiTarget
  exact rhPiWitnessData_of_correctedHyp

/-- Corrected RH-`pi` endpoint from the arbitrary-radius log half-budget
source. -/
theorem rhPiWitnessData_of_correctedPerronOnlyTargetAntiWideLogBudgetRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [PerronThresholdTowerWideLogBudgetHyp] :
    RhPiWitnessData := by
  rcases correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiWideLogBudgetRoute with
    ⟨hTarget, hAntiTarget⟩
  letI : TargetTowerPhaseCouplingFamilyHyp_corrected := hTarget
  letI : AntiTargetTowerPhaseCouplingFamilyHyp_corrected := hAntiTarget
  exact rhPiWitnessData_of_correctedHyp

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

/-- Corrected RH-`pi` witness endpoint from the Perron log half-budget and an
explicitly budgeted target/anti finite-zero relative-density theorem. -/
theorem rhPiWitnessData_of_correctedPerronOnlyBudgetedRadiusRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [PerronThresholdTowerLogHalfBudgetHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseBudgetedRelativelyDenseHyp] :
    RhPiWitnessData := by
  rcases exactSeed_of_correctedPerronOnlyBudgetedRadiusRoute with
    ⟨hTarget, hAntiTarget⟩
  letI : TargetTowerExactSeedAbovePerronThresholdPerronHyp := hTarget
  letI : AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp := hAntiTarget
  exact rhPiWitnessData_of_exactSeedAboveThreshold_perron_corrected_hyp

/-- Corrected RH-`pi` witness endpoint from paired zeta compatibility and a
relation-compatible quantitative Kronecker theorem with explicit budgeted
radii. -/
theorem rhPiWitnessData_of_correctedPerronOnlyRelationCompatibleBudgetedRadiusRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [PerronThresholdTowerLogHalfBudgetHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [TargetAntiFiniteZeroRelationCompatibleBudgetedRelativelyDenseKroneckerHyp] :
    RhPiWitnessData := by
  letI : TargetAntiFiniteZeroInhomogeneousPhaseBudgetedRelativelyDenseHyp :=
    targetAntiFiniteZeroInhomogeneousPhaseBudgetedRelativelyDense_of_relationCompatibleBudgetedKronecker_hyp
  exact rhPiWitnessData_of_correctedPerronOnlyBudgetedRadiusRoute

/-- Corrected RH-`pi` witness endpoint from the existing relation-compatible
finite-set Kronecker source plus a half-budget bound for the actual selected
target/anti Kronecker radii. -/
theorem rhPiWitnessData_of_correctedPerronOnlyRelationCompatibleKroneckerRadiusBudgetRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [PerronThresholdTowerLogHalfBudgetHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp] :
    RhPiWitnessData := by
  letI : TargetAntiFiniteZeroRelationCompatibleBudgetedRelativelyDenseKroneckerHyp :=
    targetAntiFiniteZeroRelationCompatibleBudgetedRelativelyDenseKronecker_of_relationCompatibleKronecker_radiusBudget_hyp
  exact rhPiWitnessData_of_correctedPerronOnlyRelationCompatibleBudgetedRadiusRoute

/-- Corrected RH-`pi` witness endpoint from the existing relation-compatible
finite-set Kronecker source plus one-sided target and anti-target bounds for
the actual selected Kronecker radii. -/
theorem rhPiWitnessData_of_correctedPerronOnlyOneSidedKroneckerRadiusBudgetRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [PerronThresholdTowerLogHalfBudgetHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp]
    [AntiTargetFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp] :
    RhPiWitnessData := by
  letI : TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp :=
    targetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudget_of_oneSided_hyp
  exact rhPiWitnessData_of_correctedPerronOnlyRelationCompatibleKroneckerRadiusBudgetRoute

/-- Corrected RH-`pi` witness endpoint from paired zeta compatibility and a
generic finite-set pair Kronecker theorem with explicit same-budget target and
anti-target radii. -/
theorem rhPiWitnessData_of_correctedPerronOnlyFiniteSetBudgetedKroneckerRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [PerronThresholdTowerLogHalfBudgetHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [FiniteSetRelationCompatibleBudgetedPairKroneckerHyp] :
    RhPiWitnessData := by
  letI : TargetAntiFiniteZeroRelationCompatibleBudgetedRelativelyDenseKroneckerHyp :=
    targetAntiFiniteZeroRelationCompatibleBudgetedRelativelyDenseKronecker_of_finiteSetBudgetedPairKronecker_hyp
  exact rhPiWitnessData_of_correctedPerronOnlyRelationCompatibleBudgetedRadiusRoute

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
  letI : TargetAntiFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
    targetAntiDensity_of_relationCompatibleKroneckerAndCompatibility
  letI : TargetFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
    targetFiniteZeroInhomogeneousPhaseRelativelyDense_of_paired_hyp
  letI : AntiTargetFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
    antiTargetFiniteZeroInhomogeneousPhaseRelativelyDense_of_paired_hyp
  letI : PerronThresholdTowerExpHalfBudgetMajorantHyp :=
    perronThresholdTowerExpHalfBudgetMajorant_of_canonical_hyp
  letI : TargetAntiFiniteZeroPhaseRadiusHalfBudgetMajorantHyp :=
    targetAntiFiniteZeroPhaseRadiusHalfBudgetMajorant_of_targetAnti_hyp
  exact rhPiWitnessData_of_correctedPerronOnlyMajorantBudgetRoute

/-- Corrected Perron-only route from canonical Perron and one-sided canonical
radius half-budget inequalities. -/
theorem rhPiWitnessData_of_correctedPerronOnlyCanonicalRadiusRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [PerronThresholdTowerExpHalfBudgetCanonicalMajorantHyp]
    [TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp]
    [AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp] :
    RhPiWitnessData := by
  letI : TargetAntiFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
    targetAntiDensity_of_relationCompatibleKroneckerAndCompatibility
  letI : TargetFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
    targetFiniteZeroInhomogeneousPhaseRelativelyDense_of_paired_hyp
  letI : AntiTargetFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
    antiTargetFiniteZeroInhomogeneousPhaseRelativelyDense_of_paired_hyp
  letI : TargetFiniteZeroPhaseRadiusHalfBudgetMajorantHyp :=
    targetFiniteZeroPhaseRadiusHalfBudgetMajorant_of_canonical_hyp
  letI : AntiTargetFiniteZeroPhaseRadiusHalfBudgetMajorantHyp :=
    antiTargetFiniteZeroPhaseRadiusHalfBudgetMajorant_of_canonical_hyp
  exact rhPiWitnessData_of_correctedPerronOnlyCanonicalRadiusMajorantRoute

/-- Corrected Perron-only phase-coupling from the exact residual predicates
for the canonical Perron budget and the actual target/anti chosen radii. -/
theorem correctedPhaseCoupling_of_correctedPerronOnlyCanonicalResidualRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    (hPerron :
      PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual)
    (hTarget :
      TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual)
    (hAnti :
      AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual) :
    TargetTowerPhaseCouplingFamilyHyp_corrected ∧
      AntiTargetTowerPhaseCouplingFamilyHyp_corrected := by
  letI : TargetAntiFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
    targetAntiDensity_of_relationCompatibleKroneckerAndCompatibility
  letI : TargetFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
    targetFiniteZeroInhomogeneousPhaseRelativelyDense_of_paired_hyp
  letI : AntiTargetFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
    antiTargetFiniteZeroInhomogeneousPhaseRelativelyDense_of_paired_hyp
  letI : PerronThresholdTowerExpHalfBudgetCanonicalMajorantHyp :=
    perronThresholdTowerExpHalfBudgetCanonicalMajorant_of_residual hPerron
  letI : TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp :=
    targetFiniteZeroPhaseRadiusHalfBudgetCanonical_of_residual hTarget
  letI : AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp :=
    antiTargetFiniteZeroPhaseRadiusHalfBudgetCanonical_of_residual hAnti
  exact correctedPhaseCoupling_of_correctedPerronOnlyHalfBudgetRoute

/-- Corrected Perron-only RH-`pi` endpoint from the exact residual predicates
for the canonical Perron budget and the actual target/anti chosen radii. -/
theorem rhPiWitnessData_of_correctedPerronOnlyCanonicalResidualRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    (hPerron :
      PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual)
    (hTarget :
      TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual)
    (hAnti :
      AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual) :
    RhPiWitnessData := by
  rcases correctedPhaseCoupling_of_correctedPerronOnlyCanonicalResidualRoute
      hPerron hTarget hAnti with
    ⟨hTargetPhase, hAntiTargetPhase⟩
  letI : TargetTowerPhaseCouplingFamilyHyp_corrected := hTargetPhase
  letI : AntiTargetTowerPhaseCouplingFamilyHyp_corrected := hAntiTargetPhase
  exact rhPiWitnessData_of_correctedHyp

/-- Corrected Perron-only route through the exact canonical residual predicates,
with those residuals closed by the existing same-height Perron and paired
chosen-radius growth facts. -/
theorem rhPiWitnessData_of_correctedPerronOnlyGrowthResidualRoute
    [PerronSqrtErrorEventuallyAtHeightHyp]
    [FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp]
    [TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp]
    [PerronThresholdTowerExpHalfBudgetGrowthHyp]
    [TargetAntiFiniteZeroPhaseRadiusHalfBudgetGrowthHyp] :
    RhPiWitnessData := by
  letI : TargetAntiFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
    targetAntiDensity_of_relationCompatibleKroneckerAndCompatibility
  letI : TargetFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
    targetFiniteZeroInhomogeneousPhaseRelativelyDense_of_paired_hyp
  letI : AntiTargetFiniteZeroInhomogeneousPhaseRelativelyDenseHyp :=
    antiTargetFiniteZeroInhomogeneousPhaseRelativelyDense_of_paired_hyp
  exact rhPiWitnessData_of_correctedPerronOnlyCanonicalResidualRoute
    perronThresholdTowerExpHalfBudgetCanonicalMajorantResidual_of_growth_hyp
    targetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual_of_pairedGrowth_hyp
    antiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual_of_pairedGrowth_hyp

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
