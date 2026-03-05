# Checkpoint Manifest (2026-03-05)

## Identity
- Branch: `checkpoint/full-state-2026-03-05`
- Commit: `cc9e2bf8d4772eef20d80548600cc836d207b979`
- Tag: `checkpoint-2026-03-05-fullstate`
- Created (UTC): `2026-03-05 15:17:43 UTC`

## Intent
This checkpoint is a full-state rollback anchor before re-dividing workstreams. It contains the complete mixed state from all active windows (tracked + untracked content that existed at freeze time).

## Status Snapshot (at checkpoint)
- `main_sorries=0`
- `delegated_sorries=13`
- `main_axiom_postulate_lines=0`
- `delegated_axiom_postulate_lines=0`

## Delegated Frontier (13 sorry leaves)
1. `Littlewood/Aristotle/Standalone/B2TailVdcDeepLeaf.lean:166`
2. `Littlewood/Aristotle/RSBlockBounds.lean:115`
3. `Littlewood/Aristotle/RSBlockBounds.lean:120`
4. `Littlewood/Aristotle/RSBlockBounds.lean:144`
5. `Littlewood/Aristotle/ErrorTermExpansion.lean:107`
6. `Littlewood/Aristotle/ErrorTermExpansion.lean:251`
7. `Littlewood/Aristotle/ErrorTermExpansion.lean:260`
8. `Littlewood/Aristotle/ErrorTermExpansion.lean:297`
9. `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean:32`
10. `Littlewood/Aristotle/Standalone/HardyAfeSignedGapDeepLeaf.lean:107`
11. `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean:45`
12. `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean:52`
13. `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean:56`

## Unsynthesized Root Constructors (15)
1. `ZetaMeanSquareHalfBound`
2. `Aristotle.Standalone.B2TailVdcRootInfra.B2TailVdcRootPayload`
3. `Aristotle.Standalone.B2VdcFirstDerivTailRootInfra.B2VdcFirstDerivTailRootPayload`
4. `Aristotle.Standalone.B2SupportPhaseRootInfra.B2SupportPhaseRootPayload`
5. `HardyFirstMomentWiring.HardyThetaDifferentiableOnSupportHyp`
6. `HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp`
7. `HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp`
8. `HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp`
9. `HardyFirstMomentWiring.HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp`
10. `HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp`
11. `HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp`
12. `HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp`
13. `Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp`
14. `Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries.ExplicitFormulaPsiGeneralHyp`
15. `Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra.RHPiUnconditionalExactSeedRootPayload`

## Unsynthesized Main-Chain Assumptions (2)
1. `Aristotle.Standalone.PsiZeroSumOscillationFromIngham.CriticalZeroSumDivergesHyp`
2. `Aristotle.DirichletPhaseAlignment.PhaseAlignmentToTargetHyp`
