# Main-Chain Blocker Catalog (Checkpoint `cc9e2bf`)

## A) Concrete delegated blockers (red nodes)

| Blocker | File | Upstream route | Blocker type | Closure target |
|---|---|---|---|---|
| `afe_signed_integral_gap_bound_leaf` | `Littlewood/Aristotle/Standalone/HardyAfeSignedGapDeepLeaf.lean:107` | `littlewood_psi/littlewood_pi_li -> DeepSorries.combined_atoms -> DeepBlockersResolved.deep_blocker_B1 -> HardyMeanSquareAsymptoticFromZetaMoment -> HardyAfeSignedGapAtomic` | delegated `sorry` theorem | Prove signed AFE gap `O(T)` unconditionally (non-circular root/provider) |
| `tailVdcSqrtModeClass_leaf` | `Littlewood/Aristotle/Standalone/B2TailVdcDeepLeaf.lean:166` | `... -> DeepBlockersResolved.deep_blocker_B2 -> B2StationaryWindowLeaves.mainTermFirstMomentBoundHyp_from_windowLeaves` | delegated `sorry` theorem | Prove tail VdC sqrt-mode class or provide unconditional support payload constructor |
| `shifted_remainder_bound_leaf` | `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean:32` | `... -> DeepBlockersResolved.deep_blocker_B5a -> ExplicitFormulaPsiSkeleton -> ExplicitFormulaPsiB5aComponents -> Atomic` | delegated `sorry` theorem | Prove shifted remainder bound or provide non-circular `ExplicitFormulaPsiGeneralHyp` constructor |
| `theta_stirling_expansion` | `Littlewood/Aristotle/ErrorTermExpansion.lean:107` | `... -> DeepBlockersResolved.deep_blocker_B3 -> RSCompleteBlockAsymptotic -> RSBlockBounds -> ErrorTermExpansion` | delegated `sorry` theorem | Prove Stirling theta expansion with stated bound |
| `off_resonance_integral_bound` | `Littlewood/Aristotle/ErrorTermExpansion.lean:251` | same B3 route | delegated `sorry` theorem | Prove VdC off-resonance integral estimate |
| `off_resonance_sum_bound` | `Littlewood/Aristotle/ErrorTermExpansion.lean:260` | same B3 route | delegated `sorry` theorem | Prove weighted off-resonance sum `O(sqrt(k+1))` |
| `errorTerm_expansion` | `Littlewood/Aristotle/ErrorTermExpansion.lean:297` | same B3 route | delegated `sorry` theorem | Prove RS block expansion core theorem |
| `c_block_nonneg` | `Littlewood/Aristotle/RSBlockBounds.lean:115` | `... -> RSBlockBounds.rs_block_analysis_proof` | delegated `sorry` theorem | Prove correction sequence nonnegativity |
| `c_block_antitone` | `Littlewood/Aristotle/RSBlockBounds.lean:120` | same B3 route | delegated `sorry` theorem | Prove correction sequence antitonicity on `Ici 1` |
| `block_interpolation` | `Littlewood/Aristotle/RSBlockBounds.lean:144` | same B3 route | delegated `sorry` theorem | Prove partial block interpolation bound |
| `truncatedExplicitFormulaPi_unconditional` | `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean:45` | `... -> DeepBlockersResolved.deep_blocker_B7_coeff_control_leaf` | delegated `sorry` theorem | Prove truncated explicit formula payload or provide `RHPiUnconditionalExactSeedRootPayload` |
| `targetTowerExactSeedAbovePerronThreshold_unconditional` | `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean:52` | same B7 route | delegated `sorry` theorem | Prove positive exact-seed endpoint |
| `antiTargetTowerExactSeedAbovePerronThreshold_unconditional` | `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean:56` | same B7 route | delegated `sorry` theorem | Prove anti-target exact-seed endpoint |

## B) Main-chain assumption blockers (amber nodes)

| Blocker | Where required | Current status |
|---|---|---|
| `Aristotle.Standalone.PsiZeroSumOscillationFromIngham.CriticalZeroSumDivergesHyp` | `Littlewood/Main/LittlewoodPsi.lean` and `Littlewood/Main/LittlewoodPi.lean` (via `DeepSorries`/`DeepBlockersResolved`) | `#synth` fails |
| `Aristotle.DirichletPhaseAlignment.PhaseAlignmentToTargetHyp` | same as above | `#synth` fails |

## C) Missing root constructor frontier (amber nodes)

| Missing constructor | Primary blocked lane |
|---|---|
| `ZetaMeanSquareHalfBound` | B1 provider chain |
| `Aristotle.Standalone.B2TailVdcRootInfra.B2TailVdcRootPayload` | B2 leaf/provider chain |
| `Aristotle.Standalone.B2VdcFirstDerivTailRootInfra.B2VdcFirstDerivTailRootPayload` | B2 upstream phase-tail chain |
| `Aristotle.Standalone.B2SupportPhaseRootInfra.B2SupportPhaseRootPayload` | B2 non-circular support constructor chain |
| `HardyFirstMomentWiring.HardyThetaDifferentiableOnSupportHyp` | B2 support-class synthesis |
| `HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp` | B2 support-class synthesis |
| `HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp` | B2 support-class synthesis |
| `HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp` | B2 support-class synthesis |
| `HardyFirstMomentWiring.HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp` | B2 tail synthesis |
| `HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp` | B2 tail synthesis |
| `HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp` | B2 tail synthesis |
| `HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp` | B2 delegated leaf target class |
| `Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp` | B5a legacy provider alternative |
| `Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries.ExplicitFormulaPsiGeneralHyp` | B5a provider/assembly route |
| `Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra.RHPiUnconditionalExactSeedRootPayload` | RH-pi/B7 exact-seed closure route |

## D) Structural note
The main-chain exported theorems are proved conditionally on the two unsynthesized assumptions in section B. The concrete frontier in section A is where delegated theorem bodies remain unresolved.
