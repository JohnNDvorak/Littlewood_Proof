# Parallel Attack Matrix (Checkpoint branch `checkpoint/full-state-2026-03-05`)

## Snapshot
- `main_sorries=0`
- `delegated_sorries=13`
- `delegated_axiom_postulate_lines=0`
- Missing root constructors: `15`
- Missing main-chain assumptions: `2`

## Hard Guardrails
1. No `axiom`, `postulate`, `sorry`, `admit` added.
2. Do not weaken theorem signatures.
3. Keep non-circularity strict: provider files must not import the deep leaf they are closing.
4. Use lane ownership below to avoid stepping on parallel work.

## Lane Ownership (No file overlap)
| Lane | Owned files |
|---|---|
| `B1-root` | `Littlewood/Aristotle/Standalone/HardyAfeSignedGapDeepLeaf.lean` plus new B1 provider module(s) under `Littlewood/Aristotle/Standalone/` |
| `B2-root` | `Littlewood/Aristotle/Standalone/B2TailVdcDeepLeaf.lean` plus new B2 support-provider module(s) under `Littlewood/Aristotle/Standalone/` |
| `B5a-root` | `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean` plus new B5a provider module(s) under `Littlewood/Aristotle/Standalone/` |
| `RS7-core` | `Littlewood/Aristotle/ErrorTermExpansion.lean` and optional helper infra files under `Littlewood/Aristotle/` |
| `RS7-block` | `Littlewood/Aristotle/RSBlockBounds.lean` |
| `B7-root` | `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean` plus new RH-pi root provider module(s) under `Littlewood/Aristotle/Standalone/` |

## 13-Blocker Matrix
| ID | Blocker theorem | Owner lane | Depends on | Non-circular closure route | Required upstream proof/instance | Risk |
|---|---|---|---|---|---|---|
| `B1-1` | `HardyAfeSignedGapDeepLeaf.afe_signed_integral_gap_bound_leaf` | `B1-root` | none inside B1 leaf | close by `exact` from provider theorem in new upstream module | independent theorem of shape `(fun T => (∫ t in Ioc 1 T, hardyZ^2) - T*log T) =O(T)` or equivalent `mean_square_zeta (1/2)` asymptotic instance `ZetaMeanSquareHalfBound` | high (root analytic payload missing) |
| `B2-1` | `B2TailVdcDeepLeaf.tailVdcSqrtModeClass_leaf` | `B2-root` | support-class package | close by `exact tailVdcSqrtModeClass_of_noncircular_support_constructor` | non-circular support-class constructors: `HardyGammaInSlitPlaneOnSupportHyp`, `HardyThetaPhaseGapLowerSqrtModeOnSupportHyp`, `HardyPhaseDerivDifferentiableOnSupportHyp`, `HardyExpPhaseSecondDerivAbsBoundOnSupportHyp` | high |
| `B5a-1` | `ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.shifted_remainder_bound_leaf` | `B5a-root` | none inside deep leaf | close by `exact shifted_remainder_bound_of_legacy_explicit_formula` or `...of_general_hyp` from root infra/provider | upstream global witness for `Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp` or `ExplicitFormulaPsiGeneralHyp` (non-circular source) | high |
| `RS7-1` | `ErrorTermExpansion.theta_stirling_expansion` | `RS7-core` | none | derive from derivative/asymptotic route (avoid principal-branch `arg Gamma`) | stable bridge lemmas from `BinetStirling`/theta-derivative infra into exact `hardyTheta` statement | high (structural branch-cut landmine) |
| `RS7-2` | `ErrorTermExpansion.off_resonance_integral_bound` | `RS7-core` | `phase_deriv_off_resonance` | apply `OffResonanceInfra.off_resonance_integral_bound_of_vdc` | prove VdC side-conditions (`Differentiable`, derivative lower bound, second-derivative nonneg on block) | medium |
| `RS7-3` | `ErrorTermExpansion.off_resonance_sum_bound` | `RS7-core` | `RS7-2` | apply `OffResonanceInfra.off_resonance_sum_bound_of_mode_and_kernel` | weighted kernel-sum lemma `<= C_off * sqrt(k+1)` | medium |
| `RS7-4` | `ErrorTermExpansion.errorTerm_expansion` | `RS7-core` | `RS7-1`, `RS7-2`, `RS7-3` | complete RS expansion using existing block scaffolding and sign chain | core RS remainder expansion estimate per block | very high |
| `RS7-5` | `RSBlockBounds.c_block_nonneg` | `RS7-block` | `RS7-4` | derive from block expansion lower main term plus error | explicit inequality from `errorTerm_expansion` and `A_block` definition | medium |
| `RS7-6` | `RSBlockBounds.c_block_antitone` | `RS7-block` | `RS7-5`, `RS7-4` | prove antitone on `Ici 1` from asymptotic decay in block residual | monotonicity lemma for correction residual | high |
| `RS7-7` | `RSBlockBounds.block_interpolation` | `RS7-block` | `RS7-4` | prove with sign coherence and block-local interpolation bound | bounded interpolation error constant `C₂_block` route from expansion | medium |
| `B7-1` | `RHPiUnconditionalExactSeedExistence.truncatedExplicitFormulaPi_unconditional` | `B7-root` | none | close by `exact truncatedExplicitFormulaPi_unconditional_of_rootPayload` | upstream `RHPiUnconditionalExactSeedRootPayload` instance | high |
| `B7-2` | `RHPiUnconditionalExactSeedExistence.targetTowerExactSeedAbovePerronThreshold_unconditional` | `B7-root` | `B7-1` class context | close by `exact targetTowerExactSeedAbovePerronThreshold_unconditional_of_rootPayload` | same upstream `RHPiUnconditionalExactSeedRootPayload` | high |
| `B7-3` | `RHPiUnconditionalExactSeedExistence.antiTargetTowerExactSeedAbovePerronThreshold_unconditional` | `B7-root` | `B7-1` class context | close by `exact antiTargetTowerExactSeedAbovePerronThreshold_unconditional_of_rootPayload` | same upstream `RHPiUnconditionalExactSeedRootPayload` | high |

## Root Constructor Mapping (What blocks each lane)
| Missing constructor/class | Lane |
|---|---|
| `ZetaMeanSquareHalfBound` | `B1-root` |
| `Aristotle.Standalone.B2SupportPhaseRootInfra.B2SupportPhaseRootPayload` | `B2-root` |
| `Aristotle.Standalone.B2TailVdcRootInfra.B2TailVdcRootPayload` | `B2-root` |
| `Aristotle.Standalone.B2VdcFirstDerivTailRootInfra.B2VdcFirstDerivTailRootPayload` | `B2-root` |
| `HardyFirstMomentWiring.HardyThetaDifferentiableOnSupportHyp` | `B2-root` |
| `HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp` | `B2-root` |
| `HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp` | `B2-root` |
| `HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp` | `B2-root` |
| `HardyFirstMomentWiring.HardyExpPhaseVdcPhaseCalculusOnTailSupportHyp` | `B2-root` |
| `HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp` | `B2-root` |
| `HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnTailSupportHyp` | `B2-root` |
| `HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp` | `B2-root` |
| `Aristotle.DirichletPhaseAlignment.ExplicitFormulaPsiHyp` | `B5a-root` |
| `Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries.ExplicitFormulaPsiGeneralHyp` | `B5a-root` |
| `Aristotle.Standalone.RHPiUnconditionalExactSeedRootInfra.RHPiUnconditionalExactSeedRootPayload` | `B7-root` |

## Suggested Parallel Execution Order
1. `RS7-core`: start `RS7-2` and `RS7-1` in parallel.
2. `B1-root`, `B2-root`, `B5a-root`, `B7-root`: build upstream provider/root constructors in parallel.
3. `RS7-core`: finish `RS7-3`, then `RS7-4`.
4. `RS7-block`: close `RS7-5` and `RS7-7`, then `RS7-6`.
5. Close wrappers immediately after provider availability: `B1-1`, `B2-1`, `B5a-1`, `B7-1/2/3`.

## Validation Contract Per Lane
1. `lake build Littlewood.Aristotle.Standalone.DeepBlockersResolved`
2. `lake build Littlewood.Aristotle.DeepSorries`
3. `./scripts/critical_path_expanded_status.sh`
4. `./scripts/root_constructor_status.sh`

## Honest Structural Blockers
1. `StirlingArgGamma.lean` contains contradiction markers (`stirling_arg_gamma_asymp_false`, `stirling_arg_gamma_false`), so RS7 must avoid principal-branch `arg Gamma` routes.
2. `HardyMeanSquareAsymptoticFromZetaMoment` currently depends on B1 atomic/deep path, so it cannot be used as the non-circular source for B1 closure.
3. B5a and B7 wrappers are ready, but both require upstream class/payload providers not yet synthesized.
