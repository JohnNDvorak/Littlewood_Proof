# Littlewood Provider Matrix

Date: 2026-04-21
Branch: `recovery/provider-forensics-2026-04-21`
Active repo HEAD: `5c08167ed9dab415fe4959d8982eadcd90030a47`

This matrix is computed from the active tracked repo, not from CloudDocs.
The purpose is to distinguish:

- reachable tracked providers
- tracked but off-path providers
- tracked but axiom-backed or sorry-backed providers
- forwarding-only bridges
- genuinely missing providers

## Public-path facts

- Minimal-import invocation currently fails for both public theorems on the first class:
  `Aristotle.Standalone.PsiZeroSumOscillationFromIngham.CriticalZeroSumDivergesHyp`.
- `#print axioms Littlewood.littlewood_psi` reports only:
  `propext`, `Classical.choice`, `Quot.sound`.
- `#print axioms LittlewoodPi.littlewood_pi_li` reports only:
  `propext`, `Classical.choice`, `Quot.sound`.

So the public theorem constants are axiom-clean at the declaration level, but they are not
usable through the public import path.

Latest strict trace result:

- the minimal-import error still reports `CriticalZeroSumDivergesHyp`;
- but direct `trace.Meta.synthInstance` now shows that the public path reaches
  the tracked `CriticalZeroSumDivergesHyp` instance, then crosses
  `HardyDirichletPhaseAlignmentWiring` and
  `HardyCriticalLineZerosFromStandalone`, synthesizes
  `AtkinsonSmallShiftPrefixBoundHyp`,
  `AtkinsonLargeShiftPrefixBoundHyp`, and
  `AtkinsonShiftedInversePhaseCorePrefixBoundHyp`, and then honestly stops at
  `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`.

So the public failure surface is no longer "missing critical-zero provider".
The critical-zero lane is now live, and the first live provider failure on the
active recovery path is the Atkinson inverse-phase-cell / correction theorem
layer, with inverse-phase-cell now exposed as the first missing class.

Latest declaration-level check:

- `@Aristotle.DeepSorries.psi_full_strength_oscillation` now explicitly
  requires `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`, but no longer
  explicitly requires:
  - `AtkinsonSmallShiftPrefixBoundHyp`
  - `AtkinsonLargeShiftPrefixBoundHyp`
  - `AtkinsonShiftedInversePhaseCorePrefixBoundHyp`
  - `AtkinsonShiftedCorrectionPrefixBoundHyp`
- `@Aristotle.DeepSorries.pi_li_full_strength_oscillation` has the same reduced
  Atkinson boundary.

So the declaration surface now matches the traced provider frontier: the first
explicit Atkinson theorem-content requirement is inverse-phase-cell.

Latest focused-file fact:

- A forced rebuild of
  [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean)
  now confirms that the large-shift helper
  `atkinson_largeShiftBoundaryAbelRemainder_bound_of_largeShiftPrefix`
  compiles cleanly, and exposes the remaining live file-local blocker directly:
  `atkinson_largeShiftBoundaryAbelRemainder_bound` at line 12464 still carries
  the lone direct-Abel `sorry`.
- This is consistent with the current provider frontier. The new theorem
  `atkinson_shiftedInversePhaseCellPrefixBound_of_no_log` only packages a
  stronger no-log cell-prefix estimate into the public class surface; it does
  not resolve the direct-Abel remainder leaf.

Latest branch-health certification:

- After the newest helper reductions, `AtkinsonFormula.lean` briefly regressed
  on two non-mathematical fronts:
  1. a parser error from placing a doc comment directly before
     `omit ... in theorem`
  2. two hidden, unused `AtkinsonLargeShiftPrefixBoundHyp` dependencies in
     the large-shift wrapper section
- Both issues are now fixed on the recovery branch.
- Validation now passes again:
  - direct `lean Littlewood/Aristotle/Standalone/AtkinsonFormula.lean`
  - `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`
- So the branch is certified healthy again, and the remaining work in
  `AtkinsonFormula.lean` is back to theorem content rather than elaboration
  noise.

Latest analytic-axiom checkpoint:

- On 2026-04-28, baseline `bd6c8f3`, the recovery branch removed the active
  analytic provider shim from the public path.
- `B1B3AnalyticDeepLeaf.lean` no longer imports `AnalyticAxioms.lean`.
- `AnalyticAxioms.lean` remains only as a no-provider compatibility stub:
  no `axiom`, no `private axiom`, and no global analytic class instances.
- Static audit after the change finds only the accepted first-zero pair plus
  the unimported Chebyshev quarantine axioms.
- Focused validation passed for:
  - `lake env lean Littlewood/Aristotle/Standalone/B1B3AnalyticDeepLeaf.lean`
  - `lake env lean Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean`
  - `import Littlewood.Main.LittlewoodPsi`
  - `import Littlewood.Main.LittlewoodPi`
- Additional focused Lake module builds passed serially:
  - `lake build Littlewood.Aristotle.Standalone.AnalyticAxioms`
  - `lake build Littlewood.Aristotle.Standalone.B1B3AnalyticDeepLeaf`
  - `lake build Littlewood.Aristotle.Standalone.DeepBlockersResolved`
  - `lake build Littlewood.Main.LittlewoodPsi`
  - `lake build Littlewood.Main.LittlewoodPi`
- No bare `lake build` was run for this checkpoint.

## Matrix

| Class | Active public path | Current tracked status | Reachability from minimal imports | Evidence |
| --- | --- | --- | --- | --- |
| `CriticalZeroSumDivergesHyp` | yes | tracked provider now reachable on the public path | reachable, but blocked downstream | [`CriticalZeroSumDiverges.lean`](../../Aristotle/Standalone/CriticalZeroSumDiverges.lean) has the tracked instance at line 187; the recovery branch now routes its Hardy prerequisite through [`HardyCriticalLineZerosFromStandalone.lean`](../../Bridge/HardyCriticalLineZerosFromStandalone.lean) plus [`HardyDirichletPhaseAlignmentWiring.lean`](../../Bridge/HardyDirichletPhaseAlignmentWiring.lean), and `trace.Meta.synthInstance` confirms that synthesis enters this provider chain before failing later at the Atkinson correction / inverse-phase-cell layer |
| `PhaseAlignmentToTargetHyp` | yes | tracked payload bridge exists | off-path / unwired | [`DirichletPhaseAlignment.lean`](../../Aristotle/DirichletPhaseAlignment.lean) defines the class; [`ExternalPort/B5bPayloadAutoInstances.lean`](../../Aristotle/Standalone/ExternalPort/B5bPayloadAutoInstances.lean) auto-wires payload at line 51 |
| `AtkinsonShiftedInversePhaseCorePrefixBoundHyp` | yes | tracked reconstruction now exists from the small+large leaves on the recovery branch | reachable on the active recovery path | class declared in [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean) around line 7178; the recovery branch now adds an instance from the split-leaf theorem around lines 9052-9088, and the live `trace.Meta.synthInstance` path through [`CriticalAssumptions.lean`](../../CriticalAssumptions.lean) confirms that `#synth AtkinsonShiftedInversePhaseCorePrefixBoundHyp` succeeds once the active path pulls in small-shift plus the current `CorePrefixDirect` large-shift instance |
| `AtkinsonSmallShiftPrefixBoundHyp` | yes | tracked provider now exists and synthesizes from `AtkinsonFormula` alone | reachable from the module, not yet enough for the full public API | [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean) now contains a clean duplicate chain plus the unconditional instance `instAtkinsonSmallShiftPrefixBoundHyp`; direct `#synth Aristotle.Standalone.AtkinsonFormula.AtkinsonSmallShiftPrefixBoundHyp` succeeds after importing only `Littlewood.Aristotle.Standalone.AtkinsonFormula` |
| `AtkinsonLargeShiftPrefixBoundHyp` | yes | tracked provider now reachable on the active recovery path, but still sorry-backed | reachable, but supplied only through the direct-Abel wrapper | the active trace now uses `Aristotle.Standalone.CorePrefixDirect.instAtkinsonLargeShiftPrefixBoundHyp`; [`CorePrefixDirect.lean`](../../Aristotle/Standalone/CorePrefixDirect.lean) is now only a wrapper around `atkinson_largeShiftPrefixBound_of_direct_abel`, the subordinate remainder helper at lines 12375-12460 now compiles cleanly, and the live literal tracked `sorry` has now been moved onto the sharper theorem `atkinson_largeShiftWeightedBoundarySum_bound` in [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean), while `atkinson_largeShiftBoundaryAbelRemainder_bound` has been reduced to that weighted-boundary statement. The recovery branch also exposes the direct structural reductions `atkinson_largeShiftBoundaryAbelRemainder_eq_weightedBoundarySum` and `atkinson_largeShiftWeightedBoundarySum_eq_prefix_sub_headCore`, so the wrapper debt is now pinned exactly to the weighted boundary sum while making explicit that this sum is the same object as `large-shift prefix - j1 headcore`. A fresh source audit also shows that the generic induction route `atkinson_largeShiftPrefixBound_atomic_of_nextShift` is not currently instantiable from tracked inputs: its successor hypothesis requires a contraction `γ < 1`, while the only available tracked predecessor-tail theorem `atkinson_largeShiftPrefix_succ_htail_of_nextShift_and_smallShift` still carries factor `8`, so the direct-Abel wrapper remains real debt rather than stale packaging |
| `AtkinsonShiftedInversePhaseCellPrefixBoundHyp` | yes | still no base tracked provider found | first honest missing class on the active public path | class declared in [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean) around line 7106; after removing the global correction→cell instance, `trace.Meta.synthInstance` now stops here rather than silently routing through correction, and a focused scratch probe importing `AtkinsonFormula` plus `CorePrefixDirect` still fails to synthesize this class even though small-shift, large-shift, and inverse-core all synthesize. The recovery branch now also contains the explicit reduction theorems `atkinson_shiftedInversePhaseCellPrefix_no_log_of_eventual_and_finite_patch`, `atkinson_shiftedInversePhaseCellPrefixBound_of_eventual_and_finite_patch`, and the concrete `J0 = 3` specialization `atkinson_shiftedInversePhaseCellPrefixBound_of_eventual_j3_and_j1_j2`. The newest direct attack tightens that again: `atkinson_shiftedInversePhaseCellPrefix_no_log_j3_of_rowIntegral_and_head`, `atkinson_shiftedInversePhaseCell_head_no_log_eventually`, and `atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_rowIntegral` now reduce the large-`j` side of the public leaf to a single eventual no-log row-tail theorem plus the already-explicit finite small-shift patch. |
| `AtkinsonShiftedCorrectionPrefixBoundHyp` | no longer required by the public boundary | still no concrete tracked source found | still needed internally by the older resolved layer, but now supplied only locally in `DeepSorries` | class declared in [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean) around line 14395; `DeepSorries.combined_atoms` now creates a local `letI` via `atkinson_shiftedCorrectionPrefixBound_of_inversePhaseCellPrefix` before calling `DeepBlockersResolved.combined_atoms_resolved_unconditional` |
| `SiegelSaddleExpansionHyp` | yes | no accepted global provider; explicit theorem/class debt | carried as a class requirement, not supplied by `AnalyticAxioms` | [`AnalyticAxioms.lean`](../../Aristotle/Standalone/AnalyticAxioms.lean) is now a no-provider stub. The old private axiom provider was removed from the public path on 2026-04-28. |
| `GabckePhaseCouplingHyp` | yes | conditional tracked theorem layer remains; no axiom-backed shortcut | depends on real upstream Siegel/Gabcke atoms | [`GabckePhaseCouplingHyp.lean`](../../Aristotle/Standalone/GabckePhaseCouplingHyp.lean) still contains the conditional bridge structure, but the old direct synthesis route through `AnalyticAxioms.lean` is no longer available. |
| `ShiftedRemainderSegmentBoundLargeTHyp` | yes | tracked providers exist | probably reachable only through lower-layer imports | [`ShiftedRemainderInterface.lean`](../../Development/ShiftedRemainderInterface.lean) defines the class; [`ZetaLogDerivBound.lean`](../../Aristotle/Standalone/ZetaLogDerivBound.lean) has concrete instances at lines 87 and 97 |
| `Littlewood.Development.HadamardProductZeta.SmallTPerronBoundHyp` | yes | no global instance visible from its defining module | namespace/provider mismatch | the active class is defined in [`HadamardProductZeta.lean`](../../Development/HadamardProductZeta.lean) line 616; direct `inferInstance` after importing that module fails. A different namespaced class/provider exists in [`ExplicitFormulaPsiB5aDefs.lean`](../../Aristotle/Standalone/ExplicitFormulaPsiB5aDefs.lean) lines 344 and 349 |
| `TruncatedExplicitFormulaPiHyp` | yes | tracked candidate instance exists | off-path or import-chain broken | [`RHPiUnconditionalExactSeedExistence.lean`](../../Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean) defines an instance at line 328, but direct `inferInstance` after importing that file still fails in the targeted audit |
| `PerronPiApproxCompatibilityHyp` | yes | conditional tracked bridges exist | conditional only | [`PerronExplicitFormulaProvider.lean`](../../Aristotle/Standalone/PerronExplicitFormulaProvider.lean) defines the class at line 1719 and bridges from `PiApproxAtFixedHeightOfPsiFormulaHyp` and `ExternalTruncatedPiWitnessPayload` at lines 1733 and 1743 |
| `InhomogeneousPhaseFitAbovePerronThresholdHyp` | yes | conditional tracked bridge exists | conditional only | class defined in [`PerronExplicitFormulaProvider.lean`](../../Aristotle/Standalone/PerronExplicitFormulaProvider.lean) line 2095; instance at line 2147 requires `TruncatedExplicitFormulaPiHyp` |
| `TargetTowerPhaseCouplingFamilyHyp_corrected` | yes | conditional tracked bridges exist | not globally available from public path | class defined in [`RHPiCorrectedCanonicalWitnessClasses.lean`](../../Aristotle/Standalone/RHPiCorrectedCanonicalWitnessClasses.lean) line 46; bridges at lines 57 and 77 |
| `AntiTargetTowerPhaseCouplingFamilyHyp_corrected` | yes | conditional tracked bridges exist | not globally available from public path | class defined in [`RHPiCorrectedCanonicalWitnessClasses.lean`](../../Aristotle/Standalone/RHPiCorrectedCanonicalWitnessClasses.lean) line 50; bridges at lines 66 and 88 |

## Immediate conclusions

1. The public API failure is a provider-reachability problem, not a theorem-axiom pollution problem.
2. Earlier prose claiming that several classes had "zero provider instances" was too loose.
3. The two corrected tower families are not zero-provider classes on tracked main; they have tracked conditional bridges.
4. The first real break is no longer the critical-zero provider itself.
   The sharper diagnosis now is:
   tracked provider code is reachable from the public path, and the first live
   missing provider leaf exposed by the trace is
   `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`.
5. The Atkinson family has now split more cleanly:
   - small-shift is closed on tracked main and synthesizes from `AtkinsonFormula` alone,
   - large-shift now synthesizes on the recovery path, but only through the
     direct-Abel wrapper and its single remaining `sorry`,
   - inverse-phase is no longer an independent leaf on the recovery branch: it
     reconstructs from small+large once large-shift is supplied,
   - a focused scratch probe importing only `AtkinsonFormula` plus
     `CorePrefixDirect` confirms that small-shift, large-shift, and
     inverse-core synthesize together, while both
     `AtkinsonShiftedInversePhaseCellPrefixBoundHyp` and
     `AtkinsonShiftedCorrectionPrefixBoundHyp` still fail,
   - so the remaining tracked theorem-content now sits at the cell-prefix /
     correction layer, with the separate direct-Abel remainder still the only
     literal Atkinson `sorry`.
6. The public/deep Atkinson leaf is now reduced more sharply than before:
   - the large-`j` side has been pushed down from a generic row-tail statement
     to the native complex shifted complete-block prefix form via
     `atkinsonWeightedShiftedCompleteBlockComplex_eq_rowIntegral` and
     `atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_completeBlockPrefix`,
   - so the remaining public-side obligations are now exactly:
     1. one eventual no-log complex shifted complete-block prefix theorem for
        `j ≥ 3`,
     2. the native `j = 1` patch,
     3. the native `j = 2` patch.
11. A focused de-pollution attempt on 2026-04-21 confirmed the Atkinson diagnosis without landing code:
    stripping only the obvious helper declarations was not enough. The still-trapped chain also runs through
    `atkinson_shift1_upperMinusLowerBoundaryTerm_eq_blockMode_two_minus_one`,
    `atkinson_shift1_upperBoundaryPrefix_bound_atomic_native`,
    `atkinson_shift1_upperBoundaryPrefix_bound_atomic_of_blockOmega_linear_model_upto_two_eventually`,
    `atkinson_shift1_boundaryPrefix_bound_atomic_local_of_upper_and_j1`, and
    `atkinson_inversePhaseCorePrefix_bound_j2_of_blockOmega_linear_model_upto_two_eventually_and_j1`.
6. The Hardy-class mismatch between `Schmidt.HardyCriticalLineZerosHyp` and
   `Aristotle.DirichletPhaseAlignment.HardyCriticalLineZerosHyp` is now repaired
   locally by [`HardyDirichletPhaseAlignmentWiring.lean`](../../Bridge/HardyDirichletPhaseAlignmentWiring.lean),
   and that file compiles.
7. Two non-circular local bridges now also compile:
   [`HardyMeanSquareAsymptoticWiring.lean`](../../Bridge/HardyMeanSquareAsymptoticWiring.lean)
   and
   [`ZetaMeanSquareHalfFromHardyAsymptotic.lean`](../../../../.recovery_artifacts/2026-04-21/banked/ZetaMeanSquareHalfFromHardyAsymptotic.lean).
8. Despite those bridges, [`MeanSquareBridge.lean`](../../Bridge/MeanSquareBridge.lean)
   still cannot synthesize `ZetaMeanSquareHalfBound` on the active path.
   So the first failure is not just "missing imports"; the non-circular B1 lane
   still lacks upstream provider supply.
9. After the 2026-04-28 de-axiom checkpoint, the upstream analytic supply gap is
   explicit theorem debt again. `SiegelSaddleExpansionHyp`, Hadamard zero-sum
   bounds, and the Perron contour decomposition are no longer supplied by
   `AnalyticAxioms.lean`.
10. `GabckePhaseCouplingHyp` remains a real conditional theorem layer fed by
    Siegel/Gabcke atoms; it is no longer considered closed by the removed
    analytic-axiom chain.
11. The public API still *reports* failure at `CriticalZeroSumDivergesHyp`, but
    that is now only the outer class. A direct synthesis trace shows the live
    path is:
    `CriticalZeroSumDivergesHyp`
    → `Aristotle.DirichletPhaseAlignment.HardyCriticalLineZerosHyp`
    → `Schmidt.HardyCriticalLineZerosHyp`
    → `AtkinsonShiftedInversePhaseCorePrefixBoundHyp`
    → `AtkinsonSmallShiftPrefixBoundHyp`
    → `AtkinsonLargeShiftPrefixBoundHyp`
    → `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`.
12. So the first honest tracked-main public-path leaf is now
    the Atkinson inverse-phase-cell / correction theorem layer, not the critical-zero
    class itself.
13. The deep/public theorem signatures have now been cleaned to reflect that:
    they no longer quantify explicitly over small-shift, large-shift,
    inverse-core, or correction-prefix.

## Atkinson internal closure axis

This is not itself a public theorem signature obligation, but it is now the
sharpest internal tracked-main frontier inside
[`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean):

- `AtkinsonSmallShiftPrefixBoundHyp` synthesizes from the module alone.
- `AtkinsonLargeShiftPrefixBoundHyp` is now reached on the active recovery path
  through `CorePrefixDirect`.
- `AtkinsonShiftedInversePhaseCorePrefixBoundHyp` now synthesizes on the active
  recovery path.
- the remaining active provider failures are:
  - `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`
  - `AtkinsonShiftedCorrectionPrefixBoundHyp`

So the current Atkinson closure problem is no longer broad provider fog. The
remaining theorem-content sits at the cell-prefix / correction layer, while the
honest large-shift debt has collapsed to the single direct-Abel remainder
theorem inside
[`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean).

## 2026-04-26 sidecar update

- The Aristotle sidecar for the large-`j` public theorem completed with errors
  and did **not** solve the live public target
  `atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_completeBlockPrefix`.
- It did return one usable reduction on the **separate cleanup lane**, and that
  reduction has now been transplanted and validated locally:
  - new isolated helper in
    [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean):
    `atkinson_inversePhaseCorePrefix_bound_large_j`
  - `atkinson_largeShiftWeightedBoundarySum_bound` is now proved from that
    helper plus the existing `j = 1` head-core bound
- Validation after transplant:
  - direct `lean Littlewood/Aristotle/Standalone/AtkinsonFormula.lean`
  - `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`
- Therefore the active public frontier is unchanged, but the cleanup lane is
  sharper:
  - public leaf still: `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`
  - live large-`j` theorem under it still:
    `atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_completeBlockPrefix`
  - separate non-public cleanup leaf is now:
    `atkinson_inversePhaseCorePrefix_bound_large_j`
