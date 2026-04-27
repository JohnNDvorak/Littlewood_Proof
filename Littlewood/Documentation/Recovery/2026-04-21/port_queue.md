# Littlewood Port Queue

Date: 2026-04-21
Branch: `recovery/provider-forensics-2026-04-21`

No files have been ported yet. This queue is ordered by leverage, not by convenience.

| Priority | Candidate | Source of truth | Why it matters | Current status |
| --- | --- | --- | --- | --- |
| 1 | `Littlewood/Aristotle/DeepSorries.lean` | tracked history first, CloudDocs committed objects later if needed | central consolidated theorem path; regression boundary visible here | pending targeted diff |
| 2 | `Littlewood/Main/LittlewoodPsi.lean` | tracked history first | public theorem signature regression and class propagation | pending targeted diff |
| 3 | `Littlewood/Main/LittlewoodPi.lean` | tracked history first | public theorem signature and public invocation target | pending targeted diff |
| 4 | `Littlewood/Bridge/LandauOscillation.lean` | tracked history first | main-path bridge that currently claims to bypass false `TruncatedExplicitFormulaPiHyp` while still carrying the 15-class surface | pending targeted diff |
| 5 | `Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean` | tracked history first | closest tracked blocker graph to the older near-closure story | pending targeted diff |
| 6 | `Littlewood/Aristotle/Standalone/CriticalZeroSumDiverges.lean` | tracked main | first missing public-path class has a tracked provider candidate here | pending import-path audit |
| 6.5 | `Littlewood/Bridge/HardyCriticalLineZerosFromStandalone.lean` | recovery branch tracked file | new non-circular Hardy provider path for the critical-zero lane | builds green; public path now reaches the critical-zero provider through this file |
| 7 | `Littlewood/Bridge/HardyDirichletPhaseAlignmentWiring.lean` | local tracked-main recovery branch | compiled mismatch repair for Hardy-zero classes; evidence that the first failure is not purely theorem-level | compiled locally; not yet imported into public path |
| 8 | `Littlewood/Bridge/HardyMeanSquareAsymptoticWiring.lean` | local tracked-main recovery branch | compiled non-circular B1 bridge from the tracked theorem package | compiled locally; no public-path effect yet |
| 9 | `.recovery_artifacts/2026-04-21/banked/ZetaMeanSquareHalfFromHardyAsymptotic.lean` | banked local recovery artifact | compiled bridge from B1 package to `ZetaMeanSquareHalfBound` | quarantined off-path; `MeanSquareBridge` still lacks upstream supply |
| 10 | `Littlewood/Aristotle/Standalone/ExternalPort/B5bPayloadAutoInstances.lean` | tracked main | carries payload auto-instances for the first two public-path classes | pending import-path audit |
| 11 | `Littlewood/Aristotle/Standalone/AtkinsonFormula.lean` | tracked main | likely upstream blocker for non-circular B1; small-shift route exists but is trapped behind private / section-polluted helpers, while inverse and correction still lack honest public providers | pending targeted helper cleanup audit |
| 12 | `Littlewood/Aristotle/Standalone/GabckePhaseCouplingHyp.lean` | tracked main | provider chain is real but off-path; evidence says this is no longer the root blocker for B1 | import-path evidence gathered; no immediate port needed |
| 13 | `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean` | tracked main | defines conditional bridges for the Perron / inhomogeneous / tower family | pending bridge audit |
| 14 | `Littlewood/Aristotle/Standalone/RHPiCorrectedCanonicalWitnessClasses.lean` | tracked main | corrects the earlier false "zero provider" claim for the tower classes | pending bridge audit |
| 15 | `Littlewood/Aristotle/Standalone/AnalyticAxioms.lean` | tracked main | confirms the named private axiom for `SiegelSaddleExpansionHyp` | evidence only |
| 16 | `Littlewood/Development/HadamardProductZeta.lean` | tracked main | active-path class definition for `SmallTPerronBoundHyp`; currently no direct global provider under direct import | pending namespace/provider audit |
| 17 | `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean` | tracked main | contains a tracked candidate instance for `TruncatedExplicitFormulaPiHyp` that is not yet reachable by minimal import | pending reachability audit |
| 18 | `Littlewood/ZetaZeros/PairedFarZeroCancellationBridge.lean` | recovered local file | evidence only until mapped to an active class | not eligible for port yet |
| 19 | `Littlewood/Bridge/ContourRemainderMultLeaf.lean` | recovered local file | evidence only until mapped to an active class | not eligible for port yet |
| 20 | `Littlewood/ZetaZeros/ZeroAvoidingHeight.lean` | recovered local file | evidence only until mapped to an active class | not eligible for port yet |

## Port rules

- No CloudDocs working-tree copy.
- No early commit of the three recovered local files.
- No blind merge from CloudDocs.
- Each future port must name:
  - class or blocker discharged
  - validation command
  - rollback path

## Immediate tracked-main next moves

### Critical-zero lane

This lane has now advanced.

- `CriticalAssumptions.lean` imports the tracked
  `CriticalZeroSumDiverges.lean` provider.
- The Hardy prerequisite is now routed through
  [`HardyCriticalLineZerosFromStandalone.lean`](../../Bridge/HardyCriticalLineZerosFromStandalone.lean)
  instead of the old direct circular path.
- `trace.Meta.synthInstance` confirms the live public path is now:
  `CriticalZeroSumDivergesHyp`
  → `Aristotle.DirichletPhaseAlignment.HardyCriticalLineZerosHyp`
  → `Schmidt.HardyCriticalLineZerosHyp`
  → `AtkinsonShiftedInversePhaseCorePrefixBoundHyp`
  → `AtkinsonLargeShiftPrefixBoundHyp`.

So do **not** spend the next pass on the critical-zero class itself. The public
path now reaches it. The next honest public-path provider leaf is now
`AtkinsonShiftedInversePhaseCellPrefixBoundHyp`, with correction-prefix kept as
an internal equivalent package.

Latest reduction:

- `DeepSorries`, `LittlewoodPsi`, `LittlewoodPi`, `HardyCriticalLineZerosDirect`,
  `SmoothedExplicitFormula`, `LandauContradiction`, `LandauLittlewood`, and
  `LandauMellinContradiction` have all been reduced to the same declaration
  boundary.
- So the next tracked-main pass should not spend time re-removing
  small-shift/large-shift/inverse-core/correction from public signatures.
  That cleanup is done.
- The next honest public/deep theorem leaf is now exactly:
  `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`.

### Atkinson lane

Before any CloudDocs work, inspect these helper declarations in
[`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean):

- `atkinson_shift1_lowerBoundaryPrefix_bound_atomic_of_j1`
- `atkinson_shift1_upperMinusLowerBoundaryTerm_eq_blockMode_two_minus_one`
- `atkinson_shift1_upperBoundaryPrefix_bound_atomic_native`
- `atkinson_shift1_upperBoundaryPrefix_bound_atomic_of_blockOmega_linear_model_upto_two_eventually`
- `atkinson_shift1_boundaryPrefix_bound_atomic_local_of_upper_and_j1`
- `atkinson_j2_kernelWeighted_j1_headCore_bound_of_j1`
- `atkinson_inversePhaseCorePrefix_bound_j2_of_blockOmega_linear_model_upto_two_eventually_and_j1`
- `atkinson_smallShiftPrefixBound_of_native_j1_and_upper`
- `atkinson_smallShiftPrefixBound_of_native_j1_and_blockOmega_linear_model_upto_two_eventually`

The current evidence says the first tracked repair opportunity is to remove
ambient section-variable pollution from that small-shift helper chain and only
then retry public exposure. Do not touch CloudDocs or the April-20 local files
until that audit is complete.

Latest refinement from the 2026-04-21 source-theorem pass:

- The obstruction is not confined to the later `j2` convenience wrappers.
- A direct source-level `omit` pass reduced the failure surface, but the native
  upper-bound chain still leaked `AtkinsonShiftedInversePhaseCorePrefixBoundHyp`.
- The sharpest remaining native choke points are now:
  - `atkinson_shift1_lowerBoundaryPrefix_bound_atomic_of_j1`
  - `atkinson_shift1_upperBoundaryPrefix_bound_atomic_native`
  - `atkinson_shift1_boundaryPrefix_bound_atomic_local_of_upper_and_j1`
- So the next tracked-main pass should start **there**, not at the later
  `atkinson_inversePhaseCorePrefix_bound_j2_*` packaging layer.

One level earlier still:

- The first declaration that needs honest rework is
  `atkinson_smallShiftPrefixBound_of_native_j1_j2` at line `8123`.
- It sits before the later class declarations and under an attached doc-comment
  shape, so "just add `omit`" is not mechanically clean there.
- That means the next tracked-main attempt should likely introduce a **fresh
  re-stated small-shift theorem** in a cleaner location, then wire later
  wrappers to that theorem instead of trying to mutate the original declaration
  in place.

Latest refinement:

- Even that clean re-statement still failed immediately on the first call to
  `atkinson_shiftedInversePhaseCorePrefix_bound_shifted_of_native_fixedShift`
  at line `7982`.
- So the next honest tracked-main target has moved one level earlier again:
  the fixed-shift transport theorem itself is carrying the
  `AtkinsonShiftedInversePhaseCorePrefixBoundHyp` pollution.
- The next pass should begin at line `7982`, not at `8123` and not at the
  12k-line wrappers.

Concrete source fact:

- Line `7982` is still inside the live scope introduced by
  `variable [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]` at line `7186`.
- So the next repair is likely structural, not just proof-local:
  restate/move the `7982` transport theorem outside that section, or apply
  `omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in` at that theorem
  itself and then repair any genuine downstream dependencies exposed there.

Latest refinement from the helper-chain export attempt:

- There is already a theorem-level small-shift closure route on tracked main:
  `atkinson_smallShiftPrefixBound_of_native_j1_and_blockOmega_linear_model_upto_two_eventually`.
- The attempt to expose it as a real zero-input instance showed that the real
  blocker is the polluted support chain underneath it, not the theorem-level
  argument itself.
- The first support lemmas exposed by that attempt were:
  - `atkinsonResonantShiftedBoundaryTerm_norm_le`
  - `atkinsonBoundary_jMinusOne_le`
  - `atkinson_j2_kernelWeighted_j1_headCore_bound_of_j1`
  - `atkinson_shift1_lowerBoundaryPrefix_bound_atomic_of_j1`
- Therefore the next tracked-main pass should choose one of two clean tactics:
  1. **bottom-up de-pollution** from those low-level support lemmas upward, or
  2. **clean duplicate chain**: restate the small-shift route in a fresh scope
     and avoid the polluted in-place declarations entirely.
- The repo has been restored to the last green state after this diagnosis, so
  future work should start from the current file, not from the reverted
  experimental variants.

Current choice:

- We are now actively on the **clean duplicate chain** path.
- Validated clean duplicates already in `AtkinsonFormula.lean`:
  - `atkinsonUpperBoundaryTerm_norm_clean`
  - `atkinsonResonantShiftedBoundaryTerm_norm_le_clean`
  - `atkinsonBoundary_jMinusOne_le_clean`
  - `atkinson_j2_kernelWeighted_j1_headCore_bound_of_j1_clean`
  - `atkinson_shift1_lowerBoundaryPrefix_bound_atomic_of_j1_clean`
  - `atkinson_shift1_upperBoundaryTerm_eq_blockMode_two_clean`
  - `atkinson_shift1_lowerBoundaryTerm_eq_blockMode_one_clean`
  - `atkinson_shift1_upperMinusLowerBoundaryTerm_eq_blockMode_two_minus_one_clean`
- These are not wrapper aliases. The copied proofs compile under the new `omit`
  scopes, which means the detachment is theorem-level, not cosmetic.

Latest landed tracked-main closure work:

1. `atkinson_shift1_upperBoundaryPrefix_bound_atomic_native_clean`
2. `atkinson_shift1_boundaryPrefix_bound_atomic_local_of_upper_and_j1_clean`
3. `atkinson_j2_kernelWeighted_boundaryGap_bound_local_of_upper_and_j1_clean`
4. `atkinson_inversePhaseCorePrefix_bound_j2_of_upper_and_j1_clean`
5. `atkinson_smallShiftPrefixBound_of_native_j1_j2_clean`
6. `atkinson_smallShiftPrefixBound_of_native_j1_and_upper_clean`
7. `atkinson_smallShiftPrefixBound_of_native_j1_and_blockOmega_linear_model_upto_two_eventually_clean`
8. `instAtkinsonSmallShiftPrefixBoundHyp`

This queue item is complete:

- `#synth Aristotle.Standalone.AtkinsonFormula.AtkinsonSmallShiftPrefixBoundHyp`
  now succeeds after importing only `AtkinsonFormula`.

Immediate next tracked-main targets in order:

1. Branch health is no longer the blocker:
   - direct `lean` on `AtkinsonFormula.lean` is green again
   - focused `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula` is
     green again
   - so the next pass should not spend time on parser/elaboration cleanup
     unless a new hard error appears
2. Stay on the Atkinson inverse-phase-cell / correction layer:
   - the recovery branch now weakens both
     `HardyMeanSquareAsymptoticWiring.lean`
     and
     `HardyCriticalLineZerosFromStandalone.lean`
     to depend on
     `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`
   - after the public-boundary cleanup, the active public-path trace now
     honestly bottoms out there
   - `AtkinsonShiftedCorrectionPrefixBoundHyp` remains theorem-equivalent and
     internally needed by `DeepBlockersResolved`, but it is no longer the
     public boundary class
3. Keep the direct-Abel large-shift debt in scope, but do not treat
   `CorePrefixDirect.lean` as the active frontier file:
   - `AtkinsonLargeShiftPrefixBoundHyp` is now reached on the active path via
     `CorePrefixDirect.instAtkinsonLargeShiftPrefixBoundHyp`
   - `CorePrefixDirect.lean` itself is only a thin wrapper
   - the real remaining large-shift theorem-content is
     `atkinson_largeShiftBoundaryAbelRemainder_bound`
     in [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean)
   - exported dependency remains:
     `atkinson_kernelWeightedNextShift_abel_bound_of_shiftedInversePhaseCore`

Latest refinement:

- The public/deep Atkinson leaf has now been reduced again inside
  [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean):
  - `atkinsonWeightedShiftedCompleteBlockComplex_eq_rowIntegral`
  - `atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_completeBlockPrefix`
- So the next honest work order is now:
  1. prove the eventual no-log complex shifted complete-block prefix theorem
     for `j ≥ 3`,
  2. discharge the native `j = 1` patch,
  3. discharge the native `j = 2` patch,
  4. package `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`,
  5. rerun the strict minimal-import public probe,
  6. only then return to the separate cleanup leaf
     `atkinson_largeShiftWeightedBoundarySum_bound`.
   - but large-shift is no longer the first active provider failure
4. Treat inverse-phase as repaired on the active recovery path:
   - small-shift synthesizes from `AtkinsonFormula`
   - large-shift is supplied from `CorePrefixDirect`
   - inverse-core then synthesizes automatically
5. The newest tracked theorem packaging now makes the next cell-prefix target
   fully explicit:
   - `atkinson_shiftedInversePhaseCellPrefixBound_of_no_log` shows that a
     stronger no-log inverse-phase cell-prefix estimate is sufficient to close
     the public class `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`
   - `atkinson_shiftedInversePhaseCellPrefix_no_log_of_eventual_and_finite_patch`
     and
     `atkinson_shiftedInversePhaseCellPrefixBound_of_eventual_and_finite_patch`
     now reduce that stronger target one step further: it is enough to prove an
     eventual large-`j` no-log estimate and then patch the finitely many small
     shifts
   - `atkinson_shiftedInversePhaseCellPrefixBound_of_eventual_j3_and_j1_j2`
     now makes that finite patch concrete: the live public leaf is exactly one
     large-`j` theorem for `j ≥ 3` plus two native patches at `j = 1, 2`
    - the newest direct reduction now sharpens the large-`j` side again:
      `atkinson_shiftedInversePhaseCellPrefix_no_log_j3_of_rowIntegral_and_head`,
      `atkinson_shiftedInversePhaseCell_head_no_log_eventually`, and
      `atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_rowIntegral`
      reduce the remaining large-`j` work to one eventual row-tail theorem
      inside `AtkinsonFormula.lean`
    - so the next honest closure-axis target is no longer “some provider for
      inverse-phase-cell”; it is the exact eventual no-log row-tail theorem
      plus the explicit finite small-shift patch already isolated in
      `AtkinsonFormula.lean`
5. In parallel, keep the focused large-shift rebuild fact in view:
   - forcing a rebuild of `AtkinsonFormula.lean` now surfaces the live file
     blocker directly at
     `atkinson_largeShiftWeightedBoundarySum_bound`
   - the subordinate helper
     `atkinson_largeShiftBoundaryAbelRemainder_bound_of_largeShiftPrefix`
     is now proved and the file builds past it
   - the branch now also has the exact structural reductions
     `atkinson_largeShiftBoundaryAbelRemainder_eq_weightedBoundarySum` and
     `atkinson_largeShiftWeightedBoundarySum_eq_prefix_sub_headCore`, so the
     wrapper has been collapsed to the single weighted boundary sum it still
     needs to bound, with that sum exposed directly as
     `large-shift prefix - j1 headcore`
   - `atkinson_largeShiftBoundaryAbelRemainder_bound` is now only a reduction
     from that sharper weighted-boundary statement
   - that weighted-boundary theorem is now the only literal Atkinson `sorry`
     in tracked code
   - it remains the separate direct-Abel debt below the large-shift wrapper,
     not the active public inverse-phase-cell / correction frontier
   - current source evidence does not support bypassing it through
     `atkinson_largeShiftPrefixBound_atomic_of_nextShift`: that induction needs
     a contraction `γ < 1`, while the only tracked successor-tail input still
     has factor `8`
5. New local priority inside
   [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean):
   - first decide whether the existing tracked material can package
     `AtkinsonShiftedInversePhaseCellPrefixBoundHyp` directly,
   - only use the restored oscillatory lemmas
     (`atkinsonShiftedPacketPhase_integral_bound`,
     `atkinsonWeightedResonantBlockMode_deriv_bound_eventually`,
     `atkinsonShiftedSinglePrimitive_norm_bound`)
     when they explicitly feed that exact field,
   - do not detour into weighted-complete-block theorems that are already
     downstream of `AtkinsonShiftedCorrectionPrefixBoundHyp`.
6. Latest evidence from the focused probe:
   - importing only `AtkinsonFormula` plus `CorePrefixDirect`,
     `#synth AtkinsonSmallShiftPrefixBoundHyp`,
     `#synth AtkinsonLargeShiftPrefixBoundHyp`, and
     `#synth AtkinsonShiftedInversePhaseCorePrefixBoundHyp` all succeed,
   - `#synth AtkinsonShiftedInversePhaseCellPrefixBoundHyp` still fails,
   - `#synth AtkinsonShiftedCorrectionPrefixBoundHyp` still fails,
   - so the next pass should treat inverse-phase-cell as the true tracked leaf
     unless a direct theorem route appears inside `AtkinsonFormula`.

Latest large-shift hygiene result:

- A direct attempt to isolate the Abel remainder in
  [`CorePrefixDirect.lean`](../../Aristotle/Standalone/CorePrefixDirect.lean)
  from outside `AtkinsonFormula` failed structurally:
  the needed kernel/phase/boundary pieces are private to
  `AtkinsonFormula.lean`.
- That experiment was reverted and the file was restored to its last green
  tracked state.
- The stable follow-up was to export the exact next-shift Abel bridge as the
  public theorem
  `atkinson_kernelWeightedNextShift_abel_bound_of_shiftedInversePhaseCore`.
- So the next honest large-shift work should happen either:
  1. inside `AtkinsonFormula.lean`, where the private kernel language is
     available, or
  2. in `CorePrefixDirect.lean`, but only through exported
     theorems/classes, not by spelling private Atkinson internals directly.

Current sub-queue inside the correction lane:

1. Treat the new theorem
   `atkinson_shiftedCorrectionPrefixBound_of_inversePhaseCellPrefix`
   as a structural cleanup, not closure:
   - it shows correction-prefix is recoverable from inverse-phase-cell-prefix
     plus the boundary packet,
   - it is deliberately **not** an instance, to avoid a typeclass loop with the
     existing reverse bridge.
   - the matching downstream corollary
     `mainTerm_first_moment_sqrt_of_inversePhaseCellPrefix`
     is now also present, so the remaining Atkinson assumption surface is
     explicit end-to-end.
2. Re-open the missing route to
   `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`:
   - either find a tracked-main bridge from the reconstructed
     `AtkinsonShiftedInversePhaseCorePrefixBoundHyp`,
   - or prove directly that no such tracked bridge exists.
3. Treat correction and inverse-phase-cell as the same remaining theorem layer
   for planning purposes:
   - correction -> cell already exists as an instance,
   - cell -> correction already exists as a theorem,
   - so whichever one closes first should immediately collapse the other.

Validation rule for this queue:

- after each clean duplicate or clean assembly theorem:
  - `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`
- do not replace the original polluted declarations yet
- do not touch CloudDocs while this tracked-main duplicate chain is still
  climbing successfully

## 2026-04-26 queue update

1. Keep the public target fixed:
   `atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_completeBlockPrefix`
   remains the next theorem to prove in
   [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean).
2. Treat the separate large-shift cleanup lane as sharpened:
   - `atkinson_largeShiftWeightedBoundarySum_bound` is no longer the cleanup
     leaf,
   - the cleanup leaf is now
     `atkinson_inversePhaseCorePrefix_bound_large_j`.
3. Do not spend another Aristotle ticket on the old weighted-boundary wrapper.
   The previous sidecar already showed that route only yields off-path cleanup
   reductions.
