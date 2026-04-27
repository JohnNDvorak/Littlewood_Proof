# Post-Port Ledger

Date: 2026-04-21
Branch: `recovery/provider-forensics-2026-04-21`

## Baseline

- No recovery ports have been applied yet.
- The three recovered Session-46 files remain untracked evidence objects:
  - `Littlewood/Bridge/ContourRemainderMultLeaf.lean`
  - `Littlewood/ZetaZeros/PairedFarZeroCancellationBridge.lean`
  - `Littlewood/ZetaZeros/ZeroAvoidingHeight.lean`
- Public minimal-import invocation still fails on:
  `CriticalZeroSumDivergesHyp`.

## Latest tracked-main public-path recovery

- Added tracked bridge:
  - `Littlewood/Bridge/HardyCriticalLineZerosFromStandalone.lean`
- Updated tracked public-path assumptions:
  - `Littlewood/CriticalAssumptions.lean`
    - swapped in `HardyCriticalLineZerosFromStandalone`
    - added import of `Aristotle/Standalone/CriticalZeroSumDiverges.lean`
- Focused validation:
  - `lake build Littlewood.Bridge.HardyCriticalLineZerosFromStandalone` — green
  - `lake build Littlewood.CriticalAssumptions` — green
  - `lake build Littlewood.Main.LittlewoodPsi` — green

Public minimal-import invocation still reports:

- `CriticalZeroSumDivergesHyp`

but the direct synthesis trace now reaches the tracked provider and then fails
later at:

- `AtkinsonLargeShiftPrefixBoundHyp`

So this pass changed the public-path diagnosis materially:

1. `CriticalZeroSumDivergesHyp` is now on a live tracked provider path.
2. The first honest public-path theorem/provider leaf exposed by that path is
   no longer critical-zero itself.
3. The next tracked-main work should stay on:
   - `CorePrefixDirect.lean`
   - the Atkinson cell-prefix / correction layer in `AtkinsonFormula.lean`

## Latest tracked-main dependency reduction

- Updated tracked theorem/provider files:
  - `Littlewood/Aristotle/Standalone/AtkinsonFormula.lean`
    - made `atkinson_shiftedCorrectionPrefixBound_of_inversePhaseCellPrefix`
      public
  - `Littlewood/Bridge/HardyMeanSquareAsymptoticWiring.lean`
    - reduced the bridge to depend on
      `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`
    - synthesizes `AtkinsonShiftedCorrectionPrefixBoundHyp` only locally
  - `Littlewood/Bridge/HardyCriticalLineZerosFromStandalone.lean`
    - reduced the bridge to depend on
      `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`
    - derives the main-term first-moment class directly from
      `mainTerm_first_moment_sqrt_of_inversePhaseCellPrefix`
    - synthesizes `AtkinsonShiftedCorrectionPrefixBoundHyp` only locally for
      the RS block-sign bridge

Focused validation:

- `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula` — green
- `lake build Littlewood.Bridge.HardyMeanSquareAsymptoticWiring` — green
- `lake build Littlewood.Bridge.HardyCriticalLineZerosFromStandalone` — green

Updated strict trace:

- the public minimal-import invocation still reports the outer failure as
  `CriticalZeroSumDivergesHyp`
- but `trace.Meta.synthInstance` now shows the active recovery path reaches:
  - `AtkinsonSmallShiftPrefixBoundHyp`
  - `AtkinsonLargeShiftPrefixBoundHyp`
  - `AtkinsonShiftedInversePhaseCorePrefixBoundHyp`
  - and now honestly bottoms out at
    `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`

Current honest frontier:

1. The public-path provider frontier is now the Atkinson inverse-phase-cell / correction theorem layer.
2. `CorePrefixDirect` is no longer the first *provider* break on the active
   recovery path.
3. `CorePrefixDirect` still remains theorem-content debt, because the active
   large-shift route is not yet the pre-crash fully closed one.

## Latest public-boundary reduction

- Updated tracked public-surface files:
  - `Littlewood/Aristotle/DeepSorries.lean`
  - `Littlewood/Bridge/LandauOscillation.lean`
  - `Littlewood/Main/LittlewoodPsi.lean`
  - `Littlewood/Main/LittlewoodPi.lean`
  - `Littlewood/Bridge/HardyCriticalLineZerosDirect.lean`
- Removed the global theorem-to-instance hop
  `AtkinsonShiftedCorrectionPrefixBoundHyp -> AtkinsonShiftedInversePhaseCellPrefixBoundHyp`
  from `AtkinsonFormula.lean`, replacing it with a theorem-only bridge:
  `atkinson_shiftedInversePhaseCellPrefixBound_of_shiftedCorrectionPrefix`
- Kept the older `DeepBlockersResolved` layer intact, but supplied
  `AtkinsonShiftedCorrectionPrefixBoundHyp` only locally inside
  `DeepSorries.combined_atoms` via
  `atkinson_shiftedCorrectionPrefixBound_of_inversePhaseCellPrefix`

Focused validation:

- `lake build Littlewood.Aristotle.DeepSorries` — green

What changed:

1. The public boundary now asks only for
   `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`, which matches the live
   recovery-path trace.
2. `AtkinsonShiftedCorrectionPrefixBoundHyp` is no longer silently reintroduced
   by a global instance during strict synthesis.
3. The internal older resolved path still uses correction-prefix, but only
   behind a local `letI` at the `DeepSorries` boundary.

## Latest tracked-main large-shift recovery

- Exported a new tracked theorem from
  [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean):
  `atkinson_kernelWeightedNextShift_abel_bound_of_shiftedInversePhaseCore`
- Focused validation:
  - `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula` — green
  - `lake build Littlewood.Aristotle.Standalone.CorePrefixDirect` — green

What changed:

1. The exact next-shift Abel bridge is now available through a public theorem
   rather than only as a private local declaration inside `AtkinsonFormula`.
2. A direct refactor attempt in `CorePrefixDirect.lean` showed that the file
   cannot safely talk about Atkinson's private kernel primitives from outside
   `AtkinsonFormula`.
3. That experiment was backed out, and `CorePrefixDirect.lean` was restored to
   its last green tracked state.

Current stable diagnosis:

- `CorePrefixDirect.lean` still contains the live tracked `sorry` in
  `atkinsonLargeShiftPrefixBound_direct`.
- The next exported large-shift dependency is now explicit:
  `atkinson_kernelWeightedNextShift_abel_bound_of_shiftedInversePhaseCore`.
- No public-surface change came from this pass; the strict minimal-import
  failure still ultimately bottoms out at Atkinson large-shift.

## Latest deep/public signature cleanup

- Updated tracked files:
  - `Littlewood/Aristotle/DeepSorries.lean`
  - `Littlewood/Main/LittlewoodPsi.lean`
  - `Littlewood/Main/LittlewoodPi.lean`
  - `Littlewood/Bridge/HardyCriticalLineZerosDirect.lean`
  - `Littlewood/Aristotle/SmoothedExplicitFormula.lean`
  - `Littlewood/Aristotle/LandauContradiction.lean`
  - `Littlewood/Aristotle/LandauLittlewood.lean`
  - `Littlewood/Aristotle/LandauMellinContradiction.lean`

What changed:

1. `DeepSorries` now imports `CorePrefixDirect` and no longer explicitly asks
   for:
   - `AtkinsonSmallShiftPrefixBoundHyp`
   - `AtkinsonLargeShiftPrefixBoundHyp`
   - `AtkinsonShiftedInversePhaseCorePrefixBoundHyp`
2. The Landau contradiction forwarding stack now uses
   `AtkinsonShiftedInversePhaseCellPrefixBoundHyp` instead of the older
   correction-prefix boundary.
3. The public theorem files and `HardyCriticalLineZerosDirect` now match that
   same declaration surface.

Direct check result:

- `@Aristotle.DeepSorries.psi_full_strength_oscillation` now quantifies first
  over `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`, then the later analytic
  classes, then `CriticalZeroSumDivergesHyp` and
  `PhaseAlignmentToTargetHyp`.
- `@Aristotle.DeepSorries.pi_li_full_strength_oscillation` matches the same
  reduced Atkinson boundary.

Focused validation:

- `lake build Littlewood.Aristotle.DeepSorries` — green
- `lake build Littlewood.Aristotle.SmoothedExplicitFormula` — green
- `lake build Littlewood.Aristotle.LandauContradiction` — green
- `lake build Littlewood.Aristotle.LandauLittlewood` — green
- `lake build Littlewood.Aristotle.LandauMellinContradiction` — green
- `lake build Littlewood.Main.LittlewoodPsi` — green
- `lake build Littlewood.Main.LittlewoodPi` — green

Current honest frontier after this pass:

1. The strict public error still surfaces first as `CriticalZeroSumDivergesHyp`.
2. The deep/public theorem signatures no longer overstate small-shift,
   large-shift, inverse-core, or correction-prefix.
3. The first explicit Atkinson theorem-content requirement on the deep/public
   boundary is now `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`.

## Latest Atkinson leaf classification

Focused scratch probe:

- imports:
  - `Littlewood.Aristotle.Standalone.AtkinsonFormula`
  - `Littlewood.Aristotle.Standalone.CorePrefixDirect`
- direct synthesis result:
  - `#synth AtkinsonSmallShiftPrefixBoundHyp` — succeeds
  - `#synth AtkinsonLargeShiftPrefixBoundHyp` — succeeds
  - `#synth AtkinsonShiftedInversePhaseCorePrefixBoundHyp` — succeeds
  - `#synth AtkinsonShiftedInversePhaseCellPrefixBoundHyp` — fails
  - `#synth AtkinsonShiftedCorrectionPrefixBoundHyp` — fails

What this changes:

1. `CorePrefixDirect.lean` is no longer its own skeleton file. It is now only a
   direct wrapper around `atkinson_largeShiftPrefixBound_of_direct_abel`.
2. The only literal tracked `sorry` still living in the Atkinson lane is now:
   - `atkinson_largeShiftBoundaryAbelRemainder_bound`
3. The public/deep inverse-phase-cell leaf is now reduced more explicitly than
   before:
   - `atkinsonWeightedShiftedCompleteBlockComplex_eq_rowIntegral`
   - `atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_completeBlockPrefix`
   - `atkinson_shiftedInversePhaseCellPrefixBound_of_eventual_j3_and_j1_j2`
   together show that the remaining public-side work is exactly:
   - one eventual no-log complex shifted complete-block prefix theorem for
     `j ≥ 3`
   - one native `j = 1` patch
   - one native `j = 2` patch

## Latest large-`j` public-leaf reduction

- Updated tracked file:
  - `Littlewood/Aristotle/Standalone/AtkinsonFormula.lean`

What changed:

1. Added `atkinsonWeightedShiftedCompleteBlockComplex_eq_rowIntegral`, which
   factors the repeated equality between the native complex shifted
   complete-block integral and the resonant row-integral form.
2. Added
   `atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_completeBlockPrefix`,
   which replaces the old row-tail wrapper leaf with the cleaner native
   complete-block prefix leaf.
3. Validation is green again:
   - direct `lean Littlewood/Aristotle/Standalone/AtkinsonFormula.lean`
   - `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`

Current honest frontier after this pass:

1. The public/deep Atkinson leaf is still
   `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`.
2. Its remaining large-`j` content is now exactly an eventual no-log complex
   shifted complete-block prefix theorem.
3. The finite small-shift side is now explicitly isolated to the native
   `j = 1, 2` patches.
4. The separate large-shift cleanup leaf remains
   `atkinson_largeShiftWeightedBoundarySum_bound`; it is no longer the first
   public-path blocker.

## Latest branch-health certification

- Fixed a parser regression in
  [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean)
  caused by a doc comment sitting directly before `omit ... in theorem`.
- Fixed two hidden unused
  `AtkinsonLargeShiftPrefixBoundHyp` dependencies in the large-shift wrapper
  section so the file no longer fails elaboration there.

Validation:

- direct `lean Littlewood/Aristotle/Standalone/AtkinsonFormula.lean` — green
- `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula` — green

Current honest status after certification:

1. The branch is healthy again.
2. The remaining proof work is now cleanly split:
   - large-shift cleanup leaf:
     `atkinson_largeShiftWeightedBoundarySum_bound`
   - public/deep Atkinson leaf:
     `AtkinsonShiftedInversePhaseCellPrefixBoundHyp` via
     `atkinson_shiftedInversePhaseCellPrefixBound_of_no_log`
3. No CloudDocs or evidence-file recovery is needed for the next pass.

## Latest no-log packaging cleanup

- Updated tracked file:
  - `Littlewood/Aristotle/Standalone/AtkinsonFormula.lean`
- Added theorem:
  - `atkinson_shiftedInversePhaseCellPrefixBound_of_no_log`
  - `atkinson_shiftedInversePhaseCellPrefix_no_log_of_eventual_and_finite_patch`
  - `atkinson_shiftedInversePhaseCellPrefixBound_of_eventual_and_finite_patch`
  - `atkinson_shiftedInversePhaseCellPrefixBound_of_eventual_j3_and_j1_j2`

What changed:

1. The expensive unused fixed-`j` weighted cell-prefix experiment was removed.
   It was not on the active provider path and was not worth the compile cost.

## Latest large-`j` no-log direct reduction

- Updated tracked file:
  - `Littlewood/Aristotle/Standalone/AtkinsonFormula.lean`
- Added reduction theorems:
  - `atkinson_shiftedInversePhaseCellPrefix_no_log_j3_of_rowIntegral_and_head`
  - `atkinson_shiftedInversePhaseCell_head_no_log_eventually`
  - `atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_rowIntegral`
- Validation:
  - direct `lean Littlewood/Aristotle/Standalone/AtkinsonFormula.lean` — green
  - `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula` — green

What changed:

1. The old large-`j` public leaf is no longer phrased as an undifferentiated
   inverse-phase-cell estimate.
2. The branch now has an exact structural reduction from the large-`j`
   inverse-phase-cell prefix to:
   - an eventual no-log bound for the genuine row tail
   - the isolated head cell
3. The head cell is now discharged separately by a native eventual theorem from
   the existing single-cell complete-block bound.
4. So the remaining large-`j` public/deep work is now one theorem:
   an eventual no-log row-tail estimate inside `AtkinsonFormula.lean`.

Current honest status after this pass:

1. `AtkinsonFormula.lean` is still healthy after the new reduction.
2. The public/deep inverse-phase-cell leaf is now split into:
   - one eventual row-tail theorem for large `j`
   - the already explicit finite small-shift patch
3. The separate direct-Abel large-shift cleanup leaf remains:
   `atkinson_largeShiftWeightedBoundarySum_bound`
2. The new theorem makes the real remaining Atkinson leaf explicit:
   any tracked proof of the stronger no-log inverse-phase cell-prefix estimate
   immediately packages into
   `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`
   by paying only a universal `1 / log 2` factor.
3. The branch now also has the exact reduction needed for the next honest proof
   pass:
   if we can prove the stronger no-log inverse-phase cell-prefix estimate for
   all sufficiently large shifts `j`, and separately patch the finitely many
   small shifts, then the new theorems
   `atkinson_shiftedInversePhaseCellPrefix_no_log_of_eventual_and_finite_patch`
   and `atkinson_shiftedInversePhaseCellPrefixBound_of_eventual_and_finite_patch`
   package that data into the active public leaf automatically.
4. That finite patch is now concrete rather than schematic:
   the new theorem
   `atkinson_shiftedInversePhaseCellPrefixBound_of_eventual_j3_and_j1_j2`
   reduces the leaf to one large-shift theorem for `j ≥ 3` plus two native
   fixed-shift patches at `j = 1, 2`, matching the split-shift architecture
   already used elsewhere in `AtkinsonFormula.lean`.
5. A forced rebuild of `AtkinsonFormula.lean` now shows a sharper split:
   the subordinate helper
   `atkinson_largeShiftBoundaryAbelRemainder_bound_of_largeShiftPrefix`
   compiles cleanly, while the already-known direct-Abel frontier in the file
   itself remains:
   the live literal `sorry` has now been moved onto the sharper theorem
   `atkinson_largeShiftWeightedBoundarySum_bound`, while
   `atkinson_largeShiftBoundaryAbelRemainder_bound` has been reduced to that
   weighted-boundary statement.
   The recovery branch now also exposes
   `atkinson_largeShiftBoundaryAbelRemainder_eq_weightedBoundarySum` and
   `atkinson_largeShiftWeightedBoundarySum_eq_prefix_sub_headCore`, which make
   the remaining wrapper debt explicit as the single weighted boundary sum and
   identify that sum directly with `large-shift prefix - j1 headcore`, rather
   than the older head-tail / increment presentation.
5. The earlier idea of bypassing this through the generic next-shift induction
   is not supported by the tracked file as it stands:
   `atkinson_largeShiftPrefixBound_atomic_of_nextShift` needs a successor
   estimate with a contraction `γ < 1`, but the only tracked predecessor-tail
   input currently available is
   `atkinson_largeShiftPrefix_succ_htail_of_nextShift_and_smallShift`, which
   gives factor `8 * C_prev` rather than `γ * C_prev` with `γ < 1`.
   So the direct-Abel wrapper is still genuine theorem debt, not dead code.

Current honest frontier after this pass:

1. The public/deep Atkinson boundary remains
   `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`.
2. The exact stronger theorem-content target immediately below it is now
   explicit:
   a no-log bound for the inverse-phase cell-prefix sum, now reduced further to
   “eventual large-`j` theorem + finite small-`j` patch” by the new reduction
   theorems.
3. Separately, the tracked large-shift lane still has one live local debt:
   `atkinson_largeShiftBoundaryAbelRemainder_bound`.
3. The separate tracked large-shift debt is still the direct-Abel remainder
   theorem at line 12464 of `AtkinsonFormula.lean`.
   - in [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean)
3. Even with small-shift, large-shift, and inverse-core all available on the
   recovery branch, there is still no tracked provider route to:
   - `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`
   - `AtkinsonShiftedCorrectionPrefixBoundHyp`
4. So the next honest tracked-main recovery target is the inverse-phase-cell
   theorem layer inside `AtkinsonFormula.lean`, not more provider rewiring.
5. The large-shift closure debt is now a separate single-theorem cleanup task,
   not the first public-path provider break.

## Local tracked-main wiring work

- Added local experimental bridge files:
  - `Littlewood/Bridge/HardyDirichletPhaseAlignmentWiring.lean`
  - `Littlewood/Bridge/HardyMeanSquareAsymptoticWiring.lean`
  - `.recovery_artifacts/2026-04-21/banked/ZetaMeanSquareHalfFromHardyAsymptotic.lean`
- Direct build results:
  - `lake build Littlewood.Bridge.HardyDirichletPhaseAlignmentWiring` — green
  - `lake build Littlewood.Bridge.HardyMeanSquareAsymptoticWiring` — green
  - `lake build Littlewood.Bridge.ZetaMeanSquareHalfFromHardyAsymptotic` — green
  - `lake build Littlewood.Bridge.MeanSquareBridge` — still fails on
    `ZetaMeanSquareHalfBound`
  - `lake build Littlewood.Bridge.HardyCriticalLineWiring` — still blocked via
    `MeanSquareBridge`
- Interpretation:
  - one real class mismatch is now repaired,
  - but the active non-circular B1 lane still lacks upstream provider supply,
  - so there is no public-API improvement yet.
- Direct synthesis checks added after the bridge pass:
  - `GabckePhaseCouplingHyp` synthesizes from tracked main once
    `AnalyticAxioms` + `GabckePhaseCouplingHyp` are imported.
  - `AtkinsonShiftedInversePhaseCorePrefixBoundHyp` does not synthesize from
    tracked main.
  - `AtkinsonShiftedCorrectionPrefixBoundHyp` does not synthesize from tracked
    main.
- Updated interpretation:
  - the remaining tracked-main blocker for the non-circular Hardy/B1 lane is now
    concentrated on the Atkinson side, not the Gabcke side.
- Atkinson source audit added after the synth pass:
  - `AtkinsonSmallShiftPrefixBoundHyp` is not genuinely absent from tracked main.
    The file has a non-circular constructor near lines 12309-12327 of
    [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean),
    but it is private and inherits ambient section variables, so it is not
    reachable as a public zero-input provider.
  - `AtkinsonLargeShiftPrefixBoundHyp` is still genuinely open on tracked main.
    The closest direct tracked route is
    [`CorePrefixDirect.lean`](../../Aristotle/Standalone/CorePrefixDirect.lean),
    where `atkinsonLargeShiftPrefixBound_direct` still ends with `sorry`.
  - `AtkinsonShiftedCorrectionPrefixBoundHyp` still appears one-way: tracked
    consumers exist, but no tracked source/provider was found.
- Attempted tracked-main exposure on 2026-04-21:
  - I tried to promote the trapped small-shift constructor to a public instance
    inside `AtkinsonFormula.lean`.
  - That edit was reverted immediately after validation failed.
  - Failure mode: the helper chain itself inherits ambient section variables, so
    the right fix is not a one-line public instance; it is a targeted cleanup of
    the helper declarations first.
  - The concrete extra choke points exposed by that failed attempt were:
    `atkinson_shift1_upperMinusLowerBoundaryTerm_eq_blockMode_two_minus_one`,
    `atkinson_shift1_upperBoundaryPrefix_bound_atomic_native`,
    `atkinson_shift1_upperBoundaryPrefix_bound_atomic_of_blockOmega_linear_model_upto_two_eventually`,
    `atkinson_shift1_boundaryPrefix_bound_atomic_local_of_upper_and_j1`, and
    `atkinson_inversePhaseCorePrefix_bound_j2_of_blockOmega_linear_model_upto_two_eventually_and_j1`.
- Follow-up source-level de-pollution attempt on 2026-04-21:
  - I moved the `omit` boundary upstream into the source theorems feeding the
    small-shift chain, not just the later `j2` wrappers.
  - That reduced the noise, but it did **not** produce a clean public
    `AtkinsonSmallShiftPrefixBoundHyp` instance.
  - The failure collapsed to the native upper-bound chain:
    `atkinson_shift1_boundaryPrefix_bound_atomic_local_of_upper_and_j1` and then
    back into the lower/upper native first-lane lemmas around
    `atkinson_shift1_lowerBoundaryPrefix_bound_atomic_of_j1` and
    `atkinson_shift1_upperBoundaryPrefix_bound_atomic_native`.
  - A more aggressive pass then exposed earlier breakpoints around the native
    first-lane proof body (notably the calls near lines `11318`, `11582`, and
    `11652` in `AtkinsonFormula.lean`), so this is no longer well-described as
    "just section-variable leakage in the `j2` packaging."
  - I reverted the file again and restored a green
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Current best diagnosis:
    the first honest tracked-main obstruction is the **native upper-bound /
    small-shift helper spine**, and the missing supply is upstream of the
    `j2` convenience wrappers.
- Additional refinement from the next source pass on 2026-04-21:
  - The first polluted declaration is actually the base small-shift theorem
    `atkinson_smallShiftPrefixBound_of_native_j1_j2` at line `8123`.
  - A direct `omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in` at that
    site is not a drop-in edit, because the attached doc-comment position causes
    parser trouble (`unexpected token 'omit'; expected 'lemma'`) and the theorem
    body itself still immediately leaks the class at the first `obtain`.
  - So the next serious tracked-main attempt should not start at the later
    wrappers. It should either:
    1. restate the `j1/j2` small-shift theorem in a fresh declaration below the
       class declarations, or
    2. refactor the original declaration shape before retrying any public
       zero-input instance.
- Re-stated theorem experiment on 2026-04-21:
  - I tried option (1): restate the `j1/j2` small-shift theorem later in the
    file, below the class declarations, and redirect the later wrapper to use
    the re-stated theorem.
  - That experiment still failed immediately on the first `obtain`:
    the call to
    `atkinson_shiftedInversePhaseCorePrefix_bound_shifted_of_native_fixedShift`
    at line `7982` tried to synthesize
    `AtkinsonShiftedInversePhaseCorePrefixBoundHyp`.
  - This is the strongest diagnosis so far:
    the first real polluted theorem is not the 12k-line wrapper layer, and not
    even just the original `8123` declaration. The fixed-shift transport theorem
    at line `7982` is already carrying the inverse-phase class through the live
    section.
  - I reverted the experiment and restored a green
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
- Structural source confirmation:
  - The fixed-shift transport theorem at line `7982` sits *inside* the active
    section opened by `variable [AtkinsonShiftedInversePhaseCorePrefixBoundHyp]`
    at line `7186`.
  - So the current failure is not just hidden theorem dependency. The file
    layout itself places the first transport theorem under the live inverse-phase
    class scope.
  - That makes the next honest repair shape clearer:
    either move/restate the `7982` transport theorem outside that section, or
    insert an `omit [AtkinsonShiftedInversePhaseCorePrefixBoundHyp] in` at that
    exact theorem and repair from there.
- Critical-zero lane refinement after the tracked-main dependency scratch:
  - `CriticalZeroSumDiverges.lean` is not just off-path.
  - Its tracked upstream source for `HardyCriticalLineZerosHyp` is
    `Bridge/HardyCriticalLineZerosDirect.lean`, and that file already assumes
    `CriticalZeroSumDivergesHyp` together with the deep stack.
  - So the current tracked critical-zero supply is circular, not merely missing
    one import.
- Small-shift theorem-level closure refinement after the 2026-04-21 helper-chain pass:
  - Tracked main already contains a theorem-level small-shift closure route:
    `atkinson_smallShiftPrefixBound_of_native_j1_and_blockOmega_linear_model_upto_two_eventually`.
  - The mathematical input for that route is the unconditional theorem
    `StationaryPhaseMainMode.blockOmega_linear_model_upto_two_eventually`.
  - So the obstruction is **not** that tracked main lacks a small-shift proof.
    The obstruction is that exporting this route as a real zero-input instance
    exposes deeper section-variable pollution in the helper chain.
  - The attempted public instance uncovered repeated hidden dependencies on
    `AtkinsonShiftedInversePhaseCorePrefixBoundHyp` in the support lemmas around:
    `atkinsonResonantShiftedBoundaryTerm_norm_le`,
    `atkinsonBoundary_jMinusOne_le`,
    `atkinson_j2_kernelWeighted_j1_headCore_bound_of_j1`,
    `atkinson_shift1_lowerBoundaryPrefix_bound_atomic_of_j1`,
    and the native first-lane upper/boundary transport chain through the
    `11.5k`-`12.3k` region of `AtkinsonFormula.lean`.
  - I reverted that broader de-pollution attempt and restored a green
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Current stable state:
    the only retained source edit is the confirmed `omit` repair at the
    fixed-shift transport theorem around line `7982`.
  - Best next tracked-main move is now bifurcated:
    1. systematic helper-chain cleanup from the low-level norm/boundary lemmas
       upward, or
    2. a fresh duplicate small-shift provider chain in a clean scope, rather
       than trying to mutate the polluted in-place declarations piecemeal.

- Clean duplicate-chain progress after the first low-level replication pass:
  - `AtkinsonFormula.lean` now builds green with fresh duplicate lemmas that
    live in explicit `omit` scopes rather than inheriting the live inverse-phase
    class surface.
  - The first retained clean support lemmas are:
    - `atkinsonUpperBoundaryTerm_norm_clean`
    - `atkinsonResonantShiftedBoundaryTerm_norm_le_clean`
    - `atkinsonBoundary_jMinusOne_le_clean`
  - The next pass proved that mere wrapper aliases were not enough:
    calling the original theorems still tried to synthesize
    `AtkinsonShiftedInversePhaseCorePrefixBoundHyp`.
  - I replaced those wrapper aliases with full copied proofs for:
    - `atkinson_j2_kernelWeighted_j1_headCore_bound_of_j1_clean`
    - `atkinson_shift1_lowerBoundaryPrefix_bound_atomic_of_j1_clean`
  - I then pushed one layer further and detached the `j = 1` identity lemmas:
    - `atkinson_shift1_upperBoundaryTerm_eq_blockMode_two_clean`
    - `atkinson_shift1_lowerBoundaryTerm_eq_blockMode_one_clean`
    - `atkinson_shift1_upperMinusLowerBoundaryTerm_eq_blockMode_two_minus_one_clean`
  - Each of those additions was validated by a fresh green
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
- This materially changes the local frontier:
  the clean duplicate-chain tactic is not speculative anymore.
  It can detach real theorems from the polluted class scope, provided we keep
  copying proof bodies instead of aliasing polluted declarations.
- The next natural tracked-main target is the clean upper-prefix theorem:
  `atkinson_shift1_upperBoundaryPrefix_bound_atomic_native`, then the local
  boundary-gap / `j = 2` assembly theorem above it.

- Closure-axis progress after the next duplicate-chain pass:
  - Added clean duplicates for:
    - `atkinson_shift1_upperBoundaryPrefix_bound_atomic_native_clean`
    - `atkinson_shift1_boundaryPrefix_bound_atomic_local_of_upper_and_j1_clean`
    - `atkinson_j2_kernelWeighted_boundaryGap_bound_local_of_upper_and_j1_clean`
    - `atkinson_inversePhaseCorePrefix_bound_j2_of_upper_and_j1_clean`
    - `atkinson_smallShiftPrefixBound_of_native_j1_j2_clean`
    - `atkinson_smallShiftPrefixBound_of_native_j1_and_upper_clean`
    - `atkinson_smallShiftPrefixBound_of_native_j1_and_blockOmega_linear_model_upto_two_eventually_clean`
  - Added the first unconditional tracked-main Atkinson provider:
    `instAtkinsonSmallShiftPrefixBoundHyp`.
  - Validation now succeeds for:
    - `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`
    - `#synth Aristotle.Standalone.AtkinsonFormula.AtkinsonSmallShiftPrefixBoundHyp`
      after importing only `Littlewood.Aristotle.Standalone.AtkinsonFormula`
  - Validation still fails for:
    - `#synth Aristotle.Standalone.AtkinsonFormula.AtkinsonLargeShiftPrefixBoundHyp`
    - `#synth Aristotle.Standalone.AtkinsonFormula.AtkinsonShiftedInversePhaseCorePrefixBoundHyp`
  - Minimal-import public invocation of `Littlewood.littlewood_psi` still fails
    first on `CriticalZeroSumDivergesHyp`.
  - So the Atkinson small-shift leaf is now genuinely closed on tracked main.
    The next exposed blockers are:
    1. the critical-zero circularity on the public path,
    2. the tracked lack of large-shift closure,
    3. the resulting absence of a tracked inverse-phase-core provider.

- Atkinson large/inverse/correction frontier refinement after the 2026-04-21
  CorePrefix probe:
  - `AtkinsonFormula.lean` now builds green with one additional recovery-branch
    wiring step:
    an instance reconstructing
    `AtkinsonShiftedInversePhaseCorePrefixBoundHyp`
    from
    `AtkinsonSmallShiftPrefixBoundHyp`
    and
    `AtkinsonLargeShiftPrefixBoundHyp`.
  - Validation:
    - `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula` — green
    - focused scratch with a locally supplied
      `AtkinsonLargeShiftPrefixBoundHyp` gives:
      - `#synth AtkinsonShiftedInversePhaseCorePrefixBoundHyp` — succeeds
      - `#synth AtkinsonShiftedInversePhaseCellPrefixBoundHyp` — still fails
      - `#synth AtkinsonShiftedCorrectionPrefixBoundHyp` — still fails
  - Interpretation:
    - inverse-phase is no longer an independent open Atkinson leaf on this
      branch,
    - `CorePrefixDirect.lean` remains the tracked non-circular large-shift
      candidate, but it is still only a skeleton theorem ending in `sorry`,
    - the remaining theorem-content after hypothetical large-shift closure is
      now the cell/correction layer, not inverse-phase.
  - I also audited the existing large-shift scaffold in
    [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean):
    the induction package
    `atkinson_largeShiftPrefixBound_atomic_of_nextShift`
    still needs an honest boundary-row input `hbdryRow`, while the tracked tail
    theorem
    `atkinson_largeShiftPrefix_succ_htail_of_nextShift_and_smallShift`
    carries factor `γ = 8`, so it does not by itself close the contraction
    route.
  - Conclusion:
    `CorePrefixDirect.lean` is still a real closure-axis file, not a missed
    wrapper, and the cell-prefix / correction layer is now the next honest
    theorem-content source after it.

- Exact Atkinson frontier after the direct local-supply probe:
  - closed on this branch:
    - `AtkinsonSmallShiftPrefixBoundHyp`
    - `AtkinsonShiftedInversePhaseCorePrefixBoundHyp` from small + large
  - still not derivable from current tracked material even when large-shift is
    supplied locally:
    - `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`
    - `AtkinsonShiftedCorrectionPrefixBoundHyp`
  - this means the Atkinson problem is no longer best described as provider
    wiring once large-shift is available; the remaining gap is theorem content.

## 2026-04-21 - Local oscillatory infrastructure restored in `AtkinsonFormula`

- Files touched:
  - [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean)
- Added local lemmas:
  - `atkinsonShiftedPacketOmega_hasDerivAt`
  - `atkinson_deriv_shiftedPacketOmega`
  - `atkinson_differentiable_shiftedPacketOmega`
  - `atkinson_continuous_deriv_shiftedPacketOmega`
  - `atkinson_norm_shiftedPacketPhase`
  - `atkinsonShiftedPacketOmega_lower`
  - `atkinsonShiftedRelativeWeight_le_sqrt_two`
  - `atkinsonWeightedResonantBlockMode_deriv_norm`
  - `atkinsonShiftedPacketPhase_integral_bound`
  - `atkinsonWeightedResonantBlockMode_deriv_bound_eventually`
  - `atkinsonShiftedSinglePrimitive_norm_bound`
  - `atkinson_blockOmega_continuous`
- Validation:
  - `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula` — green
- Interpretation:
  - the standalone Atkinson file was missing the exact packet-phase and
    derivative infrastructure already present in the older stationary-phase
    development,
  - this restores the real local oscillatory toolkit needed for the
    correction-prefix lane,
  - the next honest theorem target is now the per-cell weighted near-band bound
    (the Atkinson analogue of
    `weighted_shifted_completeBlock_complex_bound_eventually`), not CloudDocs.

## 2026-04-21 - Correction-prefix frontier reduced to a single honest leaf

- Files touched:
  - [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean)
- Snapshot audit:
  - targeted searches through the local Aristotle snapshots in `~/Downloads`
    found **no committed provider** of
    `AtkinsonShiftedCorrectionPrefixBoundHyp`,
  - the round-3 recovery artifact
    `CORRECTION_PREFIX_BRIDGE.md` confirms only the already-known downstream
    bridge
    `[AtkinsonShiftedCorrectionPrefixBoundHyp] -> AtkinsonShiftedInversePhaseCellPrefixBoundHyp`,
    not a hidden constructor for the correction class itself,
  - the older
    [`StationaryPhaseDecomposition.lean`](../../../../../Downloads/Littlewood_Proof_aristotle/Littlewood/Aristotle/StationaryPhaseDecomposition.lean)
    still preserves the **proof pattern** for a correction-prefix transport, but
    not an Atkinson-side dropped-in provider.
- New structural finding inside
  [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean):
  - `mainTerm_first_moment_sqrt` already depends only on
    `AtkinsonShiftedCorrectionPrefixBoundHyp`,
  - so the shortest remaining Atkinson path is now the correction-prefix leaf,
    not large-shift "for its own sake",
  - the file already contains the full downstream correction-only package, but
    no upstream constructor for that class.
- New theorem added on the recovery branch:
  - `atkinson_shiftedCorrectionPrefixBound_of_inversePhaseCellPrefix`
  - this is a **named theorem**, not a global instance, to avoid a typeclass
    cycle with the existing reverse bridge,
  - it proves that the correction-prefix package and the inverse-phase-cell
    package differ only by the already-bounded boundary packet.
- New downstream corollary added on the recovery branch:
  - `mainTerm_first_moment_sqrt_of_inversePhaseCellPrefix`
  - this packages the exact remaining Atkinson dependency:
    if inverse-phase-cell closes, the current branch already carries the rest of
    the `MainTerm` first-moment route.
- Interpretation:
  - the correction leaf is now isolated more sharply than before,
  - if an honest route to
    `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`
    is found later, the correction class can now be recovered locally without
    new CloudDocs input,
  - if no such route exists, then
    `AtkinsonShiftedCorrectionPrefixBoundHyp`
    is the unique remaining Atkinson theorem-content target.

## Future entries

Each port bundle should record:

- source file or commit object
- active-path classes affected
- validation command(s)
- build result
- whether the public API invocation improved

## 2026-04-26 Aristotle artifact harvest

- Artifact source:
  Aristotle project `90a38311-fa2e-4572-b51f-f2c59b6d8cee`
- Classification:
  `CONDITIONAL_REDUCTION` on the separate large-shift cleanup lane, not a proof
  of the live public theorem
- Landed in tracked source:
  - new helper
    `atkinson_inversePhaseCorePrefix_bound_large_j`
  - `atkinson_largeShiftWeightedBoundarySum_bound` rewritten to reduce to that
    helper
- Validation:
  - direct `lean Littlewood/Aristotle/Standalone/AtkinsonFormula.lean`
  - `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`
- Public effect:
  - none yet; the live public theorem-content target remains
    `atkinson_shiftedInversePhaseCellPrefix_no_log_eventual_j3_of_completeBlockPrefix`
- Interpretation:
  - the sidecar did not close the requested large-`j` inverse-phase-cell leaf
  - it did remove wrapper noise from the separate cleanup lane and leave one
    cleaner analytic core behind
