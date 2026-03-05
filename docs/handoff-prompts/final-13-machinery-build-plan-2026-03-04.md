# Final 13 Machinery Build Plan (Unconditional)

Date: 2026-03-04
Status source: `./scripts/critical_path_expanded_status.sh`

## Current truth

- Main-path sorries: `0`
- Delegated-leaf sorries: `13`
- Axioms/postulates on main+delegated: `0`

Remaining delegated sorry sites:

1. `Littlewood/Aristotle/Standalone/B2StationaryWindowLeaves.lean:86`
2. `Littlewood/Aristotle/Standalone/HardyAfeSignedGapDeepLeaf.lean:28`
3. `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean:29`
4. `Littlewood/Aristotle/RSBlockBounds.lean:115`
5. `Littlewood/Aristotle/RSBlockBounds.lean:120`
6. `Littlewood/Aristotle/RSBlockBounds.lean:144`
7. `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean:20`
8. `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean:27`
9. `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean:31`
10. `Littlewood/Aristotle/ErrorTermExpansion.lean:107`
11. `Littlewood/Aristotle/ErrorTermExpansion.lean:251`
12. `Littlewood/Aristotle/ErrorTermExpansion.lean:260`
13. `Littlewood/Aristotle/ErrorTermExpansion.lean:297`

## Dependency DAG (what must move first)

### RS7 block (hard dependency cluster)

- `ErrorTermExpansion` (4 sorries) -> `RSBlockBounds` (3 sorries) -> B3 route (`RSCompleteBlockAsymptotic`) -> Hardy chain support.
- This is one coupled analytic cluster. Do not split across incompatible definitions.

### Direct leaves (independent)

- B1 leaf: `HardyAfeSignedGapDeepLeaf` (1 sorry)
- B2 leaf: `B2StationaryWindowLeaves` (1 sorry)
- B5a leaf: `ExplicitFormulaPsiB5aShiftedBoundDeepLeaf` (1 sorry)
- RH-pi exact-seed leaf: `RHPiUnconditionalExactSeedExistence` (3 sorries)

## Root-cause assessment per frontier

### Frontier A: B2 tail stationary-phase (`B2StationaryWindowLeaves`)

- Not a plumbing gap.
- The class `HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp` is not inferable in this checkout.
- Closing this requires supplying one of the upstream class packages in `HardyFirstMomentWiring`:
  - `HardyExpPhaseVdcSqrtModeOnTailSupportHyp`, or
  - `HardyExpPhaseVdcSqrtModeOnSupportHyp` + restriction bridge, or
  - direct tail bound theorem in the required shape.

### Frontier B: B1 signed AFE gap (`HardyAfeSignedGapDeepLeaf`)

- This leaf is the missing constructor for the signed bridge:
  - `(fun T => ∫_1^T (|ζ|² - 2|S_N|²)) =O(T)`.
- Existing files already have all algebraic bridge infrastructure.
- Needed new machinery is the analytic signed AFE remainder integration bound (Ingham/Titchmarsh style).

### Frontier C: B5a shifted remainder (`ExplicitFormulaPsiB5aShiftedBoundDeepLeaf`)

- All combiners are done (`Perron`, `Residue`, `ContourBounds`, `FromShiftedBound`).
- Missing only the root shifted remainder estimate:
  - `|shiftedRemainderRe x T| <= C*(sqrt/log + log^2)` for `x,T>=2`.
- This needs real contour/perron analytic payload, not further refactoring.

### Frontier D: RS7 (`ErrorTermExpansion` + `RSBlockBounds`)

- Structural blocker already documented in repo: principal-branch `hardyTheta` is incompatible with global Stirling-value asymptotic targets.
- Practical consequence:
  - need phase-lift/refactor of theta/arg conventions in this RS chain,
  - then finish `errorTerm_expansion`-strength lemmas,
  - then discharge `c_block_nonneg`, `c_block_antitone`, `block_interpolation` in `RSBlockBounds`.

### Frontier E: RH-pi exact-seed triple (`RHPiUnconditionalExactSeedExistence`)

- No non-circular constructor currently exists for exact-seed+truncated classes.
- Existing corrected-canonical scaffolding is useful, but still requires an upstream constructor of arg/phase payloads.
- Unconditional closure requires a real upstream theorem family; wrappers cannot replace it.

## Execution plan (unconditional)

## Phase 1 (parallel, no shared-theta risk)

1. Close B1 deep leaf
- File: `Standalone/HardyAfeSignedGapDeepLeaf.lean`
- Deliverable: proof of `afe_signed_integral_gap_bound_leaf`.
- Validation:
  - `lake build Littlewood.Aristotle.Standalone.HardyAfeSignedGapDeepLeaf`
  - `lake build Littlewood.Aristotle.Standalone.HardyMeanSquareAsymptoticFromZetaMoment`

2. Close B5a deep leaf
- File: `Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean`
- Deliverable: proof of `shifted_remainder_bound_leaf` in current statement.
- Validation:
  - `lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf`
  - `lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiSkeleton`

3. Close B2 tail leaf
- File: `Standalone/B2StationaryWindowLeaves.lean`
- Deliverable: proof of `tailHardyExpPhaseBound_sorry`.
- Recommended approach:
  - prove and instantiate one tail-support VdC class in `HardyFirstMomentWiring` chain,
  - use `B2StationaryWindowSplit.tailWindowPayload_of_hardyExpPhaseTailBound`.
- Validation:
  - `lake build Littlewood.Aristotle.Standalone.B2StationaryWindowLeaves`
  - `lake build Littlewood.Aristotle.Standalone.DeepBlockersResolved`

## Phase 2 (coupled RS7 cluster)

4. Phase-lift + fix `ErrorTermExpansion`
- Files: `ErrorTermExpansion.lean` (+ any theta/arg helper files needed).
- Deliverable: all 4 sorries removed with branch-consistent statements/proofs.

5. Finish `RSBlockBounds`
- File: `RSBlockBounds.lean`
- Deliverable: remove 3 sorries using strengthened `ErrorTermExpansion` outputs.

- Validation for phase 2:
  - `lake build Littlewood.Aristotle.ErrorTermExpansion`
  - `lake build Littlewood.Aristotle.RSBlockBounds`
  - `lake build Littlewood.Aristotle.Standalone.RSCompleteBlockAsymptotic`

## Phase 3 (RH-pi exact-seed)

6. Build non-circular exact-seed constructor family
- File: `Standalone/RHPiUnconditionalExactSeedExistence.lean` (and upstream provider modules).
- Deliverable: remove 3 sorries with genuine constructors.
- Preferred route:
  - prove upstream arg/phase payload constructors,
  - derive exact-seed interfaces as corollaries (not axioms).

- Validation:
  - `lake build Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedExistence`
  - `lake build Littlewood.Aristotle.Standalone.RHPiDeepCoeffControlWitnesses`
  - `lake build Littlewood.Aristotle.Standalone.DeepBlockersResolved`

## Global finish checks

Run in order:

1. `./scripts/critical_path_expanded_status.sh`
2. `lake build Littlewood.Aristotle.Standalone.DeepBlockersResolved`
3. `lake build Littlewood.Aristotle.DeepSorries`
4. `./scripts/critical_path_expanded_status.sh`

Target finish state:

- `main_sorries=0`
- `delegated_sorries=0`
- `main_axiom_postulate_lines=0`
- `delegated_axiom_postulate_lines=0`

## Lane assignment recommendation (3 Codex windows)

- Lane 1: B1 + B5a direct leaves (analytic one-shot leaves, independent).
- Lane 2: B2 tail VdC class construction and wiring.
- Lane 3: RS7 phase-lift cluster (`ErrorTermExpansion` + `RSBlockBounds`) first, then RH-pi exact-seed.

Reason: RS7 is definition-coupled and risky; keep it isolated.

## Completion criterion for full unconditional Littlewood chain

After all 13 delegated sorries are closed with no axioms/postulates, the current main chain wiring already yields the full unconditional combined-atoms path (`DeepSorries`/`DeepBlockersResolved`) in this repo structure.
