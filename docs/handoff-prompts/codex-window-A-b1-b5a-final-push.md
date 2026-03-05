# Codex Window A Prompt — Close B1 + B5a Deep Leaves (No Overlap)

You are Codex Window A in `/Users/john.n.dvorak/Documents/Git/Littlewood_Proof`.

## Mission
Close exactly these two delegated deep leaves **unconditionally** (no new axioms/postulates):

1. `Littlewood/Aristotle/Standalone/HardyAfeSignedGapDeepLeaf.lean`
   - theorem: `afe_signed_integral_gap_bound_leaf`
2. `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean`
   - theorem: `shifted_remainder_bound_leaf`

These are currently the B1 and B5a deep analytic roots.

## Hard constraints

1. Do **not** touch RS7/B2/RH-pi frontier files:
   - `Littlewood/Aristotle/ErrorTermExpansion.lean`
   - `Littlewood/Aristotle/RSBlockBounds.lean`
   - `Littlewood/Aristotle/Standalone/B2StationaryWindowLeaves.lean`
   - `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean`
2. No new `axiom`, `postulate`, or extra `sorry`.
3. If you must add helper lemmas/modules, keep them in `Littlewood/Aristotle/Standalone/` and wire only B1/B5a chain.
4. Preserve theorem signatures consumed by existing wrappers.

## Context and expected wiring

- B1 wrapper already exists:
  - `Littlewood/Aristotle/Standalone/HardyAfeSignedGapAtomic.lean`
  - `afe_signed_integral_gap_bound_atomic := ...DeepLeaf...`
- B5a wrapper already exists:
  - `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundAtomic.lean`
  - `shifted_remainder_bound_atomic := ...DeepLeaf...`
- B1 and B5a infrastructure/combiners are already proved and should be reused:
  - `HardyAfeMeanSquareBridgeInfra.lean`
  - `HardyAfeSignedGapScaffold.lean`
  - `ExplicitFormulaPsiB5aPerron.lean`
  - `ExplicitFormulaPsiB5aResidues.lean`
  - `ExplicitFormulaPsiB5aContourBounds.lean`
  - `ExplicitFormulaPsiB5aFromShiftedBound.lean`

## Suggested approach

### B1 (`afe_signed_integral_gap_bound_leaf`)

Goal:
`(fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t) =O[atTop] (fun T => T)`

- Prefer proving from already available mean-square asymptotics and scaffold bridge in `HardyAfeSignedGapScaffold`.
- Keep proof local to deep leaf + helper lemmas if needed.
- Avoid introducing new global typeclass assumptions unless they are already available/instantiated in existing chain.

### B5a (`shifted_remainder_bound_leaf`)

Goal:
`∃ C₂ > 0, ∀ x T ≥ 2, |shiftedRemainderRe x T| ≤ C₂ * (sqrt/log + log^2)`.

- Prefer deriving from existing component-level proved files and contour/Perron combiners.
- If equivalent theorem exists elsewhere, bridge by `simpa`.
- Keep statement unchanged.

## Required validation commands

Run and report results:

1. `lake build Littlewood.Aristotle.Standalone.HardyAfeSignedGapDeepLeaf`
2. `lake build Littlewood.Aristotle.Standalone.HardyAfeSignedGapAtomic`
3. `lake build Littlewood.Aristotle.Standalone.HardyMeanSquareAsymptoticFromZetaMoment`
4. `lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf`
5. `lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundAtomic`
6. `lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiSkeleton`
7. `./scripts/critical_path_expanded_status.sh`

## Success criteria

- Both target deep leaves have no `sorry`.
- No axioms/postulates added.
- Global status should drop delegated sorries by 2 (assuming no one else modifies concurrently).
- Main path remains `main_sorries=0`.

## Final report format

Return:
1. Files changed.
2. Exact theorem bodies closed.
3. Build outputs summary.
4. Updated delegated sorry count from status script.
