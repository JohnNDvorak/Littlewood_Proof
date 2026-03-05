# Codex Window B Prompt — Close RH-pi Exact-Seed Triple (No Overlap)

You are Codex Window B in `/Users/john.n.dvorak/Documents/Git/Littlewood_Proof`.

## Mission
Close exactly the 3 delegated sorries in:

- `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean`
  1. `truncatedExplicitFormulaPi_unconditional`
  2. `targetTowerExactSeedAbovePerronThreshold_unconditional`
  3. `antiTargetTowerExactSeedAbovePerronThreshold_unconditional`

Unconditional only. No new axioms/postulates.

## Hard constraints

1. Do **not** touch B1/B2/B5a/RS7 files:
   - `Littlewood/Aristotle/Standalone/HardyAfeSignedGapDeepLeaf.lean`
   - `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean`
   - `Littlewood/Aristotle/Standalone/B2StationaryWindowLeaves.lean`
   - `Littlewood/Aristotle/ErrorTermExpansion.lean`
   - `Littlewood/Aristotle/RSBlockBounds.lean`
2. No new `axiom`, `postulate`, or additional `sorry`.
3. Preserve theorem signatures in `RHPiUnconditionalExactSeedExistence.lean`.
4. Keep downstream compatibility with:
   - `DeepBlockersResolved`
   - `RHPiDeepCoeffControlWitnesses`
   - RH-pi class-bridge modules.

## Context and known structure

- Exact-seed classes currently feed B7 coeff-control chain.
- There are many proved bridge modules in `Standalone/RHPi*`.
- Existing corrected-canonical and arg/phase scaffolding is available; use it if it helps construct real unconditional payloads.
- Do not resolve by circular reference back into the same unresolved theorem.

## Expected deliverable

A non-circular constructor path that provides all 3 theorems in `RHPiUnconditionalExactSeedExistence`.

It is acceptable to add helper modules in `Littlewood/Aristotle/Standalone/` if they are theorem-based and sorry-free.

## Required validation commands

Run and report:

1. `lake build Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedExistence`
2. `lake build Littlewood.Aristotle.Standalone.RHPiDeepCoeffControlWitnesses`
3. `lake build Littlewood.Aristotle.Standalone.DeepBlockersResolved`
4. `lake build Littlewood.Aristotle.DeepSorries`
5. `./scripts/critical_path_expanded_status.sh`

## Success criteria

- All 3 sorries in `RHPiUnconditionalExactSeedExistence.lean` are closed.
- No axioms/postulates added.
- Downstream B7 assembly builds remain green.

## Final report format

Return:
1. Files changed.
2. The exact non-circular theorem path used for each of the 3 target theorems.
3. Build outputs summary.
4. Updated delegated sorry count.
