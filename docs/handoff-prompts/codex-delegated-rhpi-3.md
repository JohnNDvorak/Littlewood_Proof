# Codex Handoff — Delegated RH-pi 3-Sorry Closure

You are closing the delegated RH-pi exact-seed chain sorries for `Littlewood_Proof`.

Repo root:
`/Users/john.n.dvorak/Documents/Git/Littlewood_Proof`

## Goal
Close 3 sorries in `RHPiUnconditionalExactSeedExistence` with unconditional proofs and unchanged signatures.

## Target sorries
File:
`Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean`

Theorems:
1. `truncatedExplicitFormulaPi_unconditional : TruncatedExplicitFormulaPiHyp`
2. `targetTowerExactSeedAbovePerronThreshold_unconditional : TargetTowerExactSeedAbovePerronThreshold`
3. `antiTargetTowerExactSeedAbovePerronThreshold_unconditional : AntiTargetTowerExactSeedAbovePerronThreshold`

## Why this matters
`DeepBlockersResolved` uses all three directly in B7 assembly (`deep_blocker_B7_coeff_control_leaf`).

## Hard constraints
1. No `axiom`, no `postulate`, no `sorry`, no `admit`.
2. Preserve theorem signatures.
3. Do not weaken hypotheses.
4. Do not touch active main-2 files:
- `Littlewood/Aristotle/Standalone/HardyMeanSquareAsymptoticFromZetaMoment.lean`
- `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiSkeleton.lean`

## Required method
1. Search for already-proved theorem paths that discharge each target by `exact`.
2. If names differ, add small adapter lemmas only.
3. If direct discharge is unavailable, build from existing RH-pi standalone witness/bridge modules (arg-above-threshold, phase-coupling, exact-seed bridge, coeff-control, target-height builders).
4. Keep this file as the canonical unconditional endpoint imported by `DeepBlockersResolved`.

## Validation loop
After each theorem:
1. `lake build Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedExistence`

At end:
1. `lake build Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedExistence`
2. `lake build Littlewood.Aristotle.Standalone.DeepBlockersResolved`
3. `lake build Littlewood.Aristotle.DeepSorries`
4. `./scripts/critical_path_expanded_status.sh`

## Success criteria
1. All 3 target sorries closed.
2. No new axioms/postulates.
3. DeepBlockersResolved compiles.
4. Expanded delegated sorry count drops by 3.

## Return format
1. Files changed
2. Upstream theorem path used for each target
3. Updated delegated sorry count
