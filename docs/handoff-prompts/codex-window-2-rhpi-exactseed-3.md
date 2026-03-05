# Codex Window 2 — RH-pi Exact-Seed 3

Repo root:
`/Users/john.n.dvorak/Documents/Git/Littlewood_Proof`

## Scope (only these 3 sorries)
File:
`Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean`

Targets:
1. `truncatedExplicitFormulaPi_unconditional`
2. `targetTowerExactSeedAbovePerronThreshold_unconditional`
3. `antiTargetTowerExactSeedAbovePerronThreshold_unconditional`

## Do not touch
- `Littlewood/Aristotle/ErrorTermExpansion.lean`
- `Littlewood/Aristotle/RSBlockBounds.lean`
- `Littlewood/Aristotle/Standalone/HardyAfeSignedGapDeepLeaf.lean`
- `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean`

## Hard constraints
- No `axiom`, `postulate`, `sorry`, `admit`.
- Preserve theorem signatures.
- No circular self-reference through the same file.

## Guidance
- First search for non-circular existing constructors for:
  - `PiLiDirectOscillationBridge.TruncatedExplicitFormulaPiHyp`
  - `TargetTowerExactSeedAbovePerronThreshold`
  - `AntiTargetTowerExactSeedAbovePerronThreshold`
- If unavailable, construct from existing proved standalone chain modules.
- Keep this file as canonical unconditional endpoint consumed by
  `DeepBlockersResolved`.

## Validation commands
```bash
cd /Users/john.n.dvorak/Documents/Git/Littlewood_Proof
lake build Littlewood.Aristotle.Standalone.RHPiUnconditionalExactSeedExistence
lake build Littlewood.Aristotle.Standalone.DeepBlockersResolved
lake build Littlewood.Aristotle.DeepSorries
./scripts/critical_path_expanded_status.sh
```

## Success criteria
- All 3 target sorries closed.
- No new axioms/postulates.
- Expanded delegated sorry count drops by 3.

## Return format
1. Files changed
2. Upstream theorem/instance path used per target
3. Build outputs summary
4. Updated delegated sorry count
