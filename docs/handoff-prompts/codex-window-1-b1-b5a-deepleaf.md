# Codex Window 1 — Deep Leaves B1 + B5a

Repo root:
`/Users/john.n.dvorak/Documents/Git/Littlewood_Proof`

## Scope (only these 2 sorries)
- `Littlewood/Aristotle/Standalone/HardyAfeSignedGapDeepLeaf.lean`
  - `afe_signed_integral_gap_bound_leaf`
- `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean`
  - `shifted_remainder_bound_leaf`

## Do not touch
- `Littlewood/Aristotle/ErrorTermExpansion.lean`
- `Littlewood/Aristotle/RSBlockBounds.lean`
- `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean`
- `Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean`

## Hard constraints
- No `axiom`, `postulate`, `sorry`, `admit`.
- Preserve theorem signatures.
- No weakening of statements.

## Existing proved scaffolds you should reuse
- B1:
  - `Standalone/HardyAfeMeanSquareBridgeInfra.lean`
  - `Standalone/HardyAfeSignedGapScaffold.lean`
  - `Standalone/HardyMeanSquareAsymptoticFromZetaMoment.lean`
- B5a:
  - `Standalone/ExplicitFormulaPsiB5aDefs.lean`
  - `Standalone/ExplicitFormulaPsiB5aPerron.lean`
  - `Standalone/ExplicitFormulaPsiB5aResidues.lean`
  - `Standalone/ExplicitFormulaPsiB5aContourBounds.lean`
  - `Standalone/ExplicitFormulaPsiB5aFromShiftedBound.lean`

## Validation commands
```bash
cd /Users/john.n.dvorak/Documents/Git/Littlewood_Proof
lake build Littlewood.Aristotle.Standalone.HardyAfeSignedGapDeepLeaf
lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf
lake build Littlewood.Aristotle.Standalone.HardyAfeSignedGapAtomic
lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundAtomic
./scripts/critical_path_expanded_status.sh
```

## Success criteria
- Both target sorries closed.
- No new axioms/postulates.
- Expanded delegated sorry count drops by 2.

## Return format
1. Files changed
2. Proof path used for each theorem
3. Build outputs summary
4. Updated delegated sorry count
