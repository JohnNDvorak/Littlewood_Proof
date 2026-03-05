# Codex Handoff — Delegated RS 7-Sorry Closure

You are closing the delegated RS chain sorries for `Littlewood_Proof`.

Repo root:
`/Users/john.n.dvorak/Documents/Git/Littlewood_Proof`

## Goal
Close the 7 delegated RS sorries with unconditional proofs.

## Target sorries
1. `Littlewood/Aristotle/ErrorTermExpansion.lean`
- `theta_stirling_expansion`
- `off_resonance_integral_bound`
- `off_resonance_sum_bound`
- `errorTerm_expansion`

2. `Littlewood/Aristotle/RSBlockBounds.lean`
- `c_block_nonneg`
- `c_block_antitone`
- `block_interpolation`

## Why this matters
These are delegated in status scripts but still semantically used by main assembly:
`RSBlockBounds -> RSCompleteBlockAsymptotic -> DeepBlockersResolved (B3)`.

## Hard constraints
1. No `axiom`, no `postulate`, no `sorry`, no `admit`.
2. Preserve theorem signatures.
3. Do not weaken hypotheses.
4. Do not touch active main-2 files:
- `Littlewood/Aristotle/Standalone/HardyMeanSquareAsymptoticFromZetaMoment.lean`
- `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiSkeleton.lean`

## Suggested attack order
1. Close `theta_stirling_expansion`.
2. Close `off_resonance_integral_bound` via phase derivative lower bound + imported first-derivative oscillatory bounds.
3. Close `off_resonance_sum_bound` by summing per-mode bounds.
4. Close `errorTerm_expansion` using existing RS/Fresnel/block-param infrastructure.
5. Close RSBlockBounds trio:
- `c_block_nonneg`
- `c_block_antitone`
- `block_interpolation`

## Validation loop
After each theorem:
1. `lake build Littlewood.Aristotle.ErrorTermExpansion` (or RSBlockBounds module as applicable)

At end:
1. `lake build Littlewood.Aristotle.ErrorTermExpansion`
2. `lake build Littlewood.Aristotle.RSBlockBounds`
3. `lake build Littlewood.Aristotle.Standalone.RSCompleteBlockAsymptotic`
4. `lake build Littlewood.Aristotle.Standalone.DeepBlockersResolved`
5. `./scripts/critical_path_expanded_status.sh`

## Success criteria
1. All 7 target sorries closed.
2. No new axioms/postulates.
3. DeepBlockersResolved still compiles.
4. Expanded delegated sorry count drops by 7.

## Return format
1. Files changed
2. Theorem-by-theorem closure summary
3. Updated delegated sorry count
