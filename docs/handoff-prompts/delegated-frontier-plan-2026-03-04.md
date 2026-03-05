# Delegated Frontier Plan (2026-03-04)

Main critical path is clean (`main_sorries=0`, `main_axiom_postulate_lines=0`).
Remaining work is the delegated frontier (12 sorries, 0 axioms/postulates).

Use:
```bash
./scripts/critical_path_expanded_status.sh
./scripts/delegated_frontier_report.sh
```

## Remaining delegated leaves
- `Littlewood/Aristotle/Standalone/HardyAfeSignedGapDeepLeaf.lean`
  - `afe_signed_integral_gap_bound_leaf`
- `Littlewood/Aristotle/Standalone/ExplicitFormulaPsiB5aShiftedBoundDeepLeaf.lean`
  - `shifted_remainder_bound_leaf`
- `Littlewood/Aristotle/RSBlockBounds.lean`
  - `c_block_nonneg`
  - `c_block_antitone`
  - `block_interpolation`
- `Littlewood/Aristotle/ErrorTermExpansion.lean`
  - `theta_stirling_expansion`
  - `off_resonance_integral_bound`
  - `off_resonance_sum_bound`
  - `errorTerm_expansion`
- `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean`
  - `truncatedExplicitFormulaPi_unconditional`
  - `targetTowerExactSeedAbovePerronThreshold_unconditional`
  - `antiTargetTowerExactSeedAbovePerronThreshold_unconditional`

## Execution split
- Track A (B1/B5a analytics):
  - close the two deep-leaf atomics directly.
  - do not edit wrappers (`HardyAfeSignedGapAtomic`, `ExplicitFormulaPsiB5aShiftedBoundAtomic`).
- Track B (RS7):
  - resolve `theta_stirling_expansion` against current `hardyTheta` model first.
  - then close `off_resonance_integral_bound` and `off_resonance_sum_bound`.
  - only then attack `errorTerm_expansion`, then `RSBlockBounds` triple.
- Track C (RH-pi exact-seed constructors):
  - construct real providers for `TruncatedExplicitFormulaPiHyp` and exact-seed-above-threshold payloads.
  - wire through `RHPiUnconditionalExactSeedExistence` only after provider theorems exist.

## Known structural blockers to account for
- Principal-branch incompatibility markers exist in:
  - `Littlewood/Aristotle/StirlingArgGamma.lean`:
    - `stirling_arg_gamma_asymp_false`
    - `stirling_arg_gamma_false`
- RH-pi constructor bottleneck currently concentrates at:
  - `Littlewood/Aristotle/Standalone/RHPiUnconditionalExactSeedExistence.lean`

## Acceptance target
- `./scripts/critical_path_expanded_status.sh` reports:
  - `main_sorries=0`
  - `delegated_sorries=0`
  - `main_axiom_postulate_lines=0`
  - `delegated_axiom_postulate_lines=0`
