# Codex Window Prompt: B2 Root-Chain Closure (No Axioms)

You are closing the B2 delegated leaf on the Littlewood repo:
`Littlewood/Aristotle/Standalone/B2TailVdcDeepLeaf.lean:75`.

## Hard constraints
- No `axiom`, no `postulate`, no new `sorry`.
- Keep theorem signatures stable unless absolutely necessary for non-circularity.
- Do not touch B1/B5a/RH-pi files in this pass.

## Current blocked constructor chain
Run:

```bash
./scripts/root_constructor_status.sh
```

B2-relevant missing constructors are:
- `HardyFirstMomentWiring.HardyThetaDifferentiableOnSupportHyp`
- `HardyFirstMomentWiring.HardyPhaseDerivDifferentiableOnSupportHyp`
- `HardyFirstMomentWiring.HardyExpPhaseDerivAbsLowerSqrtModeOnSupportHyp`
- `HardyFirstMomentWiring.HardyExpPhaseSecondDerivAbsBoundOnSupportHyp`
- `HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp`
- `Aristotle.Standalone.B2TailVdcRootInfra.B2TailVdcRootPayload`

## Existing useful wiring
- `Littlewood/Aristotle/Standalone/B2TailVdcRootInfra.lean`
  - already lifts tail/support class packages into `B2TailVdcRootPayload`.
- `Littlewood/Aristotle/Standalone/B2TailVdcDeepLeaf.lean`
  - has ready wrappers:
    - `tailVdcSqrtModeClass_of_tailPhaseClasses`
    - `tailVdcSqrtModeClass_candidate_of_rootPayload`

Once `B2TailVdcRootPayload` is constructible, leaf should be one-line:

```lean
theorem tailVdcSqrtModeClass_leaf :
    HardyFirstMomentWiring.HardyExpPhaseVdcSqrtModeOnTailSupportHyp := by
  exact tailVdcSqrtModeClass_candidate_of_rootPayload
```

## What to implement
1. Build non-circular providers for the four support classes above.
2. Verify they synthesize in scope imported by `DeepBlockersResolved`.
3. Verify `#synth Aristotle.Standalone.B2TailVdcRootInfra.B2TailVdcRootPayload` succeeds.
4. Replace the B2 leaf sorry with the one-line rootPayload candidate.
5. Run:

```bash
lake build Littlewood.Aristotle.Standalone.B2TailVdcDeepLeaf
./scripts/critical_path_expanded_status.sh
./scripts/root_constructor_status.sh
```

## Deliverable format
Report:
1. Files changed.
2. The exact theorem/instance path that now synthesizes B2 root payload.
3. delegated_sorries before/after.
4. Confirmation: no axiom/postulate lines added.
