# Codex Handoff: B2 Support Provider (Non-Circular)

## Objective
Construct an unconditional upstream provider for:

- `Aristotle.Standalone.B2SupportPhaseRootInfra.B2SupportPhaseRootPayload`

so that B2 can close through:

- `Aristotle.Standalone.B2StationaryWindowLeaves.mainTermFirstMomentBoundHyp_from_windowLeaves_of_supportRootPayload`
- `Aristotle.Standalone.B2TailVdcDeepLeaf.tailVdcSqrtModeClass_candidate_of_supportRootPayload`

without using `tailVdcSqrtModeClass_leaf`.

## Current Facts (already in tree)
- B2 main-path is sorry-free.
- Delegated B2 leaf still open:
  - `Littlewood/Aristotle/Standalone/B2TailVdcDeepLeaf.lean:164`
- New non-circular endpoint exists:
  - `Littlewood/Aristotle/Standalone/B2StationaryWindowLeaves.lean`
    - `mainTermFirstMomentBoundHyp_from_windowLeaves_of_noncircular_support_constructor`
    - `mainTermFirstMomentBoundHyp_from_windowLeaves_of_supportRootPayload`

## Required payload fields
`B2SupportPhaseRootPayload` requires exactly:

1. `thetaDiff`
2. `phaseDerivDiff`
3. `derivLowerSqrt`
4. `secondDerivBound`

(see `Littlewood/Aristotle/Standalone/B2SupportPhaseRootInfra.lean`)

## Constraints
- No axioms.
- No new `sorry`.
- Non-circular imports only.
- Do not modify main-chain theorem signatures.

## Suggested lane
1. Build a new standalone provider module (or modules) that proves enough upstream lemmas to instantiate the 4 payload fields.
2. Add a theorem:
   - `provide_unconditional_B2SupportPhaseRootPayload : B2SupportPhaseRootPayload`
3. Add an instance (high priority but below local explicit `letI` use):
   - `instance : B2SupportPhaseRootPayload := provide_unconditional_B2SupportPhaseRootPayload`
4. Replace B2 deep leaf body with the existing candidate route:
   - `exact tailVdcSqrtModeClass_candidate_of_supportRootPayload`

## Validation checklist
Run all:

```bash
lake build Littlewood.Aristotle.Standalone.B2SupportPhaseRootInfra \
           Littlewood.Aristotle.Standalone.B2TailVdcDeepLeaf \
           Littlewood.Aristotle.Standalone.B2StationaryWindowLeaves \
           Littlewood.Aristotle.Standalone.DeepBlockersResolved
./scripts/critical_path_expanded_status.sh
```

Expected:
- B2 leaf sorry removed.
- `main_sorries = 0`
- delegated sorries decrease by exactly 1.
- `delegated_axiom_postulate_lines = 0`.

## Non-goals
- Do not touch B1/B5a/RH-pi files in this lane.
- Do not rewrite `DeepSorries.lean` wiring in this pass.
