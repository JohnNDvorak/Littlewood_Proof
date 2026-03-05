# Lane 3 B2: Branch-Free Tail Machinery (March 4, 2026)

## Goal
Close delegated B2 leaf:
- `Littlewood/Aristotle/Standalone/B2StationaryWindowLeaves.lean:87`
  `hardyCosExpTailBound_sorry`

without adding axioms/sorries and without using the principal-branch `hardyTheta` differentiability chain.

## Current status
- `main_sorries=0`
- `delegated_sorries=13`
- `main_axiom_postulate_lines=0`
- `delegated_axiom_postulate_lines=0`

## What is already done
1. Near-window bound is proved:
   - `nearWindowBound_sorry` is solved in `B2StationaryWindowLeaves.lean`.
2. Tail leaf has been refactored so the missing object is explicit:
   - `hardyCosExpTailBound_sorry`: tail bound stated directly for
     `HardyCosSmooth.hardyCosExp`.
   - The bridge
     `Aristotle.Standalone.B2TailStationaryBranchFree.stationaryTailClass_of_hardyCosExpTailBound`
     converts this into
     `HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp`.
3. Class-synthesis trace confirms the old route bottoms out at
   `HardyGammaInSlitPlaneOnSupportHyp`.

## Dead-end to avoid
The automatic class route in `HardyFirstMomentWiring` reduces B2 to:
- `HardyGammaInSlitPlaneOnSupportHyp` (then `HardyThetaDifferentiableOnSupportHyp`, etc.)

This is not currently constructively supplied in repo, and is not the right lane for branch-free closure.

## Non-circular route to build
Use the branch-free oscillatory factor and angular-velocity identity:
- `HardyCosSmooth.hardyCosExp`
- `Aristotle.HardyCosExpOmega.hardyCosExp_angular_velocity`

together with
- `ThetaDerivAsymptotic.theta_deriv_asymptotic`
- `ThetaDerivAsymptotic.thetaDeriv_eventually_pos`
- `Aristotle.PhaseDerivBounds` (lower-away templates)

to build a direct stationary-tail `sqrt(n+1)` bound for
`HardyFirstMomentWiring.hardyExpPhase`.

## Required terminal theorem shape
Produce a theorem of this exact shape (or stronger) and wire it into B2 leaf:

```lean
∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
  HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1) ≤ T →
  ‖∫ t in (HardyEstimatesPartial.hardyStart n + Real.sqrt (n + 1))..T,
      HardyFirstMomentWiring.hardyExpPhase n t‖ ≤ B * Real.sqrt (n + 1)
```

Then prove `hardyCosExpTailBound_sorry` directly; the class payload is now automatic.

## Practical integration steps
1. Add a new branch-free tail module (recommended new file):
   - `Littlewood/Aristotle/Standalone/B2TailStationaryBranchFree.lean` (already added)
2. Prove `hardyExpPhase` replacement by `hardyCosExp` on tail intervals (already available as equality).
3. Prove the required integral tail estimate there.
4. In `B2StationaryWindowLeaves.lean`, replace:
   - `hardyCosExpTailBound_sorry` by `by exact <new theorem>`.
5. Run:
   - `lake build Littlewood.Aristotle.Standalone.B2StationaryWindowLeaves`
   - `./scripts/critical_path_expanded_status.sh`

## Build checks that must remain true
- `main_sorries=0`
- `delegated_axiom_postulate_lines=0`
