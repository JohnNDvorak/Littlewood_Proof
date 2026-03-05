# Codex Window Prompt: B2 `hardyCosExp` Tail Leaf

## Target
Close exactly this delegated sorry:
- `Littlewood/Aristotle/Standalone/B2StationaryWindowLeaves.lean:87`
- theorem name: `hardyCosExpTailBound_sorry`

```lean
private theorem hardyCosExpTailBound_sorry :
    ∃ B > 0, ∀ n : ℕ, ∀ T : ℝ, T ≥ 2 →
      hardyStart n + Real.sqrt (n + 1) ≤ T →
      ‖∫ t in (hardyStart n + Real.sqrt (n + 1))..T,
          HardyCosSmooth.hardyCosExp n t‖ ≤ B * Real.sqrt (n + 1) := by
  sorry
```

## Important repo context
- Main path is already sorry-free and axiom-free.
- This leaf is delegated.
- A proved bridge already exists:
  - `Littlewood/Aristotle/Standalone/B2TailStationaryBranchFree.lean`
  - `stationaryTailClass_of_hardyCosExpTailBound`

So you only need to prove the theorem above. If you do, B2 delegated leaf closes automatically.

## Constraints
- No axioms, no new sorrys.
- Keep signatures unchanged.
- Build with:
  - `lake build Littlewood.Aristotle.Standalone.B2StationaryWindowLeaves`
  - `./scripts/critical_path_expanded_status.sh`

## Recommended analytic lane
Use branch-free objects:
- `HardyCosSmooth.hardyCosExp`
- `Aristotle.HardyCosExpOmega.hardyCosExp_angular_velocity`

Avoid trying to discharge via `HardyGammaInSlitPlaneOnSupportHyp` class synthesis.

## Deliverables
1. The leaf proof in place.
2. Build output summary.
3. Updated delegated sorry count.
