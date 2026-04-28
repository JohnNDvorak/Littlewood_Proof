# Littlewood Blocker Crosswalk

Date: 2026-04-21
Branch: `recovery/provider-forensics-2026-04-21`

This note maps the tracked regression spine to the current hypothesis surface.

## Verified tracked timeline

### `7015e09`

Commit message:

```text
wire DeepSorries through DeepBlockersResolved: 0 sorry in main chain
```

Verified public shape:

- [`LittlewoodPsi.lean`](../../Main/LittlewoodPsi.lean) stated the strong public theorem
  `ψ(x) - x = Ω±(√x * lll x)`.
- [`DeepSorries.lean`](../../Aristotle/DeepSorries.lean) still described the single consolidated
  `combined_atoms` route and exported:
  - `psi_full_strength_oscillation : Ω±(√x * lll x)`
  - `pi_li_full_strength_oscillation : Ω±((√x / log x) * lll x)`
- No 15-class boundary surface appeared in the public `LittlewoodPsi` file.

Interpretation:

- This is the strongest tracked public state in the current history.
- It is still not the same thing as "all leaves proved"; it is a more direct theorem path.

### `f8b3ee4`

Commit message:

```text
fix B3: remove false local clause from PerBlockSignedBoundHyp, wire through RSCompleteBlockAsymptotic
```

Verified public change:

- [`LittlewoodPsi.lean`](../../Main/LittlewoodPsi.lean) weakens the public theorem to
  `ψ(x) - x = Ω±(√x)`.
- [`DeepSorries.lean`](../../Aristotle/DeepSorries.lean) changes `combined_atoms` so the ψ lane is
  already at `Ω±(√x)`, while the `π-li` lane still retains the `lll` factor.

Interpretation:

- This is the first tracked public regression in theorem strength.
- The public ψ theorem was weakened before the 15-class surface was propagated.

### `d2778c4`

Commit message:

```text
Fix all build errors: 0 errors, 8277 jobs clean build
```

Verified architectural change:

- [`LittlewoodPsi.lean`](../../Main/LittlewoodPsi.lean) now carries the 15-class hypothesis surface.
- [`DeepSorries.lean`](../../Aristotle/DeepSorries.lean) carries the same class surface.
- [`LandauOscillation.lean`](../../Bridge/LandauOscillation.lean) now also carries the same class surface.

Interpretation:

- This is the tracked point where the public theorem path stopped being a direct theorem route and
  became an interface bundle over unresolved providers.

### `HEAD` (`5c08167`)

- For the files above, `HEAD` matches the `d2778c4` architectural shape.
- The current green build therefore reflects boundary propagation, not closure.

### `bd6c8f3` plus 2026-04-28 de-axiom checkpoint

- The recovery branch removes the active `AnalyticAxioms.lean` provider shim
  from the public path.
- This restores the old frontier style: analytic content is visible as
  theorem/class debt and temporary `sorry`, not as private global axioms.
- The only accepted non-Lean mathematical input remains the first-zero /
  zero-free-below-14.13 pair in `ZeroCountingAssumptions.lean`.

## Current class families mapped back to older blocker families

| Current family | Older blocker / leaf family | Interpretation |
| --- | --- | --- |
| `CriticalZeroSumDivergesHyp`, `PhaseAlignmentToTargetHyp` | RH / zero-sum alignment lane (older B5b-style payload) | These are the RH constructive alignment leaves that used to feed the strong ψ lane directly |
| 4 Atkinson prefix classes + `SiegelSaddleExpansionHyp` + `GabckePhaseCouplingHyp` | Hardy / Riemann-Siegel / B1-B3 first-moment lane | This cluster corresponds to the old Hardy-chain and Riemann-Siegel leaf package |
| `ShiftedRemainderSegmentBoundLargeTHyp`, `SmallTPerronBoundHyp` | Perron contour remainder lane | Large-`T` plus small-`T` contour control |
| `TruncatedExplicitFormulaPiHyp`, `PerronPiApproxCompatibilityHyp`, `InhomogeneousPhaseFitAbovePerronThresholdHyp`, corrected tower pair | RH-`π` exact-seed / B7 coefficient-control lane | This is the modern wrapper surface around the old `π-li` constructive phase machinery |

## Consequences

1. The tracked regression happened in two steps:
   - theorem-strength weakening first
   - interface-boundary propagation second
2. The current 15-class surface is not "the old blockers plus names"; it is a wrapper layer around the old blocker graph.
3. Any recovery that skips this map and jumps straight to CloudDocs file porting is likely to bless the wrong files.
4. Any future provider claim must pass the axiom audit: no analytic class may be
   treated as closed merely because `AnalyticAxioms.lean` exists.
