# Littlewood Public API Audit

Date: 2026-04-21
Branch: `recovery/provider-forensics-2026-04-21`

## Minimal-import invocation tests

### `Littlewood.littlewood_psi`

Scratch file:

```lean
import Littlewood.Main.LittlewoodPsi
example := Littlewood.littlewood_psi
#print axioms Littlewood.littlewood_psi
```

Result:

```text
error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Aristotle.Standalone.PsiZeroSumOscillationFromIngham.CriticalZeroSumDivergesHyp
'Littlewood.littlewood_psi' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `LittlewoodPi.littlewood_pi_li`

Scratch file:

```lean
import Littlewood.Main.LittlewoodPi
example := LittlewoodPi.littlewood_pi_li
#print axioms LittlewoodPi.littlewood_pi_li
```

Result:

```text
error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Aristotle.Standalone.PsiZeroSumOscillationFromIngham.CriticalZeroSumDivergesHyp
'LittlewoodPi.littlewood_pi_li' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Interpretation

1. The public theorem constants themselves are axiom-clean at the declaration level.
2. The public API is still broken because the public import chain does not supply the required instances.
3. The first unsatisfied class in both public theorems is the same:
   `CriticalZeroSumDivergesHyp`.
4. A future acceptance test must keep this exact standard:
   minimal import of the public module, then theorem invocation with no provider grab-bag.

## 2026-04-21 critical-zero rewiring pass

This pass added a tracked public-path bridge:

- [`HardyCriticalLineZerosFromStandalone.lean`](../../Bridge/HardyCriticalLineZerosFromStandalone.lean)

and rewired:

- [`CriticalAssumptions.lean`](../../CriticalAssumptions.lean)

to import both the standalone Hardy bridge and the tracked
[`CriticalZeroSumDiverges.lean`](../../Aristotle/Standalone/CriticalZeroSumDiverges.lean)
provider.

Focused validation:

- `lake build Littlewood.Bridge.HardyCriticalLineZerosFromStandalone` — green
- `lake build Littlewood.CriticalAssumptions` — green
- `lake build Littlewood.Main.LittlewoodPsi` — green

Strict minimal-import invocation still reports the outer failure as
`CriticalZeroSumDivergesHyp`, but the direct synthesis trace changed
materially:

```text
CriticalZeroSumDivergesHyp
  -> Aristotle.DirichletPhaseAlignment.HardyCriticalLineZerosHyp
  -> Schmidt.HardyCriticalLineZerosHyp
  -> AtkinsonShiftedInversePhaseCorePrefixBoundHyp
  -> AtkinsonSmallShiftPrefixBoundHyp   (resolved)
  -> AtkinsonLargeShiftPrefixBoundHyp   (resolved on active path)
  -> AtkinsonShiftedInversePhaseCellPrefixBoundHyp   (first live missing provider)
```

So the critical-zero lane is no longer blocked by a missing or circular public
provider. The public path now reaches the tracked critical-zero provider and
bottoms out honestly at `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`.

## 2026-04-21 tracked-main wiring pass

The first tracked-main wiring pass sharpened the diagnosis:

1. [`HardyDirichletPhaseAlignmentWiring.lean`](../../Bridge/HardyDirichletPhaseAlignmentWiring.lean)
   compiles and fixes a real class mismatch between
   `Schmidt.HardyCriticalLineZerosHyp` and
   `Aristotle.DirichletPhaseAlignment.HardyCriticalLineZerosHyp`.
2. [`HardyMeanSquareAsymptoticWiring.lean`](../../Bridge/HardyMeanSquareAsymptoticWiring.lean)
   compiles and exposes a non-circular local bridge from the tracked B1 theorem
   package to `HardyMeanSquareAsymptoticHyp`.
3. [`ZetaMeanSquareHalfFromHardyAsymptotic.lean`](../../../../.recovery_artifacts/2026-04-21/banked/ZetaMeanSquareHalfFromHardyAsymptotic.lean)
   compiles and exposes the derived bridge from
   `HardyMeanSquareAsymptoticHyp` to `ZetaMeanSquareHalfBound`.
4. Even with those bridges present,
   [`MeanSquareBridge.lean`](../../Bridge/MeanSquareBridge.lean) still fails to
   synthesize `ZetaMeanSquareHalfBound`, so the non-circular Hardy/B1 lane is
   still not supplied on the active path.
5. Therefore the first failure is no longer best described as "just missing import
   reachability". One mismatch is fixed, but the active provider graph still has
   an upstream analytic supply gap.

## 2026-04-21 Atkinson closure checkpoint

The tracked-main duplicate-chain pass has now produced one real closure result:

- `#synth Aristotle.Standalone.AtkinsonFormula.AtkinsonSmallShiftPrefixBoundHyp`
  succeeds after importing only
  [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean).
- `#synth Aristotle.Standalone.AtkinsonFormula.AtkinsonLargeShiftPrefixBoundHyp`
  still fails.
- `#synth Aristotle.Standalone.AtkinsonFormula.AtkinsonShiftedInversePhaseCorePrefixBoundHyp`
  still fails.

So the public minimal-import error message is unchanged at the surface, but the
actual active-path frontier has moved past small-shift, large-shift, and
inverse-core. The next live missing provider is now the correction / cell
layer.

## 2026-04-21 conditional large-shift probe

After the next recovery-branch wiring step in
[`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean),
the Atkinson dependency graph is sharper:

- with a local scratch assumption
  supplying `AtkinsonLargeShiftPrefixBoundHyp`,
  `#synth Aristotle.Standalone.AtkinsonFormula.AtkinsonShiftedInversePhaseCorePrefixBoundHyp`
  now succeeds;
- under that same scratch assumption,
  `#synth Aristotle.Standalone.AtkinsonFormula.AtkinsonShiftedInversePhaseCellPrefixBoundHyp`
  still fails;
- under that same scratch assumption,
  `#synth Aristotle.Standalone.AtkinsonFormula.AtkinsonShiftedCorrectionPrefixBoundHyp`
  still fails.

So inverse-phase is no longer an independent open Atkinson leaf on the recovery
branch. The current recovery branch now also weakens both
[`HardyMeanSquareAsymptoticWiring.lean`](../../Bridge/HardyMeanSquareAsymptoticWiring.lean)
and
[`HardyCriticalLineZerosFromStandalone.lean`](../../Bridge/HardyCriticalLineZerosFromStandalone.lean)
to depend on `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`, synthesizing
`AtkinsonShiftedCorrectionPrefixBoundHyp` only locally from the public theorem
`atkinson_shiftedCorrectionPrefixBound_of_inversePhaseCellPrefix`.

That pushed the live public-path provider frontier down to the remaining
Atkinson theorem layer:

- `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`
- `AtkinsonShiftedCorrectionPrefixBoundHyp`

## 2026-04-21 public-boundary cleanup

The next recovery pass made the public surface match that traced dependency:

- removed the global instance
  `[AtkinsonShiftedCorrectionPrefixBoundHyp] -> AtkinsonShiftedInversePhaseCellPrefixBoundHyp`
  from [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean),
  replacing it with the theorem
  `atkinson_shiftedInversePhaseCellPrefixBound_of_shiftedCorrectionPrefix`
- weakened the active public-path signatures in:
  - [`DeepSorries.lean`](../../Aristotle/DeepSorries.lean)
  - [`LandauOscillation.lean`](../../Bridge/LandauOscillation.lean)
  - [`LittlewoodPsi.lean`](../../Main/LittlewoodPsi.lean)
  - [`LittlewoodPi.lean`](../../Main/LittlewoodPi.lean)
  - [`HardyCriticalLineZerosDirect.lean`](../../Bridge/HardyCriticalLineZerosDirect.lean)
  from `AtkinsonShiftedCorrectionPrefixBoundHyp` to
  `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`
- kept the older resolved layer unchanged, but supplied
  `AtkinsonShiftedCorrectionPrefixBoundHyp` only locally inside
  `DeepSorries.combined_atoms` via
  `atkinson_shiftedCorrectionPrefixBound_of_inversePhaseCellPrefix`

Focused validation:

- `lake build Littlewood.Aristotle.DeepSorries` — green

Interpretation:

1. The public theorem boundary no longer overstates the stronger correction-prefix
   requirement.
2. The first honest missing public-path class is now
   `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`.
3. Correction-prefix remains theorem-equivalent and still needed internally by
   `DeepBlockersResolved`, but it is no longer part of the public requirement
   surface.

## 2026-04-21 focused Atkinson provider probe

Focused scratch import:

```lean
import Littlewood.Aristotle.Standalone.AtkinsonFormula
import Littlewood.Aristotle.Standalone.CorePrefixDirect
```

Direct synthesis result:

- `#synth AtkinsonSmallShiftPrefixBoundHyp` — succeeds
- `#synth AtkinsonLargeShiftPrefixBoundHyp` — succeeds
- `#synth AtkinsonShiftedInversePhaseCorePrefixBoundHyp` — succeeds
- `#synth AtkinsonShiftedInversePhaseCellPrefixBoundHyp` — fails
- `#synth AtkinsonShiftedCorrectionPrefixBoundHyp` — fails

Interpretation:

1. The active recovery branch now has a complete tracked provider path through
   small-shift, large-shift, and inverse-core.
2. `CorePrefixDirect.lean` is no longer the main open file. It is only the
   wrapper that exposes `AtkinsonLargeShiftPrefixBoundHyp`.
3. The only literal tracked `sorry` left in the Atkinson lane is the direct
   Abel remainder theorem
   `atkinson_largeShiftBoundaryAbelRemainder_bound` in
   [`AtkinsonFormula.lean`](../../Aristotle/Standalone/AtkinsonFormula.lean).
4. The first honest provider failure on the active public/deep path is now
   exactly `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`.
5. `AtkinsonShiftedCorrectionPrefixBoundHyp` remains equivalent at theorem
   level, but it is not the public boundary anymore and it still has no tracked
   standalone provider route once inverse-phase-cell is absent.

## 2026-04-21 deep/public signature cleanup

The next tracked-main cleanup removed stale Atkinson assumptions that were no
longer real declaration-level requirements.

Updated files:

- [`DeepSorries.lean`](../../Aristotle/DeepSorries.lean)
- [`LittlewoodPsi.lean`](../../Main/LittlewoodPsi.lean)
- [`LittlewoodPi.lean`](../../Main/LittlewoodPi.lean)
- [`HardyCriticalLineZerosDirect.lean`](../../Bridge/HardyCriticalLineZerosDirect.lean)
- [`SmoothedExplicitFormula.lean`](../../Aristotle/SmoothedExplicitFormula.lean)
- [`LandauContradiction.lean`](../../Aristotle/LandauContradiction.lean)
- [`LandauLittlewood.lean`](../../Aristotle/LandauLittlewood.lean)
- [`LandauMellinContradiction.lean`](../../Aristotle/LandauMellinContradiction.lean)

What changed:

- `DeepSorries` now imports
  [`CorePrefixDirect.lean`](../../Aristotle/Standalone/CorePrefixDirect.lean)
  and no longer quantifies explicitly over:
  - `AtkinsonSmallShiftPrefixBoundHyp`
  - `AtkinsonLargeShiftPrefixBoundHyp`
  - `AtkinsonShiftedInversePhaseCorePrefixBoundHyp`
- the forwarding Landau stack now depends on
  `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`, not the older correction
  surface
- the public theorem files and `HardyCriticalLineZerosDirect` now match that
  same reduced declaration boundary

Direct declaration probe:

```text
@Aristotle.DeepSorries.psi_full_strength_oscillation : ∀
  [AtkinsonShiftedInversePhaseCellPrefixBoundHyp] ...
  [CriticalZeroSumDivergesHyp] [PhaseAlignmentToTargetHyp], ...

@Aristotle.DeepSorries.pi_li_full_strength_oscillation : ∀
  [AtkinsonShiftedInversePhaseCellPrefixBoundHyp] ...
  [CriticalZeroSumDivergesHyp] [PhaseAlignmentToTargetHyp], ...
```

So the deep/public declaration boundary is now honest about the current live
Atkinson frontier: the first explicit Atkinson theorem-content requirement is
inverse-phase-cell, not small-shift, large-shift, inverse-core, or
correction-prefix.

Focused validation:

- `lake build Littlewood.Aristotle.DeepSorries` — green
- `lake build Littlewood.Aristotle.SmoothedExplicitFormula` — green
- `lake build Littlewood.Aristotle.LandauContradiction` — green
- `lake build Littlewood.Aristotle.LandauLittlewood` — green
- `lake build Littlewood.Aristotle.LandauMellinContradiction` — green
- `lake build Littlewood.Main.LittlewoodPsi` — green
- `lake build Littlewood.Main.LittlewoodPi` — green

Strict minimal-import invocation is unchanged at the outer surface:

- `example := Littlewood.littlewood_psi` still fails first on
  `CriticalZeroSumDivergesHyp`
- `example := LittlewoodPi.littlewood_pi_li` still fails first on
  `CriticalZeroSumDivergesHyp`

But the declaration surface is now aligned with the traced provider frontier.
