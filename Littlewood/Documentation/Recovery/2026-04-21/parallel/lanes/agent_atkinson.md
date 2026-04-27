# Agent Atkinson Ledger

Branch: `codex/atkinson-large-j`

## Ownership

- Writable code: `Littlewood/Aristotle/Standalone/AtkinsonFormula.lean`
- Writable ledger: this file only
- Coordinator-owned shared files are read-only unless explicitly reassigned.

## Live Targets

1. Prove the large-`j` no-log inverse-phase cell-prefix estimate feeding
   `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`.
2. Close or cleanly bypass the direct-Abel cleanup leaf
   `atkinson_largeShiftBoundaryAbelRemainder_bound`.
3. Keep all Atkinson provider packaging inside the tracked public/deep theorem
   layer.

## Guardrails

- Do not split Atkinson work across another lane.
- Do not add a global instance that hides the public provider gap through a
  stale correction-prefix route.
- Do not replace the no-log target with a logged estimate unless the implication
  back to the public class is explicit and already proved.
- Record failed routes here before trying a different reduction.

## Required Checks

- `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`
- minimal import check for `Littlewood.Main.LittlewoodPsi`
- minimal import check for `Littlewood.Main.LittlewoodPi`
- `lake build` before requesting merge

## Session Log

### 2026-04-27 Baseline

- Status: lane created.
- Current smallest target: large-`j` no-log cell-prefix theorem below
  `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`.
- Coordinator action requested: none.
