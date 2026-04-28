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

### 2026-04-27 Atkinson Large-J Conditional Reduction

- Status: `CONDITIONAL_REDUCTION`.
- Current theorem attacked: the live sorry at
  `AtkinsonFormula.lean:14202`,
  `atkinson_inversePhaseCorePrefix_bound_large_j`.
- Public class names verified locally:
  `AtkinsonShiftedInversePhaseCellPrefixBoundHyp` at the inverse-phase
  cell-prefix surface and `AtkinsonLargeShiftPrefixBoundHyp` at the large-shift
  inverse-phase-core prefix surface.
- Facts banked:
  `atkinson_inversePhaseCorePrefix_bound_large_j_of_contracting_nextShift`
  proves the exact large-`j` theorem shape from the already-present
  `atkinson_largeShiftPrefixBound_atomic_of_nextShift` package, assuming
  `AtkinsonSmallShiftPrefixBoundHyp`, a strict contraction `γ < 1`, the boundary
  row estimate, and the reciprocal-step predecessor-tail estimate.
- Secondary cleanup banked:
  `atkinson_largeShiftBoundaryAbelRemainder_bound_of_contracting_nextShift`
  removes the ambient `AtkinsonLargeShiftPrefixBoundHyp` assumption from the
  direct-Abel remainder path under the same strict-contraction inputs.
- Failed route not to retry: replacing the line-14202 sorry by
  `AtkinsonLargeShiftPrefixBoundHyp.bound` only makes the theorem conditional on
  the class it is supposed to provide; it is a circular reformulation, not a
  closure.
- Validation status: no successful Lean validation in this pass. A focused
  `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula` was started
  before the updated coordinator rule, but the cold dependency build exited with
  code `-1` before reaching `AtkinsonFormula`.
- Requested validation command for coordinator:
  `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
- Smallest next theorem:
  prove the strict-contraction predecessor-tail input with some `γ < 1`:
  the `htail` hypothesis of
  `atkinson_inversePhaseCorePrefix_bound_large_j_of_contracting_nextShift`.
- Coordinator action requested: run the focused Atkinson module build when
  validation is serialized again.
