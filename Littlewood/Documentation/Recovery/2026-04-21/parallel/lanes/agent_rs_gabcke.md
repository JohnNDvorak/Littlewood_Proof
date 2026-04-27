# Agent RS/Gabcke Ledger

Branch: `codex/rs-gabcke`

## Ownership

- Writable code: RS expansion, Siegel, Gabcke, and Hardy first-moment bridge
  files.
- Writable ledger: this file only.
- Coordinator-owned shared files are read-only unless explicitly reassigned.

## Live Targets

1. Close or reduce the RS/Gabcke coupling surfaces without editing Atkinson.
2. Keep any analytic atoms theorem-shaped and isolated.
3. Preserve compatibility with the tracked public Hardy bridge.

## Guardrails

- Do not edit `Littlewood/Aristotle/Standalone/AtkinsonFormula.lean`.
- Do not edit public main files directly.
- Do not turn a coupling obstruction into a broader axiom without recording the
  exact lost implication.
- Record whether a result is `PROVED`, `CONDITIONAL_REDUCTION`,
  `FAILED_ROUTE`, or `CIRCULAR_REFORMULATION`.

## Required Checks

- focused build of the touched RS/Gabcke module
- minimal import check for `Littlewood.Main.LittlewoodPsi`
- minimal import check for `Littlewood.Main.LittlewoodPi`
- `lake build` before requesting merge

## Session Log

### 2026-04-27 Baseline

- Status: lane created.
- Current smallest target: RS/Gabcke coupling reduction that leaves Atkinson
  untouched.
- Coordinator action requested: none.
