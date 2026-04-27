# Agent Perron/Hadamard Ledger

Branch: `codex/perron-hadamard`

## Ownership

- Writable code: Perron, Hadamard, small-`T`, and shifted-remainder provider
  files.
- Writable ledger: this file only.
- Coordinator-owned shared files are read-only unless explicitly reassigned.

## Live Targets

1. Establish a non-circular provider path for `SmallTPerronBoundHyp`.
2. Audit Hadamard/Perron bridges for hidden dependence on the class being
   supplied.
3. Produce theorem-level handoff notes for any remaining analytic atom instead
   of routing through circular packaging.

## Guardrails

- Do not use `ContourRemainderBoundHyp.bound` to prove `SmallTPerronBoundHyp`
  if that contour provider already consumes `SmallTPerronBoundHyp`.
- Do not edit Atkinson files.
- Do not edit public main files directly.
- Treat generated self-drive runtime files as non-durable; record durable state
  here.

## Required Checks

- focused build of the touched Perron/Hadamard module
- minimal import check for `Littlewood.Main.LittlewoodPsi`
- minimal import check for `Littlewood.Main.LittlewoodPi`
- `lake build` before requesting merge

## Session Log

### 2026-04-27 Baseline

- Status: lane created.
- Current smallest target: non-circular small-`T` Perron provider.
- Coordinator action requested: none.
