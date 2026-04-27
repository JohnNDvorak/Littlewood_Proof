# Agent Pi/Phase Ledger

Branch: `codex/pi-phase`

## Ownership

- Writable code: pi oscillation, phase coupling, exact-seed, and compatibility
  files.
- Writable ledger: this file only.
- Coordinator-owned shared files are read-only unless explicitly reassigned.

## Live Targets

1. Repair or bypass downstream dependence on the false
   `TruncatedExplicitFormulaPiHyp.pi_approx` field.
2. Keep the public pi path on theorem statements that are mathematically true.
3. Coordinate any interface change through the community board before touching
   public API files.

## Guardrails

- Do not prove `TruncatedExplicitFormulaPiHyp.pi_approx` as stated; the
  singleton/empty-set analysis marks it false.
- Do not edit Atkinson files.
- Do not edit `Littlewood/Main/LittlewoodPi.lean` directly.
- If a replacement class is needed, state the exact proposed interface here
  before code edits.

## Required Checks

- focused build of the touched pi/phase module
- minimal import check for `Littlewood.Main.LittlewoodPi`
- minimal import check for `Littlewood.Main.LittlewoodPsi`
- `lake build` before requesting merge

## Session Log

### 2026-04-27 Baseline

- Status: lane created.
- Current smallest target: honest replacement or bypass for false `pi_approx`
  usage.
- Coordinator action requested: none.
