# Agent Pi/Phase Ledger

Branch: `proofdebt/20260428-pi-phase`

Worktree: `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260428/pi-phase`

## Ownership

- Writable code: pi oscillation, phase, exact-seed, Perron compatibility, and
  corrected witness provider files.
- Writable ledger: this file only.
- Coordinator-owned shared files are read-only.

## Live Targets

1. Remove public reliance on false `TruncatedExplicitFormulaPiHyp.pi_approx`.
2. Produce honest Perron-only target/anti-target phase coupling providers.
3. Audit any `False`-based global provider route before it reaches public API.

## Guardrails

- Do not prove `TruncatedExplicitFormulaPiHyp.pi_approx` as stated.
- Do not add a global contradiction-based provider without explicit coordinator
  approval.
- Do not edit Atkinson, Perron/B5a, RS/Gabcke, or public main files.
- Do not run a full build.

## Requested Checks

- focused build for touched Pi/Phase module(s)
- strict public import probes for `Littlewood.Main.LittlewoodPsi` and
  `Littlewood.Main.LittlewoodPi`

## Session Log

### 2026-04-28 Launch

- Baseline: `acdc136`.
- Initial target: Perron-only replacement for false `pi_approx` usage.
- Coordinator action: initial agent dispatched; Aristotle sidecar planned.
