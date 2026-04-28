# Agent RS/Gabcke Ledger

Branch: `proofdebt/20260428-rs-gabcke`

Worktree: `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260428/rs-gabcke`

## Ownership

- Writable code: RS, Siegel, Gabcke, Hardy first-moment bridge, and related
  coefficient files.
- Writable ledger: this file only.
- Coordinator-owned shared files are read-only.

## Live Targets

1. Reduce or prove `SiegelSaddleExpansionHyp`.
2. Prove the explicit Gabcke adjacent coefficient identity, nonnegativity, and
   antitonicity atoms.
3. Keep legacy `GabckePhaseCouplingHyp` as a wrapper, not the analytic target.

## Guardrails

- Do not edit `AtkinsonFormula.lean`.
- Do not introduce broad analytic axioms or provider shortcuts.
- Do not edit public main files.
- Do not run a full build.

## Requested Checks

- focused build for touched RS/Gabcke module(s)
- strict public import probes for `Littlewood.Main.LittlewoodPsi` and
  `Littlewood.Main.LittlewoodPi`

## Session Log

### 2026-04-28 Launch

- Baseline: `acdc136`.
- Initial target: `SiegelSaddleExpansionHyp` / Gabcke adjacent atoms.
- Coordinator action: initial agent dispatched; Aristotle sidecar planned.
