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

### 2026-04-28 Aristotle Harvest Integration

- Job: `32a1df6a-be94-4cc2-81c3-05623533b222`.
- Classification: `INTERFACE_REDUCTION`.
- Target audited:
  Perron-only replacement for the false `TruncatedExplicitFormulaPiHyp`
  route.
- Result:
  the delivered `PerronPhaseCouplingReduction.lean` is a useful reduction but
  is not integrated as active source. It is sorry-backed and failed a
  standalone Lean check on the current branch because `RiemannHypothesis` is
  ambiguous between root and `ZetaZeros` namespaces.
- Guardrail:
  avoid `PerronPiApproxCompatibilityHyp`, `TruncatedExplicitFormulaPiHyp`,
  and the constant-1 `PerronSqrtErrorEventuallyAtHeightHyp` route.
- Honest route:
  work at `piScale x = sqrt(x) / log(x) * lll(x)`, where fixed Perron
  constants can be absorbed by `lll(x)`.
- Smallest honest inputs:
  a T-parameterized pi-level Perron O-bound, bounded-window Kronecker for the
  finite zero set, and tower/lll absorption.
- Current lane guidance:
  continue the already-validated target/anti realized phase-radius geometry
  and zeta finite-zero compatibility route. Do not add the harvested reduction
  module until it compiles and closes a provider.
