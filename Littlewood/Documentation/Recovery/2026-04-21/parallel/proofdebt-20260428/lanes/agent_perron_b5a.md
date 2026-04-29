# Agent Perron/B5a Ledger

Branch: `proofdebt/20260428-perron-b5a`

Worktree: `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260428/perron-b5a`

## Ownership

- Writable code: B5a, Perron truncation, Hadamard, small-`T`, and shifted
  remainder provider files.
- Writable ledger: this file only.
- Coordinator-owned shared files are read-only.

## Live Targets

1. Close `shifted_remainder_bound_leaf`.
2. Produce a non-circular provider route for
   `ShiftedRemainderSegmentBoundLargeTHyp` and `SmallTPerronBoundHyp`.
3. Repair or bypass false/off-path Perron truncation statements instead of
   proving them as stated.

## Guardrails

- Do not prove `perron_tail_bound_core` as stated.
- Do not use a provider theorem that already consumes the provider class being
  supplied.
- Do not edit Atkinson, Pi/Phase, RS/Gabcke, or public main files.
- Do not run a full build.

## Requested Checks

- focused build for touched Perron/B5a module(s)
- strict public import probes for `Littlewood.Main.LittlewoodPsi` and
  `Littlewood.Main.LittlewoodPi`

## Session Log

### 2026-04-28 Launch

- Baseline: `acdc136`.
- Initial target: `shifted_remainder_bound_leaf`.
- Coordinator action: initial agent dispatched; Aristotle sidecar planned.

### 2026-04-28 Aristotle Harvest Integration

- Job: `43160ae0-78e7-4d7e-b8af-76332fd6c59f`.
- Classification: `NON_CIRCULAR_REDUCTION`.
- Target audited:
  `shifted_remainder_bound_leaf` and its small-T provider route.
- Result:
  the clean public-path shape is a reduction to two independent classes,
  `ShiftedRemainderSegmentBoundLargeTHyp` and
  `HadamardProductZeta.SmallTPerronBoundHyp`.
- Guardrail:
  do not derive small-T Perron from `shifted_remainder_bound_atomic`, because
  that route consumes the shifted-remainder provider class through the
  skeleton namespace and is circular.
- Failed route:
  do not prove or depend on `perron_tail_bound_core` as stated.
- Current lane guidance:
  the lane has already validated the exact-hit split. Continue on the
  punctured-window decaying kernel estimate, then off-boundary and compact
  residue extraction.
