# Proof-Debt Community Board

Date: 2026-04-28 CDT

Launch ID: `proofdebt-20260428`

## Baseline

- Repository: `JohnNDvorak/Littlewood_Proof`
- Coordinator branch: `recovery/provider-forensics-2026-04-21`
- Baseline tag: `recovered-baseline-2026-04-28`
- Baseline commit: `acdc136`
- Rollback tags:
  - `pre-recovered-baseline-2026-04-28`
  - `recovered-mainchain-2026-04-28`
  - `recovered-baseline-2026-04-28`
- Stale worktree diffs archived under:
  `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/archive-20260428-*`

## Hard Rules

- Exactly one Lean/Lake validation job may run at a time across the machine.
- Full project builds are coordinator-only.
- Agents may inspect all files, but may edit only their lane-owned code and
  their own lane ledger.
- Coordinator owns public API files, shared proof assembly files, this board,
  integration, pushes, and Aristotle harvesting.
- Do not commit API keys, Aristotle runtime logs, raw prompt payloads, or
  downloaded result archives.
- Aristotle is a theorem-shaped sidecar only. Durable findings go into lane
  ledgers as reductions, failed routes, or exact Lean snippets.

## Active Worktrees

| Lane | Agent | Branch | Worktree | Ledger |
| --- | --- | --- | --- | --- |
| Atkinson | Hooke | `proofdebt/20260428-atkinson-large-j` | `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260428/atkinson` | `lanes/agent_atkinson.md` |
| Perron/B5a | Halley | `proofdebt/20260428-perron-b5a` | `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260428/perron-b5a` | `lanes/agent_perron_b5a.md` |
| Pi/Phase | Planck | `proofdebt/20260428-pi-phase` | `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260428/pi-phase` | `lanes/agent_pi_phase.md` |
| RS/Gabcke | Hume | `proofdebt/20260428-rs-gabcke` | `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260428/rs-gabcke` | `lanes/agent_rs_gabcke.md` |

All active worktrees symlink `.lake` to the coordinator tree cache.

## Current Targets

1. Atkinson:
   close `atkinson_inversePhaseCorePrefix_bound_large_j` and then package or
   validate `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`.
2. Perron/B5a:
   close `shifted_remainder_bound_leaf` or reduce it to a strictly smaller,
   non-circular Perron/Hadamard theorem.
3. Pi/Phase:
   remove public reliance on the false `TruncatedExplicitFormulaPiHyp.pi_approx`
   route and produce Perron-only target/anti-target phase coupling providers.
4. RS/Gabcke:
   reduce/prove `SiegelSaddleExpansionHyp` and the explicit Gabcke adjacent
   coefficient identity, nonnegativity, and antitonicity atoms.

## Validation Queue

Agents request validation in their lane ledger. The coordinator serializes:

1. focused build for the touched module(s),
2. strict public import probes for `Littlewood.Main.LittlewoodPsi` and
   `Littlewood.Main.LittlewoodPi`,
3. `#print axioms` / `#synth` probes only after a public-path closure,
4. full `lake build Littlewood` only at major checkpoints.

## Merge Queue

| Order | Branch | Status | Required before merge |
| --- | --- | --- | --- |
| 1 | `proofdebt/20260428-atkinson-large-j` | active | focused Atkinson build + public import probes |
| 2 | `proofdebt/20260428-perron-b5a` | active | focused Perron/B5a builds + public import probes |
| 3 | `proofdebt/20260428-pi-phase` | active | focused Pi/Phase builds + public import probes |
| 4 | `proofdebt/20260428-rs-gabcke` | active | focused RS/Gabcke builds + public import probes |

## Agent Report Contract

Each agent report must state:

- exact theorem/file attacked,
- files changed,
- proof facts banked,
- failed routes that must not be retried,
- requested validation command,
- smallest next theorem,
- whether coordinator action is required.

## Coordinator Status

- Setup completed from `acdc136`.
- Fresh worktrees created and stale worktrees preserved.
- Initial lane agents dispatched.
- Initial Aristotle sidecars submitted:
  - Atkinson: `b895c2cb-ccbc-4edc-b13a-8076b5be5eb6`
  - Perron/B5a: `43160ae0-78e7-4d7e-b8af-76332fd6c59f`
  - Pi/Phase: `32a1df6a-be94-4cc2-81c3-05623533b222`
  - RS/Gabcke: `381b8764-543a-4024-a84f-9a9f91be9eba`
- Atkinson lane produced local commit `4e2e825`
  (`Reduce Atkinson shifted blockMode leaf`), a conditional reduction from
  the native shifted `blockMode` remainder to two quadratic-anchor atoms.
- Coordinator validation completed for Atkinson:
  `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula` passed in the
  Atkinson worktree on 2026-04-28.
- Next coordinator action: harvest Aristotle results as they complete, then
  validate and integrate lane commits in merge-queue order. Keep public import
  probes for `Littlewood.Main.LittlewoodPsi` and `Littlewood.Main.LittlewoodPi`
  queued until a lane closes a public-path provider rather than just a
  conditional reduction.
