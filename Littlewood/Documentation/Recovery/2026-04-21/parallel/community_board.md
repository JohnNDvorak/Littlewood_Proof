# Parallel Recovery Community Board

Date: 2026-04-27 CDT

Launch ID: `overnight-20260428`

This is the tracked coordination board for the four-agent recovery run. The
baseline commit is the commit that first contains this file.

## Baseline

- Repository: `JohnNDvorak/Littlewood_Proof`
- Baseline branch: `recovery/provider-forensics-2026-04-21`
- Baseline commit: `d2a6f8555c3ff8107a3559eeb6d3a774eef5f30b`
- Draft PR: pending until the baseline branch is pushed
- Certification required before launch:
  - `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`
  - `lake build`
  - minimal public imports for `Littlewood.Main.LittlewoodPsi`
  - minimal public imports for `Littlewood.Main.LittlewoodPi`

## Overnight Worktrees

- Coordinator tree: `/Users/john.n.dvorak/Projects/Littlewood_Proof`
- Worktree root: `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/overnight-20260428`
- Old `codex/*` worktrees are stale at commit `0993b9d58ab47dd7cbfa8875b1a14b6e1765bae9`
  and are read-only for this run.

## Coordination Rules

- Every agent reads this board and all four lane ledgers before editing.
- Each agent may update only its own lane ledger under `parallel/lanes/`.
- The coordinator is the only writer for this board, public API files, and merge
  queue state.
- Agents may inspect all files, but code edits must stay inside the lane
  ownership listed below.
- Shared interface edits require a handoff note in the lane ledger and a
  coordinator merge.
- Do not commit API keys, Aristotle keys, or generated self-drive runtime logs.
  Use environment variables for credentials.
- Aristotle may be used only as a targeted sidecar for narrowed
  theorem-shaped subgoals. Raw prompts/results stay untracked; durable findings
  go in the lane ledger.
- Do not try to prove `TruncatedExplicitFormulaPiHyp.pi_approx` as stated; it is
  documented as mathematically false.
- Do not route `SmallTPerronBoundHyp` through a theorem that already depends on
  `SmallTPerronBoundHyp`.
- Full project builds are coordinator-only. No agent may run bare `lake build`.
- While worktrees are cold, all Lake commands are coordinator-scheduled. Agents
  should record requested validation commands in their lane ledgers instead of
  starting builds themselves.
- Exactly one Lean/Lake validation job may run at a time across the whole
  machine.
- Green lane work may be committed and pushed for durability, but no lane branch
  is auto-merged into the recovery branch overnight.

## Lanes

| Lane | Branch | Writable ledger | Owned code surface | Primary target |
| --- | --- | --- | --- | --- |
| Atkinson | `overnight/20260428-atkinson` | `lanes/agent_atkinson.md` | `Littlewood/Aristotle/Standalone/AtkinsonFormula.lean` | Close the large-`j` no-log public Atkinson leaf and the direct-Abel cleanup leaf. |
| Perron/Hadamard | `overnight/20260428-perron-hadamard` | `lanes/agent_perron_hadamard.md` | Perron, Hadamard, and small-`T` provider files | Produce a non-circular provider path for the small-`T` Perron surface. |
| Pi/Phase | `overnight/20260428-pi-phase` | `lanes/agent_pi_phase.md` | Pi oscillation, phase, exact-seed, and compatibility files | Repair or bypass false `pi_approx` usage and keep the public pi path honest. |
| RS/Gabcke | `overnight/20260428-rs-gabcke` | `lanes/agent_rs_gabcke.md` | RS, Siegel, Gabcke, and Hardy first-moment bridge files | Close or sharply reduce the RS/Gabcke coupling surfaces without touching Atkinson. |

## Coordinator-Owned Shared Files

- `Littlewood/Main/LittlewoodPsi.lean`
- `Littlewood/Main/LittlewoodPi.lean`
- `Littlewood/CriticalAssumptions.lean`
- `Littlewood/Aristotle/DeepSorries.lean`
- `Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean`
- this `community_board.md`

Lane agents may request changes to these files in their own ledger, but should
not edit them directly.

## Current Public Gaps

1. `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`
   - Active public Atkinson provider gap.
   - First attack: no-log inverse-phase cell-prefix estimate for large `j`,
     then finite `j = 1, 2` patch.
2. `SmallTPerronBoundHyp`
   - Must be proved without circular dependence on the full contour remainder
     provider that consumes it.
3. `TruncatedExplicitFormulaPiHyp`
   - The `pi_approx` field is false as stated. Treat this as an interface
     repair or bypass problem, not a theorem-proving target.
4. RS/Gabcke coupling
   - Keep separate from Atkinson so both lanes can progress without file
     conflicts.

## Merge Queue

| Order | Branch | Status | Required checks |
| --- | --- | --- | --- |
| 1 | `overnight/20260428-atkinson` | launched | focused Atkinson build, public import checks |
| 2 | `overnight/20260428-perron-hadamard` | launched | focused provider build, public import checks |
| 3 | `overnight/20260428-pi-phase` | launched | focused pi/phase build, public import checks |
| 4 | `overnight/20260428-rs-gabcke` | launched | focused RS/Gabcke build, public import checks |

## Update Protocol

At the end of each work session, each agent appends to its own ledger:

- current theorem or file attacked
- exact command results, or requested validation commands if the build mutex is
  active
- proof facts banked
- failed routes that should not be retried
- smallest next theorem or diagnostic
- whether coordinator action is requested
