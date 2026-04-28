# Parallel Recovery Community Board

Date: 2026-04-28 CDT

Launch ID: `overnight-20260428`

This is the tracked coordination board for the four-agent recovery run. The
baseline commit is the commit that first contains this file.

## Baseline

- Repository: `JohnNDvorak/Littlewood_Proof`
- Baseline branch: `recovery/provider-forensics-2026-04-21`
- Baseline commit: `d2a6f8555c3ff8107a3559eeb6d3a774eef5f30b`
- Coordination commit: `4a204b7`
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
- Green lane work may be committed and pushed for durability. Lane branches are
  merged into the recovery branch only by the coordinator after serialized
  validation.

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
   - Current reduction: prove the mode-eventual shifted-interval native
     `StationaryPhaseMainMode.blockMode` estimate:
     `∃ C_err > 0, ∃ N_err, ∀ n ≥ N_err, ∀ j ≥ 3, j ≤ n → ... ≤
     C_err * (atkinsonModeWeight (n + j) / j)`.
   - The older large-shift direct-Abel debt remains isolated and should be
     cleaned up after the public leaf is closed.
2. `SmallTPerronBoundHyp`
   - Must be proved without circular dependence on the full contour remainder
     provider that consumes it.
   - Current reduction: prove the finite weighted Perron-kernel cutoff estimate
     `perronKernelWeightedCutoffError x T ≤ Cw * (Real.log x)^2` for
     `x ≥ 2`, `2 ≤ T ≤ 16`.
3. Perron-only pi phase boundary
   - The false `TruncatedExplicitFormulaPiHyp.pi_approx` route is bypassed in
     the new Perron-only path.
   - Current remaining leaves:
     `PerronThresholdTowerDominationHyp` and
     `FiniteZeroInhomogeneousPhaseWindowHyp`.
4. RS/Gabcke coupling
   - Current reduction: define the explicit signed first Gabcke coefficient
     formula `C k p` and prove the identity, nonnegativity, and adjacent
     antitonicity atoms for `normalizedSignedSPR`.

## Merge Queue

| Order | Branch | Status | Required checks |
| --- | --- | --- | --- |
| 1 | `overnight/20260428-atkinson` | merged: `d506491` from `f393526` | focused Atkinson build passed; public `Psi`/`Pi` import probes passed |
| 2 | `overnight/20260428-perron-hadamard` | merged: `1d7f253` from `20b39f2` | focused PerronTruncationInfra build passed; public `Psi`/`Pi` import probes passed |
| 3 | `overnight/20260428-pi-phase` | merged: `6b6f567` from `881d196` | focused PerronExplicitFormulaProvider build passed; public `Psi`/`Pi` import probes passed |
| 4 | `overnight/20260428-rs-gabcke` | merged: `d70d921` from `887db7a` | focused RS/Gabcke/Hardy builds passed; public `Psi`/`Pi` import probes passed |

## Coordinator Status

- Main recovery branch is ahead of `origin/recovery/provider-forensics-2026-04-21`
  by validated coordination/checkpoint/integration commits.
- Strict public import probes on the main recovery branch passed:
  - `import Littlewood.Main.LittlewoodPsi`
  - `import Littlewood.Main.LittlewoodPi`
- All fresh overnight worktrees reuse the main `.lake` cache through local
  symlinks; `.lake` is excluded locally and must remain untracked.
- No full `lake build` has been run in this overnight coordinator pass.
- Integrated head after lane merges: `d70d921`.
- Current next pass should continue from the integrated heads. Coordinator
  remains the sole Lean/Lake validator, with exactly one Lean/Lake validation
  job allowed at a time.

## Current Lane Heads

- Atkinson: `f393526 Reduce Atkinson blockMode estimate to mode form`
- Perron/Hadamard:
  `20b39f2 Reduce Perron kernel cutoff to weighted error`
- Pi/Phase:
  `881d196 Reduce pi phase window to tower domination`
- RS/Gabcke:
  `887db7a Atomize Gabcke coefficient boundary`

## Newly Exposed Debt

- `PerronTruncationInfra.perron_vertical_eq_tsum` remains an explicit private
  `sorry` leaf, separate from the newly reduced finite weighted cutoff atom.
- Perron/Hadamard still needs the finite weighted cutoff proof near the sharp
  `n = x` boundary, then the small-`T` provider can be packaged honestly.
- Atkinson's public leaf is reduced to a native mode-eventual shifted-interval
  `blockMode` stationary-phase estimate.
- Pi/Phase's Perron-only path needs same-height tower domination plus a
  bounded-window finite inhomogeneous phase theorem.
- RS/Gabcke signed coupling is reduced to an explicit normalized Gabcke
  coefficient identity plus nonnegativity and adjacent antitonicity.

## Update Protocol

At the end of each work session, each agent appends to its own ledger:

- current theorem or file attacked
- exact command results, or requested validation commands if the build mutex is
  active
- proof facts banked
- failed routes that should not be retried
- smallest next theorem or diagnostic
- whether coordinator action is requested
