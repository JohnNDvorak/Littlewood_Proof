# Agent Atkinson Ledger

Branch: `proofdebt/20260428-atkinson-large-j`

Worktree: `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260428/atkinson`

## Ownership

- Writable code: `Littlewood/Aristotle/Standalone/AtkinsonFormula.lean`
- Writable ledger: this file only.
- Coordinator-owned shared files are read-only.

## Live Targets

1. Close `atkinson_inversePhaseCorePrefix_bound_large_j`.
2. Package or validate `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`.
3. Record any irreducible smaller theorem if the direct closure fails.

## Guardrails

- Do not use `AtkinsonLargeShiftPrefixBoundHyp` circularly to prove the large
  shift provider.
- Do not import stale CloudDocs or quarantine files.
- Do not edit public main files or other lanes.
- Do not run a full build.

## Requested Checks

- `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`
- strict public import probes for `Littlewood.Main.LittlewoodPsi` and
  `Littlewood.Main.LittlewoodPi`

## Session Log

### 2026-04-28 Launch

- Baseline: `acdc136`.
- Initial target: `atkinson_inversePhaseCorePrefix_bound_large_j`.
- Coordinator action: initial agent dispatched; Aristotle sidecar planned.

### 2026-04-28 Round 1 Shifted Quadratic Anchor Split

- Classification: `CONDITIONAL_REDUCTION`, not closed.
- Theorem/file attacked:
  `Littlewood/Aristotle/Standalone/AtkinsonFormula.lean`,
  below
  `atkinson_blockMode_stationaryPhase_of_mode_eventual_shifted_interval_remainder`,
  which is the current non-circular public no-log route under the live
  `atkinson_inversePhaseCorePrefix_bound_large_j` gap.
- Facts banked:
  `atkinsonShiftedQuadraticAnchorModel` names the shifted quadratic-anchor
  model over `p ∈ Ioc j (j + 1)`, and
  `atkinson_mode_eventual_shifted_interval_remainder_of_quadratic_anchor_model`
  proves the mode-eventual native `blockMode` remainder from two smaller atoms:
  blockMode-to-quadratic-anchor control and quadratic-anchor target matching
  against `atkinsonCompleteBlockTargetK (n + j) j`.
- Failed routes:
  the direct predecessor-tail route through
  `atkinson_largeShiftPrefix_succ_htail_hypothesis_gamma_eight` still only
  gives coefficient `8`, so it cannot feed
  `atkinson_inversePhaseCorePrefix_bound_large_j_of_contracting_nextShift`
  where `γ < 1` is required. The existing public first-block
  `StationaryPhaseMainMode` theorems control `Ioc 0 1`, not the shifted
  interval `Ioc j (j + 1)`.
- Files changed:
  `Littlewood/Aristotle/Standalone/AtkinsonFormula.lean` and this ledger.
- Requested validation:
  `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  Strict public import probes for `Littlewood.Main.LittlewoodPsi` and
  `Littlewood.Main.LittlewoodPi` if the focused module passes.
- Next smallest theorem:
  prove the native shifted-interval quadratic-anchor approximation
  `∃ C_quad > 0, ∃ N_quad : ℕ, ∀ n : ℕ, N_quad ≤ n → ∀ j : ℕ,`
  `3 ≤ j → 1 ≤ j → j ≤ n →`
  `‖((((atkinsonModeWeight n : ℝ) : ℂ) * ∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),`
  `Aristotle.StationaryPhaseMainMode.blockMode n p * blockJacobian n p)`
  `- atkinsonShiftedQuadraticAnchorModel n j)‖`
  `≤ C_quad * (atkinsonModeWeight (n + j) / j)`, plus the companion target
  matching bound
  `‖atkinsonShiftedQuadraticAnchorModel n j - atkinsonCompleteBlockTargetK (n + j) j‖`
  `≤ C_target * (atkinsonModeWeight (n + j) / j)`.
- Coordinator action required:
  run the requested serialized validation; no local Lean/Lake/full-build
  validation was run in this round.
