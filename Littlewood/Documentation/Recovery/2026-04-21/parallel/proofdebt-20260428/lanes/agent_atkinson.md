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

### 2026-04-28 Coordinator Validation

- Commit `4e2e825` (`Reduce Atkinson shifted blockMode leaf`) passed:
  `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
- Branch was pushed to origin by the coordinator.

### 2026-04-28 Round 2 Zero-Model Anchor Replacement

- Classification: `CONDITIONAL_REDUCTION`, not closed.
- Theorem/file attacked:
  `Littlewood/Aristotle/Standalone/AtkinsonFormula.lean`, the first atom
  isolated in Round 1: the native shifted-interval quadratic-anchor
  approximation.
- Facts banked:
  `atkinsonShiftedQuadraticBlockModeZeroModel` names the shifted quadratic
  model before replacing `blockMode n 0` by the stationary anchor, and
  `atkinson_shifted_interval_quadratic_anchor_approx_of_zero_model_and_kernel_bound`
  uses the existing
  `Aristotle.StationaryPhaseMainMode.blockMode_zero_asymptotic` to reduce the
  quadratic-anchor approximation to two smaller atoms:
  zero-model approximation and a shifted quadratic-kernel integral bound with
  the required `1 / j` cancellation.
- Failed routes:
  `blockMode_quadratic_model_eventually` is only a pointwise first-block
  estimate on `p ∈ Icc 0 1`; applying it directly on
  `p ∈ Ioc j (j + 1)` is not available from the current API. A crude
  no-cancellation bound on the quadratic kernel integral is too large to
  combine with `blockMode_zero_asymptotic`; the kernel atom must provide the
  explicit shifted oscillatory `1 / j` gain.
- Files changed:
  `Littlewood/Aristotle/Standalone/AtkinsonFormula.lean` and this ledger.
- Requested validation:
  `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  Strict public import probes for `Littlewood.Main.LittlewoodPsi` and
  `Littlewood.Main.LittlewoodPi` if the focused module passes.
- Next smallest theorem:
  prove the shifted quadratic-kernel oscillatory bound
  `∃ C_kernel > 0, ∀ n j : ℕ, 3 ≤ j → 1 ≤ j → j ≤ n →`
  `‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),`
  `Aristotle.StationaryPhaseMainMode.quadraticKernel p * blockJacobian n p‖`
  `≤ C_kernel * ((((n : ℝ) + 1) / atkinsonModeWeight n) *`
  `(atkinsonModeWeight (n + j) / j))`, and separately prove the zero-model
  approximation against `atkinsonShiftedQuadraticBlockModeZeroModel`.
- Coordinator action required:
  run the requested serialized validation; no local Lean/Lake/full-build
  validation was run in this round.

### 2026-04-28 Coordinator Validation, Round 2

- Commit amended/pushed by coordinator as `16f1fd7`
  (`Reduce Atkinson anchor approximation to zero model`) passed:
  `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
- Hard rule update after coordinator intervention:
  do not run `lake`, `lake env lean`, `lean`, focused builds, or any
  compilation/check commands locally. All Lean/Lake validation is coordinator
  serialized.
- Note:
  a local `lake env lean Littlewood/Aristotle/Standalone/AtkinsonFormula.lean`
  diagnostic was started before this rule was clarified and was stopped by the
  coordinator; no usable diagnostic output was produced.

### 2026-04-28 Round 3 Kernel Integral Split

- Classification: `CONDITIONAL_REDUCTION`, not closed.
- Theorem/file attacked:
  `Littlewood/Aristotle/Standalone/AtkinsonFormula.lean`, the shifted
  quadratic-kernel integral bound introduced in Round 2.
- Facts banked:
  `atkinson_shifted_quadratic_kernel_integral_bound_of_mass_moment_scale`
  decomposes
  `∫ p in Ioc j (j + 1), quadraticKernel p * blockJacobian n p`
  using `blockJacobian_eq_affine`. The full kernel bound now follows from
  three smaller atoms: a shifted quadratic mass bound `O(1 / j)`, a uniformly
  bounded `4πp`-weighted shifted quadratic moment, and an elementary Atkinson
  weight-scale comparison.
- Failed routes:
  a crude norm bound on the kernel integral loses the oscillatory cancellation
  and leaves a term of size `n`, too large for the anchor-replacement step.
  The required input is the shifted Fresnel cancellation, not another
  no-cancellation integral estimate.
- Files changed:
  `Littlewood/Aristotle/Standalone/AtkinsonFormula.lean` and this ledger.
- Requested validation:
  `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  Strict public import probes for `Littlewood.Main.LittlewoodPsi` and
  `Littlewood.Main.LittlewoodPi` if the focused module passes.
- Next smallest theorem:
  prove the shifted quadratic mass bound
  `∃ C_mass > 0, ∀ j : ℕ, 1 ≤ j →`
  `‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),`
  `Aristotle.StationaryPhaseMainMode.quadraticKernel p‖ ≤ C_mass / j`,
  and the weighted moment companion
  `∃ C_moment > 0, ∀ j : ℕ, 1 ≤ j →`
  `‖∫ p in Ioc (j : ℝ) ((j : ℝ) + 1),`
  `(((4 * Real.pi * p : ℝ) : ℂ) * Aristotle.StationaryPhaseMainMode.quadraticKernel p)‖`
  `≤ C_moment`.
- Coordinator action required:
  run the requested serialized validation; no local Lean/Lake/build/check
  validation should be run by this lane agent.
