# Agent Perron/Hadamard Ledger

Branch: `overnight/20260428-perron-hadamard`

Worktree: `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/overnight-20260428/perron-hadamard`

## Ownership

- Writable code: Perron, Hadamard, small-`T`, and shifted-remainder provider
  files.
- Writable ledger: this file only.
- Coordinator-owned shared files are read-only unless explicitly reassigned.

## Live Targets

1. Establish a non-circular provider path for `SmallTPerronBoundHyp`.
2. Audit Hadamard/Perron bridges for hidden dependence on the class being
   supplied.
3. Produce theorem-level handoff notes for any remaining analytic atom instead
   of routing through circular packaging.

## Guardrails

- Do not use `ContourRemainderBoundHyp.bound` to prove `SmallTPerronBoundHyp`
  if that contour provider already consumes `SmallTPerronBoundHyp`.
- Do not edit Atkinson files.
- Do not edit public main files directly.
- Treat generated self-drive runtime files as non-durable; record durable state
  here.

## Required Checks

- focused build of the touched Perron/Hadamard module
- minimal import check for `Littlewood.Main.LittlewoodPsi`
- minimal import check for `Littlewood.Main.LittlewoodPi`
- `lake build` before requesting merge

## Session Log

### 2026-04-27 Overnight Launch

- Status: lane relaunched from recovery commit
  `d2a6f8555c3ff8107a3559eeb6d3a774eef5f30b`.
- Build policy: request coordinator validation; do not run full `lake build`.
- Aristotle policy: targeted theorem-shaped sidecar only; no credentials or raw
  runtime logs in tracked files.
- Current smallest target remains a direct non-circular proof input for
  `HadamardProductZeta.small_T_perron_bound_hyp_of_direct_bound`.

### 2026-04-27 Baseline

- Status: lane created.
- Current smallest target: non-circular small-`T` Perron provider.
- Coordinator action requested: none.

### 2026-04-27 Perron/Hadamard Static Audit

- Current theorem/file attacked:
  `Littlewood/Development/HadamardProductZeta.lean`,
  `SmallTPerronBoundHyp`.
- Code change:
  added two non-instance provider adapters:
  `small_T_perron_bound_hyp_of_direct_bound` packages the exact direct
  small-`T` theorem into `SmallTPerronBoundHyp`;
  `small_T_perron_bound_hyp_of_global_bound` restricts an independently
  supplied full shifted-remainder bound to the small-`T` provider surface.
- Audit result:
  no existing non-circular instance provider for
  `Littlewood.Development.HadamardProductZeta.SmallTPerronBoundHyp` was found.
  Existing source uses are variables/wrappers, except
  `ExplicitFormulaPsiB5aDefs.SmallTPerronBoundHyp`, which is a separate local
  class and its instance delegates back to
  `HadamardProductZeta.perron_small_T_bound`.
- Exact circular edge not to retry:
  `PerronAssumptionsBridge.small_T_contour_bound`
  → `general_formula_accessible`
  → `PerronExplicitFormulaProvider.general_explicit_formula_from_perron`
  → `shifted_remainder_bound_from_perron`
  → `contour_shift_atomic`
  → `contour_integral_remainder_bound`
  → `ExplicitFormulaPsiB5aDefs.ContourRemainderBoundHyp.bound`
  → `ExplicitFormulaPsiB5aDefs.contour_from_small_T`
  → `ExplicitFormulaPsiB5aDefs.SmallTPerronBoundHyp.bound`
  → `HadamardProductZeta.perron_small_T_bound`
  → `HadamardProductZeta.SmallTPerronBoundHyp.bound`.
- Smallest next theorem that breaks the cycle:
  prove the direct hypothesis of
  `HadamardProductZeta.small_T_perron_bound_hyp_of_direct_bound`, namely
  `∃ C₂ > 0, ∀ x T, x ≥ 2 → 2 ≤ T → T ≤ 16 →
    |shiftedRemainderRe x T| ≤
      C₂ * (Real.sqrt x * (Real.log T)^2 / Real.sqrt T + (Real.log x)^2)`,
  without using `ContourRemainderBoundHyp.bound`,
  `general_formula_accessible`, or any theorem consuming
  `SmallTPerronBoundHyp`.
- Static checks run:
  `git diff --check` succeeded.
  `git status --short` showed only
  `M Littlewood/Development/HadamardProductZeta.lean` before this ledger edit.
- Validation status:
  attempted focused `lake build Littlewood.Development.HadamardProductZeta`,
  but cold dependency compilation was stopped/then interrupted under the
  coordinator memory-serialization rule; no Lake validation is certified from
  this lane session.
- Requested coordinator validation commands, when serialization permits:
  `lake build Littlewood.Development.HadamardProductZeta`;
  minimal import probe for `Littlewood.Main.LittlewoodPsi`;
  minimal import probe for `Littlewood.Main.LittlewoodPi`.
- Coordinator action requested:
  run the above serialized validation commands; no full `lake build` requested
  by this lane.

### 2026-04-28 Overnight Round 1

- Classification: `CONDITIONAL_REDUCTION`.
- Current theorem/file attacked:
  `Littlewood/Development/HadamardProductZeta.lean`,
  `SmallTPerronBoundHyp`.
- Theorem added:
  `HadamardProductZeta.small_T_direct_bound_from_three_piece_bounds`.
- Reduction banked:
  the exact direct hypothesis of
  `HadamardProductZeta.small_T_perron_bound_hyp_of_direct_bound` now follows
  from a strictly theorem-shaped three-piece bounded-height decomposition:
  two pieces bounded by
  `P * (Real.sqrt x * (Real.log T)^2 / Real.sqrt T)` and one bookkeeping piece
  bounded by `P * (Real.log x)^2`, uniformly for `2 ≤ T ≤ 16`.
  The assembly is triangle inequality plus nonnegativity of the two error
  channels, with output constant `3 * P`.
- Circular routes avoided:
  did not use `ContourRemainderBoundHyp.bound`,
  `general_formula_accessible`, `small_T_contour_bound`, or any theorem that
  consumes `HadamardProductZeta.SmallTPerronBoundHyp`.
- Files changed:
  `Littlewood/Development/HadamardProductZeta.lean`;
  this ledger.
- Static command results:
  `git diff --check` succeeded with no output.
  No Lean/Lake/build/cache commands were run in this round.
- Smallest next theorem:
  prove the hypothesis of
  `small_T_direct_bound_from_three_piece_bounds` by constructing the concrete
  bounded-height Perron/residue/log pieces for
  `shiftedRemainderRe x T`, uniformly on `2 ≤ T ≤ 16`, without routing through
  full-range contour packaging.
- Requested coordinator validation commands:
  `lake build Littlewood.Development.HadamardProductZeta`;
  minimal import probe for `Littlewood.Main.LittlewoodPsi`;
  minimal import probe for `Littlewood.Main.LittlewoodPi`.
- Coordinator action requested:
  run serialized validation when the build mutex permits; no full project build
  requested by this lane.

### 2026-04-28 Coordinator Validation, Round 2

- `lake build Littlewood.Development.HadamardProductZeta`: passed.
- `import Littlewood.Main.LittlewoodPsi`: passed.
- `import Littlewood.Main.LittlewoodPi`: passed.
- Validation output included linter warnings in existing imported files and
  unused-variable warnings in `HadamardProductZeta.lean`; no errors.
- This round remains a conditional reduction. The live theorem is now the
  concrete bounded-height construction of `perronIntegralRe` plus the two
  component estimates recorded above.

### 2026-04-28 Coordinator Validation

- First validation found an elaboration issue in
  `small_T_direct_bound_from_three_piece_bounds`: `abs_add` was not available
  under that name in this module.
- Coordinator patch: replaced the two triangle-inequality calls by
  `abs_add_le`.
- `lake build Littlewood.Development.HadamardProductZeta`: passed.
- Residual risk: this is still a conditional reduction; the concrete
  three-piece bounded-height decomposition remains open.

### 2026-04-28 Overnight Continuation

- Classification: `CONDITIONAL_REDUCTION`.
- Current theorem/file attacked:
  `Littlewood/Development/HadamardProductZeta.lean`,
  concrete small-`T` decomposition below `SmallTPerronBoundHyp`.
- Theorems added:
  `HadamardProductZeta.small_T_three_piece_bounds_from_perron_components`;
  `HadamardProductZeta.small_T_direct_bound_from_perron_components`.
- Reduction banked:
  the three-piece bounded-height decomposition now follows from a single
  concrete Perron integral `perronIntegralRe` satisfying two uniform estimates
  on `2 ≤ T ≤ 16`:
  `|chebyshevPsi x - perronIntegralRe x T| ≤ Cₚ * (Real.log x)^2`
  and
  `|perronIntegralRe x T - (x - zeroSumRe x T)| ≤
    Cᵣ * (Real.sqrt x * (Real.log T)^2 / Real.sqrt T)`.
  The decomposition identity used is
  `ψ - x + Z = (Perron - (x - Z)) + 0 + (ψ - Perron)`,
  with output three-piece constant `max Cₚ Cᵣ`; composing with
  `small_T_direct_bound_from_three_piece_bounds` gives the direct small-`T`
  provider hypothesis.
- Circular routes avoided:
  did not use `ContourRemainderBoundHyp.bound`,
  `general_formula_accessible`, `small_T_contour_bound`, or any theorem that
  consumes `HadamardProductZeta.SmallTPerronBoundHyp`.
- Files changed:
  `Littlewood/Development/HadamardProductZeta.lean`;
  this ledger.
- Static command results:
  `git diff --check` succeeded with no output.
  No Lean/Lake/build/cache commands were run in this continuation.
- Smallest next theorem:
  construct the concrete bounded-height Perron integral `perronIntegralRe` and
  prove the two component estimates above directly from bounded-height Perron
  summation plus residue/contour extraction, without routing through full-range
  contour packaging.
- Requested coordinator validation commands:
  `lake build Littlewood.Development.HadamardProductZeta`;
  minimal import probe for `Littlewood.Main.LittlewoodPsi`;
  minimal import probe for `Littlewood.Main.LittlewoodPi`.
- Coordinator action requested:
  run serialized validation when the build mutex permits; no full project build
  requested by this lane.
