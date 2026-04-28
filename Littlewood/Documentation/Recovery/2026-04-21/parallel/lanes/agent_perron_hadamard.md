# Agent Perron/Hadamard Ledger

Branch: `codex/perron-hadamard`

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
