# Agent Pi/Phase Ledger

Branch: `overnight/20260428-pi-phase`

Worktree: `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/overnight-20260428/pi-phase`

## Ownership

- Writable code: pi oscillation, phase coupling, exact-seed, and compatibility
  files.
- Writable ledger: this file only.
- Coordinator-owned shared files are read-only unless explicitly reassigned.

## Live Targets

1. Repair or bypass downstream dependence on the false
   `TruncatedExplicitFormulaPiHyp.pi_approx` field.
2. Keep the public pi path on theorem statements that are mathematically true.
3. Coordinate any interface change through the community board before touching
   public API files.

## Guardrails

- Do not prove `TruncatedExplicitFormulaPiHyp.pi_approx` as stated; the
  singleton/empty-set analysis marks it false.
- Do not edit Atkinson files.
- Do not edit `Littlewood/Main/LittlewoodPi.lean` directly.
- If a replacement class is needed, state the exact proposed interface here
  before code edits.

## Required Checks

- Validation is coordinator-owned while cold worktrees are memory constrained.
  Lane agents must not run Lean/Lake/build commands locally.
- focused build of the touched pi/phase module, when coordinator serializes it
- minimal import check for `Littlewood.Main.LittlewoodPi`
- minimal import check for `Littlewood.Main.LittlewoodPsi`

## Session Log

### 2026-04-27 Overnight Launch

- Status: lane relaunched from recovery commit
  `d2a6f8555c3ff8107a3559eeb6d3a774eef5f30b`.
- Build policy: request coordinator validation; do not run full `lake build`.
- Aristotle policy: targeted theorem-shaped sidecar only; no credentials or raw
  runtime logs in tracked files.
- Current smallest target remains the coordinated provider split away from the
  false `TruncatedExplicitFormulaPiHyp.pi_approx` surface.

### 2026-04-27 Baseline

- Status: lane created.
- Current smallest target: honest replacement or bypass for false `pi_approx`
  usage.
- Coordinator action requested: none.

### 2026-04-27 Pi Approx Interface Audit

- Status: LOCAL_REDUCTION_PENDING_VALIDATION.
- Current theorem/file attacked:
  - `RHPiPerronFromTruncatedPiBridge.lean`
  - `RHPiTargetTowerFromPerronThreshold.lean`
  - `RHPiArgApproxFromPerronThreshold.lean`
  - downstream phase/corrected/coeff-control wrappers.
- Change made:
  - Added honest replacement class
    `PerronSqrtErrorEventuallyAtHeightHyp`, carrying exactly the fixed-height
    eventual `sqrt/log` Perron error bound consumed by `perronThreshold`.
  - Repointed `perronThreshold`, phase-above-threshold, arg-above-threshold,
    phase-coupling, corrected-canonical, and phase/coeff-control wrappers to
    require `PerronSqrtErrorEventuallyAtHeightHyp` instead of the full false
    `TruncatedExplicitFormulaPiHyp`.
  - Kept one compatibility instance
    `perronSqrtErrorEventuallyAtHeightHyp_of_truncatedPiBridge` for legacy
    consumers; this is now the single local bridge from false `pi_approx` to the
    repaired threshold surface.
- Exact consumers still requiring false `pi_approx`:
  - `PiLiDirectOscillation.lean`: legacy direct oscillation extraction calls
    `TruncatedExplicitFormulaPiHyp.pi_approx` in both `omega_minus_from_zeros`
    and `omega_plus_from_zeros`. The public route has a higher-priority Landau
    instance, so this is compatibility/dead-risk, not the intended public path.
  - `RHPiPerronFromTruncatedPiBridge.lean`: the compatibility theorem
    `perron_sqrt_error_eventually_at_height_of_truncatedPiBridge` calls
    `pi_approx` to manufacture the honest fixed-height surface.
  - `PerronExplicitFormulaProvider.lean`: still owns
    `PerronPiApproxCompatibilityHyp`, constructs
    `pi_explicit_formula_from_perron`, and has exact-seed declarations using
    `@TargetTowerExactSeedAbovePerronThreshold pi_explicit_formula_from_perron`.
    I did not edit this coordinator/Perron-owned provider.
- Proof facts banked:
  - The public `LittlewoodPi.littlewood_pi_li` theorem body uses
    `DeepSorries.pi_li_full_strength_oscillation`, not a direct `.pi_approx`
    call.
  - The honest threshold/arg/phase wrappers only need fixed-height eventual
    Perron error and can be stated without the arbitrary finite-set
    `pi_approx` field.
- Failed/avoided route:
  - I started moving exact-seed payload types to the new class, then static
    review found provider-owned explicit applications
    `@TargetTowerExactSeedAbovePerronThreshold pi_explicit_formula_from_perron`.
    Completing that move requires coordinated edits in
    `PerronExplicitFormulaProvider.lean`, so I narrowed the local change and did
    not touch the provider.
- Command results:
  - `git status --short --branch`: clean at start on `codex/pi-phase`.
  - `rg`/`sed` audits found direct `.pi_approx` calls in
    `PiLiDirectOscillation.lean`, `RHPiPerronFromTruncatedPiBridge.lean`, and
    `PerronExplicitFormulaProvider.lean`; public main files only carry typeclass
    variables.
  - Attempted focused check
    `lake build Littlewood.Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox`
    before the coordinator rule changed; it was interrupted during cold
    dependency build and produced no module result.
  - After the updated coordinator rule, no Lake commands were run.
- Validation deferred by coordinator rule. Requested commands when validation is
  serialized:
  - `lake build Littlewood.Aristotle.Standalone.RHPiTargetTowerFromPerronThreshold`
  - `lake build Littlewood.Aristotle.Standalone.RHPiArgApproxFromPerronThreshold`
  - `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromThresholdBridge`
  - `lake build Littlewood.Aristotle.Standalone.RHPiPhasePerronSynthesis`
  - `lake build Littlewood.Aristotle.Standalone.RHPiDeepCoeffControlWitnesses`
  - minimal import probe for `Littlewood.Main.LittlewoodPi`
- Smallest next theorem/interface:
  - Coordinator-owned: split the provider exact-seed declarations so
    `TargetTowerExactSeedAbovePerronThreshold` and
    `AntiTargetTowerExactSeedAbovePerronThreshold` are parameterized by
    `PerronSqrtErrorEventuallyAtHeightHyp`, with a separate legacy theorem that
    derives that class from `pi_explicit_formula_from_perron` only for backward
    compatibility.
- Coordinator action requested:
  - Validate the listed focused modules under serialized Lake policy.
  - If accepted, plan a coordinated provider edit to remove the remaining
    exact-seed dependence on `TruncatedExplicitFormulaPiHyp`.

### 2026-04-28 First Overnight Round

- Classification: LOCAL_INTERFACE_SPLIT_PENDING_VALIDATION.
- Current theorem/file attacked:
  - `RHPiExactSeedToPerronThresholdArgApprox.lean`
  - `RHPiPhaseCouplingFromExactSeedBridge.lean`
  - `RHPiCoeffControlClassInstances.lean`
  - `RHPiDeepCoeffControlWitnesses.lean`
- Changed interfaces:
  - Added Perron-only exact-seed payload aliases
    `TargetTowerExactSeedAbovePerronThresholdPerron` and
    `AntiTargetTowerExactSeedAbovePerronThresholdPerron`.
  - Added class wrappers
    `TargetTowerExactSeedAbovePerronThresholdPerronHyp` and
    `AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp`.
  - Added Perron-only bridges from exact-seed payloads to
    `TargetTowerArgApproxAbovePerronThresholdHyp`,
    `AntiTargetTowerArgApproxAbovePerronThresholdHyp`,
    phase-coupling classes, RH-`pi` witness data, 7a/7c endpoints, and B7
    coefficient-control endpoints.
- Files changed:
  - `Littlewood/Aristotle/Standalone/RHPiExactSeedToPerronThresholdArgApprox.lean`
  - `Littlewood/Aristotle/Standalone/RHPiPhaseCouplingFromExactSeedBridge.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCoeffControlClassInstances.lean`
  - `Littlewood/Aristotle/Standalone/RHPiDeepCoeffControlWitnesses.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/lanes/agent_pi_phase.md`
- False-surface audit after this split:
  - New Perron-only exact-seed interfaces do not require
    `TruncatedExplicitFormulaPiHyp`.
  - Legacy exact-seed names remain in place for compatibility and still require
    `TruncatedExplicitFormulaPiHyp`.
  - Provider declarations still consuming the false surface:
    `PerronExplicitFormulaProvider.truncatedPiHyp_contradicts_rh` calls
    `TruncatedExplicitFormulaPiHyp.pi_approx`; the local instance
    `InhomogeneousPhaseFitAbovePerronThresholdHyp` is synthesized from that
    contradiction; `arg_above_threshold_from_perron_core`,
    `arg_above_threshold_pair_from_perron_core`,
    `exact_seed_pair_from_perron_core`, `target_exact_seed_from_perron`, and
    `anti_target_exact_seed_from_perron` still flow through the legacy
    provider/class shape.
  - `RHPiPerronFromTruncatedPiBridge.perron_sqrt_error_eventually_at_height_of_truncatedPiBridge`
    remains the compatibility bridge from the false legacy field to the honest
    fixed-height Perron surface.
- Likely first compile-risk area:
  - `RHPiDeepCoeffControlWitnesses.lean`, explicit arguments of the new
    abbrev forms
    `@TargetTowerExactSeedAbovePerronThresholdPerron hPerron` and
    `@AntiTargetTowerExactSeedAbovePerronThresholdPerron hPerron`, matching the
    existing legacy style but unvalidated.
  - Secondary risk: instance search diamonds where both legacy exact-seed
    classes and Perron-only exact-seed classes are present.
- Commands run:
  - Static only: `git status --short --branch`, `rg`, `sed`, and `git diff`.
  - No Lean/Lake/build commands were run.
- Requested coordinator validation, in order:
  - `lake build Littlewood.Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox`
  - `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
  - `lake build Littlewood.Aristotle.Standalone.RHPiCoeffControlClassInstances`
  - `lake build Littlewood.Aristotle.Standalone.RHPiDeepCoeffControlWitnesses`
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
  - minimal import probe for `Littlewood.Main.LittlewoodPi`
  - minimal import probe for `Littlewood.Main.LittlewoodPsi`
- Smallest next theorem/interface:
  - Provider-owned: add an honest provider theorem producing
    `TargetTowerExactSeedAbovePerronThresholdPerron` and
    `AntiTargetTowerExactSeedAbovePerronThresholdPerron` directly from a
    Perron-only inhomogeneous phase-fit boundary, then leave legacy
    `target_exact_seed_from_perron` and `anti_target_exact_seed_from_perron` as
    compatibility wrappers only.

### 2026-04-28 Coordinator Validation

- `lake build Littlewood.Aristotle.Standalone.RHPiExactSeedToPerronThresholdArgApprox`: passed.
- `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`: passed.
- `lake build Littlewood.Aristotle.Standalone.RHPiCoeffControlClassInstances`: passed.
- `lake build Littlewood.Aristotle.Standalone.RHPiDeepCoeffControlWitnesses`: passed.
- `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`: passed.
- Residual risk: the provider still consumes the false legacy surface through
  `truncatedPiHyp_contradicts_rh`, `InhomogeneousPhaseFitAbovePerronThresholdHyp`,
  `exact_seed_pair_from_perron_core`, `target_exact_seed_from_perron`, and
  `anti_target_exact_seed_from_perron`. The next provider move should construct
  Perron-only exact-seed payloads from an honest Perron-only inhomogeneous
  phase-fit boundary.
