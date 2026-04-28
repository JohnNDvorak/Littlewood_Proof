# Agent Pi/Phase Ledger

Branch: `codex/pi-phase`

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

- focused build of the touched pi/phase module
- minimal import check for `Littlewood.Main.LittlewoodPi`
- minimal import check for `Littlewood.Main.LittlewoodPsi`
- `lake build` before requesting merge

## Session Log

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
