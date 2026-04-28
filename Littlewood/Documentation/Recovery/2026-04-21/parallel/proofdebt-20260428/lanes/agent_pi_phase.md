# Agent Pi/Phase Ledger

Branch: `proofdebt/20260428-pi-phase`

Worktree: `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260428/pi-phase`

## Ownership

- Writable code: pi oscillation, phase, exact-seed, Perron compatibility, and
  corrected witness provider files.
- Writable ledger: this file only.
- Coordinator-owned shared files are read-only.

## Live Targets

1. Remove public reliance on false `TruncatedExplicitFormulaPiHyp.pi_approx`.
2. Produce honest Perron-only target/anti-target phase coupling providers.
3. Audit any `False`-based global provider route before it reaches public API.

## Guardrails

- Do not prove `TruncatedExplicitFormulaPiHyp.pi_approx` as stated.
- Do not add a global contradiction-based provider without explicit coordinator
  approval.
- Do not edit Atkinson, Perron/B5a, RS/Gabcke, or public main files.
- Do not run a full build.

## Requested Checks

- focused build for touched Pi/Phase module(s)
- strict public import probes for `Littlewood.Main.LittlewoodPsi` and
  `Littlewood.Main.LittlewoodPi`

## Session Log

### 2026-04-28 Launch

- Baseline: `acdc136`.
- Initial target: Perron-only replacement for false `pi_approx` usage.
- Coordinator action: initial agent dispatched; Aristotle sidecar planned.

### 2026-04-28 Round 1: Corrected Perron-Only Phase-Coupling Endpoint

- Classification: `HONEST_PROVIDER_REDUCTION_PENDING_VALIDATION`.
- Theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/RHPiPhaseCouplingFromExactSeedBridge.lean`
  - Public-provider audit of `Littlewood/Main/LittlewoodPi.lean`,
    `Littlewood/Aristotle/DeepSorries.lean`, and the Pi exact-seed/provider
    cone.
- Facts banked:
  - The active public `littlewood_pi_li` theorem body routes through
    `DeepSorries.pi_li_full_strength_oscillation`; that theorem's visible
    signature only needs `CriticalZeroSumDivergesHyp` and
    `PhaseAlignmentToTargetHyp`, but the imported public/deep files still
    carry legacy variables for `TruncatedExplicitFormulaPiHyp`,
    `PerronPiApproxCompatibilityHyp`, and
    `InhomogeneousPhaseFitAbovePerronThresholdHyp`.
  - Existing Perron-only exact-seed classes are already present:
    `TargetTowerExactSeedAbovePerronThresholdPerronHyp` and
    `AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp`.
  - Added corrected-canonical provider instances from those Perron-only
    exact-seed classes:
    `TargetTowerPhaseCouplingFamilyHyp_corrected` and
    `AntiTargetTowerPhaseCouplingFamilyHyp_corrected`.
  - Added
    `correctedPhaseCoupling_of_exactSeedAboveThreshold_perron_hyp` and
    `rhPiWitnessData_of_exactSeedAboveThreshold_perron_corrected_hyp`.
    These endpoints do not introduce `TruncatedExplicitFormulaPiHyp` and do
    not depend on `PerronPiApproxCompatibilityHyp`.
- Failed routes that must not be retried:
  - Do not prove `TruncatedExplicitFormulaPiHyp.pi_approx`; the field remains
    mathematically false for `S = ∅`.
  - Do not use the existing `truncatedPiHyp_contradicts_rh` compatibility
    instance as a public provider; it is a quarantined legacy route pending
    coordinator audit.
  - Do not edit `Littlewood/Main/LittlewoodPi.lean` or `DeepSorries.lean` from
    this lane. The public variable cleanup is coordinator-owned.
- Files changed:
  - `Littlewood/Aristotle/Standalone/RHPiPhaseCouplingFromExactSeedBridge.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane check; no full or bare `lake build` was run.
  - `git diff --check` passed.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
  - `printf 'import Littlewood.Main.LittlewoodPsi\n' | lake env lean --stdin`
  - `printf 'import Littlewood.Main.LittlewoodPi\n' | lake env lean --stdin`
- Smallest next theorem/interface:
  - Remove or bypass the remaining false public variables by routing the
    public Pi assembly through
    `rhPiWitnessData_of_exactSeedAboveThreshold_perron_corrected_hyp`.
  - Below that, the true live leaves are an honest provider for
    `PerronSqrtErrorEventuallyAtHeightHyp` and the Perron-only phase-fit
    leaves feeding `TargetTowerExactSeedAbovePerronThresholdPerronHyp` /
    `AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp`.
- Coordinator action requested:
  - Run the validation commands above and, if they pass, perform the
    coordinator-owned public API cleanup to drop the false-surface variables.
