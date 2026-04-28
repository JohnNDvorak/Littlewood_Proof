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

### 2026-04-28 Round 2: Relative-Density Perron Phase-Fit Adapter

- Classification: `HONEST_PROVIDER_REDUCTION_PENDING_VALIDATION`.
- Theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - Remaining provider cone below
    `TargetTowerExactSeedAbovePerronThresholdPerronHyp` /
    `AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp`.
- Target choice:
  - Chose the Perron-only phase-fit provider cone over
    `PerronSqrtErrorEventuallyAtHeightHyp`. The current fixed-height Perron
    error route still has only the legacy `TruncatedExplicitFormulaPiHyp`
    bridge in this baseline, while the phase-fit cone already has a clean
    Perron-only interface that can be reduced further without touching public
    files.
- Facts banked:
  - Added `FiniteZeroInhomogeneousPhaseRelativelyDenseHyp`, the standard
    finite-dimensional inhomogeneous Kronecker shape: for each fixed cutoff,
    tolerance, and target phase function, every logarithmic starting point has
    a hit within some bounded search radius.
  - Added `PerronThresholdTowerPhaseWideWindowHyp`, the tower-side companion
    requiring the same-height Perron/tower logarithmic window to be wider than
    an externally supplied search radius.
  - Added
    `inhomogeneousPhaseFitAbovePerronThresholdPerron_of_relative_dense_hyp`
    and a lower-priority instance deriving
    `InhomogeneousPhaseFitAbovePerronThresholdPerronHyp` from those two honest
    leaves.
- False-surface audit:
  - The new route does not mention `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, or `truncatedPiHyp_contradicts_rh`.
  - Existing legacy wrappers and contradiction quarantine remain unchanged.
- Failed routes that must not be retried:
  - Do not treat `FiniteZeroInhomogeneousPhaseWindowHyp` as ordinary
    Kronecker. As stated, it demands a target hit inside every arbitrary
    nonempty interval `(L, U)`, which is stronger than the relative-density
    theorem normally obtained from compact torus dynamics.
  - Do not attempt the fixed-height Perron error class via the false
    `pi_approx` field.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane check; no full or bare `lake build` was run.
  - `git diff --check` passed.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
  - `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
  - `printf 'import Littlewood.Main.LittlewoodPsi\n' | lake env lean --stdin`
  - `printf 'import Littlewood.Main.LittlewoodPi\n' | lake env lean --stdin`
- Smallest next theorem/interface:
  - Prove/source `FiniteZeroInhomogeneousPhaseRelativelyDenseHyp` from the
    finite-dimensional inhomogeneous Kronecker theorem plus the needed
    rational-independence facts for ordinates in `(finite_zeros_le T)`.
  - Prove/source `PerronThresholdTowerPhaseWideWindowHyp`, i.e. same-height
    tower growth strong enough to leave a logarithmic interval wider than the
    relative-density radius while staying above `X` and
    `perronThreshold hRH T`.
- Coordinator action requested:
  - Run the requested validation commands and report the first elaboration
    risk, likely around the local `radius`/`Classical.choose` packaging in
    `inhomogeneousPhaseFitAbovePerronThresholdPerron_of_relative_dense_hyp`.

### 2026-04-28 Round 3: Wide Tower Window Reduction

- Classification: `HONEST_PROVIDER_REDUCTION_PENDING_VALIDATION`.
- Theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - Leaf below `PerronThresholdTowerPhaseWideWindowHyp`.
- Target choice:
  - Chose `PerronThresholdTowerPhaseWideWindowHyp` over
    `FiniteZeroInhomogeneousPhaseRelativelyDenseHyp`. The finite-zero leaf
    still needs a general finite-dimensional inhomogeneous Kronecker theorem
    plus zeta-zero ordinate independence. The tower leaf can be reduced
    locally to a same-height growth inequality.
- Facts banked:
  - Added `PerronThresholdTowerWideDominationHyp`.
  - Added
    `perronThresholdTowerPhaseWideWindow_of_wide_domination_hyp`, deriving the
    wide logarithmic window by taking
    `L = log (max X (perronThreshold hRH T) + 1)` and
    `U = L + radius T ε + 1`.
  - Added the instance form routing
    `PerronThresholdTowerPhaseWideWindowHyp` through the new wide-domination
    leaf.
- False-surface audit:
  - The new reduction depends only on
    `PerronSqrtErrorEventuallyAtHeightHyp` and the new
    `PerronThresholdTowerWideDominationHyp`.
  - It does not use `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, or `truncatedPiHyp_contradicts_rh`.
- Failed routes that must not be retried:
  - Do not use ordinary `tower_cap_unbounded_with_eps` alone for the wide
    window. It gives a large cap for a prescribed constant, but not at a height
    where the opaque `perronThreshold hRH T` and the relative-density radius
    are simultaneously controlled.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane check; no full or bare `lake build` was run.
  - `git diff --check` passed.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
  - `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
  - `printf 'import Littlewood.Main.LittlewoodPsi\n' | lake env lean --stdin`
  - `printf 'import Littlewood.Main.LittlewoodPi\n' | lake env lean --stdin`
- Smallest next theorem/interface:
  - Prove/source `PerronThresholdTowerWideDominationHyp`: for every positive
    radius family, find one height/tolerance where the tower cap beats
    `exp (log (max X (perronThreshold hRH T) + 1) + radius T ε + 1)`.
  - In parallel, the remaining phase-side leaf is
    `FiniteZeroInhomogeneousPhaseRelativelyDenseHyp`.
- Coordinator action requested:
  - Run the requested validation commands and report any elaboration repair
    needed around the local `L`/`U` aliases in
    `perronThresholdTowerPhaseWideWindow_of_wide_domination_hyp`.

### 2026-04-28 Round 4: Finite-Zero Phase Leaf to Concrete Kronecker

- Classification: `HONEST_PROVIDER_REDUCTION_PENDING_VALIDATION`.
- Theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - Leaf below `FiniteZeroInhomogeneousPhaseRelativelyDenseHyp`.
- Target choice:
  - Chose `FiniteZeroInhomogeneousPhaseRelativelyDenseHyp` for this round.
    `PerronThresholdTowerWideDominationHyp` remains a true same-height growth
    theorem involving an arbitrary positive radius family; existing
    `tower_cap_unbounded_with_eps` is not enough without a growth bound on
    that radius.
- Facts banked:
  - Added `FiniteSetInhomogeneousPhaseRelativelyDenseKroneckerHyp`, a concrete
    finite-set Kronecker relative-density interface with no zeta-specific
    Perron/tower data.
  - Added
    `finiteZeroInhomogeneousPhaseRelativelyDense_of_finiteSetKronecker_hyp`,
    deriving the project finite-zero leaf by applying the concrete finite-set
    theorem to `(finite_zeros_le T).toFinset`.
  - Added the instance form routing
    `FiniteZeroInhomogeneousPhaseRelativelyDenseHyp` through the concrete
    finite-set Kronecker boundary.
- False-surface audit:
  - The new reduction does not mention `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, or `truncatedPiHyp_contradicts_rh`.
- Failed routes that must not be retried:
  - Do not try to prove relative density from the existing homogeneous
    `exists_large_x_aligned_at_height` lemma; that only targets phase `1` and
    does not support arbitrary target-phase functions.
  - Do not use `FiniteZeroInhomogeneousPhaseWindowHyp` as the source theorem;
    it remains a stronger arbitrary-short-window surface, not standard
    relative-density Kronecker.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane check; no `lean`, `lake`, or focused build was run.
  - `git diff --check` passed.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
  - `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
  - `printf 'import Littlewood.Main.LittlewoodPsi\n' | lake env lean --stdin`
  - `printf 'import Littlewood.Main.LittlewoodPi\n' | lake env lean --stdin`
- Smallest next theorem/interface:
  - Prove/source `FiniteSetInhomogeneousPhaseRelativelyDenseKroneckerHyp`,
    likely from the finite-dimensional inhomogeneous Kronecker theorem on the
    torus plus the needed rational-independence condition for the chosen
    finite frequency set.
  - Separately prove/source `PerronThresholdTowerWideDominationHyp` with a
    usable growth bound for the relative-density radius and the Perron
    threshold.
- Coordinator action requested:
  - Run the requested validation commands and report whether the new finite-set
    interface elaborates cleanly.
