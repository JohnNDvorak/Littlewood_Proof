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

### 2026-04-28 Aristotle Harvest Integration

- Job: `32a1df6a-be94-4cc2-81c3-05623533b222`.
- Classification: `INTERFACE_REDUCTION`.
- Target audited:
  Perron-only replacement for the false `TruncatedExplicitFormulaPiHyp`
  route.
- Result:
  the delivered `PerronPhaseCouplingReduction.lean` is a useful reduction but
  is not integrated as active source. It is sorry-backed and failed a
  standalone Lean check on the current branch because `RiemannHypothesis` is
  ambiguous between root and `ZetaZeros` namespaces.
- Guardrail:
  avoid `PerronPiApproxCompatibilityHyp`, `TruncatedExplicitFormulaPiHyp`,
  and the constant-1 `PerronSqrtErrorEventuallyAtHeightHyp` route.
- Honest route:
  work at `piScale x = sqrt(x) / log(x) * lll(x)`, where fixed Perron
  constants can be absorbed by `lll(x)`.
- Smallest honest inputs:
  a T-parameterized pi-level Perron O-bound, bounded-window Kronecker for the
  finite zero set, and tower/lll absorption.
- Current lane guidance:
  continue the already-validated target/anti realized phase-radius geometry
  and zeta finite-zero compatibility route. Do not add the harvested reduction
  module until it compiles and closes a provider.

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

### 2026-04-28 Round 5: Relation-Compatible Finite Kronecker Source

- Classification: `HONEST_PROVIDER_REDUCTION_PENDING_VALIDATION`.
- Theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - Source theorem shape below
    `FiniteSetInhomogeneousPhaseRelativelyDenseKroneckerHyp` and
    `FiniteZeroInhomogeneousPhaseRelativelyDenseHyp`.
- Target choice:
  - Focused on `FiniteSetInhomogeneousPhaseRelativelyDenseKroneckerHyp`.
    The broad arbitrary-target finite-set class is not a safe theorem shape
    without integer-relation compatibility among the selected ordinates.
- Facts banked:
  - Added `finiteSetInhomogeneousPhaseRelationCompatible`, the explicit
    integer-relation compatibility predicate for one-parameter inhomogeneous
    phase fitting.
  - Added
    `FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp`,
    the honest finite-dimensional Kronecker source interface requiring that
    compatibility predicate.
  - Added `FiniteZeroInhomogeneousPhaseRelationCompatibleHyp`, the remaining
    zeta finite-zero compatibility leaf for the target phase function.
  - Added
    `finiteZeroInhomogeneousPhaseRelativelyDense_of_relationCompatibleKronecker_hyp`
    and a lower-priority instance deriving
    `FiniteZeroInhomogeneousPhaseRelativelyDenseHyp` from the compatible
    finite-set Kronecker source plus the zeta compatibility leaf.
- False-surface audit:
  - No new declaration mentions `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
- Failed routes that must not be retried:
  - Do not try to prove the arbitrary-target
    `FiniteSetInhomogeneousPhaseRelativelyDenseKroneckerHyp` directly as a
    general theorem. Equal or rationally related ordinates impose congruence
    conditions on the target phases.
  - Do not infer inhomogeneous relative density from homogeneous phase
    alignment lemmas; they do not supply arbitrary target phases.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane check; no `lean`, `lake`, `lake env lean`, focused build,
    or public import probe was run.
  - `git diff --check` passed.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
  - `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
  - `printf 'import Littlewood.Main.LittlewoodPsi\n' | lake env lean --stdin`
  - `printf 'import Littlewood.Main.LittlewoodPi\n' | lake env lean --stdin`
- Smallest next theorem/interface:
  - Prove/source
    `FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp`
    from finite-dimensional Kronecker on the closure of the one-parameter
    torus orbit.
  - Prove/source `FiniteZeroInhomogeneousPhaseRelationCompatibleHyp` for the
    target phases used by the Perron-only phase-fit boundary, or narrow the
    target-phase interface so compatibility is carried with the payload.
  - Separately, `PerronThresholdTowerWideDominationHyp` remains the tower-side
    growth leaf.
- Coordinator action requested:
  - Run the requested validation commands and report the first compile risk,
    likely around subtype finite sums in
    `finiteSetInhomogeneousPhaseRelationCompatible`.

### 2026-04-28 Round 6: Target-Specific Relation-Compatible Phase Route

- Classification: `HONEST_PROVIDER_REDUCTION_PENDING_VALIDATION`.
- Theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - Atoms below `FiniteZeroInhomogeneousPhaseRelationCompatibleHyp` and the
    Perron-only exact-seed providers.
- Target choice:
  - Focused on `FiniteZeroInhomogeneousPhaseRelationCompatibleHyp`. Static
    audit showed it is still too broad as stated because it quantifies over
    arbitrary target phase functions. The real public Pi route only needs
    `Complex.arg` and `fun ρ => Complex.arg ρ + Real.pi`.
- Facts banked:
  - Added `TargetFiniteZeroInhomogeneousPhaseRelationCompatibleHyp` and
    `AntiTargetFiniteZeroInhomogeneousPhaseRelationCompatibleHyp`, the
    target/anti-target relation-compatibility leaves.
  - Added `TargetFiniteZeroInhomogeneousPhaseRelativelyDenseHyp` and
    `AntiTargetFiniteZeroInhomogeneousPhaseRelativelyDenseHyp`.
  - Added
    `targetFiniteZeroInhomogeneousPhaseRelativelyDense_of_relationCompatibleKronecker_hyp`
    and
    `antiTargetFiniteZeroInhomogeneousPhaseRelativelyDense_of_relationCompatibleKronecker_hyp`,
    deriving the target-specific relative-density leaves from
    `FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp`
    plus the matching target/anti-target compatibility leaf.
  - Added `TargetPhaseFitAbovePerronThresholdPerronHyp` and
    `AntiTargetPhaseFitAbovePerronThresholdPerronHyp`.
  - Added
    `targetPhaseFitAbovePerronThresholdPerron_of_relative_dense_hyp` and
    `antiTargetPhaseFitAbovePerronThresholdPerron_of_relative_dense_hyp`,
    deriving the target-specific Perron phase-fit surfaces from the wide
    tower window plus target-specific relative density.
  - Added
    `target_exact_seed_above_threshold_perron_from_target_phase_fit` and
    `anti_target_exact_seed_above_threshold_perron_from_target_phase_fit`,
    then routed the repaired Perron-only exact-seed classes through these
    narrower phase-fit providers at lower priority.
- False-surface audit:
  - No new declaration uses `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - Existing broad compatibility wrappers remain intact for validated
    compatibility, but the new target/anti-target route no longer needs the
    arbitrary-target finite-zero compatibility leaf.
- Failed routes that must not be retried:
  - Do not prove `FiniteZeroInhomogeneousPhaseRelationCompatibleHyp` as a
    theorem for arbitrary `targetPhase`; integer-relation congruence can fail
    for arbitrary target functions.
  - Do not prove the arbitrary-target
    `FiniteSetInhomogeneousPhaseRelativelyDenseKroneckerHyp` directly without
    relation compatibility.
  - Do not derive target/anti-target phase fit from homogeneous phase
    alignment; it does not carry the needed phase targets.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, or static check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
  - `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem/interface:
  - Prove/source
    `FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp`
    from finite-dimensional Kronecker on the relation-compatible torus orbit.
  - Prove/source
    `TargetFiniteZeroInhomogeneousPhaseRelationCompatibleHyp` and
    `AntiTargetFiniteZeroInhomogeneousPhaseRelationCompatibleHyp` for the
    actual zeta target phases, or carry relation compatibility directly in the
    phase payload.
  - `PerronThresholdTowerWideDominationHyp` remains the independent tower-side
    growth atom.
- Coordinator action requested:
  - Run the requested validation commands and report the first compile risk,
    likely around exact unification of target-specific relative-density
    witnesses with the shared helper
    `phaseFitAbovePerronThresholdPerron_of_relative_dense_witness`.

### 2026-04-28 Round 7: Realized-Radius Tower Domination Leaves

- Classification: `HONEST_PROVIDER_REDUCTION_PENDING_VALIDATION`.
- Theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - Tower-side atom below target/anti-target Perron-only phase fit.
- Target choice:
  - Focused on `PerronThresholdTowerWideDominationHyp`. Static audit showed
    the generic leaf is stronger than the target/anti route needs because it
    requires the tower cap to dominate every positive radius function. The
    phase route only needs domination of the actual relative-density radius
    supplied by the target or anti-target finite-zero phase payload.
- Facts banked:
  - Added
    `TargetPerronThresholdTowerWideDominationWithPhaseRadiusHyp` and
    `AntiTargetPerronThresholdTowerWideDominationWithPhaseRadiusHyp`.
    These leaves package one height, tolerance, realized relative-density
    radius, the corresponding finite-zero phase hit family, and the same-height
    Perron/tower domination inequality.
  - Added
    `targetPerronThresholdTowerWideDominationWithPhaseRadius_of_wideDomination_hyp`
    and
    `antiTargetPerronThresholdTowerWideDominationWithPhaseRadius_of_wideDomination_hyp`,
    proving the realized-radius leaves from the older arbitrary-radius
    `PerronThresholdTowerWideDominationHyp` plus the matching target/anti
    relative-density payload.
  - Added
    `targetPhaseFitAbovePerronThresholdPerron_of_realizedRadiusDomination_hyp`
    and
    `antiTargetPhaseFitAbovePerronThresholdPerron_of_realizedRadiusDomination_hyp`,
    deriving the target/anti Perron-only phase-fit boundaries directly from
    realized-radius tower domination.
- False-surface audit:
  - No new declaration uses `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - No new declaration revives arbitrary-target Kronecker as a theorem to be
    proved. Existing compatibility wrappers remain for already validated
    routes only.
  - The round does not use the structurally too-strong constant-1
    `PerronSqrtErrorEventuallyAtHeightHyp` route flagged by the Aristotle
    harvest.
- Failed routes that must not be retried:
  - Do not attempt to close `PerronThresholdTowerWideDominationHyp` for every
    positive radius function as the main Pi route; the realized phase-radius
    theorem is the smaller target.
  - Do not use `TruncatedExplicitFormulaPiHyp` or arbitrary-target finite-set
    Kronecker to package target/anti phase coupling.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, or check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
  - `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem/interface:
  - Prove/source
    `TargetPerronThresholdTowerWideDominationWithPhaseRadiusHyp` and
    `AntiTargetPerronThresholdTowerWideDominationWithPhaseRadiusHyp` directly,
    using a growth bound for the actual Kronecker relative-density radius and
    the Perron threshold at the same height.
  - Prove/source
    `TargetFiniteZeroInhomogeneousPhaseRelationCompatibleHyp` and
    `AntiTargetFiniteZeroInhomogeneousPhaseRelationCompatibleHyp`, or refine
    the phase payload so relation compatibility is carried with each target.
- Coordinator action requested:
  - Run the requested validation commands and report the first compile risk,
    likely around the two realized-radius phase-fit proofs and the
    `Real.exp_log` rewrites for the lower endpoint.

### 2026-04-28 Round 8: Chosen Phase Radius Geometry Split

- Classification: `HONEST_PROVIDER_REDUCTION_PENDING_VALIDATION`.
- Theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - Realized-radius leaves below target/anti-target Perron-only phase fit.
- Target choice:
  - Continued the target/anti realized-radius route. The goal was to separate
    the finite-zero Kronecker payload from the same-height Perron/tower
    geometry instead of proving the bundled realized-radius class directly.
- Facts banked:
  - Added `targetFiniteZeroInhomogeneousPhaseRadius` and
    `antiTargetFiniteZeroInhomogeneousPhaseRadius`, total chosen-radius
    selectors from the target/anti finite-zero relative-density payloads.
  - Added private specs
    `targetFiniteZeroInhomogeneousPhaseRadius_spec` and
    `antiTargetFiniteZeroInhomogeneousPhaseRadius_spec`, recovering positivity
    and the corresponding phase-hit family for `4 ≤ T`, `0 < ε`.
  - Added `TargetPerronThresholdTowerGeometryForPhaseRadiusHyp` and
    `AntiTargetPerronThresholdTowerGeometryForPhaseRadiusHyp`. These are the
    tower-only leaves: for some same height/tolerance, the tower cap dominates
    `log (max X (perronThreshold hRH T) + 1)` plus the chosen target/anti
    phase radius.
  - Added
    `targetPerronThresholdTowerWideDominationWithPhaseRadius_of_geometry_hyp`
    and
    `antiTargetPerronThresholdTowerWideDominationWithPhaseRadius_of_geometry_hyp`,
    deriving the bundled realized-radius domination leaves from finite-zero
    relative density plus the new geometry leaves.
- False-surface audit:
  - No new declaration uses `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - The new route avoids arbitrary-target Kronecker. Target/anti relative
    density still flows through the relation-compatible finite-set Kronecker
    source and target/anti zeta compatibility leaves.
  - No constant-1 `PerronSqrtErrorEventuallyAtHeightHyp` shortcut was used.
- Failed routes that must not be retried:
  - Do not close realized-radius domination by reintroducing generic
    all-positive-radius tower domination as the primary leaf.
  - Do not assert arbitrary target-phase compatibility for zeta finite zeros.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, or check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
  - `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem/interface:
  - Prove/source `TargetPerronThresholdTowerGeometryForPhaseRadiusHyp` and
    `AntiTargetPerronThresholdTowerGeometryForPhaseRadiusHyp`, requiring a
    same-height growth bound for `perronThreshold hRH T` and the chosen
    target/anti Kronecker radius.
  - Prove/source `TargetFiniteZeroInhomogeneousPhaseRelationCompatibleHyp` and
    `AntiTargetFiniteZeroInhomogeneousPhaseRelationCompatibleHyp`, or carry
    relation compatibility explicitly with the target/anti phase payload.
- Coordinator action requested:
  - Run the requested validation commands and report the first compile risk,
    likely around definitional unfolding of the chosen-radius selectors in the
    two `_of_geometry_hyp` adapters.

### 2026-04-28 Round 9: Paired Phase-Radius Geometry Endpoint

- Classification: `HONEST_PROVIDER_REDUCTION_PENDING_VALIDATION`.
- Theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - Target/anti realized phase-radius geometry leaves feeding the corrected
    Perron-only exact-seed and phase-coupling route.
- Target choice:
  - Continued below the realized-radius geometry leaves. The target and
    anti-target sides need the same kind of tower geometry, so this round
    introduced one paired atom that dominates the maximum of the two chosen
    finite-zero phase radii.
- Facts banked:
  - Added `TargetAntiPerronThresholdTowerGeometryForPhaseRadiiHyp`, a paired
    geometry leaf requiring one height/tolerance where the tower cap dominates
    `max targetFiniteZeroInhomogeneousPhaseRadius
    antiTargetFiniteZeroInhomogeneousPhaseRadius` plus the Perron lower
    endpoint.
  - Added
    `targetPerronThresholdTowerGeometryForPhaseRadius_of_pairedGeometry_hyp`
    and
    `antiTargetPerronThresholdTowerGeometryForPhaseRadius_of_pairedGeometry_hyp`,
    deriving the one-sided geometry leaves by monotonicity from the paired
    maximum-radius leaf.
  - Added
    `exactSeedAboveThreshold_perron_of_pairedPhaseRadiusGeometry_hyp`, which
    packages both repaired Perron-only exact-seed classes from:
    `FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp`,
    the target/anti finite-zero relation-compatibility leaves, and the paired
    phase-radius tower geometry leaf.
- False-surface audit:
  - No new declaration uses `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - The new endpoint avoids arbitrary-target Kronecker and keeps target/anti
    compatibility separate.
  - No constant-1 `PerronSqrtErrorEventuallyAtHeightHyp` shortcut was used.
- Failed routes that must not be retried:
  - Do not prove target and anti geometry independently if the paired
    max-radius geometry theorem is available; that duplicates the same
    Perron/tower growth obligation.
  - Do not replace the target/anti compatibility leaves with the false
    arbitrary-target compatibility leaf.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, or check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
  - `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem/interface:
  - Prove/source `TargetAntiPerronThresholdTowerGeometryForPhaseRadiiHyp`,
    requiring a same-height growth bound for `perronThreshold hRH T` and the
    paired chosen Kronecker radius.
  - Prove/source `TargetFiniteZeroInhomogeneousPhaseRelationCompatibleHyp` and
    `AntiTargetFiniteZeroInhomogeneousPhaseRelationCompatibleHyp`, or carry
    relation compatibility explicitly in the target/anti phase payload.
- Coordinator action requested:
  - Run the requested validation commands and report the first compile risk,
    likely around typeclass synthesis for
    `exactSeedAboveThreshold_perron_of_pairedPhaseRadiusGeometry_hyp` or the
    monotonic `Real.exp_le_exp` steps in the paired-geometry adapters.

### 2026-04-28 Round 10: Paired Zeta Compatibility Endpoint

- Classification: `HONEST_PROVIDER_REDUCTION_PENDING_VALIDATION`.
- Theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - Zeta finite-zero compatibility atoms feeding the paired phase-radius
    geometry route.
- Target choice:
  - Continued the realized phase-radius geometry and zeta finite-zero
    compatibility route. The harvested `PerronPhaseCouplingReduction.lean` is
    documentation-only for now because it is sorry-backed and failed
    current-branch standalone Lean due to `RiemannHypothesis` ambiguity.
- Facts banked:
  - Added `TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp`, a
    paired zeta finite-zero compatibility leaf for exactly the two target
    phases used by corrected Pi: `Complex.arg` and
    `fun ρ => Complex.arg ρ + Real.pi`.
  - Added
    `targetFiniteZeroInhomogeneousPhaseRelationCompatible_of_paired_hyp` and
    `antiTargetFiniteZeroInhomogeneousPhaseRelationCompatible_of_paired_hyp`,
    deriving the one-sided target/anti compatibility classes from the paired
    compatibility leaf.
  - Added
    `exactSeedAboveThreshold_perron_of_pairedCompatibilityAndGeometry_hyp`,
    packaging both repaired Perron-only exact-seed classes from
    `FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp`,
    `TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp`, and
    `TargetAntiPerronThresholdTowerGeometryForPhaseRadiiHyp`.
- False-surface audit:
  - No new declaration uses `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - The route still avoids arbitrary-target Kronecker and only packages the
    target/anti phase functions required by corrected Pi.
  - No constant-1 `PerronSqrtErrorEventuallyAtHeightHyp` shortcut was used.
- Failed routes that must not be retried:
  - Do not import or depend on the harvested
    `PerronPhaseCouplingReduction.lean` as code until it is made sorry-free
    and its `RiemannHypothesis` namespace ambiguity is fixed.
  - Do not replace paired target/anti compatibility with the false
    arbitrary-target finite-zero compatibility leaf.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, or check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
  - `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem/interface:
  - Prove/source `TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp`
    for the actual zeta finite-zero target and anti-target phases.
  - Prove/source `TargetAntiPerronThresholdTowerGeometryForPhaseRadiiHyp`,
    requiring same-height growth for `perronThreshold hRH T` and the paired
    chosen Kronecker radius.
  - Prove/source
    `FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp`
    from finite-dimensional Kronecker on the relation-compatible torus orbit.
- Coordinator action requested:
  - Run the requested validation commands and report the first compile risk,
    likely around typeclass synthesis for
    `exactSeedAboveThreshold_perron_of_pairedCompatibilityAndGeometry_hyp`.

### 2026-04-29 Round 11: Paired Relation-Compatible Relative Density

- Classification: `HONEST_PROVIDER_REDUCTION_PENDING_VALIDATION`.
- Theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - Paired finite-zero compatibility and relation-compatible finite-set
    Kronecker surface.
- Target choice:
  - Attacked the paired finite-zero compatibility route by adding a paired
    finite-zero relative-density payload. This carries the target and
    anti-target phase-hit families together after the relation-compatibility
    predicate has been supplied, instead of routing through arbitrary-target
    Kronecker.
- Facts banked:
  - Added `TargetAntiFiniteZeroInhomogeneousPhaseRelativelyDenseHyp`, a paired
    finite-zero relative-density payload for the two corrected Pi targets
    `Complex.arg` and `fun ρ => Complex.arg ρ + Real.pi`.
  - Added
    `targetAntiFiniteZeroInhomogeneousPhaseRelativelyDense_of_relationCompatibleKronecker_hyp`,
    deriving the paired payload from
    `FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp`
    plus `TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp`.
  - Added
    `targetFiniteZeroInhomogeneousPhaseRelativelyDense_of_paired_hyp` and
    `antiTargetFiniteZeroInhomogeneousPhaseRelativelyDense_of_paired_hyp`,
    exposing the paired payload to the existing one-sided radius selectors and
    geometry classes.
  - Added
    `exactSeedAboveThreshold_perron_of_pairedRelativeDensityAndGeometry_hyp`,
    packaging both repaired Perron-only exact-seed classes from paired
    finite-zero relative density and paired phase-radius tower geometry.
- False-surface audit:
  - No new declaration uses `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - No arbitrary-target Kronecker theorem was introduced; relation
    compatibility is an explicit premise of the finite-set Kronecker source.
  - No constant-1 `PerronSqrtErrorEventuallyAtHeightHyp` shortcut or
    harvested sorry-backed file was used.
- Failed routes that must not be retried:
  - Do not prove arbitrary-target finite-zero compatibility. The paired class
    only carries the target and anti-target phase functions needed by corrected
    Pi.
  - Do not activate the harvested `PerronPhaseCouplingReduction.lean` until it
    is sorry-free and namespace-clean.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, or compilation/check command was run.
  - `git diff --check` passed.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
  - `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem/interface:
  - Prove/source `FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp`
    from finite-dimensional Kronecker on the relation-compatible torus orbit.
  - Prove/source `TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp`
    for the actual zeta target/anti-target phases.
  - Prove/source `TargetAntiPerronThresholdTowerGeometryForPhaseRadiiHyp` from
    same-height Perron-threshold growth and the paired chosen phase radius.
- Coordinator action requested:
  - Run the requested validation commands and report the first compile risk,
    likely around typeclass synthesis from
    `TargetAntiFiniteZeroInhomogeneousPhaseRelativelyDenseHyp` to the
    one-sided radius classes.

### 2026-04-29 Round 12: Log-Level Paired Tower Geometry

- Classification: `HONEST_PROVIDER_REDUCTION_PENDING_VALIDATION`.
- Theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `TargetAntiPerronThresholdTowerGeometryForPhaseRadiiHyp`.
- Target choice:
  - Attacked the paired tower geometry leaf. The existing geometry statement
    still has an outer `Real.exp` on both sides, so this round peeled off that
    final monotone exponential and isolated the smaller log-scale tower
    domination atom.
- Facts banked:
  - Added `TargetAntiPerronThresholdTowerLogGeometryForPhaseRadiiHyp`.
    This asks for one height/tolerance where
    `log (max X (perronThreshold hRH T) + 1)` plus the larger chosen
    target/anti phase radius is bounded by the double-exponential tower scale
    `exp (exp (((1 - ε) * (N T / (T + 1))) / 2))`.
  - Added
    `targetAntiPerronThresholdTowerGeometryForPhaseRadii_of_logGeometry_hyp`,
    deriving the previous paired geometry leaf from the log-level leaf by
    monotonicity of `Real.exp`.
  - Added
    `exactSeedAboveThreshold_perron_of_pairedRelativeDensityAndLogGeometry_hyp`,
    packaging both repaired Perron-only exact-seed classes from paired
    finite-zero relative density plus the log-level paired tower geometry.
- False-surface audit:
  - No new declaration uses `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - No arbitrary-target Kronecker theorem was introduced.
  - No constant-1 `PerronSqrtErrorEventuallyAtHeightHyp` shortcut or
    harvested sorry-backed file was used.
- Failed routes that must not be retried:
  - Do not attack the all-radius tower domination leaf as the primary route.
    The live geometry route is paired, target/anti-specific, and now
    log-level.
  - Do not replace relation-compatible finite-set Kronecker with an
    arbitrary-target Kronecker theorem.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, or compilation command was run.
  - `git diff --check` passed.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
  - `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem/interface:
  - Prove/source
    `TargetAntiPerronThresholdTowerLogGeometryForPhaseRadiiHyp` from
    same-height Perron-threshold growth and the paired chosen phase radius.
  - Prove/source `TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp`
    and `FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp`.
- Coordinator action requested:
  - Run the requested validation commands and report the first compile risk,
    likely around the `Real.exp_le_exp.mpr` adapter from log-level geometry to
    paired geometry.

### 2026-04-29 Round 13: Budgeted Paired Log Geometry

- Classification: `HONEST_PROVIDER_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `TargetAntiPerronThresholdTowerLogGeometryForPhaseRadiiHyp`.
- Target choice:
  - Attacked the paired log-scale tower domination source. The live log
    geometry still combines the Perron lower endpoint and the paired phase
    radius in a single inequality, so this round split it into two same-height
    half-budget estimates.
- Banked inputs:
  - The existing paired phase radius is
    `max (targetFiniteZeroInhomogeneousPhaseRadius T ε)
      (antiTargetFiniteZeroInhomogeneousPhaseRadius T ε)`.
  - The existing log tower scale is
    `Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2))`.
- Facts banked:
  - Added `TargetAntiPerronThresholdTowerLogBudgetForPhaseRadiiHyp`.
    This asks for one height/tolerance where:
    `log (max X (perronThreshold hRH T) + 1)` is at most half the log tower
    scale, and the paired chosen phase radius plus `1` is at most the other
    half.
  - Added
    `targetAntiPerronThresholdTowerLogGeometryForPhaseRadii_of_budget_hyp`,
    deriving `TargetAntiPerronThresholdTowerLogGeometryForPhaseRadiiHyp` by
    adding the two half-budget inequalities.
  - Added
    `exactSeedAboveThreshold_perron_of_pairedRelativeDensityAndBudgetGeometry_hyp`,
    packaging both repaired Perron-only exact-seed classes from paired
    finite-zero relative density plus the budgeted log geometry leaf.
- False-surface audit:
  - No new declaration uses `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - No arbitrary-target Kronecker theorem was introduced.
  - No constant-1 `PerronSqrtErrorEventuallyAtHeightHyp` shortcut or
    harvested sorry-backed file was used.
- Failed routes:
  - Do not replace this paired budget leaf with ambient all-radius domination
    unless the exact implication back to the paired budget scale is proved.
  - Do not split target and anti-target geometry into independent heights; the
    corrected phase route needs a coupled same-height/tolerance package.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, `git diff --check`, or other check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
  - `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Prove/source
    `TargetAntiPerronThresholdTowerLogBudgetForPhaseRadiiHyp`.
  - Then prove/source the two analytic inputs it encodes: same-height Perron
    threshold logarithmic growth and a bound for the paired chosen
    relation-compatible Kronecker phase radius.
- Coordinator action requested:
  - Run the requested validation commands and report the first compile risk,
    likely around the `linarith` step adding the two half-budget inequalities.

### 2026-04-29 Round 14: Split Budget Atom Into Same-Height Halves

- Classification: `HONEST_PROVIDER_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `TargetAntiPerronThresholdTowerLogBudgetForPhaseRadiiHyp`.
- Target choice:
  - Attacked the new budgeted paired log tower atom. Existing tower-height
    budget infrastructure only gives unbounded domination of fixed external
    budgets; it does not control the same-height opaque quantities
    `perronThreshold hRH T` or the chosen finite-zero phase radii after `T, ε`
    have been selected.
- Banked inputs:
  - `RHPiTowerHeightBudget.tower_cap_unbounded_with_eps` remains useful only
    for fixed budgets independent of the selected height.
  - The current paired route needs one shared `T, ε`, so independent target
    and anti-target witnesses, or independent Perron/radius heights, are not
    enough.
- Facts banked:
  - Added `PerronThresholdTowerLogHalfBudgetHyp`, the Perron lower-endpoint
    half-budget source:
    `log (max X (perronThreshold hRH T) + 1) ≤ tower(T, ε) / 2`.
  - Added `TargetAntiFiniteZeroPhaseRadiusHalfBudgetAtPerronThresholdHyp`, the
    same-height phase-radius half-budget source: at the `T, ε` selected by the
    Perron half, the larger target/anti chosen finite-zero radius plus `1`
    fits under the other half of the same double-exponential tower budget.
  - Added
    `targetAntiPerronThresholdTowerLogBudgetForPhaseRadii_of_halfBudgets_hyp`,
    deriving `TargetAntiPerronThresholdTowerLogBudgetForPhaseRadiiHyp` from
    those two same-height inputs.
  - Added
    `exactSeedAboveThreshold_perron_of_pairedRelativeDensityAndHalfBudgets_hyp`,
    packaging both repaired Perron-only exact-seed classes from paired
    relative density plus the two half-budget source atoms.
- Failed route guardrails:
  - Do not try to use `tower_cap_unbounded_with_eps` directly on
    `perronThreshold hRH T` or the chosen phase radii; those quantities depend
    on the same `T, ε` being selected.
  - Do not split target and anti-target into separate heights, and do not
    replace the paired radius with an ambient all-radius domination theorem
    unless the implication back to the paired same-height budget is proved.
  - Do not use `TruncatedExplicitFormulaPiHyp`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`,
    `truncatedPiHyp_contradicts_rh`, arbitrary-target Kronecker, or the
    constant-1 Perron sqrt-error shortcut.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, `git diff --check`, or other check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Prove/source `PerronThresholdTowerLogHalfBudgetHyp`.
  - Prove/source
    `TargetAntiFiniteZeroPhaseRadiusHalfBudgetAtPerronThresholdHyp`, probably
    from an explicit same-height quantitative bound on the paired
    relation-compatible Kronecker search radius.

### 2026-04-29 Round 15: Corrected Perron-Only Packaging Endpoint

- Classification: `HONEST_PACKAGING_ENDPOINT_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - Added `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`.
  - The sidecar endpoint does not prove
    `TargetAntiPerronThresholdTowerLogBudgetForPhaseRadiiHyp`; it packages the
    already-bankable corrected route from the four honest classes:
    `PerronSqrtErrorEventuallyAtHeightHyp`,
    `FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp`,
    `TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp`, and
    `TargetAntiPerronThresholdTowerGeometryForPhaseRadiiHyp`.
- Facts banked:
  - Added `targetAntiDensity_of_relationCompatibleKroneckerAndCompatibility`,
    forwarding the paired relation-compatible finite-set Kronecker and zeta
    compatibility inputs to `TargetAntiFiniteZeroInhomogeneousPhaseRelativelyDenseHyp`.
  - Added `exactSeed_of_correctedPerronOnlyRoute`, forwarding the four-class
    corrected route to both Perron-only exact-seed classes.
  - Added `correctedPhaseCoupling_of_correctedPerronOnlyRoute`, forwarding the
    exact-seed pair to both corrected canonical phase-coupling classes.
  - Added `rhPiWitnessData_of_correctedPerronOnlyRoute`, forwarding the same
    route to `RhPiWitnessData`.
  - Added `rh_pi_7a_7c_pair_of_correctedPerronOnlyRoute`, forwarding the same
    route to the concrete RH 7a/7c pair.
- False-surface audit:
  - The new endpoint file does not mention `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - It imports the current provider and exact-seed bridge only for existing
    Perron-only and corrected-canonical wiring; it adds no new analytic axiom.
  - No sidecar API key or external credential was used, recorded, or exposed.
- Failed route guardrails:
  - Do not treat this packaging endpoint as closing the live log-budget atom.
    The remaining analytic leaves are still
    `PerronThresholdTowerLogHalfBudgetHyp` and
    `TargetAntiFiniteZeroPhaseRadiusHalfBudgetAtPerronThresholdHyp`, or an
    equivalent direct proof of
    `TargetAntiPerronThresholdTowerLogBudgetForPhaseRadiiHyp`.
- Files changed:
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, `git diff --check`, or other check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Continue with `PerronThresholdTowerLogHalfBudgetHyp`.
  - Continue with `TargetAntiFiniteZeroPhaseRadiusHalfBudgetAtPerronThresholdHyp`.

### 2026-04-29 Round 16: Corrected Route From Half-Budget Leaves

- Classification: `HONEST_PACKAGING_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - Exposed the corrected Perron-only route directly from the two current
    half-budget leaves below
    `TargetAntiPerronThresholdTowerLogBudgetForPhaseRadiiHyp`.
- Facts banked:
  - Added `exactSeed_of_correctedPerronOnlyHalfBudgetRoute`, which packages
    both Perron-only exact-seed classes from:
    `PerronSqrtErrorEventuallyAtHeightHyp`,
    `FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp`,
    `TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp`,
    `PerronThresholdTowerLogHalfBudgetHyp`, and
    `TargetAntiFiniteZeroPhaseRadiusHalfBudgetAtPerronThresholdHyp`.
  - Added `correctedPhaseCoupling_of_correctedPerronOnlyHalfBudgetRoute`,
    forwarding the same half-budget route to the corrected canonical
    phase-coupling classes.
  - Added `rhPiWitnessData_of_correctedPerronOnlyHalfBudgetRoute`, forwarding
    the same half-budget route to `RhPiWitnessData`.
  - Added `rh_pi_7a_7c_pair_of_correctedPerronOnlyHalfBudgetRoute`,
    forwarding the same half-budget route to the concrete RH 7a/7c pair.
- Guardrails:
  - This is a packaging reduction, not a proof of the two half-budget leaves.
  - The half-budget route preserves the paired same-height `T, ε` structure:
    paired finite-zero relative density feeds target/anti relative density;
    half budgets feed budgeted log geometry; budgeted log geometry feeds
    paired phase-radius geometry; the repaired corrected route then builds
    exact seeds without `TruncatedExplicitFormulaPiHyp`.
  - Static forbidden-name scan of the edited endpoint found no references to
    `TruncatedExplicitFormulaPiHyp`, `pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
- Failed route guardrails:
  - Do not collapse the paired half-budget leaves into independent target and
    anti-target heights.
  - Do not use `tower_cap_unbounded_with_eps` directly on same-height opaque
    quantities depending on the selected `T, ε`.
  - Do not revive arbitrary-target Kronecker or the constant-1 Perron
    sqrt-error shortcut.
- Files changed:
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, `git diff --check`, or other check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Prove/source `PerronThresholdTowerLogHalfBudgetHyp`.
  - Prove/source
    `TargetAntiFiniteZeroPhaseRadiusHalfBudgetAtPerronThresholdHyp`.

### 2026-04-29 Round 17: Explicit Growth Sources Below Half-Budgets

- Classification: `HONEST_PROVIDER_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `PerronThresholdTowerLogHalfBudgetHyp`
  - `TargetAntiFiniteZeroPhaseRadiusHalfBudgetAtPerronThresholdHyp`
- Target choice:
  - Attacked the Perron log half-budget first. No existing same-height growth
    theorem for `perronThreshold hRH T` was present; existing
    `tower_cap_unbounded_with_eps` remains a fixed-budget unboundedness lemma
    and cannot be applied directly to `perronThreshold hRH T` after `T` is
    selected.
  - Also isolated the paired phase-radius half-budget into a height-only
    quantitative radius growth source.
- Facts banked:
  - Added `PerronThresholdTowerExpHalfBudgetGrowthHyp`. This is a pre-log
    same-height fixed-point growth source: for each `hRH, X`, it selects one
    `T, ε` where both `X + 1` and `perronThreshold hRH T + 1` are below
    `exp((exp(expArg)) / 2)`, i.e. the exponential of the required log
    half-budget.
  - Added `perronThresholdTowerLogHalfBudget_of_expHalfBudgetGrowth_hyp`,
    deriving `PerronThresholdTowerLogHalfBudgetHyp` by combining the two
    pre-log bounds under `max` and applying `Real.log_le_iff_le_exp`.
  - Added `TargetAntiFiniteZeroPhaseRadiusHalfBudgetGrowthHyp`. This is the
    narrower quantitative Kronecker-radius growth source: for each same
    `T, ε`, the larger chosen target/anti relative-density radius plus `1`
    fits below half the double-exponential log budget. It drops `hRH`, `X`,
    and the Perron lower-endpoint half-budget proof from the premise.
  - Added
    `targetAntiFiniteZeroPhaseRadiusHalfBudgetAtPerronThreshold_of_growth_hyp`,
    deriving the existing Perron-selected phase-radius half-budget leaf from
    the height-only growth source.
  - Added `rhPiWitnessData_of_correctedPerronOnlyGrowthBudgetRoute`, exposing
    the corrected Perron-only packaging route directly from the two new growth
    source classes plus the relation-compatible finite-zero inputs.
- Guardrails:
  - The new Perron growth class is still a genuine same-height fixed-point
    growth leaf; it does not pretend that zero-count tower unboundedness alone
    controls `perronThreshold hRH T`.
  - The new phase-radius growth class preserves one shared `T, ε` for target
    and anti-target radii.
  - No new route uses `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - No arbitrary-target Kronecker or constant-1 Perron sqrt-error shortcut was
    introduced.
- Failed route guardrails:
  - Do not split target and anti-target phase radii into independent heights.
  - Do not use `tower_cap_unbounded_with_eps` directly on same-height opaque
    quantities depending on the selected `T, ε`; an actual fixed-point/growth
    lemma is still needed.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, `git diff --check`, or other check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Prove/source `PerronThresholdTowerExpHalfBudgetGrowthHyp`.
  - Prove/source `TargetAntiFiniteZeroPhaseRadiusHalfBudgetGrowthHyp`.

### 2026-04-29 Round 18: Majorant Splits Below Growth Budgets

- Classification: `HONEST_PROVIDER_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `PerronThresholdTowerExpHalfBudgetGrowthHyp`
  - `TargetAntiFiniteZeroPhaseRadiusHalfBudgetGrowthHyp`
- Target choice:
  - Split the Perron exponential half-budget into the smallest explicit
    same-height fixed-point form: produce one majorant `B` at the selected
    `T, ε` for both `X + 1` and `perronThreshold hRH T + 1`, then prove the
    same zero-count tower half-budget dominates `B`.
  - Split the phase-radius growth budget analogously: produce one majorant
    `R` for the paired target/anti chosen relative-density radius at the same
    `T, ε`, then prove the same half-budget tower dominates `R`.
- Facts banked:
  - Added `PerronThresholdTowerExpHalfBudgetMajorantHyp`, the fixed-point
    Perron-threshold majorant/tower source below
    `PerronThresholdTowerExpHalfBudgetGrowthHyp`.
  - Added `perronThresholdTowerExpHalfBudgetGrowth_of_majorant_hyp`, deriving
    `PerronThresholdTowerExpHalfBudgetGrowthHyp` by transitivity through the
    same majorant `B`.
  - Added `TargetAntiFiniteZeroPhaseRadiusHalfBudgetMajorantHyp`, the
    quantitative paired Kronecker-radius majorant/tower source below
    `TargetAntiFiniteZeroPhaseRadiusHalfBudgetGrowthHyp`.
  - Added `targetAntiFiniteZeroPhaseRadiusHalfBudgetGrowth_of_majorant_hyp`,
    deriving `TargetAntiFiniteZeroPhaseRadiusHalfBudgetGrowthHyp` by
    transitivity through the same radius majorant `R`.
  - Added `rhPiWitnessData_of_correctedPerronOnlyMajorantBudgetRoute`, exposing
    the corrected Perron-only endpoint directly from the two new majorant
    source classes plus the relation-compatible finite-zero inputs.
- Guardrails:
  - The selected `T, ε` remain shared on both sides of each majorant split.
  - The new Perron majorant class still requires the missing fixed-point
    bridge for `perronThreshold hRH T`; it does not use
    `tower_cap_unbounded_with_eps` on height-dependent quantities.
  - The new phase-radius majorant class preserves the paired target/anti
    radius through one shared `R`; no independent target/anti heights were
    introduced.
  - No new route uses `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - No arbitrary-target Kronecker or constant-1 Perron sqrt-error shortcut was
    introduced.
- Failed route guardrails:
  - Do not replace the Perron majorant source with a bare tower unboundedness
    call; the missing theorem is a same-height fixed-point/growth theorem.
  - Do not replace the paired radius majorant with two independent one-sided
    radius bounds unless there is an explicit same-height max recombination.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, `git diff --check`, or other check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Prove/source `PerronThresholdTowerExpHalfBudgetMajorantHyp`.
  - Prove/source `TargetAntiFiniteZeroPhaseRadiusHalfBudgetMajorantHyp`.

### 2026-04-29 Round 19: Canonical Perron Majorant And Same-Height Radius Recombination

- Classification: `HONEST_PROVIDER_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `PerronThresholdTowerExpHalfBudgetMajorantHyp`
  - `TargetAntiFiniteZeroPhaseRadiusHalfBudgetMajorantHyp`
- Target choice:
  - The Perron majorant class itself still cannot be closed from local facts:
    `perronThreshold hRH T` is an opaque `Classical.choose` threshold for a
    fixed-height eventual statement, and no monotone/growth bridge in `T` is
    available.
  - Reduced it to the canonical same-height max-majorant inequality, removing
    the arbitrary existential majorant `B`.
  - Split the paired phase-radius majorant into target-side and anti-target
    side same-height radius majorants, then recombined them at the same
    `T, ε` by taking `R = max Rt Ra`.
- Facts banked:
  - Added `PerronThresholdTowerExpHalfBudgetCanonicalMajorantHyp`, the exact
    canonical Perron growth source:
    `max (X + 1) (perronThreshold hRH T + 1)` is dominated by the tower
    half-budget at the selected same height.
  - Added `perronThresholdTowerExpHalfBudgetMajorant_of_canonical_hyp`,
    deriving `PerronThresholdTowerExpHalfBudgetMajorantHyp` by choosing
    `B = max (X + 1) (perronThreshold hRH T + 1)`.
  - Added `TargetFiniteZeroPhaseRadiusHalfBudgetMajorantHyp` and
    `AntiTargetFiniteZeroPhaseRadiusHalfBudgetMajorantHyp`, the one-sided
    radius majorant leaves at a fixed shared `T, ε`.
  - Added `targetAntiFiniteZeroPhaseRadiusHalfBudgetMajorant_of_targetAnti_hyp`,
    deriving the paired radius majorant from the one-sided leaves without
    splitting heights.
  - Added
    `rhPiWitnessData_of_correctedPerronOnlyCanonicalRadiusMajorantRoute`, which
    exposes the corrected Perron-only endpoint from the canonical Perron
    majorant and one-sided same-height radius majorants.
- Guardrails:
  - No use of `tower_cap_unbounded_with_eps` on `perronThreshold hRH T` or any
    height-dependent chosen radius.
  - The target and anti-target radius bounds are recombined at the same
    `T, ε`; no independent heights were introduced.
  - No new route uses `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - No arbitrary-target Kronecker or constant-1 Perron sqrt-error shortcut was
    introduced.
- Failed route guardrails:
  - Do not treat the canonical Perron max-majorant as a proof of the
    fixed-point growth theorem; it is the remaining exact same-height growth
    atom.
  - Do not replace the same-height target/anti radius recombination with
    independently selected target/anti heights.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, `git diff --check`, or other check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Prove/source `PerronThresholdTowerExpHalfBudgetCanonicalMajorantHyp`.
  - Prove/source `TargetFiniteZeroPhaseRadiusHalfBudgetMajorantHyp` and
    `AntiTargetFiniteZeroPhaseRadiusHalfBudgetMajorantHyp` with a shared
    same-height quantitative Kronecker-radius estimate.

### 2026-04-29 Round 20: Canonical One-Sided Radius Leaves

- Classification: `HONEST_PROVIDER_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `TargetFiniteZeroPhaseRadiusHalfBudgetMajorantHyp`
  - `AntiTargetFiniteZeroPhaseRadiusHalfBudgetMajorantHyp`
- Target choice:
  - Closed the existential-majorant part of the one-sided radius leaves
    deterministically. For each side, the optimal majorant is just the chosen
    realized radius plus `1`; the remaining content is the direct same-height
    tower inequality.
- Facts banked:
  - Added `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp`, the direct
    target-side tower domination of
    `targetFiniteZeroInhomogeneousPhaseRadius T ε + 1`.
  - Added `targetFiniteZeroPhaseRadiusHalfBudgetMajorant_of_canonical_hyp`,
    deriving `TargetFiniteZeroPhaseRadiusHalfBudgetMajorantHyp` by choosing
    `R = targetFiniteZeroInhomogeneousPhaseRadius T ε + 1`.
  - Added `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp`, the direct
    anti-target-side tower domination of
    `antiTargetFiniteZeroInhomogeneousPhaseRadius T ε + 1`.
  - Added `antiTargetFiniteZeroPhaseRadiusHalfBudgetMajorant_of_canonical_hyp`,
    deriving `AntiTargetFiniteZeroPhaseRadiusHalfBudgetMajorantHyp` by
    choosing `R = antiTargetFiniteZeroInhomogeneousPhaseRadius T ε + 1`.
  - Added `rhPiWitnessData_of_correctedPerronOnlyCanonicalRadiusRoute`,
    exposing the corrected Perron-only endpoint from the canonical Perron
    majorant plus the two direct one-sided canonical radius leaves.
- Guardrails:
  - No target/anti height split was introduced; both one-sided canonical
    radius leaves are still quantified over the same given `T, ε` and then
    recombined through the existing same-height max route.
  - No use of `tower_cap_unbounded_with_eps` on a height-dependent chosen
    radius.
  - No new route uses `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - No arbitrary-target Kronecker or constant-1 Perron sqrt-error shortcut was
    introduced.
- Failed route guardrails:
  - Do not treat either canonical one-sided radius leaf as a Kronecker proof;
    each is now the exact quantitative radius-growth atom still needed.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, `git diff --check`, or other check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Prove/source `PerronThresholdTowerExpHalfBudgetCanonicalMajorantHyp`.
  - Prove/source `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp`.
  - Prove/source `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp`.

### 2026-04-29 Round 21: Canonical Leaf Comparison Reductions

- Classification: `HONEST_COMPARISON_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `PerronThresholdTowerExpHalfBudgetCanonicalMajorantHyp`
  - `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp`
  - `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp`
- Facts banked:
  - Added `perronThresholdTowerExpHalfBudgetCanonicalMajorant_of_growth_hyp`,
    a non-instance comparison theorem deriving the canonical Perron
    max-majorant leaf from the older same-height two-inequality growth source
    `PerronThresholdTowerExpHalfBudgetGrowthHyp` by `max_le`.
  - Added `targetFiniteZeroPhaseRadiusHalfBudgetCanonical_of_pairedGrowth_hyp`,
    a non-instance projection from paired radius growth to the target-side
    canonical radius leaf.
  - Added
    `antiTargetFiniteZeroPhaseRadiusHalfBudgetCanonical_of_pairedGrowth_hyp`,
    the analogous non-instance projection for the anti-target side.
- Failed routes and guardrails:
  - These are intentionally not typeclass instances: the current validated
    provider chain already has canonical-to-majorant-to-growth edges, so
    installing the reverse implications as instances would risk a typeclass
    loop.
  - The comparison theorems do not close the analytic debt from public/deep
    inputs. They record exact equivalence/projection structure and keep the
    remaining atoms honest.
  - No use of `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - No arbitrary-target Kronecker, independent target/anti heights,
    `tower_cap_unbounded_with_eps` fixed-point shortcut, or constant-1 Perron
    sqrt-error shortcut was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, `git diff --check`, or other check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Source a true fixed-height growth provider for
    `PerronThresholdTowerExpHalfBudgetCanonicalMajorantHyp` from a bound on
    `perronThreshold hRH T` at the same selected `T`.
  - Source a quantitative Kronecker-radius provider for
    `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp` and
    `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp`; bounding a
    different existential radius is insufficient unless the chosen-radius
    definition is changed or a direct bounded witness route is added.

### 2026-04-29 Round 22: Canonical Budget Exact-Seed Endpoint

- Classification: `HONEST_ROUTE_PACKAGING_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `exactSeedAboveThreshold_perron_of_pairedRelativeDensityAndCanonicalBudgets_hyp`
- Facts banked:
  - Added
    `exactSeedAboveThreshold_perron_of_pairedRelativeDensityAndCanonicalBudgets_hyp`,
    a non-instance endpoint packaging the current canonical Perron
    max-majorant leaf plus the target/anti canonical chosen-radius leaves into
    the paired Perron-only exact-seed classes.
  - The proof uses local `letI`s to traverse the validated chain:
    canonical Perron majorant → Perron majorant → Perron growth → Perron log
    half-budget, and canonical target/anti radii → one-sided majorants →
    paired radius majorant → paired radius growth → Perron-selected radius
    half-budget.
- Remaining goal shape:
  - `PerronThresholdTowerExpHalfBudgetCanonicalMajorantHyp`: for each
    `hRH, X`, choose one same `T, ε` with `4 ≤ T`, `0 < ε`, `ε < 1`, and
    `max (X + 1) (perronThreshold hRH T + 1)` below the half triple-exp
    tower at that same `T, ε`.
  - `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp`: for every
    same-height `T, ε`, bound
    `targetFiniteZeroInhomogeneousPhaseRadius T ε + 1` by the half
    double-exp radius budget.
  - `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp`: same statement
    with `antiTargetFiniteZeroInhomogeneousPhaseRadius T ε + 1`.
- Failed/circular route:
  - Did not add instances for the reverse comparison edges from Round 21. The
    canonical leaves already imply majorant/growth leaves by instance; making
    growth imply canonical by instance would create a typeclass cycle.
  - Did not try to prove chosen-radius bounds from a merely bounded
    existential Kronecker radius. The definitions use `Classical.choose`, so a
    separately bounded witness does not bound the chosen radius without a new
    chosen-minimum or direct bounded-route interface.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - No arbitrary-target Kronecker, independent target/anti heights,
    `tower_cap_unbounded_with_eps` fixed-point shortcut, or constant-1 Perron
    sqrt-error shortcut was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, `git diff --check`, or other check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Prove/source a fixed-height bound on `perronThreshold hRH T` strong enough
    to instantiate `PerronThresholdTowerExpHalfBudgetCanonicalMajorantHyp`.
  - Decide whether the phase-radius budget should continue to bound the
    existing `Classical.choose` radii directly or be rerouted through a
    direct bounded relative-density witness that carries the bounded radius
    instead of projecting through the chosen-radius definitions.

### 2026-04-29 Round 23: Growth-Budget Exact-Seed Endpoint

- Classification: `HONEST_ROUTE_PACKAGING_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `exactSeedAboveThreshold_perron_of_pairedRelativeDensityAndGrowthBudgets_hyp`
- Facts banked:
  - Added
    `exactSeedAboveThreshold_perron_of_pairedRelativeDensityAndGrowthBudgets_hyp`,
    a non-instance provider endpoint from paired finite-zero relative density,
    `PerronThresholdTowerExpHalfBudgetGrowthHyp`, and
    `TargetAntiFiniteZeroPhaseRadiusHalfBudgetGrowthHyp` directly to the
    target/anti Perron-only exact-seed classes.
  - This mirrors the already validated corrected RH witness route
    `rhPiWitnessData_of_correctedPerronOnlyGrowthBudgetRoute` at exact-seed
    level, using only local `letI`s for the existing growth-to-half-budget
    reductions.
- Remaining goal shape:
  - `PerronThresholdTowerExpHalfBudgetCanonicalMajorantHyp` still needs one
    same-height `T, ε` with
    `max (X + 1) (perronThreshold hRH T + 1)` below the half triple-exp
    tower.
  - `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp` and
    `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp` still need direct
    bounds on the chosen radii
    `targetFiniteZeroInhomogeneousPhaseRadius T ε` and
    `antiTargetFiniteZeroInhomogeneousPhaseRadius T ε`.
- Failed/circular route:
  - Did not make `PerronThresholdTowerExpHalfBudgetGrowthHyp` imply
    `PerronThresholdTowerExpHalfBudgetCanonicalMajorantHyp` by instance; the
    reverse canonical-to-majorant-to-growth path is already an instance path,
    so this would be circular.
  - Did not make paired radius growth imply the one-sided canonical radius
    leaves by instance for the same reason: one-sided canonical leaves already
    imply paired growth through majorants.
  - Did not attempt to bound the current `Classical.choose` radius from a
    separately bounded existential Kronecker witness. That route is invalid
    unless the bounded witness is what the chosen-radius definition chooses,
    or the exact-seed route carries the bounded radius directly.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - No arbitrary-target Kronecker, independent target/anti heights,
    `tower_cap_unbounded_with_eps` fixed-point shortcut, or constant-1 Perron
    sqrt-error shortcut was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, `git diff --check`, or other check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Prove/source the fixed-height Perron-threshold growth source
    `PerronThresholdTowerExpHalfBudgetGrowthHyp`, or keep
    `PerronThresholdTowerExpHalfBudgetCanonicalMajorantHyp` as the canonical
    non-instance surface.
  - For the radius side, introduce a direct bounded-radius exact-seed route if
    the project wants to avoid bounding the existing `Classical.choose`
    radius definitions.

### 2026-04-29 Round 24: Canonical Budget Residual Predicates

- Classification: `HONEST_RESIDUAL_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `PerronThresholdTowerExpHalfBudgetCanonicalMajorantHyp`
  - `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp`
  - `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp`
- Facts banked:
  - Added
    `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`, naming the
    exact same-height fixed Perron-threshold inequality needed for the
    canonical Perron budget leaf.
  - Added
    `perronThresholdTowerExpHalfBudgetCanonicalMajorant_of_residual`, a
    non-instance constructor from that residual predicate to
    `PerronThresholdTowerExpHalfBudgetCanonicalMajorantHyp`.
  - Added `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`, naming
    the exact direct bound on
    `targetFiniteZeroInhomogeneousPhaseRadius T ε + 1`.
  - Added `targetFiniteZeroPhaseRadiusHalfBudgetCanonical_of_residual`, a
    non-instance constructor to the target canonical radius leaf.
  - Added `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`,
    naming the exact direct bound on
    `antiTargetFiniteZeroInhomogeneousPhaseRadius T ε + 1`.
  - Added `antiTargetFiniteZeroPhaseRadiusHalfBudgetCanonical_of_residual`,
    a non-instance constructor to the anti-target canonical radius leaf.
- Remaining goal shape:
  - Prove
    `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`: for every
    `hRH, X`, choose a shared `T, ε` with `4 ≤ T`, `0 < ε`, `ε < 1`, and
    `max (X + 1) (perronThreshold hRH T + 1)` below
    `exp (exp (exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2)) / 2)`.
  - Prove `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`: for every
    valid `T, ε`, bound the chosen target radius by the half double-exp
    budget.
  - Prove `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`: same
    bound for the chosen anti-target radius.
- Failed/circular route:
  - No closure from existing local facts was found. The only local facts about
    `targetFiniteZeroInhomogeneousPhaseRadius` and
    `antiTargetFiniteZeroInhomogeneousPhaseRadius` are positivity and the
    relative-density property from `Classical.choose_spec`; they do not bound
    the chosen values.
  - Did not install residual constructors as instances, so no new
    canonical/majorant/growth reverse cycle is introduced.
  - Did not claim a bounded existential Kronecker witness controls
    `Classical.choose`; the residual names make that remaining requirement
    explicit.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - No arbitrary-target Kronecker, independent target/anti heights,
    `tower_cap_unbounded_with_eps` fixed-point shortcut, or constant-1 Perron
    sqrt-error shortcut was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, `git diff --check`, or other check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Close one residual predicate directly, or replace the radius route with a
    direct bounded-radius exact-seed interface that carries the bounded
    Kronecker witness instead of requiring a bound on the current chosen
    radius definitions.

### 2026-04-29 Round 25: Fixed-Height Transfer Inequality

- Classification: `HONEST_INEQUALITY_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`
- Facts banked:
  - Added
    `perronThresholdTowerExpHalfBudgetCanonicalMajorant_bound_of_fixedHeightTransfer`.
  - The theorem proves the concrete residual inequality from two explicit
    same-height facts:
    1. the tower half-budget at selected `T, ε` dominates the fixed-height
       majorant `max (X + 1) (perronThreshold hRH T0 + 1)`;
    2. the selected threshold satisfies
       `perronThreshold hRH T + 1 ≤ max (X + 1) (perronThreshold hRH T0 + 1)`.
  - This is strictly closer to the Perron residual because tower cofinality can
    target a fixed real majorant; the remaining nontrivial step is now exactly
    a fixed-height-to-selected-height threshold transfer.
- Remaining goal shape:
  - To close `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`, find
    `T0, T, ε` with `4 ≤ T`, `0 < ε`, `ε < 1`, the fixed-majorant tower bound,
    and the transfer inequality above.
  - The target/anti radius residuals remain unchanged: they require direct
    bounds on the current chosen radii, not on separately chosen witnesses.
- Failed/circular route:
  - The direct tower-cofinality route still fails because
    `perronThreshold hRH T` depends on the same selected `T`. One can dominate
    `perronThreshold hRH T0` after choosing a fixed `T0`, but the residual
    needs `perronThreshold hRH T`.
  - Did not add any reverse-comparison instance or growth-to-canonical edge.
  - Did not introduce any unproved control of `Classical.choose` radii.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - No arbitrary-target Kronecker, independent target/anti heights,
    `tower_cap_unbounded_with_eps` fixed-point shortcut, or constant-1 Perron
    sqrt-error shortcut was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, `git diff --check`, or other check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Prove the selected-height transfer inequality
    `perronThreshold hRH T + 1 ≤ max (X + 1) (perronThreshold hRH T0 + 1)`
    for a tower-selected `T`, or replace the threshold route with a direct
    fixed-height Perron error payload that avoids comparing opaque
    `Classical.choose` thresholds across heights.

### 2026-04-29 Round 26: Transfer Equivalence Analysis

- Classification: `HONEST_TRANSFER_ANALYSIS_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - transfer condition for `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`
- Facts banked:
  - Added `perronThreshold_fixedHeightTransfer_iff_selectedThreshold_bound`.
    This proves the transfer condition
    `perronThreshold hRH T + 1 ≤ max (X + 1) (perronThreshold hRH T0 + 1)`
    is exactly equivalent to the cleaner bound
    `perronThreshold hRH T ≤ max X (perronThreshold hRH T0)`.
  - Added `perronThreshold_fixedHeightTransfer_sameHeight`, proving the
    transfer is tautological when `T = T0`.
- Sharp analysis:
  - The transfer is not false in all cases: it is true for the same height.
  - The cross-height transfer needed after using tower cofinality is not
    available from the current definition. `perronThreshold hRH T` is a
    `Classical.choose` lower endpoint for an eventual statement at each
    separate height, and no monotonicity/minimality/boundedness theorem relates
    the chosen thresholds at `T0` and `T`.
  - Tower cofinality can select a height `T` that dominates a fixed real, but
    it does not itself prove the selected-height threshold bound above.
- Remaining goal shape:
  - Prove `perronThreshold hRH T ≤ max X (perronThreshold hRH T0)` for the
    tower-selected `T`, or avoid the cross-height threshold comparison by
    carrying the fixed-height Perron error witness directly through a corrected
    residual/interface.
  - Radius residuals remain unchanged and still require direct bounds on the
    existing chosen radii.
- Failed/circular route:
  - No monotonicity or minimal-threshold property for `perronThreshold` was
    found in the local provider path.
  - Did not add reverse-comparison instances, growth-to-canonical cycles,
    axioms/sorries, or `Classical.choose` radius control.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`,
    `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - No arbitrary-target Kronecker, independent target/anti heights,
    `tower_cap_unbounded_with_eps` fixed-point shortcut, or constant-1 Perron
    sqrt-error shortcut was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build,
    public import probe, `git diff --check`, or other check command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Replace the threshold residual with a direct fixed-height Perron error
    payload/interface, or add a genuine growth/monotonicity theorem for the
    selected thresholds. The latter is stronger than current local facts and
    should not be assumed from `Classical.choose`.

### 2026-04-29 Round 27: Selected-Threshold Residual Surface

- Classification: `CONDITIONAL_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual` after the transfer equivalence diagnostic.
- Facts banked:
  - Added `PerronThresholdTowerExpHalfBudgetSelectedThresholdResidual`.
  - Added `perronThresholdTowerExpHalfBudgetCanonicalMajorantResidual_of_selectedThresholdResidual`.
  - The new residual separates the two real requirements:
    1. a fixed-height tower/cofinality bound for `max (X + 1) (perronThreshold hRH T0 + 1)` at selected `T, ε`;
    2. the stripped selected-height threshold bound `perronThreshold hRH T ≤ max X (perronThreshold hRH T0)`.
- Remaining goal shape:
  - Prove `PerronThresholdTowerExpHalfBudgetSelectedThresholdResidual`, or replace the downstream canonical majorant surface with a direct fixed-height Perron error payload that never compares `perronThreshold` values at different heights.
  - The cross-height monotonicity route remains demoted: the selected threshold is a `Classical.choose` endpoint for the fixed-height eventual statement and current local facts do not relate choices at `T0` and `T`.
- Failed/circular route:
  - Did not add a monotonicity theorem for `perronThreshold`.
  - Did not use tower cofinality as if it controlled a quantity depending on the chosen height.
  - Did not add a provider instance for the new residual, avoiding reverse edges into the canonical/growth provider chain.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh` in the new route.
  - No arbitrary-target Kronecker, independent target/anti heights, constant-1 Perron sqrt-error shortcut, axioms/sorries, reverse-comparison instance, or unproved `Classical.choose` radius control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build, public import probe, `git diff --check`, or other validation command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Prove the selected-threshold residual directly, starting with a genuine bound of `perronThreshold hRH T` by a fixed-height majorant, or refactor the exact-seed/canonical majorant route to carry a fixed-height Perron-error witness instead of the opaque selected threshold.

### 2026-04-29 Round 28: Fixed-Height Perron Error Refactor Surface

- Classification: `CONDITIONAL_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `PerronThresholdTowerExpHalfBudgetSelectedThresholdResidual`.
- Facts banked:
  - Direct proof of `PerronThresholdTowerExpHalfBudgetSelectedThresholdResidual` remains blocked by the same missing selected-height threshold bound `perronThreshold hRH T ≤ max X (perronThreshold hRH T0)`.
  - Added `InhomogeneousPhaseFitWithFixedHeightPerronErrorHyp`, a direct Perron-error phase-fit boundary that carries `1 < x` and the actual fixed-height error estimate `|piLiErr x + piMainFromZeros ((finite_zeros_le T).toFinset) x| ≤ Real.sqrt x / Real.log x` instead of `perronThreshold hRH T ≤ x`.
  - Added `inhomogeneousPhaseFitWithFixedHeightPerronError_of_aboveThreshold_hyp`, proving the old Perron-threshold phase-fit surface implies the direct-error surface by one use of `perronThreshold_spec`.
  - Added direct target/anti exact-seed-shaped payloads `TargetTowerExactSeedWithFixedHeightPerronError` and `AntiTargetTowerExactSeedWithFixedHeightPerronError`.
  - Added `target_exact_seed_withFixedHeightPerronError_from_phase_fit` and `antiTarget_exact_seed_withFixedHeightPerronError_from_phase_fit`, which package direct-error phase fit into target/anti seed payloads without any threshold comparison.
- Remaining goal shape:
  - To close the current canonical threshold route, still prove `PerronThresholdTowerExpHalfBudgetSelectedThresholdResidual`.
  - To bypass it, add the next bridge from `TargetTowerExactSeedWithFixedHeightPerronError` and `AntiTargetTowerExactSeedWithFixedHeightPerronError` into the corrected phase-coupling/RH-`pi` endpoint, replacing the need for `TargetTowerExactSeedAbovePerronThresholdPerronHyp` and `AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp` on that route.
- Failed/circular route:
  - Did not assert any cross-height monotonicity/minimality for `perronThreshold`.
  - Did not add provider instances for the new direct-error classes or payloads.
  - Did not route tower cofinality through a quantity depending on the chosen height.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh` in the new route.
  - No arbitrary-target Kronecker, independent target/anti heights, constant-1 Perron sqrt-error shortcut, axioms/sorries, reverse-comparison instance, or unproved `Classical.choose` radius control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build, public import probe, `git diff --check`, or other validation command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Prove a direct-error phase-coupling bridge consuming `TargetTowerExactSeedWithFixedHeightPerronError` and `AntiTargetTowerExactSeedWithFixedHeightPerronError`, or prove the selected-threshold residual with a genuine non-`Classical.choose` growth theorem.

### 2026-04-29 Round 29: Fixed-Height Error Route Bridge

- Classification: `CONDITIONAL_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - Fixed-height Perron-error seed route below the corrected phase-coupling provider endpoint.
- Facts banked:
  - Added `targetTowerArgApproxFamily_of_exactSeedWithFixedHeightPerronError`.
  - Added `antiTargetTowerArgApproxFamily_of_exactSeedWithFixedHeightPerronError`.
  - Added `correctedPhaseCoupling_of_exactSeedWithFixedHeightPerronError`.
  - Added `rhPiWitnessData_of_exactSeedWithFixedHeightPerronError`.
  - Added `rhPiWitnessData_of_fixedHeightPerronErrorPhaseFit_hyp`.
  - Added route-file packaging endpoints `correctedPhaseCoupling_of_correctedPerronOnlyFixedHeightErrorRoute` and `rhPiWitnessData_of_correctedPerronOnlyFixedHeightErrorRoute`.
- What changed:
  - `TargetTowerExactSeedWithFixedHeightPerronError` and `AntiTargetTowerExactSeedWithFixedHeightPerronError` now feed full target/anti arg-approx families by taking `x = Real.exp t0`; the carried fixed-height Perron error estimate supplies the exact field that was previously recovered through `perronThreshold_spec`.
  - The corrected phase-coupling and `RhPiWitnessData` endpoints can now be reached from `InhomogeneousPhaseFitWithFixedHeightPerronErrorHyp` without constructing `TargetTowerExactSeedAbovePerronThresholdPerronHyp` or `AntiTargetTowerExactSeedAbovePerronThresholdPerronHyp`.
- Remaining goal shape:
  - The analytic/cofinality payload is now `InhomogeneousPhaseFitWithFixedHeightPerronErrorHyp`: for each `hRH`, lower bound `X`, and target phase, choose `x, T, ε` with the actual fixed-height Perron error bound, phase approximation, and tower cap at the same selected height.
  - The old selected-threshold residual remains available but is no longer the preferred route.
- Failed/circular route:
  - Did not prove or assume cross-height monotonicity/minimality of `perronThreshold`.
  - Did not add provider instances; all new bridges are explicit theorem endpoints.
  - Did not weaken target statements or route through the false truncated-π surface.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh` in the new route.
  - No arbitrary-target Kronecker revival, independent target/anti heights, constant-1 Perron sqrt-error shortcut, axioms/sorries, reverse-comparison instance, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build, public import probe, `git diff --check`, or other validation command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Prove or reduce `InhomogeneousPhaseFitWithFixedHeightPerronErrorHyp`, likely by combining fixed-height Perron eventuality, relation-compatible finite-zero phase approximation, and same-height tower cofinality around the chosen `x` rather than a `perronThreshold` comparison.

### 2026-04-29 Round 30: Fixed-Height Phase-Fit Window Reduction

- Classification: `CONDITIONAL_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `InhomogeneousPhaseFitWithFixedHeightPerronErrorHyp`.
- Facts banked:
  - Direct proof of `InhomogeneousPhaseFitWithFixedHeightPerronErrorHyp` is not available from the honest target/anti relation-compatible inputs because the class quantifies over arbitrary `targetPhase`.
  - Added `FixedHeightPerronErrorPhaseWideWindowHyp`, the threshold-free same-height window/cofinality source: for a selected `T, ε, L, U`, every `x ≥ exp L` has the actual fixed-height Perron error estimate, the logarithmic window is wide enough for the phase search radius, and `exp U` is below the tower cap.
  - Added `inhomogeneousPhaseFitWithFixedHeightPerronError_of_wideWindow_relativeDense_hyp`, proving the fixed-height phase-fit payload from `FixedHeightPerronErrorPhaseWideWindowHyp` plus the existing explicit `FiniteZeroInhomogeneousPhaseRelativelyDenseHyp` wrapper.
- Remaining goal shape:
  - For the arbitrary `InhomogeneousPhaseFitWithFixedHeightPerronErrorHyp` class, the remaining inputs are exactly:
    1. `FixedHeightPerronErrorPhaseWideWindowHyp`, a same-height fixed Perron-error/tower window theorem; and
    2. an arbitrary-target finite-zero relative-density theorem (`FiniteZeroInhomogeneousPhaseRelativelyDenseHyp`).
  - The public honest route should avoid promoting this arbitrary-target wrapper and instead continue with target/anti-specific relation-compatible variants if the coordinator wants provider synthesis from current deep inputs.
- Failed/circular route:
  - Did not use cross-height `perronThreshold` monotonicity or compare `Classical.choose` thresholds.
  - Did not add any provider instance for the new fixed-height window reduction.
  - Did not turn arbitrary-target Kronecker into a public provider; the theorem is explicit and conditional.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, independent target/anti heights, reverse-comparison instance, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build, public import probe, `git diff --check`, or other validation command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Prove `FixedHeightPerronErrorPhaseWideWindowHyp` from fixed-height Perron eventuality plus a same-height tower/window cofinality theorem, or introduce target/anti-specific fixed-height phase-fit classes that consume the existing relation-compatible finite-zero payloads without the arbitrary `targetPhase` quantifier.

### 2026-04-29 Round 31: Target/Anti Fixed-Height Route Split

- Classification: `CONDITIONAL_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - Target/anti-specific replacement for the arbitrary `InhomogeneousPhaseFitWithFixedHeightPerronErrorHyp` public path.
- Facts banked:
  - Added `TargetPhaseFitWithFixedHeightPerronErrorHyp` and `AntiTargetPhaseFitWithFixedHeightPerronErrorHyp`.
  - Added target/anti exact-seed bridges `target_exact_seed_withFixedHeightPerronError_from_target_phase_fit` and `antiTarget_exact_seed_withFixedHeightPerronError_from_antiTarget_phase_fit`.
  - Added corrected endpoint bridges `correctedPhaseCoupling_of_targetAntiFixedHeightPerronErrorPhaseFit_hyp` and `rhPiWitnessData_of_targetAntiFixedHeightPerronErrorPhaseFit_hyp`.
  - Added `targetPhaseFitWithFixedHeightPerronError_of_relative_dense_hyp` and `antiTargetPhaseFitWithFixedHeightPerronError_of_relative_dense_hyp`, both using the common `FixedHeightPerronErrorPhaseWideWindowHyp` plus target/anti-specific finite-zero relative density.
  - Added `targetAntiFixedHeightPerronErrorPhaseFit_of_relationCompatibleAndWindow_hyp`, packaging the target/anti phase-fit classes from relation-compatible finite-set Kronecker, paired zeta compatibility, and the fixed-height wide-window source.
  - Added route-file endpoints `correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiFixedHeightErrorRoute` and `rhPiWitnessData_of_correctedPerronOnlyTargetAntiFixedHeightErrorRoute`.
- What changed:
  - The corrected public/provider path no longer needs the arbitrary `InhomogeneousPhaseFitWithFixedHeightPerronErrorHyp` or arbitrary-target `FiniteZeroInhomogeneousPhaseRelativelyDenseHyp`.
  - The route consumes the existing relation-compatible target/anti finite-zero payloads and leaves only the common same-height fixed Perron-error/tower window source.
- Remaining goal shape:
  - Prove `FixedHeightPerronErrorPhaseWideWindowHyp`: choose one `T, ε, L, U` such that `x ≥ exp L` has the actual fixed-height Perron error estimate at height `T`, `L + radius T ε < U`, and `exp U` fits under the same-height tower cap.
- Failed/circular route:
  - Did not use cross-height `perronThreshold` monotonicity or compare `Classical.choose` thresholds.
  - Did not add provider instances for the new route; all wiring is through explicit theorem endpoints and local `letI` values only.
  - Did not promote arbitrary-target Kronecker or arbitrary target-phase density into the public path.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, independent target/anti heights, reverse-comparison instance, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build, public import probe, `git diff --check`, or other validation command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Prove or reduce `FixedHeightPerronErrorPhaseWideWindowHyp` from fixed-height Perron eventuality and a same-height tower/window cofinality theorem for the supplied radius function.

### 2026-04-29 Round 32: Same-Height Threshold Window Adapter

- Classification: `CONDITIONAL_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `FixedHeightPerronErrorPhaseWideWindowHyp`.
- Facts banked:
  - Added `fixedHeightPerronErrorPhaseWideWindow_of_perronThresholdWideWindow_hyp`.
  - The adapter proves the fixed-height Perron-error wide window from `PerronThresholdTowerPhaseWideWindowHyp` by applying `perronThreshold_spec` only at the selected same height `T`.
  - Added corrected-route endpoints `correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiThresholdWindowRoute` and `rhPiWitnessData_of_correctedPerronOnlyTargetAntiThresholdWindowRoute`, using the target/anti-specific fixed-height route with a local fixed-height-window value.
- What changed:
  - `FixedHeightPerronErrorPhaseWideWindowHyp` is no longer an isolated payload when a same-height Perron-threshold wide window is available.
  - The target/anti-specific corrected route can be validated directly from relation-compatible finite-zero data plus `PerronThresholdTowerPhaseWideWindowHyp`.
- Remaining goal shape:
  - The analytic tower source is still `PerronThresholdTowerPhaseWideWindowHyp`, equivalently its same-height domination/growth leaves. This round does not prove tower cofinality against a height-dependent threshold; it only removes the extra fixed-height-error wrapper above the already-selected same-height threshold window.
- Failed/circular route:
  - Did not add a global provider instance for `FixedHeightPerronErrorPhaseWideWindowHyp`.
  - Did not compare `perronThreshold hRH T` across two heights.
  - Did not use the arbitrary-target fixed-height route as the preferred public endpoint.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh` in the new route.
  - No axioms/sorries, statement weakening, independent target/anti heights, reverse-comparison instance, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build, public import probe, or other validation command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Prove or further reduce `PerronThresholdTowerPhaseWideWindowHyp`, preferably through the existing same-height `PerronThresholdTowerWideDominationHyp`/log-budget leaves without cross-height threshold monotonicity.

### 2026-04-29 Round 33: Wide-Domination Residual Exposure

- Classification: `CONDITIONAL_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `PerronThresholdTowerPhaseWideWindowHyp`.
- Facts banked:
  - Added `fixedHeightPerronErrorPhaseWideWindow_of_perronThresholdWideDomination_hyp`.
  - The theorem chains the existing same-height `PerronThresholdTowerWideDominationHyp → PerronThresholdTowerPhaseWideWindowHyp` adapter with the fixed-height Perron-error adapter from Round 32.
  - Added route endpoints `correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiWideDominationRoute` and `rhPiWitnessData_of_correctedPerronOnlyTargetAntiWideDominationRoute`.
- What changed:
  - The target/anti-specific fixed-height corrected route can now be validated from relation-compatible finite-zero data plus the exact arbitrary-radius same-height domination leaf `PerronThresholdTowerWideDominationHyp`.
  - `PerronThresholdTowerPhaseWideWindowHyp` is no longer the exposed route blocker for this endpoint; the exposed blocker is its smaller domination source.
- Remaining goal shape:
  - Prove or further reduce `PerronThresholdTowerWideDominationHyp`: for every positive radius function, choose the same `T, ε` so that `Real.exp (Real.log (max X (perronThreshold hRH T) + 1) + radius T ε + 1)` is below the same-height tower cap.
  - This is still stronger than target/anti realized-radius geometry; it is the arbitrary-radius window source. The target/anti route also has narrower realized-radius budget routes already available, but this round preserves the supplied-radius fixed-height window surface exactly.
- Failed/circular route:
  - Did not prove tower cofinality for a radius depending on the selected height.
  - Did not use cross-height `perronThreshold` monotonicity or compare `Classical.choose` thresholds across heights.
  - Did not add global provider instances for the new fixed-height/wide-domination adapter.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh` in the new route.
  - No axioms/sorries, statement weakening, independent target/anti heights, reverse-comparison instance, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build, public import probe, or other validation command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Either prove/reduce `PerronThresholdTowerWideDominationHyp` directly, or keep the public target/anti endpoint on the narrower realized-radius/log-budget route and continue the canonical Perron and chosen-radius residuals there.

### 2026-04-29 Round 34: Arbitrary-Radius Log Budget Split

- Classification: `CONDITIONAL_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `PerronThresholdTowerWideDominationHyp`.
- Facts banked:
  - Added `PerronThresholdTowerWideLogDominationHyp`, the log-level same-height arbitrary-radius domination source obtained by peeling off the outer monotone `Real.exp`.
  - Added `PerronThresholdTowerWideLogBudgetHyp`, splitting the arbitrary-radius log source into a Perron lower-endpoint half-budget and a supplied-radius half-budget at the same selected `T, ε`.
  - Added `perronThresholdTowerWideDomination_of_logDomination_hyp` and `perronThresholdTowerWideLogDomination_of_logBudget_hyp`.
  - Added corrected-route endpoints `correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiWideLogDominationRoute`, `correctedPhaseCoupling_of_correctedPerronOnlyTargetAntiWideLogBudgetRoute`, `rhPiWitnessData_of_correctedPerronOnlyTargetAntiWideLogDominationRoute`, and `rhPiWitnessData_of_correctedPerronOnlyTargetAntiWideLogBudgetRoute`.
- What changed:
  - The arbitrary-radius fixed-height window route now exposes a strictly log-scale residual before the exponential tower cap.
  - The next same-height obstruction can be studied as two explicit inequalities: controlling `Real.log (max X (perronThreshold hRH T) + 1)` and controlling `radius T ε + 1` by halves of the same double-exponential tower scale.
- Remaining goal shape:
  - Prove or further reduce `PerronThresholdTowerWideLogBudgetHyp`:
    for every positive supplied radius function, choose one `T, ε` such that both the Perron lower endpoint and that same supplied `radius T ε` fit within half of `Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2))`.
  - This remains an arbitrary-radius fixed-point/cofinality statement; it is stronger than the target/anti realized-radius route.
- Failed/circular route:
  - Did not use target/anti realized radii to prove an arbitrary supplied-radius theorem.
  - Did not assert cofinal tower domination for a height-dependent radius without naming the exact budget leaf.
  - Did not add provider instances for the new log/log-budget classes.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh` in the new route.
  - No axioms/sorries, statement weakening, independent target/anti heights, cross-height `perronThreshold` monotonicity, reverse-comparison instance, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build, public import probe, or other validation command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Decide whether `PerronThresholdTowerWideLogBudgetHyp` should remain as the arbitrary-radius source, or route the public endpoint through the already narrower target/anti realized-radius budget leaves and continue the canonical Perron/chosen-radius residuals.

### 2026-04-29 Round 35: Arbitrary-Radius Budget Refutation

- Classification: `REFUTED`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `PerronThresholdTowerWideLogBudgetHyp`.
- Facts banked:
  - Added `not_perronThresholdTowerWideLogBudgetHyp_of_rh`.
  - On any supplied RH branch, choose `radius T ε` to be exactly `Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2)) / 2`.
  - This radius is positive for every `T, ε`, but the second half-budget conjunct becomes `B + 1 ≤ B` at the selected height, contradiction.
- What changed:
  - The arbitrary-radius half-budget source is now diagnosed as false on the RH side and should not remain a public-path blocker.
  - The earlier arbitrary-radius `PerronThresholdTowerWideDominationHyp`/`PerronThresholdTowerWideLogDominationHyp` route is demoted for public provider synthesis; the viable public route should stay with target/anti realized radii and the canonical Perron/chosen-radius residuals.
- Remaining goal shape:
  - Continue the narrower target/anti route rather than arbitrary supplied radii:
    `PerronThresholdTowerExpHalfBudgetCanonicalMajorantHyp`,
    `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp`, and
    `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalHyp` remain the honest quantitative atoms already feeding the corrected route.
- Failed/circular route:
  - Arbitrary positive radius functions cannot be controlled by a same-height tower budget without an envelope/growth hypothesis on the supplied radius.
  - Did not infer global `¬ PerronThresholdTowerWideLogBudgetHyp` without an RH branch; the class quantifies over RH, so the precise refutation is conditional on a supplied `hRH`.
  - Did not weaken the class statement or introduce an envelope replacement in this patch.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, provider instances, independent target/anti heights, cross-height `perronThreshold` monotonicity, reverse-comparison instance, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build, public import probe, or other validation command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Return to the narrower target/anti realized-radius route and attack one of the residual canonical leaves directly, preferably `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual` if the Perron selected-height issue can be avoided, otherwise the target/anti chosen-radius residuals.

### 2026-04-29 Round 36: Canonical Residual Route Packaging

- Classification: `CONDITIONAL_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - Public/provider packaging below the target/anti realized-radius route after the arbitrary-radius budget refutation.
- Facts banked:
  - Added `correctedPhaseCoupling_of_correctedPerronOnlyCanonicalResidualRoute`.
  - Added `rhPiWitnessData_of_correctedPerronOnlyCanonicalResidualRoute`.
  - These endpoints consume the exact residual predicates:
    `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`,
    `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`, and
    `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`.
  - The route locally packages the residuals into the existing canonical classes using `perronThresholdTowerExpHalfBudgetCanonicalMajorant_of_residual`, `targetFiniteZeroPhaseRadiusHalfBudgetCanonical_of_residual`, and `antiTargetFiniteZeroPhaseRadiusHalfBudgetCanonical_of_residual`.
- What changed:
  - The public corrected Perron-only endpoint now has a direct theorem-shaped route from the actual target/anti chosen-radius residuals, not the false arbitrary external-radius budget.
  - The arbitrary-radius `PerronThresholdTowerWideLogBudgetHyp` remains demoted after Round 35; it is not used by the new route.
- Remaining goal shape:
  - Prove the three residual predicates directly:
    1. `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`;
    2. `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`;
    3. `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`.
  - The target/anti residuals must bound the actual `Classical.choose` radii, not a separately chosen Kronecker radius.
- Failed/circular route:
  - Did not add provider instances for residuals or canonical classes.
  - Did not revive arbitrary supplied radii, arbitrary-target Kronecker, or the false truncated-π route.
  - Did not assert cross-height `perronThreshold` monotonicity or selected-threshold transfer.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, independent target/anti heights, reverse-comparison instance, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build, public import probe, or other validation command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Attack `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual` only if the same-height selected threshold can be controlled without the already-demoted transfer; otherwise attack `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual` or `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual` by proving bounds for the actual chosen finite-zero phase radii.

### 2026-04-29 Round 37: Canonical Residuals From Growth Facts

- Classification: `CONDITIONAL_REDUCTION_PENDING_VALIDATION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - The three canonical residual predicates feeding the target/anti realized-radius route.
- Facts banked:
  - Added `perronThresholdTowerExpHalfBudgetCanonicalMajorantResidual_of_growth_hyp`.
  - Added `targetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual_of_pairedGrowth_hyp`.
  - Added `antiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual_of_pairedGrowth_hyp`.
  - Added `rhPiWitnessData_of_correctedPerronOnlyGrowthResidualRoute`.
- What changed:
  - `PerronThresholdTowerExpHalfBudgetGrowthHyp` now closes the exact Perron canonical residual by recombining its same-height `X + 1` and `perronThreshold hRH T + 1` bounds with `max_le`.
  - `TargetAntiFiniteZeroPhaseRadiusHalfBudgetGrowthHyp` now closes both one-sided chosen-radius residuals by projecting through the paired max; this controls the actual target/anti `Classical.choose` radii already used in the route.
  - The corrected Perron-only route can now pass explicitly through the residual predicates while consuming existing same-height growth facts.
- Remaining goal shape:
  - The live quantitative atoms are now the existing growth facts:
    `PerronThresholdTowerExpHalfBudgetGrowthHyp` and
    `TargetAntiFiniteZeroPhaseRadiusHalfBudgetGrowthHyp`.
  - The stronger arbitrary-radius `PerronThresholdTowerWideLogBudgetHyp` remains refuted/demoted and is not used.
- Failed/circular route:
  - Did not add instances from residual predicates or reverse edges into the canonical/growth graph.
  - Did not use arbitrary supplied radii, arbitrary-target Kronecker, cross-height `perronThreshold` monotonicity, or selected-threshold transfer.
  - Did not bound a separately chosen Kronecker radius; the one-sided residual reductions project the actual paired chosen radii.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, independent target/anti heights, reverse-comparison instance, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Static-only lane pass; no `lean`, `lake`, `lake env lean`, focused build, public import probe, or other validation command was run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
- Smallest next theorem:
  - Attack `PerronThresholdTowerExpHalfBudgetGrowthHyp` if a same-height Perron threshold growth theorem is available; otherwise attack `TargetAntiFiniteZeroPhaseRadiusHalfBudgetGrowthHyp` by proving a bound for the actual paired target/anti finite-zero phase radii.

### 2026-04-29 Round 38: Growth Leaves Are Canonical Residuals

- Classification: `EXACT_IDENTITY`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `PerronThresholdTowerExpHalfBudgetGrowthHyp`
  - `TargetAntiFiniteZeroPhaseRadiusHalfBudgetGrowthHyp`
- Facts banked:
  - Added `perronThresholdTowerExpHalfBudgetGrowth_of_canonicalMajorantResidual`.
  - Added `targetAntiFiniteZeroPhaseRadiusHalfBudgetGrowth_of_canonicalResiduals`.
- What changed:
  - The Perron growth leaf now has an explicit non-instance reverse reduction from the exact canonical selected-height residual.
  - The paired finite-zero radius growth leaf now has an explicit non-instance reverse reduction from the two one-sided chosen-radius canonical residuals.
  - Together with Round 37's growth-to-residual reductions, this shows the current growth leaves are not smaller than the canonical residual inequalities; they are the same selected-height quantitative content in class form.
- Remaining goal shape:
  - The Perron side still needs a genuine same-height proof of
    `max (X + 1) (perronThreshold hRH T + 1) ≤ exp (exp (exp A / 2))`
    at a selected `T, ε`.
  - The phase-radius side still needs direct bounds for the actual chosen
    `targetFiniteZeroInhomogeneousPhaseRadius T ε` and
    `antiTargetFiniteZeroInhomogeneousPhaseRadius T ε`, not a separately chosen Kronecker radius.
- Failed/circular route:
  - Did not add typeclass instances for either reverse reduction.
  - Did not use canonical residuals to claim analytic closure; the new theorems are exact equivalence diagnostics, not new analytic inputs.
  - Did not use arbitrary supplied radii, cross-height `perronThreshold` monotonicity, selected-threshold transfer, or independently selected target/anti heights.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, provider cycles, reverse-comparison instances, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Passed focused validation under the coordinator singleflight rule.
- Validation command/result:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed; existing upstream linter warnings only.
- Smallest next theorem:
  - Prove the Perron canonical residual from a real same-height growth bound on `perronThreshold hRH T`; if that remains blocked, prove a quantitative Kronecker-radius theorem that bounds the actual chosen target/anti finite-zero radii.

### 2026-04-29 Round 39: Budgeted Kronecker Radius Route

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - The phase-radius side of the canonical residual obstruction.
- Facts banked:
  - Added `TargetAntiFiniteZeroInhomogeneousPhaseBudgetedRelativelyDenseHyp`.
  - Added `targetAntiPerronThresholdTowerWideDominationWithPhaseRadius_of_logHalfBudget_budgetedRelativelyDense_hyp`.
  - Added `exactSeed_of_correctedPerronOnlyBudgetedRadiusRoute`.
  - Added `correctedPhaseCoupling_of_correctedPerronOnlyBudgetedRadiusRoute`.
  - Added `rhPiWitnessData_of_correctedPerronOnlyBudgetedRadiusRoute`.
- What changed:
  - The corrected route can now consume explicit target/anti Kronecker search radii already bounded by the same-height tower half-budget.
  - This bypasses the old chosen-radius obstruction: the route uses the budgeted radii returned by the quantitative Kronecker theorem itself, rather than trying to prove a bound for an unconstrained `Classical.choose` from the unbudgeted relative-density class.
  - The Perron side is still supplied by `PerronThresholdTowerLogHalfBudgetHyp`; no cross-height `perronThreshold` transfer is used.
- Remaining goal shape:
  - Prove `TargetAntiFiniteZeroInhomogeneousPhaseBudgetedRelativelyDenseHyp` from quantitative relation-compatible Kronecker with explicit radius estimates, or continue the Perron side by proving `PerronThresholdTowerLogHalfBudgetHyp`/the canonical Perron residual from a real same-height growth bound on `perronThreshold hRH T`.
- Failed/circular route:
  - Did not add an instance from the new budgeted class into the old chosen-radius residual classes.
  - Did not claim that the old `targetFiniteZeroInhomogeneousPhaseRadius` or `antiTargetFiniteZeroInhomogeneousPhaseRadius` choices are bounded; those remain blocked because their existence predicates carry no upper bound.
  - Did not use arbitrary supplied radii, cross-height `perronThreshold` monotonicity, selected-threshold transfer, or independently selected target/anti heights.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, provider cycles, reverse-comparison instances, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Passed focused validation under the coordinator singleflight rule.
- Validation command/result:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed; existing upstream linter warnings only.
- Smallest next theorem:
  - `TargetAntiFiniteZeroInhomogeneousPhaseBudgetedRelativelyDenseHyp`, with a proof route through quantitative relation-compatible Kronecker radius bounds for the target and anti-target finite-zero phase boxes at the same `T, ε`.

### 2026-04-29 Round 40: Relation-Compatible Budgeted Kronecker Split

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `TargetAntiFiniteZeroInhomogeneousPhaseBudgetedRelativelyDenseHyp`.
- Facts banked:
  - Added `TargetAntiFiniteZeroRelationCompatibleBudgetedRelativelyDenseKroneckerHyp`.
  - Added `targetAntiFiniteZeroInhomogeneousPhaseBudgetedRelativelyDense_of_relationCompatibleBudgetedKronecker_hyp`.
  - Added `rhPiWitnessData_of_correctedPerronOnlyRelationCompatibleBudgetedRadiusRoute`.
- What changed:
  - The budgeted-radius atom now reduces to a smaller theorem that takes the target and anti-target finite-zero relation-compatibility predicates explicitly.
  - The new source preserves the same selected height and tolerance `T, ε`, and returns both target and anti-target radii under the required tower half-budget.
  - The corrected route can now be packaged from `PerronThresholdTowerLogHalfBudgetHyp`, paired zeta compatibility, and the relation-compatible budgeted Kronecker source.
- Remaining goal shape:
  - Prove `TargetAntiFiniteZeroRelationCompatibleBudgetedRelativelyDenseKroneckerHyp`: quantitative finite-dimensional Kronecker for the target/anti zeta phase boxes, with explicit relative-density radii bounded by
    `Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2)) / 2`
    at the same `T, ε`.
- Failed/circular route:
  - Did not claim bounds for the old unconstrained `Classical.choose` radii.
  - Did not weaken target/anti compatibility or split target and anti-target into independent heights/tolerances.
  - Did not add provider instances for the new source.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-radius route, provider cycles, reverse-comparison instances, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Passed focused validation under the coordinator singleflight rule.
- Validation command/result:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed; existing upstream linter warnings only.
- Smallest next theorem:
  - `TargetAntiFiniteZeroRelationCompatibleBudgetedRelativelyDenseKroneckerHyp`.

### 2026-04-29 Round 41: Finite-Set Budgeted Pair Kronecker Source

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `TargetAntiFiniteZeroRelationCompatibleBudgetedRelativelyDenseKroneckerHyp`.
- Facts banked:
  - Added `FiniteSetRelationCompatibleBudgetedPairKroneckerHyp`.
  - Added `targetAntiFiniteZeroRelationCompatibleBudgetedRelativelyDenseKronecker_of_finiteSetBudgetedPairKronecker_hyp`.
  - Added `rhPiWitnessData_of_correctedPerronOnlyFiniteSetBudgetedKroneckerRoute`.
- What changed:
  - The zeta-specialized relation-compatible budgeted Kronecker leaf now reduces to a generic finite-set pair theorem with an externally supplied budget.
  - The reduction preserves one finite set, the same tolerance `ε`, both target/anti relation-compatibility predicates, and the same half-budget radius bound for both returned relative-density radii.
  - The corrected route can now be packaged from `PerronThresholdTowerLogHalfBudgetHyp`, paired zeta compatibility, and this generic finite-set budgeted pair Kronecker source.
- Remaining goal shape:
  - Prove `FiniteSetRelationCompatibleBudgetedPairKroneckerHyp`: quantitative finite-dimensional Kronecker for two relation-compatible phase functions on the same finite set, with target and anti-target relative-density radii both bounded by the supplied budget `B`.
- Failed/circular route:
  - Did not use or bound the old unconstrained `Classical.choose` radii.
  - Did not split target and anti-target into independent finite sets, heights, or tolerances.
  - Did not add provider instances for the new source.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-radius route, provider cycles, reverse-comparison instances, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Passed focused validation under the coordinator singleflight rule.
- Validation command/result:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed; existing upstream linter warnings only.
- Smallest next theorem:
  - `FiniteSetRelationCompatibleBudgetedPairKroneckerHyp`.

### 2026-04-29 Round 42: Budgeted Pair Source Demoted to Chosen-Radius Budget

- Classification: `FALSE_SURFACE_DIAGNOSTIC_AND_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `FiniteSetRelationCompatibleBudgetedPairKroneckerHyp`.
- Facts banked:
  - Added `not_finiteSetRelationCompatibleBudgetedPairKroneckerHyp`.
  - Added `finiteSetRelationCompatibleKroneckerRadius`.
  - Added `finiteSetRelationCompatibleKroneckerRadius_spec`.
  - Added `TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp`.
  - Added `targetAntiFiniteZeroRelationCompatibleBudgetedRelativelyDenseKronecker_of_relationCompatibleKronecker_radiusBudget_hyp`.
  - Added `rhPiWitnessData_of_correctedPerronOnlyRelationCompatibleKroneckerRadiusBudgetRoute`.
- What changed:
  - The Round 41 generic source is now explicitly diagnosed as false as stated: with empty `S` and `B = 0`, positive radii cannot satisfy `R + 1 ≤ B`.
  - The viable route now reuses the existing honest `FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp` infrastructure and only asks for the same-height tower half-budget to dominate the actual selected target/anti Kronecker radii.
  - The corrected endpoint is packaged without depending on the false generic external-budget class.
- Remaining goal shape:
  - Prove `TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp`: for the zeta finite-zero set at the same `T, ε`, the target and anti-target radii selected from the honest relation-compatible finite-set Kronecker theorem are both bounded by
    `Real.exp (Real.exp (((1 - ε) * ((N T : ℝ) / (T + 1))) / 2)) / 2 - 1`.
- Failed/circular route:
  - The arbitrary external budget theorem cannot be proved; `B = 0` is an immediate contradiction.
  - Existing `KroneckerEquidistribution.lean` and `DirichletApproximation.lean` provide 1D, some 2D, and homogeneous/incomplete infrastructure, but the file comments still mark full finite-dimensional inhomogeneous Kronecker as missing.
  - Did not claim a separately chosen radius bounds the existing `Classical.choose` radius; the new budget class names the exact selected radii it must bound.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-radius route, provider cycles, reverse-comparison instances, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Passed focused validation under the coordinator singleflight rule.
- Validation command/result:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed; existing upstream linter warnings only.
- Smallest next theorem:
  - `TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp`.

### 2026-04-29 Round 43: One-Sided Selected Kronecker Radius Budgets

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp`.
- Facts banked:
  - Added `TargetFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp`.
  - Added `AntiTargetFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp`.
  - Added `targetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudget_of_oneSided_hyp`.
  - Added `rhPiWitnessData_of_correctedPerronOnlyOneSidedKroneckerRadiusBudgetRoute`.
- What changed:
  - The paired selected-radius half-budget atom now reduces to two one-sided atoms, one for the target chosen finite-set Kronecker radius and one for the anti-target chosen radius.
  - Both one-sided atoms preserve the same finite zeta zero set, height `T`, tolerance `ε`, and relation-compatibility payload.
  - The corrected endpoint is packaged from the one-sided leaves without adding instances or reviving the arbitrary-budget finite-set source.
- Remaining goal shape:
  - Prove `TargetFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp` and `AntiTargetFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp`: each is a direct tower half-budget bound for the actual radius selected by `FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp`.
- Failed/circular route:
  - Did not use `FiniteSetRelationCompatibleBudgetedPairKroneckerHyp`, which remains false as stated.
  - Did not claim that a separately bounded Kronecker witness controls the existing selected radius.
  - Did not split target and anti-target into independent heights or tolerances.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-radius route, provider cycles, reverse-comparison instances, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Passed focused validation under the coordinator singleflight rule.
- Validation command/result:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed; existing upstream linter warnings only.
- Smallest next theorem:
  - `TargetFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp` or `AntiTargetFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp`.

### 2026-04-29 Round 44: Target Selected Radius to Canonical Compatibility

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `TargetFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp`.
- Facts banked:
  - Added `TargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`.
  - Added `targetFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudget_of_canonicalResidual`.
  - Added `rhPiWitnessData_of_correctedPerronOnlyTargetCanonicalKroneckerRadiusBudgetRoute`.
- What changed:
  - The target-side selected-radius budget now reduces to the exact radius chosen using the canonical zeta compatibility proof supplied by `TargetFiniteZeroInhomogeneousPhaseRelationCompatibleHyp`.
  - The adapter from the canonical residual back to the current one-sided class uses proof irrelevance for the arbitrary relation-compatibility proof argument.
  - The corrected endpoint can consume this target canonical residual plus the existing anti-target one-sided selected-radius budget.
- Remaining goal shape:
  - Prove `TargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`, or attack the symmetric anti-target side with the same canonical-compatibility reduction.
- Failed/circular route:
  - Did not revive `FiniteSetRelationCompatibleBudgetedPairKroneckerHyp`, which remains false as stated.
  - Did not claim that a separately chosen bounded witness controls the selected radius.
  - Did not split target and anti-target into independent heights or tolerances.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-radius route, provider cycles, reverse-comparison instances, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Passed local focused validation under the singleflight rule.
- Validation command/result:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed; existing upstream linter warnings only in `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`.
- Smallest next theorem:
  - `TargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`.

### 2026-04-29 Round 45: Anti Selected Radius to Canonical Compatibility

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `AntiTargetFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp`.
- Facts banked:
  - Added `AntiTargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`.
  - Added `antiTargetFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudget_of_canonicalResidual`.
  - Added `rhPiWitnessData_of_correctedPerronOnlyAntiTargetCanonicalKroneckerRadiusBudgetRoute`.
  - Added `rhPiWitnessData_of_correctedPerronOnlyCanonicalKroneckerRadiusBudgetRoute`.
- What changed:
  - The anti-target selected-radius budget now reduces to the exact radius chosen using the canonical zeta compatibility proof supplied by `AntiTargetFiniteZeroInhomogeneousPhaseRelationCompatibleHyp`.
  - The adapter from the anti canonical residual back to the current one-sided class uses proof irrelevance for the arbitrary relation-compatibility proof argument.
  - The corrected endpoint can now consume both target and anti-target canonical selected-radius residuals together.
- Remaining goal shape:
  - Prove `TargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual` and `AntiTargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`: direct half-budget bounds for the actual canonical chosen finite-zero Kronecker radii.
- Failed/circular route:
  - Did not revive `FiniteSetRelationCompatibleBudgetedPairKroneckerHyp`, which remains false as stated.
  - Did not claim that a separately chosen bounded witness controls the selected radius.
  - Did not introduce provider instances or split target and anti-target into independent heights or tolerances.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-budget finite-set Kronecker, arbitrary-radius route, provider cycles, reverse-comparison instances, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Passed local focused validation under the singleflight rule.
- Validation command/result:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed; existing upstream linter warnings only.
- Smallest next theorem:
  - `TargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual` or `AntiTargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`.

### 2026-04-29 Round 46: Canonical Relation Radius to Phase Radius Residuals

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `TargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`.
  - `AntiTargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`.
- Facts banked:
  - Added `targetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual_of_phaseRadiusResidual`.
  - Added `antiTargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual_of_phaseRadiusResidual`.
- What changed:
  - The target and anti-target canonical relation-compatible selected-radius residuals now reduce to the existing target/anti chosen phase-radius canonical residual predicates.
  - The comparison unfolds the relation-compatible finite-zero provider: both routes choose the same finite-set Kronecker radius from the same canonical zeta compatibility proof.
  - This keeps the selected-radius route explicit and does not introduce a provider instance.
- Remaining goal shape:
  - Prove `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual` and `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`, or prove a genuine quantitative theorem bounding the `Classical.choose` radii returned by the relation-compatible finite-dimensional Kronecker source.
- Failed/circular route:
  - Did not revive `FiniteSetRelationCompatibleBudgetedPairKroneckerHyp`, which remains false as stated.
  - Did not use a separately chosen bounded witness to control the selected radius.
  - Did not add a reverse-comparison instance or a typeclass edge from relation-compatible residuals back into phase-radius residuals.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-budget finite-set Kronecker, arbitrary-radius route, provider cycles, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Passed local focused validation under the corrected singleflight rule.
- Validation command/result:
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed; existing upstream linter warnings only.
- Smallest next theorem:
  - `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual` or `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`.

### 2026-04-29 Round 47: Target Budgeted Projection Radius

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`.
- Facts banked:
  - Added `targetFiniteZeroBudgetedRelativelyDenseRadius`, the target radius selected directly from `TargetAntiFiniteZeroInhomogeneousPhaseBudgetedRelativelyDenseHyp`.
  - Added private `targetFiniteZeroBudgetedRelativelyDenseRadius_spec`, carrying positivity, the target hit property, and the exact tower half-budget for that selected radius.
  - Added `targetFiniteZeroInhomogeneousPhaseRelativelyDense_of_budgetedRelativelyDense_hyp`, projecting the target finite-zero relative-density provider from the paired budgeted payload.
  - Added `targetFiniteZeroBudgetedRelativelyDenseRadius_halfBudget`.
  - Added `TargetFiniteZeroPhaseRadiusBudgetedProjectionComparison`.
  - Added `targetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual_of_budgetedProjectionComparison`.
- What changed:
  - The target half-budget leaf now reduces to one exact selected-radius comparison: the target-only `Classical.choose` radius from the projected provider must be no larger than the budgeted paired payload's selected target radius.
  - The budget for the paired payload's selected target radius is proved directly from `TargetAntiFiniteZeroInhomogeneousPhaseBudgetedRelativelyDenseHyp`.
  - This stays on the canonical chosen-radius route and does not use arbitrary-budget finite-set Kronecker.
- Remaining goal shape:
  - `TargetFiniteZeroPhaseRadiusBudgetedProjectionComparison`: prove the projected target-only chooser is controlled by the explicit budgeted target radius, or refactor the public target radius to expose this selected radius definitionally.
  - Symmetric anti-target work remains analogous if the target comparison route is accepted.
- Failed/circular route:
  - Directly unfolding `targetFiniteZeroInhomogeneousPhaseRadius` for the projected provider did not close `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`; Lean left an opaque `Classical.choose` goal for the target-only witness.
  - Did not claim that the budgeted witness controls the target-only chooser without the named comparison predicate.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-budget finite-set Kronecker, arbitrary-radius route, provider cycles, reverse-comparison instances, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Passed local focused validation under the corrected singleflight rule.
- Validation command/result:
  - `git diff --check`
  - Result: passed.
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
  - Result: passed.
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed; existing upstream linter warnings only.
- Smallest next theorem:
  - `TargetFiniteZeroPhaseRadiusBudgetedProjectionComparison`.

### 2026-04-29 Round 48: Anti Budgeted Projection Radius

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `TargetFiniteZeroPhaseRadiusBudgetedProjectionComparison`.
  - `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`.
- Facts banked:
  - Added `antiTargetFiniteZeroBudgetedRelativelyDenseRadius`, the anti-target radius selected directly from the second component of `TargetAntiFiniteZeroInhomogeneousPhaseBudgetedRelativelyDenseHyp`.
  - Added private `antiTargetFiniteZeroBudgetedRelativelyDenseRadius_spec`, carrying positivity, the anti-target hit property, and the exact tower half-budget for that selected radius.
  - Added `antiTargetFiniteZeroInhomogeneousPhaseRelativelyDense_of_budgetedRelativelyDense_hyp`, projecting the anti-target finite-zero relative-density provider from the paired budgeted payload.
  - Added `antiTargetFiniteZeroBudgetedRelativelyDenseRadius_halfBudget`.
  - Added `AntiTargetFiniteZeroPhaseRadiusBudgetedProjectionComparison`.
  - Added `antiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual_of_budgetedProjectionComparison`.
- What changed:
  - The anti-target half-budget leaf now has the same exact reduction as the target side: it follows once the anti-target-only `Classical.choose` radius from the projected provider is controlled by the budgeted paired payload's selected anti-target radius.
  - The anti-target selected radius from the paired budgeted payload is proved to satisfy the tower half-budget directly.
  - The target comparison was tested by making the projection transparent, but Lean still left an opaque `Classical.choose` goal; that attempted direct theorem was not kept.
- Remaining goal shape:
  - `TargetFiniteZeroPhaseRadiusBudgetedProjectionComparison`.
  - `AntiTargetFiniteZeroPhaseRadiusBudgetedProjectionComparison`.
  - Equivalently, refactor the public target/anti radius definitions or provider interfaces so the canonical route uses the explicit budgeted selected radii rather than separately chosen projected witnesses.
- Failed/circular route:
  - Did not prove `TargetFiniteZeroPhaseRadiusBudgetedProjectionComparison`; direct unfolding still requires unproved control of `Classical.choose`.
  - Did not claim a separately exhibited bounded witness controls the canonical chosen radius.
  - Did not revive arbitrary-budget finite-set Kronecker.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-budget finite-set Kronecker, arbitrary-radius route, provider cycles, reverse-comparison instances, or unproved `Classical.choose` control was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Passed local focused validation under the corrected singleflight rule.
- Validation command/result:
  - `git diff --check`
  - Result: passed.
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed; existing upstream linter warnings only.
- Smallest next theorem:
  - `TargetFiniteZeroPhaseRadiusBudgetedProjectionComparison` or `AntiTargetFiniteZeroPhaseRadiusBudgetedProjectionComparison`; if these remain blocked by choice opacity, the smallest interface change is to expose canonical budgeted target/anti radii directly in the phase-radius route.

### 2026-04-29 Round 49: Projection Choice-Spec Diagnostic

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `TargetFiniteZeroPhaseRadiusBudgetedProjectionComparison`.
  - `AntiTargetFiniteZeroPhaseRadiusBudgetedProjectionComparison`.
- Facts banked:
  - Added `TargetFiniteZeroPhaseRadiusBudgetedProjectionChoiceSpec`.
  - Added `targetFiniteZeroPhaseRadiusBudgetedProjectionComparison_of_choiceSpec`.
  - Added `targetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual_of_budgetedProjectionChoiceSpec`.
  - Added `AntiTargetFiniteZeroPhaseRadiusBudgetedProjectionChoiceSpec`.
  - Added `antiTargetFiniteZeroPhaseRadiusBudgetedProjectionComparison_of_choiceSpec`.
  - Added `antiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual_of_budgetedProjectionChoiceSpec`.
- What changed:
  - The exact missing spec is now named for both target and anti-target: the canonical projected phase-radius chooser must be identified with the explicit budgeted radius selected from the paired payload.
  - Once that chooser identity is supplied, the projection comparison and the corresponding canonical residual follow from the already-proved budgeted-radius half-budget theorem.
  - This avoids pretending that the budgeted witness controls an arbitrary `Classical.choose` result.
- Failed route:
  - Tried to make the target projection transparent enough for `Classical.choose` to reduce to the explicit budgeted target radius. Lean still left the same opaque goal:
    `Classical.choose ⋯ ≤ targetFiniteZeroBudgetedRelativelyDenseRadius T ε hT4 hεpos hεlt`.
  - The direct comparison is therefore not derivable from the existing relative-density specs alone in the current interface.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-budget finite-set Kronecker, arbitrary-radius route, provider cycles, reverse-comparison instances, or choice-control assumption was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Passed local focused validation under the corrected singleflight rule.
- Validation command/result:
  - `git diff --check`
  - Result: passed.
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed; existing upstream linter warnings only.
- Smallest next theorem:
  - Replace the projected-chooser route with an interface that makes the canonical phase-radius route consume explicit budgeted target/anti radii, or prove the new exact chooser identity specs:
    `TargetFiniteZeroPhaseRadiusBudgetedProjectionChoiceSpec` and `AntiTargetFiniteZeroPhaseRadiusBudgetedProjectionChoiceSpec`.

### 2026-04-29 Round 50: Explicit Budgeted Radius Endpoint

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `TargetFiniteZeroPhaseRadiusBudgetedProjectionChoiceSpec`.
  - `AntiTargetFiniteZeroPhaseRadiusBudgetedProjectionChoiceSpec`.
- Facts banked:
  - Added `targetAntiPhaseFitAbovePerronThresholdPerron_of_logHalfBudget_budgetedRelativelyDense_hyp`.
  - Added `exactSeedAboveThreshold_perron_of_logHalfBudget_budgetedRelativelyDense_hyp`.
- What changed:
  - The corrected exact-seed route can now consume `PerronThresholdTowerLogHalfBudgetHyp` plus `TargetAntiFiniteZeroInhomogeneousPhaseBudgetedRelativelyDenseHyp` directly.
  - This bypasses the projected canonical phase-radius chooser entirely: the lower realized-radius theorem uses the explicit target and anti-target radii returned by the budgeted paired payload.
  - No `TargetFiniteZeroPhaseRadiusBudgetedProjectionComparison`, `AntiTargetFiniteZeroPhaseRadiusBudgetedProjectionComparison`, or choice-spec equality is needed for this endpoint.
- Failed route:
  - The choice-spec route remains blocked by opacity of `Classical.choose`; no equality or inequality between the projected chosen radius and the explicitly budgeted radius follows from the existing specs alone.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-budget finite-set Kronecker, arbitrary-radius route, provider cycles, reverse-comparison instances, or choice-control assumption was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Passed local focused validation under the corrected singleflight rule.
- Validation command/result:
  - `git diff --check`
  - Result: passed.
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed; existing upstream linter warnings only.
- Smallest next theorem:
  - Close or further reduce `PerronThresholdTowerLogHalfBudgetHyp`, or source `TargetAntiFiniteZeroInhomogeneousPhaseBudgetedRelativelyDenseHyp` from the relation-compatible finite-zero/Kronecker payloads already named in the route.

### 2026-04-29 Round 51: Relation-Compatible Budgeted Radius Endpoint

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `TargetAntiFiniteZeroInhomogeneousPhaseBudgetedRelativelyDenseHyp`.
- Facts banked:
  - Added `targetAntiPhaseFitAbovePerronThresholdPerron_of_logHalfBudget_relationCompatibleBudgetedKronecker_hyp`.
  - Added `exactSeedAboveThreshold_perron_of_logHalfBudget_relationCompatibleBudgetedKronecker_hyp`.
  - Added `exactSeedAboveThreshold_perron_of_logHalfBudget_relationCompatibleKroneckerRadiusBudget_hyp`.
- What changed:
  - The explicit-radius exact-seed endpoint can now be sourced from paired zeta relation compatibility plus `TargetAntiFiniteZeroRelationCompatibleBudgetedRelativelyDenseKroneckerHyp`.
  - A further endpoint packages the existing finite-set relation-compatible Kronecker source plus `TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp`.
  - This keeps the route away from projected `Classical.choose` radii and away from arbitrary-budget finite-set Kronecker.
- Remaining goal shape:
  - Prove `PerronThresholdTowerLogHalfBudgetHyp`.
  - Prove or further reduce `TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp`, the same-height quantitative bound on the actual finite-set relation-compatible Kronecker radii.
- Failed/circular route:
  - Did not use `FiniteSetRelationCompatibleBudgetedPairKroneckerHyp`, which remains false in the arbitrary-budget form.
  - Did not add provider instances or a reverse edge from exact-seed packaging back into the budget leaves.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-budget finite-set Kronecker, arbitrary-radius route, provider cycles, reverse-comparison instances, or choice-control assumption was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Passed local focused validation under the corrected singleflight rule.
- Validation command/result:
  - `git diff --check`
  - Result: passed.
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed; existing upstream linter warnings only.
- Smallest next theorem:
  - `PerronThresholdTowerLogHalfBudgetHyp` or `TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp`.

### 2026-04-29 Round 52: Canonical Radius Residual Reduction

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp`.
- Facts banked:
  - Added `targetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudget_of_canonicalResiduals`.
  - Added `exactSeedAboveThreshold_perron_of_logHalfBudget_relationCompatibleCanonicalRadiusResiduals_hyp`.
- What changed:
  - The paired selected-radius Kronecker budget leaf now reduces directly to the two one-sided canonical relation-compatible selected-radius residuals:
    `TargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual` and
    `AntiTargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`.
  - The corrected Perron-only exact-seed endpoint can now consume those canonical residuals through the explicit-radius relation-compatible route, without using projected `Classical.choose` radius comparisons.
- Remaining goal shape:
  - Prove `PerronThresholdTowerLogHalfBudgetHyp`.
  - Prove the actual one-sided canonical selected-radius residuals, or reduce them further to a quantitative finite-zero/Kronecker theorem that bounds the selected relation-compatible radius at the same `T, ε`.
- Failed/circular route:
  - Did not use `FiniteSetRelationCompatibleBudgetedPairKroneckerHyp`; the arbitrary-budget finite-set theorem remains demoted by the empty-set/zero-budget counterexample.
  - Did not add provider instances or a reverse edge from exact-seed packaging back into the selected-radius residuals.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-budget finite-set Kronecker, arbitrary-radius route, provider cycles, reverse-comparison instances, or choice-control assumption was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Passed local focused validation under the corrected singleflight rule.
- Validation command/result:
  - `git diff --check`
  - Result: passed.
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed; existing upstream linter warnings only.
- Smallest next theorem:
  - `PerronThresholdTowerLogHalfBudgetHyp`, `TargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`, or `AntiTargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`.

### 2026-04-29 Round 53: Canonical Perron Residual Endpoint

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `PerronThresholdTowerLogHalfBudgetHyp`.
- Facts banked:
  - Added `perronThresholdTowerLogHalfBudget_of_canonicalMajorantResidual`.
  - Added `exactSeedAboveThreshold_perron_of_canonicalPerronAndRelationCompatibleRadiusResiduals_hyp`.
- What changed:
  - `PerronThresholdTowerLogHalfBudgetHyp` now has a direct non-instance reduction from
    `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`.
  - The corrected explicit-radius relation-compatible exact-seed endpoint can now consume exactly the three live canonical residual atoms:
    `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`,
    `TargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`, and
    `AntiTargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`.
  - This keeps the route on the same selected `T, ε` and avoids adding provider edges through the canonical/growth graph.
- Remaining goal shape:
  - Prove `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`, or prove the already-named selected-threshold residual that implies it.
  - Prove the target and anti-target relation-compatible canonical selected-radius residuals, or reduce them further to quantitative same-height finite-zero/Kronecker radius estimates.
- Failed/circular route:
  - Did not use projected `Classical.choose` equality for the budgeted phase-radius route.
  - Did not use `FiniteSetRelationCompatibleBudgetedPairKroneckerHyp`; arbitrary-budget finite-set Kronecker remains demoted.
  - Did not add provider instances or a reverse edge from exact-seed packaging back into the residual leaves.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-budget finite-set Kronecker, arbitrary-radius route, provider cycles, reverse-comparison instances, or choice-control assumption was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Passed local focused validation under the corrected singleflight rule.
- Validation command/result:
  - `git diff --check`
  - Result: passed.
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed; existing upstream linter warnings only.
- Smallest next theorem:
  - `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`,
    `TargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`, or
    `AntiTargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`.

### 2026-04-29 Round 54: Phase-Radius Residual Endpoint

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `TargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`.
  - `AntiTargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`.
- Facts banked:
  - Added `targetAntiFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResiduals_of_phaseRadiusResiduals`.
  - Added `exactSeedAboveThreshold_perron_of_canonicalPerronAndPhaseRadiusResiduals_hyp`.
- What changed:
  - The two relation-compatible selected Kronecker-radius residuals are now packaged directly from the two one-sided finite-zero phase-radius canonical residuals.
  - The corrected explicit-radius exact-seed route can now consume:
    `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`,
    `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`, and
    `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`.
  - This keeps the route on the canonical selected radii supplied by the relation-compatible finite-set Kronecker provider and avoids any projected budgeted-chooser equality.
- Remaining goal shape:
  - Prove `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`, or prove the selected-threshold residual that implies it.
  - Prove the direct one-sided phase-radius canonical residuals for the actual chosen target and anti-target finite-zero radii.
- Failed/circular route:
  - Did not use projected `Classical.choose` equality for the budgeted phase-radius route.
  - Did not use `FiniteSetRelationCompatibleBudgetedPairKroneckerHyp`; arbitrary-budget finite-set Kronecker remains demoted.
  - Did not add provider instances or a reverse edge from exact-seed packaging back into the residual leaves.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-budget finite-set Kronecker, arbitrary-radius route, provider cycles, reverse-comparison instances, or choice-control assumption was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Passed local focused validation under the corrected singleflight rule.
- Validation command/result:
  - `git diff --check`
  - Result: passed.
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed; existing upstream linter warnings only.
- Smallest next theorem:
  - `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`,
    `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`, or
    `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`.

### 2026-04-29 Round 55: Paired Phase-Radius Growth Reduction

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`.
  - `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`.
- Facts banked:
  - Added `targetAntiFiniteZeroPhaseRadiusHalfBudgetCanonicalResiduals_of_pairedGrowth_hyp`.
  - Added `exactSeedAboveThreshold_perron_of_canonicalPerronAndPairedPhaseRadiusGrowth_hyp`.
- What changed:
  - The target and anti-target phase-radius canonical residuals are now packaged together as projections of the paired same-height max-radius growth leaf.
  - The corrected explicit-radius exact-seed route can now consume:
    `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual` and
    `TargetAntiFiniteZeroPhaseRadiusHalfBudgetGrowthHyp`, while still passing through the relation-compatible finite-zero provider.
  - This names the smaller phase-side quantitative atom without using projected budgeted-chooser equality.
- Remaining goal shape:
  - Prove `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`, or prove the selected-threshold residual that implies it.
  - Prove `TargetAntiFiniteZeroPhaseRadiusHalfBudgetGrowthHyp`, the same-height quantitative bound for the actual paired target/anti finite-zero radii.
- Failed/circular route:
  - Did not use projected `Classical.choose` equality for the budgeted phase-radius route.
  - Did not use `FiniteSetRelationCompatibleBudgetedPairKroneckerHyp`; arbitrary-budget finite-set Kronecker remains demoted.
  - Did not add provider instances or a reverse edge from exact-seed packaging back into the residual leaves.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-budget finite-set Kronecker, arbitrary-radius route, provider cycles, reverse-comparison instances, or choice-control assumption was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation status:
  - Passed local focused validation under the corrected singleflight rule.
- Validation command/result:
  - `git diff --check`
  - Result: passed.
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed; existing upstream linter warnings only.
- Smallest next theorem:
  - `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual` or
    `TargetAntiFiniteZeroPhaseRadiusHalfBudgetGrowthHyp`.

### 2026-04-29 Round 56: Relation-Compatible Radius Residuals to Phase Growth

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `TargetAntiFiniteZeroPhaseRadiusHalfBudgetGrowthHyp`.
- Facts banked:
  - Added `targetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual_of_relationCompatibleCanonicalKroneckerRadiusResidual`.
  - Added `antiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual_of_relationCompatibleCanonicalKroneckerRadiusResidual`.
  - Added `targetAntiFiniteZeroPhaseRadiusHalfBudgetGrowth_of_relationCompatibleCanonicalRadiusResiduals`.
- What changed:
  - Proved the inverse definitional bridge from the target/anti relation-compatible canonical Kronecker-radius residuals back to the target/anti phase-radius canonical residuals under the relation-compatible finite-zero provider.
  - Reduced the paired same-height phase-radius growth leaf to the two actual selected finite-set Kronecker radius residuals.
  - Kept the reduction non-instance-only, so it does not add a provider cycle or a reverse exact-seed edge.
- Remaining goal shape:
  - Prove `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`, or prove the selected-threshold residual that implies it.
  - Prove the two direct selected finite-set Kronecker radius bounds:
    `TargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual` and
    `AntiTargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`.
- Failed/circular route:
  - Did not use projected budgeted `Classical.choose` equality.
  - Did not revive `FiniteSetRelationCompatibleBudgetedPairKroneckerHyp`; arbitrary-budget finite-set Kronecker remains false/demoted.
  - Did not add provider instances for the new bridge.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-budget finite-set Kronecker, arbitrary-radius route, opaque chooser equality, provider cycles, or broad provider was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation command/result:
  - `git diff --check`
  - Result: passed.
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed under the corrected singleflight lock; existing upstream linter warnings only.
- Smallest next theorem:
  - `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`, or
    `TargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual` /
    `AntiTargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`.

### 2026-04-29 Round 57: Chosen Radius Budget Specialization

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `TargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`.
  - `AntiTargetFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResidual`.
- Facts banked:
  - Added `targetAntiFiniteZeroRelationCompatibleCanonicalKroneckerRadiusHalfBudgetResiduals_of_chosenKroneckerRadiusHalfBudget_hyp`.
  - Added `exactSeedAboveThreshold_perron_of_canonicalPerronAndChosenKroneckerRadiusBudget_hyp`.
- What changed:
  - The paired selected-radius budget class now directly specializes to the two canonical target/anti relation-compatible selected-radius residuals using the paired zeta compatibility proof.
  - The exact-seed route now has a non-instance endpoint from:
    `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual` and
    `TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp`.
  - This avoids the phase-growth/canonical-radius loop and does not use projected budgeted chooser equality.
- Remaining goal shape:
  - Prove `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`, or prove the selected-threshold residual that implies it.
  - Prove `TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp`, i.e. the same-height half-budget bound for the actual target and anti-target finite-set relation-compatible Kronecker radii.
- Failed/circular route:
  - Did not cycle through `TargetAntiFiniteZeroPhaseRadiusHalfBudgetGrowthHyp` to recover the same canonical residuals.
  - Did not use projected budgeted `Classical.choose` equality.
  - Did not revive `FiniteSetRelationCompatibleBudgetedPairKroneckerHyp`; arbitrary-budget finite-set Kronecker remains false/demoted.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-budget finite-set Kronecker, arbitrary-radius route, opaque chooser equality, provider cycles, or broad provider was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation command/result:
  - `git diff --check`
  - Result: passed.
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed under the corrected singleflight lock; existing upstream linter warnings only.
- Smallest next theorem:
  - `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`, or
    `TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp`.

### 2026-04-29 Round 58: Chosen Radius Max-Budget Residual

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudgetHyp`.
- Facts banked:
  - Added `TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusMaxHalfBudgetResidual`.
  - Added `targetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusHalfBudget_of_maxResidual`.
  - Added `exactSeedAboveThreshold_perron_of_canonicalPerronAndChosenKroneckerRadiusMaxBudget_hyp`.
- What changed:
  - Reduced the paired chosen-radius budget class to a single same-height max-radius inequality for the actual target/anti relation-compatible finite-set Kronecker radii.
  - Added an exact-seed endpoint consuming `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual` plus the new max-radius residual.
  - This is not a return to the canonical residual loop; the finite-zero atom is now one explicit max bound over the two chosen radii for arbitrary compatible target/anti phase data.
- Remaining goal shape:
  - Prove `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`, or prove the selected-threshold residual that implies it.
  - Prove `TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusMaxHalfBudgetResidual`, the direct same-height tower half-budget bound for the larger of the actual selected target/anti relation-compatible Kronecker radii.
- Failed/circular route:
  - Did not use projected budgeted `Classical.choose` equality.
  - Did not revive `FiniteSetRelationCompatibleBudgetedPairKroneckerHyp`; arbitrary-budget finite-set Kronecker remains false/demoted.
  - Did not cycle through phase-growth or canonical one-sided residuals to recover the same paired chosen-radius budget.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`, `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-budget finite-set Kronecker, arbitrary-radius route, opaque chooser equality, provider cycles, or broad provider was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation command/result:
  - `git diff --check`
  - Result: passed.
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed under the corrected singleflight lock; existing upstream linter warnings only.
- Smallest next theorem:
  - `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`, or
    `TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusMaxHalfBudgetResidual`.

### 2026-04-29 Round 59: Chooser-Free Budgeted Endpoint

- Classification: `ROUTE_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusMaxHalfBudgetResidual`.
- Facts banked:
  - Added `exactSeedAboveThreshold_perron_of_canonicalPerronAndRelationCompatibleBudgetedKronecker_hyp`.
- What changed:
  - Added a non-instance exact-seed endpoint from
    `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual` plus
    `TargetAntiFiniteZeroRelationCompatibleBudgetedRelativelyDenseKroneckerHyp`.
  - This gives the corrected Perron-only route a chooser-free finite-zero option:
    the target/anti radii are returned already under the same-height half-budget,
    so no bound on `finiteSetRelationCompatibleKroneckerRadius` or opaque
    `Classical.choose` projection equality is needed.
- Remaining goal shape:
  - Perron side: prove `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`
    or the selected-threshold residual that implies it.
  - Finite-zero side, chooser-free route:
    prove `TargetAntiFiniteZeroRelationCompatibleBudgetedRelativelyDenseKroneckerHyp`.
  - Finite-zero side, chosen-radius route:
    `TargetAntiFiniteZeroRelationCompatibleChosenKroneckerRadiusMaxHalfBudgetResidual`
    remains open and should not be forced unless a real selected-radius bound is
    available.
- Failed/circular route:
  - Did not prove or assume control of the `Classical.choose` radius selected by
    `finiteSetRelationCompatibleKroneckerRadius`.
  - Did not revive `FiniteSetRelationCompatibleBudgetedPairKroneckerHyp`; the
    arbitrary-budget finite-set theorem remains false/demoted.
  - Did not cycle through one-sided canonical phase-radius residuals to recover
    the same paired chosen-radius budget.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-budget finite-set Kronecker,
    arbitrary-radius route, opaque chooser equality, provider cycles, or broad
    provider was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation command/result:
  - `git diff --check`
  - Result: passed.
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed under the corrected singleflight lock; existing upstream linter warnings only.
- Smallest next theorem:
  - `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`, or
    `TargetAntiFiniteZeroRelationCompatibleBudgetedRelativelyDenseKroneckerHyp`
    for the chooser-free route.

### 2026-04-29 Round 60: Same-Radius Budgeted Kronecker Residual

- Classification: `RESIDUAL_REDUCTION`.
- Exact theorem/file attacked:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `TargetAntiFiniteZeroRelationCompatibleBudgetedRelativelyDenseKroneckerHyp`.
- Facts banked:
  - Added `TargetAntiFiniteZeroRelationCompatibleBudgetedSameRadiusKroneckerResidual`.
  - Added `targetAntiFiniteZeroRelationCompatibleBudgetedRelativelyDenseKronecker_of_sameRadiusResidual`.
  - Added `exactSeedAboveThreshold_perron_of_canonicalPerronAndSameRadiusBudgetedKroneckerResidual`.
- What changed:
  - Reduced the chooser-free finite-zero budgeted route to a single same-radius
    finite-dimensional Kronecker residual.
  - The new residual preserves the same `T, ε`, the same finite zeta zero set,
    and the target/anti relation-compatibility inputs, but asks for one explicit
    radius `R` that works for both phase boxes and satisfies the tower
    half-budget bound.
  - This is strictly away from the chosen-radius route: it does not reference
    `finiteSetRelationCompatibleKroneckerRadius` or require any
    `Classical.choose` projection comparison.
- Remaining goal shape:
  - Perron side: prove `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`
    or the selected-threshold residual that implies it.
  - Finite-zero side: prove
    `TargetAntiFiniteZeroRelationCompatibleBudgetedSameRadiusKroneckerResidual`,
    an explicit same-radius relation-compatible finite-dimensional Kronecker
    theorem at the tower half-budget scale.
- Failed/circular route:
  - Did not use the chosen-radius residuals or one-sided canonical phase-radius
    residuals to rebuild the same class.
  - Did not revive `FiniteSetRelationCompatibleBudgetedPairKroneckerHyp`; the
    arbitrary external-budget theorem remains false by the empty-set/zero-budget
    diagnostic.
  - Did not introduce a provider instance for the new residual-to-class theorem.
- Guardrails:
  - No use of `TruncatedExplicitFormulaPiHyp`, `TruncatedExplicitFormulaPiHyp.pi_approx`,
    `PerronPiApproxCompatibilityHyp`, `pi_explicit_formula_from_perron`, or
    `truncatedPiHyp_contradicts_rh`.
  - No axioms/sorries, statement weakening, arbitrary-budget finite-set Kronecker,
    arbitrary-radius route, opaque chooser equality, provider cycles, or broad
    provider was introduced.
- Files changed:
  - `Littlewood/Aristotle/Standalone/PerronExplicitFormulaProvider.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_pi_phase.md`
- Validation command/result:
  - `git diff --check`
  - Result: passed.
  - `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute`
  - Result: passed under the corrected singleflight lock; existing upstream linter warnings only.
- Smallest next theorem:
  - `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`, or
    `TargetAntiFiniteZeroRelationCompatibleBudgetedSameRadiusKroneckerResidual`.
