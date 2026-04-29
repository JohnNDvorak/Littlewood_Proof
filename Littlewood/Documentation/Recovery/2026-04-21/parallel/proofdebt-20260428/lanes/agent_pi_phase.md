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
