# Agent RS/Gabcke Ledger

Branch: `proofdebt/20260428-rs-gabcke`

Worktree: `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260428/rs-gabcke`

## Ownership

- Writable code: RS, Siegel, Gabcke, Hardy first-moment bridge, and related
  coefficient files.
- Writable ledger: this file only.
- Coordinator-owned shared files are read-only.

## Live Targets

1. Reduce or prove `SiegelSaddleExpansionHyp`.
2. Prove the explicit Gabcke adjacent coefficient identity, nonnegativity, and
   antitonicity atoms.
3. Keep legacy `GabckePhaseCouplingHyp` as a wrapper, not the analytic target.

## Guardrails

- Do not edit `AtkinsonFormula.lean`.
- Do not introduce broad analytic axioms or provider shortcuts.
- Do not edit public main files.
- Do not run a full build.

## Requested Checks

- focused build for touched RS/Gabcke module(s)
- strict public import probes for `Littlewood.Main.LittlewoodPsi` and
  `Littlewood.Main.LittlewoodPi`

## Session Log

### 2026-04-28 Launch

- Baseline: `acdc136`.
- Initial target: `SiegelSaddleExpansionHyp` / Gabcke adjacent atoms.
- Coordinator action: initial agent dispatched; Aristotle sidecar planned.

### 2026-04-28 Aristotle Harvest Integration

- Job: `381b8764-543a-4024-a84f-9a9f91be9eba`.
- Classification: `AUDIT_REDUCTION`.
- Target audited:
  `SiegelSaddleExpansionHyp`, `GabckePhaseCouplingHyp`, and the Hardy
  first-moment bridge.
- Result:
  downstream RS/Gabcke wiring is already proved. The open work is the analytic
  content of `SiegelSaddleExpansionHyp`.
- Key reduction:
  `GabckePhaseCouplingHyp` only needs the signed Satz 4 fields, equivalent to
  nonnegativity and adjacent antitonicity of the normalized signed profile.
  The Satz 1 weighted-profile bound is needed for the full Siegel saddle
  expansion, not for the phase-coupling wrapper alone.
- Failed route:
  exact k-independence is mathematically false; use adjacent antitonicity.
- Current lane guidance:
  continue the standard Gabcke normalization bridge: define the correctly
  phase/parameter-normalized `stdLead` and prove
  `StandardGabckeLocalLeadingNormalizationProp stdLead`.

### 2026-04-28 Round 1: Siegel class split

- Classification: `CONDITIONAL_REDUCTION`.
- Theorem/file attacked:
  `SiegelSaddleExpansionHyp` in
  `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean` and its
  Gabcke adjacent reduction surface in
  `Littlewood/Aristotle/Standalone/GabckePhaseCouplingInfra.lean`.
- Proof facts banked:
  - Added `SiegelWeightedProfileBoundProp`, isolating the Gabcke Satz 1
    weighted-profile field from the signed adjacent Satz 4 fields.
  - Added
    `siegelWeightedProfileBoundProp_of_siegelSaddleExpansionHyp`, the direct
    projection from the current class.
  - Added
    `siegelSaddleExpansionHyp_of_weightedProfile_and_normalizedCoefficient`,
    rebuilding the full class from `SiegelWeightedProfileBoundProp` and the
    already-recovered `GabckeNormalizedCoefficientProp`.
  - Added
    `siegelSaddleExpansionHyp_iff_weightedProfile_and_normalizedCoefficient`,
    making the primary class equivalent to the weighted-profile Satz 1 atom
    plus the normalized adjacent Gabcke coefficient atom.
- Failed routes that should not be retried:
  none in this round. I did not instantiate the explicit coefficient candidate
  with `normalizedSignedSPR` itself, and did not use the legacy
  `GabckeBlockIndependence` profile route.
- Files changed:
  - `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`
  - `Littlewood/Aristotle/Standalone/GabckePhaseCouplingInfra.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - `git diff --check`: passed.
  - No Lean/Lake/full-build commands were run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp`
  - `lake build Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra`
  - `lake build Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp`
  - `lake build Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
  - `printf 'import Littlewood.Main.LittlewoodPsi\n' | lake env lean --stdin`
  - `printf 'import Littlewood.Main.LittlewoodPi\n' | lake env lean --stdin`
- Smallest next theorem:
  prove `SiegelWeightedProfileBoundProp` from the actual Gabcke/Siegel
  first-coefficient formula, and independently instantiate
  `GabckeNormalizedCoefficientProp` from the explicit signed adjacent
  coefficient identity/nonnegativity/antitonicity atoms.
- Coordinator action requested:
  run the requested serialized validation commands.

### 2026-04-28 Round 2: weighted profile to coordinate remainder

- Classification: `CONDITIONAL_REDUCTION`.
- Theorem/file attacked:
  `SiegelWeightedProfileBoundProp` in
  `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`.
- Proof facts banked:
  - Added `SiegelCoordinateRemainderBoundProp`, the coordinate pointwise form
    of the Gabcke Satz 1 absolute atom:
    `|saddlePointRemainder k (blockCoord k p)| <=
      fresnelC1Bound * (blockCoord k p)^(-(1:Real)/2)`.
  - Added
    `siegelCoordinateRemainderBoundProp_of_weightedProfile`.
  - Added
    `siegelWeightedProfileBoundProp_of_coordinateRemainder`.
  - Added
    `siegelWeightedProfileBoundProp_iff_coordinateRemainder`.
  - Reused this public equivalence in the existing private
    `saddle_remainder_fresnel_bound_on_coords` helper.
- Failed routes that should not be retried:
  none in this round. I did not use the signed coefficient surface or the
  legacy block-independence/profile route.
- Files changed:
  - `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - `git diff --check`: passed.
  - No Lean/Lake/full-build commands were run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp`
  - `lake build Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra`
  - `lake build Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp`
  - `lake build Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
  - `printf 'import Littlewood.Main.LittlewoodPsi\n' | lake env lean --stdin`
  - `printf 'import Littlewood.Main.LittlewoodPi\n' | lake env lean --stdin`
- Smallest next theorem:
  prove `SiegelCoordinateRemainderBoundProp` from the actual steepest-descent
  coefficient calculation. This is now the absolute Satz 1 target without the
  extra weighted-profile algebra.
- Coordinator action requested:
  run the requested serialized validation commands.

### 2026-04-28 Round 3: coordinate remainder to stationary-phase error

- Classification: `CONDITIONAL_REDUCTION`.
- Theorem/file attacked:
  `SiegelCoordinateRemainderBoundProp` in
  `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`.
- Proof facts banked:
  - Added `SiegelCoordinateStationaryPhaseErrorProp`, the exact block-coordinate
    stationary-phase error estimate before dividing by the saddle amplitude:
    at `t = blockCoord k p`, the raw `ErrorTerm` error after subtracting
    `(-1)^k * (2*pi/t)^(1/4) * rsPsi p` is bounded by the same amplitude times
    `fresnelC1Bound * t^(-(1:Real)/2)`.
  - Added
    `siegelCoordinateRemainderBoundProp_of_stationaryPhaseError`, using
    `blockParam_blockCoord` and positivity of the saddle amplitude to divide
    the raw stationary-phase error estimate and recover
    `SiegelCoordinateRemainderBoundProp`.
  - This places the remaining analytic content at the local Taylor/remainder
    estimate for `ErrorTerm (blockCoord k p)`, with no weighted-profile or
    signed-adjacent coefficient wrapper.
- Failed routes that should not be retried:
  none in this round. I did not route through `GabckePhaseCouplingHyp`, did not
  strengthen `GabckeNormalizedCoefficientProp`, and did not introduce a broad
  analytic axiom.
- Files changed:
  - `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - `git diff --check`: passed.
  - No Lean/Lake/full-build commands were run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp`
  - `lake build Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra`
  - `lake build Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp`
  - `lake build Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
  - `printf 'import Littlewood.Main.LittlewoodPsi\n' | lake env lean --stdin`
  - `printf 'import Littlewood.Main.LittlewoodPi\n' | lake env lean --stdin`
- Smallest next theorem:
  prove `SiegelCoordinateStationaryPhaseErrorProp` from the actual local
  stationary-phase Taylor expansion for `ErrorTerm` in block coordinates,
  including the exact leading term and the `fresnelC1Bound` first-remainder
  coefficient.
- Coordinator action requested:
  run the requested serialized validation commands.

### 2026-04-28 Round 4: stationary-phase error to coefficient atoms

- Classification: `CONDITIONAL_REDUCTION`.
- Theorem/file attacked:
  `SiegelCoordinateStationaryPhaseErrorProp` in
  `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`.
- Proof facts banked:
  - Added `SiegelStationaryPhaseCoefficientIdentityProp C`, the exact local
    Taylor identity in block coordinates:
    the raw defect
    `ErrorTerm (blockCoord k p) -
      (-1)^k * (2*pi / blockCoord k p)^(1/4) * rsPsi p`
    is the saddle amplitude times `C k p * (blockCoord k p)^(-(1:Real)/2)`.
  - Added `SiegelStationaryPhaseCoefficientBoundProp C`, the uniform
    coefficient estimate `|C k p| <= fresnelC1Bound` on `p in Ico 0 1`.
  - Added
    `siegelCoordinateStationaryPhaseErrorProp_of_coefficientAtoms`, proving
    that the identity atom plus the coefficient-bound atom imply
    `SiegelCoordinateStationaryPhaseErrorProp`.
  - This reduces the live Satz 1 source from one opaque error inequality to
    two local Taylor/coefficient facts with exact coordinates and scale.
- Failed routes that should not be retried:
  none in this round. I did not define `C` as the defect quotient, so this is
  not a circular reformulation; the remaining identity must come from the
  actual Siegel/Gabcke steepest-descent expansion.
- Files changed:
  - `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - `git diff --check`: passed.
  - No Lean/Lake/full-build commands were run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp`
  - `lake build Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra`
  - `lake build Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp`
  - `lake build Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
  - `printf 'import Littlewood.Main.LittlewoodPsi\n' | lake env lean --stdin`
  - `printf 'import Littlewood.Main.LittlewoodPi\n' | lake env lean --stdin`
- Smallest next theorem:
  instantiate a concrete `C` from Gabcke's local Taylor coefficient formula,
  then prove `SiegelStationaryPhaseCoefficientIdentityProp C` from the contour
  expansion and `SiegelStationaryPhaseCoefficientBoundProp C` from the
  first-remainder coefficient bound.
- Coordinator action requested:
  run the requested serialized validation commands.

### 2026-04-28 Round 5: concrete stationary coefficient source obstruction

- Classification: `FAILED_ROUTE`.
- Theorem/file attacked:
  `SiegelStationaryPhaseCoefficientIdentityProp C` and
  `SiegelStationaryPhaseCoefficientBoundProp C` in
  `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`.
- Static facts banked:
  - The current owned Lean files contain the block-coordinate contour
    normalizations `siegelTau`, `gabckeZ`, `gabckeQ`, `siegelU`, the shifted
    contour factor, and several coefficient-scale inequalities, but no formal
    Tabelle-1/local Taylor coefficient expression that can be used as a
    concrete `C`.
  - The standard Riemann-Siegel coefficient source gives coefficients by a
    generating/coefficient-extraction formula with
    `c_1(p) = -psi'''(p)/(96*pi^2)` for the standard Riemann-Siegel
    `psi(p) = cos(2*pi*(p^2-p-1/16))/cos(2*pi*p)`. That source formula is not
    present in the current Lean files and is not definitionally the same as
    the local `rsPsi p = cos(pi*(2*p^2 - 2*p + 1/4))`.
  - Because of that normalization mismatch, directly declaring a concrete
    coefficient in terms of the standard formula would leave an unproven
    normalization theorem before it can imply
    `SiegelStationaryPhaseCoefficientIdentityProp C`.
- Failed routes that should not be retried:
  - Do not define `C` as the raw defect quotient; that would be a circular
    reformulation of `SiegelCoordinateStationaryPhaseErrorProp`.
  - Do not instantiate `C` as a constant or a bound-only proxy such as
    `1/(6*pi)`; the current files support such bounds only as scale estimates,
    not as the exact local Taylor coefficient identity for `ErrorTerm`.
  - Do not port the standard `c_1` formula until the local `rsPsi`
    normalization has been related to the standard Riemann-Siegel `psi`.
- Files changed:
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - `git diff --check`: passed.
  - No Lean/Lake/full-build commands were run.
- Requested coordinator validation:
  - none for this ledger-only source-obstruction commit.
- Smallest next theorem:
  add, in an owned RS/Siegel/Gabcke coefficient file, a standard-coefficient
  normalization layer:
  1. define the standard Riemann-Siegel `psi` used by the coefficient source;
  2. define the first coefficient `c_1(p) = -psi'''(p)/(96*pi^2)` or the
     equivalent coefficient-extraction object;
  3. prove the normalization theorem relating that standard `psi`/`c_1` to the
     project-local `rsPsi` and the block-coordinate leading term. Only after
     that should `SiegelStationaryPhaseCoefficientIdentityProp C` be attacked.
- Coordinator action requested:
  no validation needed unless a later code patch instantiates the coefficient.

### 2026-04-28 Round 6: standard-to-local coefficient normalization bridge

- Classification: `CONDITIONAL_REDUCTION`.
- Theorem/file attacked:
  the bridge below `SiegelStationaryPhaseCoefficientIdentityProp C` and
  `SiegelStationaryPhaseCoefficientBoundProp C` in
  `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`.
- Proof facts banked:
  - Added `standardGabckeRawPsi`, the standard quotient-normalized
    Riemann-Siegel/Gabcke `psi` expression
    `cos(2*pi*(p^2 - p - 1/16)) / cos(2*pi*p)`.
  - Added `standardGabckeRawFirstCoefficient`, the source-form first
    coefficient `-deriv (deriv (deriv standardGabckeRawPsi)) p /
    (96*pi^2)`.
  - Added `StandardGabckeStationaryPhaseIdentityProp stdLead stdCoeff`, the
    standard-normalized block-coordinate stationary-phase identity before
    translating the source leading coefficient to local `rsPsi`.
  - Added `StandardGabckeLocalLeadingNormalizationProp stdLead`, the exact
    missing bridge statement `stdLead p = rsPsi p` on `p in Ico 0 1`.
  - Added `StandardGabckeCoefficientBoundProp stdCoeff`, the standard
    source-side coefficient bound by `fresnelC1Bound`.
  - Added
    `siegelStationaryPhaseCoefficientIdentityProp_of_standardGabckeNormalization`,
    proving that a standard-normalized identity plus the leading-normalization
    bridge gives the local `SiegelStationaryPhaseCoefficientIdentityProp`.
  - Added
    `siegelStationaryPhaseCoefficientBoundProp_of_standardGabckeBound`,
    carrying a standard coefficient bound to the local coefficient-bound atom.
- Failed routes that should not be retried:
  - Do not assert `standardGabckeRawPsi p = rsPsi p` directly. Static endpoint
    inspection already shows the raw quotient expression and local positive
    cosine convention do not match without an additional phase/parameter
    normalization.
  - Do not use block-independence; downstream RS/Gabcke wiring is already
    proved, and the useful live content is the normalized coefficient identity
    and coefficient bound.
- Files changed:
  - `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - Static reads/diffs only; no Lean/Lake/build/check commands were run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp`
  - `lake build Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra`
  - `lake build Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp`
  - `lake build Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
  - `printf 'import Littlewood.Main.LittlewoodPsi\n' | lake env lean --stdin`
  - `printf 'import Littlewood.Main.LittlewoodPi\n' | lake env lean --stdin`
- Smallest next theorem:
  define the correctly phase/parameter-normalized standard leading coefficient
  `stdLead` from Gabcke's source convention and prove
  `StandardGabckeLocalLeadingNormalizationProp stdLead`; then prove
  `StandardGabckeStationaryPhaseIdentityProp stdLead
    standardGabckeRawFirstCoefficient` from the contour expansion and
  `StandardGabckeCoefficientBoundProp standardGabckeRawFirstCoefficient` from
  the Tabelle-1 first-coefficient estimate.
- Coordinator action requested:
  run the requested serialized validation commands.

### 2026-04-28 Round 7: phase-normalized leading coefficient closed

- Classification: `PROVED`.
- Theorem/file attacked:
  `StandardGabckeLocalLeadingNormalizationProp stdLead` in
  `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`.
- Proof facts banked:
  - Added `standardGabckePhaseNormalizedLead p =
    cos(2*pi*(p^2 - p + 1/8))`, the phase/parameter-normalized standard
    leading coefficient in the local block convention.
  - Added `standardGabckePhaseNormalizedLead_eq_rsPsi`, proving this
    phase-normalized leading coefficient is exactly the repo-local
    `rsPsi p = cos(pi*(2*p^2 - 2*p + 1/4))`.
  - Added `standardGabckeLocalLeadingNormalization_phaseNormalized`, closing
    `StandardGabckeLocalLeadingNormalizationProp
      standardGabckePhaseNormalizedLead`.
- Failed routes that should not be retried:
  - The raw quotient-normalized `standardGabckeRawPsi` is still not asserted
    equal to local `rsPsi`; the proved bridge is through the phase-normalized
    leading coefficient, as requested.
  - Block-independence remains out of scope.
- Files changed:
  - `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - Static reads/diffs only; no Lean/Lake/build/check commands were run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp`
  - `lake build Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra`
  - `lake build Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp`
  - `lake build Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
  - `printf 'import Littlewood.Main.LittlewoodPsi\n' | lake env lean --stdin`
  - `printf 'import Littlewood.Main.LittlewoodPi\n' | lake env lean --stdin`
- Smallest next theorem:
  prove `StandardGabckeStationaryPhaseIdentityProp
    standardGabckePhaseNormalizedLead standardGabckeRawFirstCoefficient`
  from the actual contour/Taylor expansion, and prove
  `StandardGabckeCoefficientBoundProp standardGabckeRawFirstCoefficient` from
  the Tabelle-1 first-coefficient estimate.
- Coordinator action requested:
  run the requested serialized validation commands.

### 2026-04-29 Round 8: standard first-coefficient source surface

- Classification: `CONDITIONAL_REDUCTION`.
- Theorem/file attacked:
  `StandardGabckeStationaryPhaseIdentityProp
    standardGabckePhaseNormalizedLead standardGabckeRawFirstCoefficient` and
  `StandardGabckeCoefficientBoundProp standardGabckeRawFirstCoefficient` in
  `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`.
- Proof facts banked:
  - Static source search found no existing contour/Taylor theorem giving the
    phase-normalized stationary-phase identity with the raw Gabcke first
    coefficient, and no existing Tabelle-1 bound for that exact derivative
    coefficient.
  - Added `StandardGabckeContourTaylorFirstCoefficientIdentityProp`, stated
    with the unfolded source coefficient
    `-deriv (deriv (deriv standardGabckeRawPsi)) p / (96*pi^2)` and the
    already proved phase-normalized leading term
    `standardGabckePhaseNormalizedLead`.
  - Added `StandardGabckeTabelleFirstCoefficientBoundProp`, the exact
    Tabelle-1 source bound for the same unfolded first coefficient.
  - Added
    `standardGabckeStationaryPhaseIdentity_rawFirstCoefficient_of_contourTaylor`,
    proving the requested standard stationary-phase identity for
    `standardGabckeRawFirstCoefficient` from the contour/Taylor source atom.
  - Added `standardGabckeCoefficientBound_rawFirstCoefficient_of_tabelleBound`,
    proving the requested standard coefficient bound from the Tabelle-1 source
    atom.
  - Added `StandardGabckeFirstCoefficientSourceProp` and
    `standardGabckeTargets_of_firstCoefficientSource` as the paired source
    package feeding both standard target propositions.
- Failed routes that should not be retried:
  - Do not assert raw `standardGabckeRawPsi = rsPsi`; the leading bridge stays
    through `standardGabckePhaseNormalizedLead`.
  - Do not use exact k-independence or block-independence; downstream
    RS/Gabcke wiring is already proved and this round only targets
    `SiegelSaddleExpansionHyp`.
  - Do not define the coefficient as a defect quotient; the new source atoms
    are tied to the unfolded Gabcke derivative formula.
- Files changed:
  - `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - `git diff --check`: passed.
  - No Lean/Lake/build/check commands were run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
- Smallest next theorem:
  prove `StandardGabckeContourTaylorFirstCoefficientIdentityProp` from the
  actual contour/Taylor expansion, and prove
  `StandardGabckeTabelleFirstCoefficientBoundProp` from Gabcke Tabelle 1 for
  the unfolded coefficient formula.
- Coordinator action requested:
  run the requested serialized validation command.

### 2026-04-29 Round 9: Tabelle bound reduced to raw third derivative

- Classification: `CONDITIONAL_REDUCTION`.
- Theorem/file attacked:
  `StandardGabckeTabelleFirstCoefficientBoundProp` and its contribution to
  `StandardGabckeCoefficientBoundProp standardGabckeRawFirstCoefficient` in
  `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`.
- Proof facts banked:
  - Added `standardGabckeRawPsiThirdDerivative p`, the unscaled third
    derivative `deriv (deriv (deriv standardGabckeRawPsi)) p` behind the
    raw first Gabcke coefficient.
  - Added `StandardGabckeRawPsiThirdDerivativeBoundProp`, the smaller source
    theorem
    `|standardGabckeRawPsiThirdDerivative p| <=
      fresnelC1Bound * (96*pi^2)` on `p in Ico 0 1`.
  - Proved
    `standardGabckeTabelleFirstCoefficientBoundProp_of_rawPsiThirdDerivativeBound`,
    reducing the coefficient-level Tabelle atom to the unscaled derivative
    estimate using positivity of `96*pi^2`.
  - Added
    `standardGabckeFirstCoefficientSourceProp_of_contourTaylor_and_rawPsiThirdDerivativeBound`,
    wiring the original contour/Taylor identity plus the smaller derivative
    bound into `StandardGabckeFirstCoefficientSourceProp`.
  - Added
    `standardGabckeTargets_of_contourTaylor_and_rawPsiThirdDerivativeBound`,
    giving the two standard target propositions directly from the contour
    identity and the raw third-derivative bound.
- Failed routes that should not be retried:
  - Do not assert raw `standardGabckeRawPsi = rsPsi`.
  - Do not use block-independence or exact k-independence.
  - Do not define the coefficient as a defect quotient; the remaining bound is
    on the unfolded third derivative of the Gabcke source expression.
- Files changed:
  - `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - `git diff --check`: passed.
  - No Lean/Lake/build/check commands were run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
- Smallest next theorem:
  prove `StandardGabckeRawPsiThirdDerivativeBoundProp` from Gabcke Tabelle 1
  for the unfolded quotient-normalized `standardGabckeRawPsi`, while separately
  proving `StandardGabckeContourTaylorFirstCoefficientIdentityProp` from the
  actual contour/Taylor expansion.
- Coordinator action requested:
  run the requested serialized validation command.

### 2026-04-29 Round 10: raw derivative bound split at removable singularities

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  `StandardGabckeRawPsiThirdDerivativeBoundProp` in
  `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`.
- Banked inputs:
  - `standardGabckeRawPsiThirdDerivative` is the unfolded third derivative of
    the quotient-normalized source expression `standardGabckeRawPsi`.
  - Round 9 already proved that
    `StandardGabckeRawPsiThirdDerivativeBoundProp` implies the
    coefficient-level `StandardGabckeTabelleFirstCoefficientBoundProp`, and
    then the requested `StandardGabckeCoefficientBoundProp
      standardGabckeRawFirstCoefficient`.
- Proof facts banked:
  - Added `standardGabckeRawPsiDenominatorZero p`, the exact denominator-zero
    locus `cos(2*pi*p) = 0` for the raw quotient normalization.
  - Added `StandardGabckeRawPsiRegularThirdDerivativeBoundProp`, the raw
    third-derivative bound away from that locus.
  - Added `StandardGabckeRawPsiRemovableThirdDerivativeBoundProp`, the precise
    missing bridge at the removable singular points of the raw quotient.
  - Proved
    `standardGabckeRawPsiThirdDerivativeBoundProp_of_regular_and_removable`,
    recombining the regular estimate and removable-singularity bridge into the
    global raw third-derivative bound.
  - Added
    `standardGabckeTargets_of_contourTaylor_and_rawPsiThirdDerivativeSplit`,
    wiring the contour/Taylor identity plus the split derivative bounds all
    the way back to the two standard Gabcke target propositions.
- Failed routes:
  - Do not treat the raw quotient as an everywhere-regular formula; its
    denominator-zero locus must be bridged explicitly.
  - Do not assert raw `standardGabckeRawPsi = rsPsi`.
  - Do not use block-independence or exact k-independence.
  - Do not define the coefficient as a defect quotient.
- Files changed:
  - `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - `git diff --check`: passed.
  - No Lean/Lake/build/check commands were run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
- Smallest next theorem:
  prove `StandardGabckeRawPsiRegularThirdDerivativeBoundProp` from the explicit
  differentiated quotient formula on `cos(2*pi*p) != 0`, and prove
  `StandardGabckeRawPsiRemovableThirdDerivativeBoundProp` by replacing the raw
  quotient at `cos(2*pi*p) = 0` with the smooth removable extension used by
  Gabcke's coefficient table.
- Coordinator action requested:
  run the requested serialized validation command.

### 2026-04-29 Round 11: removable singularities reduced to two point checks

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  `StandardGabckeRawPsiRemovableThirdDerivativeBoundProp` in
  `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`.
- Banked inputs:
  - Round 10 separated the raw third-derivative bound into a regular quotient
    estimate and a removable-singularity estimate at
    `standardGabckeRawPsiDenominatorZero p`.
  - The live raw quotient denominator is exactly `cos(2*pi*p)`, and the
    removable singularities in `Ico 0 1` should be `p = 1/4` and `p = 3/4`.
- Proof facts banked:
  - Added `StandardGabckeRawPsiDenominatorZeroClassifiedProp`, the exact
    theorem that any denominator-zero `p in Ico 0 1` is `1/4` or `3/4`.
  - Added `StandardGabckeRawPsiRemovablePointBoundsProp`, the two pointwise
    raw third-derivative bounds at `1/4` and `3/4`.
  - Proved
    `standardGabckeRawPsiRemovableThirdDerivativeBoundProp_of_denominatorZeroClassified`,
    reducing the removable-singularity atom to the classification theorem plus
    those two point checks.
  - Added
    `standardGabckeRawPsiThirdDerivativeBoundProp_of_regular_classified_and_removablePoints`,
    recombining the regular quotient estimate, classification, and point
    checks into the global raw third-derivative bound.
  - Added
    `standardGabckeTargets_of_contourTaylor_regular_classified_and_removablePoints`,
    wiring this sharper split back to the two standard Gabcke target
    propositions.
- Failed routes:
  - Do not assert global regularity of the raw quotient.
  - Do not leave the removable side as an arbitrary denominator-zero bound;
    the exact source surface is now the two-point classification plus the
    pointwise derivative estimates.
  - Do not assert raw `standardGabckeRawPsi = rsPsi`.
  - Do not use block-independence or define the coefficient as a defect
    quotient.
- Files changed:
  - `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - Static reads/diffs only; no Lean/Lake/build/check commands were run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
- Smallest next theorem:
  prove `StandardGabckeRawPsiDenominatorZeroClassifiedProp` using
  `cos(2*pi*p) = 0` on `0 <= p < 1`, then prove
  `StandardGabckeRawPsiRemovablePointBoundsProp` by evaluating the removable
  extension of the raw quotient's third derivative at `1/4` and `3/4`.
- Coordinator action requested:
  run the requested serialized validation command.

### 2026-04-29 Round 12: denominator-zero classification split into lattice and range

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  `StandardGabckeRawPsiDenominatorZeroClassifiedProp` in
  `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`.
- Banked inputs:
  - Round 11 reduced the removable-singularity bound to
    `StandardGabckeRawPsiDenominatorZeroClassifiedProp` plus the two pointwise
    derivative checks at `1/4` and `3/4`.
  - The live denominator is still exactly `cos(2*pi*p)` from
    `standardGabckeRawPsiDenominatorZero`; no global regularity is assumed.
- Proof facts banked:
  - Added `StandardGabckeRawPsiDenominatorZeroQuarterLatticeProp`, the direct
    trigonometric source theorem that denominator-zero points in `Ico 0 1`
    lie on the quarter lattice `p = m/2 + 1/4`.
  - Added `StandardGabckeRawPsiDenominatorZeroQuarterLatticeRangeProp`, the
    elementary interval restriction showing quarter-lattice points in
    `Ico 0 1` are exactly `1/4` or `3/4`.
  - Proved
    `standardGabckeRawPsiDenominatorZeroClassifiedProp_of_quarterLattice`,
    deriving the existing two-point denominator-zero classification from
    those two smaller facts.
  - Added
    `standardGabckeTargets_of_contourTaylor_regular_quarterLattice_and_removablePoints`,
    wiring the quarter-lattice split back to the standard Gabcke target
    propositions.
- Failed routes:
  - Do not try to prove denominator classification by treating the raw quotient
    as regular at denominator-zero points.
  - Do not assert raw `standardGabckeRawPsi = rsPsi`.
  - Do not use block-independence or a defect-quotient coefficient.
- Files changed:
  - `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - Static reads/diffs only; no Lean/Lake/build/check commands were run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
- Smallest next theorem:
  prove `StandardGabckeRawPsiDenominatorZeroQuarterLatticeProp` using the
  standard real `cos_eq_zero` theorem for `2*pi*p`, and prove
  `StandardGabckeRawPsiDenominatorZeroQuarterLatticeRangeProp` by elementary
  integer/range arithmetic on `0 <= m/2 + 1/4 < 1`.
- Coordinator action requested:
  run the requested serialized validation command.

### 2026-04-29 Round 13: quarter-lattice range closed

- Classification: `PROVED`.
- Exact theorem attacked:
  `StandardGabckeRawPsiDenominatorZeroQuarterLatticeRangeProp` in
  `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`.
- Banked inputs:
  - Round 12 reduced `StandardGabckeRawPsiDenominatorZeroClassifiedProp` to
    the trig quarter-lattice theorem and an interval range theorem.
  - The raw denominator-zero locus remains explicit as
    `standardGabckeRawPsiDenominatorZero p`, with no global regularity
    assumption for the raw quotient.
- Proof facts banked:
  - Proved
    `standardGabckeRawPsiDenominatorZeroQuarterLatticeRangeProp_proved`:
    from `0 <= m/2 + 1/4 < 1`, integer discreteness gives
    `m = 0` or `m = 1`, hence the point is `1/4` or `3/4`.
  - Added
    `standardGabckeRawPsiDenominatorZeroClassifiedProp_of_quarterLattice_only`,
    so the denominator-zero classification now depends only on
    `StandardGabckeRawPsiDenominatorZeroQuarterLatticeProp`.
  - Added
    `standardGabckeTargets_of_contourTaylor_regular_latticeOnly_and_removablePoints`,
    wiring the proved range theorem back to the removable-singularity route
    and the two standard Gabcke target propositions.
- Failed routes:
  - Do not reopen the interval range theorem as an analytic problem; it is now
    pure integer arithmetic.
  - Do not treat the raw quotient as globally regular.
  - Do not assert raw `standardGabckeRawPsi = rsPsi`.
  - Do not use block-independence or a defect-quotient coefficient.
- Files changed:
  - `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - Static reads/diffs only; no Lean/Lake/build/check commands were run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
- Smallest next theorem:
  prove `StandardGabckeRawPsiDenominatorZeroQuarterLatticeProp` from the
  standard real `cos_eq_zero` theorem for `cos (2*pi*p) = 0`; after that,
  `standardGabckeRawPsiDenominatorZeroClassifiedProp_of_quarterLattice_only`
  closes `StandardGabckeRawPsiDenominatorZeroClassifiedProp`.
- Coordinator action requested:
  run the requested serialized validation command.

### 2026-04-29 Round 14: denominator-zero quarter lattice closed

- Classification: `PROVED`.
- Exact theorem attacked:
  `StandardGabckeRawPsiDenominatorZeroQuarterLatticeProp` in
  `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`.
- Banked inputs:
  - Round 13 already proved
    `standardGabckeRawPsiDenominatorZeroQuarterLatticeRangeProp_proved`.
  - The raw denominator-zero locus remains explicit as
    `standardGabckeRawPsiDenominatorZero p = (cos (2*pi*p) = 0)`.
- Proof facts banked:
  - Proved
    `standardGabckeRawPsiDenominatorZeroQuarterLatticeProp_proved` using
    `Real.cos_eq_zero_iff` for the angle `2*pi*p`, then dividing by
    `2*pi` to obtain `p = m/2 + 1/4`.
  - Added `standardGabckeRawPsiDenominatorZeroClassifiedProp_proved`, closing
    the classified denominator-zero route from the proved quarter-lattice and
    range theorems.
  - Added
    `standardGabckeTargets_of_contourTaylor_regular_and_removablePointBounds`,
    so the removable-singularity route now needs only the regular raw
    derivative bound, contour/Taylor identity, and two pointwise removable
    derivative bounds.
- Failed routes:
  - Do not treat `standardGabckeRawPsi` as globally regular.
  - Do not assert raw `standardGabckeRawPsi = rsPsi`.
  - Do not use block-independence or a defect-quotient coefficient.
- Files changed:
  - `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - Static reads/diffs only; no Lean/Lake/build/check commands were run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
- Smallest next theorem:
  prove `StandardGabckeRawPsiRemovablePointBoundsProp` by evaluating the
  removable extension of the raw quotient's third derivative at `1/4` and
  `3/4`; independently, prove
  `StandardGabckeRawPsiRegularThirdDerivativeBoundProp` on the nonzero
  denominator locus.
- Coordinator action requested:
  run the requested serialized validation command.

### 2026-04-29 Round 15: removable point values isolated

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  `StandardGabckeRawPsiRemovablePointBoundsProp` in
  `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`.
- Banked inputs:
  - `standardGabckeRawPsiDenominatorZeroClassifiedProp_proved` is closed, so
    the removable branch inside `Ico 0 1` is exactly the two points `1/4` and
    `3/4`.
  - The downstream route remains
    `standardGabckeTargets_of_contourTaylor_regular_and_removablePointBounds`.
- Proof facts banked:
  - Added `StandardGabckeRawPsiQuarterThirdDerivativeValueProp C14` and
    `StandardGabckeRawPsiThreeQuarterThirdDerivativeValueProp C34`, exact
    point-value source atoms for the raw third derivative at the two
    denominator-zero points.
  - Added `StandardGabckeRawPsiRemovablePointValueBoundsProp C14 C34`, the
    numeric bound atom for those sourced point values.
  - Proved `standardGabckeRawPsiRemovablePointBoundsProp_of_pointValues`,
    reducing the existing removable-point bound to the exact point values and
    their numeric bounds.
  - Added
    `standardGabckeTargets_of_contourTaylor_regular_and_removablePointValues`,
    preserving the direct standard Gabcke route through
    `standardGabckeTargets_of_contourTaylor_regular_and_removablePointBounds`.
- Failed routes:
  - Do not differentiate the raw quotient through the zero denominator as if
    it were globally regular; Lean's real division is totalized, so the two
    point values require an explicit removable-extension/Tabelle source
    identity.
  - Do not assert raw `standardGabckeRawPsi = rsPsi`.
  - Do not use block-independence or a defect-quotient coefficient.
- Files changed:
  - `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - Static reads/diffs only; no Lean/Lake/build/check commands were run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
- Smallest next theorem:
  identify the exact sourced constants `C14` and `C34` for
  `standardGabckeRawPsiThirdDerivative (1/4)` and
  `standardGabckeRawPsiThirdDerivative (3/4)` from Gabcke's smooth removable
  quotient/Tabelle normalization, then prove
  `StandardGabckeRawPsiRemovablePointValueBoundsProp C14 C34`.
- Coordinator action requested:
  run the requested serialized validation command.

### 2026-04-29 Round 16: removable source bridge isolated

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  the source values feeding
  `StandardGabckeRawPsiQuarterThirdDerivativeValueProp` and
  `StandardGabckeRawPsiThreeQuarterThirdDerivativeValueProp`.
- Banked inputs:
  - Round 15 reduced `StandardGabckeRawPsiRemovablePointBoundsProp` to exact
    raw point values at `1/4`, `3/4` plus numeric bounds.
  - The direct route through
    `standardGabckeTargets_of_contourTaylor_regular_and_removablePointBounds`
    remains intact.
- Proof facts banked:
  - Added `StandardGabckeRawPsiRemovableSourceBridgeProp D`, a two-point
    bridge from a smooth removable-source third derivative `D` to the raw
    totalized derivative values at `1/4` and `3/4`.
  - Added `StandardGabckeRemovableSourceThirdDerivativeValueProp D C14 C34`,
    the Tabelle/source-value atom for the smooth removable derivative at the
    same two points.
  - Proved `standardGabckeRawPsiRemovablePointValues_of_sourceBridge`, deriving
    the existing raw point-value atoms from the two-point bridge and sourced
    values.
  - Proved `standardGabckeRawPsiRemovablePointBoundsProp_of_sourceBridge`,
    deriving the removable point bounds from bridge, source values, and the
    numeric source-value bound.
  - Added
    `standardGabckeTargets_of_contourTaylor_regular_and_removableSourceBridge`,
    preserving the direct downstream Gabcke route while exposing the exact
    removable/Tabelle normalization input.
- Failed routes:
  - Do not use a global regularity assertion for `standardGabckeRawPsi`; the
    new bridge is pointwise at the classified denominator-zero locus only.
  - Do not assert raw `standardGabckeRawPsi = rsPsi`.
  - Do not use block-independence or a defect-quotient coefficient.
- Files changed:
  - `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - Static reads/diffs only; no Lean/Lake/build/check commands were run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
- Smallest next theorem:
  instantiate the removable-source derivative `D` from the actual local
  Taylor/removable quotient normalization and prove
  `StandardGabckeRawPsiRemovableSourceBridgeProp D`; then source the two
  Tabelle values and prove
  `StandardGabckeRemovableSourceThirdDerivativeValueProp D C14 C34` together
  with `StandardGabckeRawPsiRemovablePointValueBoundsProp C14 C34`.
- Coordinator action requested:
  run the requested serialized validation command.

### 2026-04-29 Round 17: removable source point atoms split

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  `StandardGabckeRawPsiRemovableSourceBridgeProp` and
  `StandardGabckeRemovableSourceThirdDerivativeValueProp`.
- Banked inputs:
  - Round 16 exposed the missing smooth removable-source derivative `D` and
    preserved the downstream route
    `standardGabckeTargets_of_contourTaylor_regular_and_removableSourceBridge`.
  - Denominator-zero classification remains closed, so only the two quarter
    points are live on the removable branch.
- Proof facts banked:
  - Added `StandardGabckeRawPsiQuarterRemovableSourceBridgeProp D` and
    `StandardGabckeRawPsiThreeQuarterRemovableSourceBridgeProp D`, splitting
    the raw/removable bridge into two independent point atoms.
  - Proved `standardGabckeRawPsiRemovableSourceBridgeProp_of_pointBridges`,
    reconstructing the paired bridge from those point atoms.
  - Added `StandardGabckeRemovableSourceQuarterThirdDerivativeValueProp D C14`
    and
    `StandardGabckeRemovableSourceThreeQuarterThirdDerivativeValueProp D C34`,
    splitting the Tabelle/source value atom into its two point values.
  - Proved
    `standardGabckeRemovableSourceThirdDerivativeValueProp_of_pointValues`,
    reconstructing the paired source-value atom from the two point-value atoms.
  - Added
    `standardGabckeTargets_of_contourTaylor_regular_and_removableSourcePointData`,
    preserving the direct route through
    `standardGabckeTargets_of_contourTaylor_regular_and_removableSourceBridge`
    while letting the next proof source one quarter point at a time.
- Failed routes:
  - Do not infer the point bridges by treating `standardGabckeRawPsi` as
    globally regular at denominator-zero points.
  - Do not assert raw `standardGabckeRawPsi = rsPsi`.
  - Do not use block-independence or a defect-quotient coefficient.
- Files changed:
  - `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - Static reads/diffs only; no Lean/Lake/build/check commands were run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
- Smallest next theorem:
  instantiate the smooth removable-source derivative `D` and prove either
  `StandardGabckeRawPsiQuarterRemovableSourceBridgeProp D` or
  `StandardGabckeRawPsiThreeQuarterRemovableSourceBridgeProp D`, then source
  the corresponding Tabelle value atom at that same quarter point.
- Coordinator action requested:
  run the requested serialized validation command.

### 2026-04-29 Round 18: removable source values closed canonically

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  `StandardGabckeRemovableSourceQuarterThirdDerivativeValueProp` and
  `StandardGabckeRemovableSourceThreeQuarterThirdDerivativeValueProp`.
- Banked inputs:
  - Round 17 split the removable-source bridge and Tabelle/source value atoms
    point-by-point at `1/4` and `3/4`.
  - The direct route through
    `standardGabckeTargets_of_contourTaylor_regular_and_removableSourceBridge`
    remains the required downstream path.
- Proof facts banked:
  - Proved
    `standardGabckeRemovableSourceQuarterThirdDerivativeValueProp_self`:
    for any smooth removable-source derivative `D`, the quarter source-value
    atom is closed by choosing the source constant `C14 = D (1/4)`.
  - Proved
    `standardGabckeRemovableSourceThreeQuarterThirdDerivativeValueProp_self`:
    the three-quarter source-value atom is closed by choosing
    `C34 = D (3/4)`.
  - Proved `standardGabckeRemovableSourceThirdDerivativeValueProp_self`,
    closing the paired source-value atom for those canonical constants.
  - Added `StandardGabckeRemovableSourceQuarterThirdDerivativeBoundProp D` and
    `StandardGabckeRemovableSourceThreeQuarterThirdDerivativeBoundProp D`, the
    remaining numeric Tabelle bounds after the source constants have been
    fixed to actual source values.
  - Added `StandardGabckeRemovableSourcePointBoundsProp D` and proved
    `standardGabckeRemovableSourcePointBoundsProp_of_pointBounds`.
  - Added
    `standardGabckeTargets_of_contourTaylor_regular_and_removableSourcePointBounds`,
    preserving the direct route while replacing arbitrary constants by the
    actual point values `D (1/4)` and `D (3/4)`.
- Failed routes:
  - Defining `D := standardGabckeRawPsiThirdDerivative` would make the
    raw/source bridge trivial but circular; it would not provide the smooth
    removable/Tabelle normalization.
  - Do not infer bridge equalities from global regularity of the raw quotient
    at denominator-zero points.
  - Do not assert raw `standardGabckeRawPsi = rsPsi`.
  - Do not use block-independence or a defect-quotient coefficient.
- Files changed:
  - `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - Static reads/diffs only; no Lean/Lake/build/check commands were run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
- Remaining goal shape:
  instantiate the smooth removable-source derivative `D`, prove the
  point-bridge equality
  `StandardGabckeRawPsiQuarterRemovableSourceBridgeProp D` or
  `StandardGabckeRawPsiThreeQuarterRemovableSourceBridgeProp D`, and prove the
  corresponding numeric point bound
  `StandardGabckeRemovableSourceQuarterThirdDerivativeBoundProp D` or
  `StandardGabckeRemovableSourceThreeQuarterThirdDerivativeBoundProp D`.
- Coordinator action requested:
  run the requested serialized validation command.

### 2026-04-29 Round 19: removable candidate source derivative instantiated

- Classification: `CONDITIONAL_REDUCTION`.
- Exact theorem attacked:
  instantiate the smooth removable-source derivative `D` and close one of the
  point-value atoms without using the raw totalized derivative as `D`.
- Banked inputs:
  - Round 18 closed the generic source-value atoms once the constants are
    chosen as actual source values.
  - The direct route through
    `standardGabckeTargets_of_contourTaylor_regular_and_removableSourceBridge`
    remains preserved.
- Proof facts banked:
  - Added `standardGabckeRemovablePsiCandidate`, the removable quotient
    candidate that agrees with `standardGabckeRawPsi` away from `1/4`, `3/4`
    and fills both removable quotient values with the common l'Hopital value
    `1/2`.
  - Added `standardGabckeRemovableSourceThirdDerivative`, the third derivative
    of that removable quotient candidate. This is the instantiated `D`; it is
    deliberately not definitionally `standardGabckeRawPsiThirdDerivative`.
  - Proved
    `standardGabckeRemovableSourceQuarterThirdDerivativeValueProp_candidate`,
    closing the quarter source-value atom for the instantiated `D` with
    constant
    `standardGabckeRemovableSourceThirdDerivative (1/4)`.
  - Proved
    `standardGabckeRemovableSourceThreeQuarterThirdDerivativeValueProp_candidate`,
    closing the three-quarter source-value atom for the instantiated `D`.
  - Added
    `standardGabckeTargets_of_contourTaylor_regular_and_removableCandidatePointBounds`,
    specializing the direct route to the instantiated removable candidate.
- Failed routes:
  - Do not define `D := standardGabckeRawPsiThirdDerivative`; that would make
    the bridge tautological but circular and would bypass the smooth
    removable/Tabelle normalization.
  - Do not infer the raw/candidate bridge from global regularity of the raw
    quotient at denominator-zero points.
  - Do not assert raw `standardGabckeRawPsi = rsPsi`.
- Files changed:
  - `Littlewood/Aristotle/Standalone/SiegelSaddleExpansionHyp.lean`
  - `Littlewood/Documentation/Recovery/2026-04-21/parallel/proofdebt-20260428/lanes/agent_rs_gabcke.md`
- Static command results:
  - Static reads/diffs only; no Lean/Lake/build/check commands were run.
- Requested coordinator validation:
  - `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
- Remaining goal shape:
  prove one raw/candidate point bridge,
  `StandardGabckeRawPsiQuarterRemovableSourceBridgeProp
    standardGabckeRemovableSourceThirdDerivative` or
  `StandardGabckeRawPsiThreeQuarterRemovableSourceBridgeProp
    standardGabckeRemovableSourceThirdDerivative`, and prove the corresponding
  numeric bound
  `StandardGabckeRemovableSourceQuarterThirdDerivativeBoundProp
    standardGabckeRemovableSourceThirdDerivative` or its three-quarter
  analogue.
- Coordinator action requested:
  run the requested serialized validation command.
