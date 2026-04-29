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
