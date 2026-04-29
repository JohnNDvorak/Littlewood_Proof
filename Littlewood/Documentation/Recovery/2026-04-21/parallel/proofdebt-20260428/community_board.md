# Proof-Debt Community Board

Date: 2026-04-28 CDT

Launch ID: `proofdebt-20260428`

## Baseline

- Repository: `JohnNDvorak/Littlewood_Proof`
- Coordinator branch: `recovery/provider-forensics-2026-04-21`
- Baseline tag: `recovered-baseline-2026-04-28`
- Baseline commit: `acdc136`
- Rollback tags:
  - `pre-recovered-baseline-2026-04-28`
  - `recovered-mainchain-2026-04-28`
  - `recovered-baseline-2026-04-28`
- Stale worktree diffs archived under:
  `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/archive-20260428-*`

## Hard Rules

- Exactly one Lean/Lake validation job may run at a time across the machine.
- Full project builds are coordinator-only.
- Agents may inspect all files, but may edit only their lane-owned code and
  their own lane ledger.
- Coordinator owns public API files, shared proof assembly files, this board,
  integration, pushes, and Aristotle harvesting.
- Do not commit API keys, Aristotle runtime logs, raw prompt payloads, or
  downloaded result archives.
- Aristotle is a theorem-shaped sidecar only. Durable findings go into lane
  ledgers as reductions, failed routes, or exact Lean snippets.

## Active Worktrees

| Lane | Agent | Branch | Worktree | Ledger |
| --- | --- | --- | --- | --- |
| Atkinson | Hooke | `proofdebt/20260428-atkinson-large-j` | `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260428/atkinson` | `lanes/agent_atkinson.md` |
| Perron/B5a | Halley | `proofdebt/20260428-perron-b5a` | `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260428/perron-b5a` | `lanes/agent_perron_b5a.md` |
| Pi/Phase | Planck | `proofdebt/20260428-pi-phase` | `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260428/pi-phase` | `lanes/agent_pi_phase.md` |
| RS/Gabcke | Hume | `proofdebt/20260428-rs-gabcke` | `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260428/rs-gabcke` | `lanes/agent_rs_gabcke.md` |

## Overnight 2026-04-29 Launch

- Coordinator launch commit: `6103c17`.
- Fresh branches and worktrees:
  - Atkinson / Hooke:
    `proofdebt/20260429-atkinson-provider`,
    `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260429/atkinson`
  - Perron/B5a / Halley:
    `proofdebt/20260429-perron-b5a`,
    `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260429/perron-b5a`
  - Pi/Phase / Planck:
    `proofdebt/20260429-pi-phase`,
    `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260429/pi-phase`
  - RS/Gabcke / Hume:
    `proofdebt/20260429-rs-gabcke`,
    `/Users/john.n.dvorak/Projects/Littlewood_Proof_worktrees/proofdebt-20260429/rs-gabcke`
- All four overnight branches were pushed at their initial `6103c17`
  checkpoint.
- Hard rule remains:
  only the coordinator may run `lake`, `lake env lean`, `lean`, or any focused
  validation; only one such process may run across the machine.
- Aristotle CLI is installed, but `ARISTOTLE_API_KEY` is not set in the
  coordinator shell at launch. Do not put keys in tracked files, shell-visible
  commands, prompts, or ledgers.
- Aristotle sidecars submitted after key injection through a masked temporary
  environment path:
  - Atkinson: `57447356-4c39-4c20-8da2-6096b6243dfe`
  - Perron/B5a: `ee5694b1-8a5d-4b26-926a-16a38549bfb4`
  - Pi/Phase: `730f40bc-99a7-49bd-89fa-46039f150c23`
  - RS/Gabcke: `55d45e98-54c8-435a-9dde-c7fc59926147`
  The raw prompts, submit logs, temporary key, and later result downloads live
  under `/tmp/littlewood_aristotle_20260429`, not in tracked source.

All active worktrees symlink `.lake` to the coordinator tree cache.

## Current Targets

1. Atkinson:
   close `atkinson_inversePhaseCorePrefix_bound_large_j` and then package or
   validate `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`.
2. Perron/B5a:
   close `shifted_remainder_bound_leaf` or reduce it to a strictly smaller,
   non-circular Perron/Hadamard theorem.
3. Pi/Phase:
   remove public reliance on the false `TruncatedExplicitFormulaPiHyp.pi_approx`
   route and produce Perron-only target/anti-target phase coupling providers.
4. RS/Gabcke:
   reduce/prove `SiegelSaddleExpansionHyp` and the explicit Gabcke adjacent
   coefficient identity, nonnegativity, and antitonicity atoms.

## Validation Queue

Agents request validation in their lane ledger. The coordinator serializes:

1. focused build for the touched module(s),
2. strict public import probes for `Littlewood.Main.LittlewoodPsi` and
   `Littlewood.Main.LittlewoodPi`,
3. `#print axioms` / `#synth` probes only after a public-path closure,
4. full `lake build Littlewood` only at major checkpoints.

## Merge Queue

| Order | Branch | Status | Required before merge |
| --- | --- | --- | --- |
| 1 | `proofdebt/20260428-atkinson-large-j` | merged at coordinator `b5ddd64`, lane pushed through `d017308` | complete |
| 2 | `proofdebt/20260428-perron-b5a` | merged at coordinator `0b18794`, lane pushed through `6aef964` | complete |
| 3 | `proofdebt/20260428-pi-phase` | merged at coordinator `d20a209`, lane pushed through `162263b` | complete |
| 4 | `proofdebt/20260428-rs-gabcke` | merged at coordinator `16865be`, lane pushed through `2b3c75b` | complete |

## Agent Report Contract

Each agent report must state:

- exact theorem/file attacked,
- files changed,
- proof facts banked,
- failed routes that must not be retried,
- requested validation command,
- smallest next theorem,
- whether coordinator action is required.

## Coordinator Status

- Setup completed from `acdc136`.
- Fresh worktrees created and stale worktrees preserved.
- Initial lane agents dispatched.
- Initial Aristotle sidecars submitted:
  - Atkinson: `b895c2cb-ccbc-4edc-b13a-8076b5be5eb6`
  - Perron/B5a: `43160ae0-78e7-4d7e-b8af-76332fd6c59f`
  - Pi/Phase: `32a1df6a-be94-4cc2-81c3-05623533b222`
  - RS/Gabcke: `381b8764-543a-4024-a84f-9a9f91be9eba`
- Aristotle CLI auth is not cached in the coordinator shell. Job IDs remain in
  ignored self-drive logs; polling should be done only with the key supplied
  through an environment variable outside repo files and commit history.
- Aristotle results harvested on 2026-04-28:
  - Atkinson: audit-only; direct contraction still needs a log-free boundary row
    bound and a true successor contraction with factor `< 1`; unchanged Abel
    decomposition remains too lossy.
  - Perron/B5a: audit/reduction only; keep small-T provision independent and
    non-circular, and do not use the false `perron_tail_bound_core` route.
  - Pi/Phase: audit/reduction only; avoid the constant-1 Perron-sqrt route and
    the false `TruncatedExplicitFormulaPiHyp` path.
  - RS/Gabcke: audit-only; downstream wiring is proved, so the live content is
    the normalized coefficient identity/bound/adjacent monotonicity.
- Aristotle harvest integrated on 2026-04-28:
  durable findings from all four finished sidecars were moved into tracked
  coordination docs and lane ledgers. See
  `aristotle_harvest_integration.md`. Raw result zips, full-repo snapshots,
  prompt payloads, and runtime logs remain ignored under `self_drive/`.
  The delivered Pi reduction Lean file was checked once with `lake env lean`;
  it failed on a current-branch `RiemannHypothesis` namespace ambiguity and
  remains documentation-only to avoid adding active-source sorry debt.
- Validation completed and pushed:
  - Atkinson `4e2e825`: `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`
    passed; reduced shifted `blockMode` remainder to two quadratic-anchor atoms.
  - Atkinson `16f1fd7`: same focused build passed after coordinator alias/nonneg
    proof fix; reduced quadratic-anchor approximation to zero-model and kernel
    atoms.
  - Atkinson `da6efa1`: same focused build passed after coordinator removed two
    redundant finishing tactics; split the shifted quadratic kernel bound into
    mass, moment, and weight-scale atoms.
  - Atkinson `5e12977`: same focused build passed after coordinator removed a
    redundant finishing tactic and normalized indentation; closed the kernel
    weight-scale atom and reduced the integral bound to mass and moment atoms.
  - Atkinson `1d6314a`: same focused build passed; reduced the weighted moment
    atom to an exact quadratic-kernel boundary identity.
  - Atkinson `cce6705`: same focused build passed after coordinator specified
    the complex interval-integrability proof; closed the exact quadratic-kernel
    boundary identity and the weighted moment atom.
  - Atkinson `70078bf`: same focused build passed; closed the shifted quadratic
    mass bound and the shifted quadratic kernel integral bound, reducing the
    next interface to zero-model approximation and explicit target matching.
  - Perron/B5a `040f565`: `lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf`
    passed; reduced shifted leaf to direct large/small Perron payloads.
  - Perron/B5a `b1f2641`: `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`
    passed; reduced small-T payload to weighted kernel and residue atoms.
  - Perron/B5a `43aa10d`: same focused build passed after coordinator coercion
    fix; split weighted cutoff into boundary-window and off-boundary atoms.
  - Perron/B5a `d186f57`: same focused build passed; reduced the boundary
    window estimate to a kernel supremum and von Mangoldt window-weight atom.
  - Perron/B5a `72d85d5`: same focused build passed after coordinator removed a
    redundant finishing tactic; corrected the boundary window weight scale.
  - Perron/B5a `1da652d`: same focused build passed; closed the corrected
    boundary-window von Mangoldt weight estimate at the linear `x / T` scale.
  - Perron/B5a `23e1a81`: same focused build passed; showed the naive
    decaying boundary-kernel estimate fails at the exact integer hit and split
    the route into exact-hit and punctured-window atoms.
  - Perron/B5a `32eaeea`: same focused build passed after coordinator fixed
    the `Finset.card_le_one_iff` intro order and supplied `0 <= Real.log x`
    to the exact-hit monotonicity step; closed the exact-hit weighted boundary
    error estimate.
  - Pi/Phase `847fa92`: `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
    passed; added Perron-only corrected phase endpoints.
  - Pi/Phase `bbedbc3`: `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
    passed after coordinator alias proof fix; added relative-density phase-fit
    adapter.
  - Pi/Phase `bb027c8`: `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
    and `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
    passed after coordinator fixed local-definition unfolding; reduced the wide
    tower window to `PerronThresholdTowerWideDominationHyp`.
  - Pi/Phase `6a9ca1d`: same two focused builds passed; reduced the finite-zero
    inhomogeneous phase fit provider to a finite-set Kronecker atom.
  - Pi/Phase `5c2066e`: same two focused builds passed; refined the finite
    Kronecker source to a relation-compatible finite-set formulation plus the
    zeta-specific compatibility leaf.
  - Pi/Phase `73831f2`: same two focused builds passed; split phase fit into
    target-specific and anti-target-specific leaves and added exact-seed routes
    from the Perron-only phase-fit classes.
  - Pi/Phase `c94204b`: same two focused builds passed; reduced tower
    domination to target/anti-target realized phase radii instead of generic
    all-radius domination.
  - Pi/Phase `4a89847`: same two focused builds passed; split the realized
    phase-radius route into target/anti tower geometry classes feeding the
    corrected tower coupling providers.
  - RS/Gabcke `fa96728`: `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`
    passed; split Siegel/Gabcke into profile and coefficient atoms.
  - RS/Gabcke `9564c41`: same focused build set passed; reduced weighted profile
    to a coordinate remainder atom.
  - RS/Gabcke `908144b`: same focused build set passed after coordinator fixed
    `blockCoord` positivity; reduced the coordinate remainder to the raw
    stationary-phase error atom.
  - RS/Gabcke `ad5064f`: same focused build set passed after coordinator
    removed one redundant finishing tactic; split the stationary-phase error
    into a concrete coefficient identity atom and a coefficient bound atom.
  - RS/Gabcke `449d4e8`: ledger-only obstruction note, no validation needed;
    the missing prerequisite is a formal bridge from the repo-local `rsPsi`
    normalization to the standard Gabcke/Riemann-Siegel coefficient formula.
  - RS/Gabcke `d1ff2f9`: same focused build set passed; added the standard
    Gabcke raw phase/coefficient interface and reduced the live bridge to a
    correctly phase/parameter-normalized `stdLead`.
  - Atkinson `4e39e2e`: `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`
    passed in the lane; reduced target matching to a scalar coefficient atom.
  - Atkinson `23095f2`: same focused build passed in the lane; reduced the
    scalar target-coefficient atom to a shifted unweighted mass-coefficient
    matching estimate.
  - Atkinson `d017308`: same focused build passed after coordinator replaced
    fragile integral notation with `atkinsonShiftedQuadraticMassCoeff` and
    fixed local unit cancellation; branch pushed and merged.
  - Perron/B5a `6aef964`: `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`
    passed; split the punctured boundary window into near-diagonal and
    separated pieces.
  - Pi/Phase `b0d5f8f`: `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
    and
    `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
    passed; paired the target/anti phase-radius geometry surface.
  - Pi/Phase `162263b`: same two focused builds passed; paired the zeta
    finite-zero compatibility leaves for target and anti-target phases.
  - RS/Gabcke `2b3c75b`: focused build set
    `SiegelSaddleExpansionHyp GabckePhaseCouplingInfra GabckePhaseCouplingHyp HardyZFirstMomentBridge`
    passed; closed the phase-normalized leading bridge
    `StandardGabckeLocalLeadingNormalizationProp standardGabckePhaseNormalizedLead`.
- Integration checkpoint on 2026-04-28:
  - All four lane branches were pushed to GitHub and merged into the coordinator
    branch through `16865be`.
  - Integrated focused validation passed:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula Littlewood.Aristotle.Standalone.PerronTruncationInfra Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundDeepLeaf Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`.
  - Strict public import probes passed:
    `import Littlewood.Main.LittlewoodPsi` and
    `import Littlewood.Main.LittlewoodPi`.

## Overnight 2026-04-29 Validation Checkpoint

Timestamp: 2026-04-28 22:56 CDT.

- Coordinator preserved the single-build rule throughout this checkpoint: no
  second Lean/Lake job was started while a validation was running.
- Pi/Phase lane pushed through `f7c8b38`
  (`proofdebt/20260429-pi-phase`):
  - `b75d132`: paired target/anti finite-zero inhomogeneous relative-density
    providers.
  - `243e1d9`: reduced paired tower geometry to log-scale domination.
  - `da02d9f`: reduced log geometry to the paired log-budget class.
  - `f7c8b38`: added the corrected Perron-only RH-`pi` route endpoint. The
    coordinator repaired the file so it does not require
    `TruncatedExplicitFormulaPiHyp`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
- Perron/B5a lane pushed through `27ed5e9`
  (`proofdebt/20260429-perron-b5a`):
  - `08ea602`: reduced near-diagonal boundary error to cardinality/kernel
    supremum.
  - `d499131`: closed the near-diagonal cardinality atom.
  - `e73a902`: closed the near-diagonal punctured kernel bound.
  - `27ed5e9`: reduced the separated Perron boundary to a weighted atom.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
- RS/Gabcke lane pushed through `7cce500`
  (`proofdebt/20260429-rs-gabcke`):
  - `c6daa97`: reduced Gabcke first coefficient to source atoms.
  - `5d29dbc`: reduced the Tabelle coefficient bound to a raw derivative bound.
  - `15cb908`: split the raw derivative bound into regular/removable atoms.
  - `7cce500`: reduced the removable bound to denominator-zero classification
    and point checks.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`.
- Atkinson lane pushed through `206673f`
  (`proofdebt/20260429-atkinson-provider`):
  - `9d55fa6`: reduced shifted quadratic mass/target surface to Fourier
    matching.
  - `ccfe50b` plus coordinator fix `8ff5a67`: exposed the corrected Fourier
    target route and fixed positivity.
  - `cee0acc`: reduced the corrected Fourier-target zero-model surface to the
    exact residual atom.
  - `206673f`: reduced that residual to compensated phase error.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
- All four lane agents were redeployed after their validated heads:
  - Hooke: compensated phase-error bound.
  - Halley: separated weighted Perron boundary atom.
  - Planck: paired log-budget / corrected Perron-only synthesis.
  - Hume: Gabcke denominator-zero classification or removable point bounds.
- Aristotle sidecar status at this checkpoint, polled with the masked temp key:
  - Atkinson `57447356-4c39-4c20-8da2-6096b6243dfe`: in progress, 38%.
  - Perron/B5a `ee5694b1-8a5d-4b26-926a-16a38549bfb4`: in progress, 32%.
  - Pi/Phase `730f40bc-99a7-49bd-89fa-46039f150c23`: complete and already
    downloaded; useful as a packaging audit, not a log-budget closure.
  - RS/Gabcke `55d45e98-54c8-435a-9dde-c7fc59926147`: in progress, 33%.
- Coordinator stopped one non-coordinator `lake env lean` process in the
  Atkinson worktree and re-issued the hard rule: agents must not run `lake`,
  `lake env lean`, `lean`, or any focused build/check themselves.
- Current live atoms:
  - Atkinson: shifted zero-model approximation and shifted unweighted
    mass-coefficient matching toward
    `atkinson_blockMode_stationaryPhase_of_zero_model_and_massCoeff`, then
    packaging `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`.
  - Perron/B5a: near-diagonal punctured weighted boundary error, separated
    punctured pointwise kernel decay, off-boundary estimate, and bounded-height
    residue extraction.
  - Pi/Phase: `TargetAntiPerronThresholdTowerGeometryForPhaseRadiiHyp`,
    `TargetAntiFiniteZeroInhomogeneousPhaseRelationCompatibleHyp`, and
    `FiniteSetRelationCompatibleInhomogeneousPhaseRelativelyDenseKroneckerHyp`.
  - RS/Gabcke: prove
    `StandardGabckeStationaryPhaseIdentityProp standardGabckePhaseNormalizedLead standardGabckeRawFirstCoefficient`
    and `StandardGabckeCoefficientBoundProp standardGabckeRawFirstCoefficient`
    from the actual contour/Taylor expansion and Tabelle-1 coefficient bound.
- Next coordinator action: redeploy the four lanes from merged coordinator
  `16865be`, validate returning commits serially, and only run public import
  probes after a lane closes a public-path provider rather than another
  conditional reduction.

## Overnight 2026-04-29 First Pass Status

- All four fresh 20260429 lane branches were validated serially by the
  coordinator and pushed:
  - Atkinson `9d55fa6`: `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`
    passed; reduced the shifted quadratic mass/target surface to the fixed
    Fourier matching atom
    `atkinsonShiftedQuadraticFourierMassCoeff n j` versus
    `atkinsonShiftedQuadraticTargetCoeff n j`.
  - Perron/B5a `08ea602`: `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`
    passed; reduced the near-diagonal punctured boundary estimate to a
    cardinality/kernel-supremum route and recorded the scale-unsafety of the
    decaying-kernel route near integer `x`.
  - Pi/Phase `b75d132`:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
    and
    `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
    passed; paired target/anti finite-zero inhomogeneous relative-density
    providers through relation-compatible Kronecker source atoms.
  - RS/Gabcke `c6daa97`: focused build set
    `SiegelSaddleExpansionHyp GabckePhaseCouplingInfra GabckePhaseCouplingHyp HardyZFirstMomentBridge`
    passed; reduced the standard Gabcke targets to contour-Taylor and
    Tabelle-1 first-coefficient source atoms.
- Second-pass assignments are active on the same four 20260429 branches.
  Agents remain barred from all Lean/Lake invocations; coordinator keeps the
  one-build-at-a-time rule.
- Current 20260429 Aristotle sidecars remain queued:
  - Atkinson: `57447356-4c39-4c20-8da2-6096b6243dfe`
  - Perron/B5a: `ee5694b1-8a5d-4b26-926a-16a38549bfb4`
  - Pi/Phase: `730f40bc-99a7-49bd-89fa-46039f150c23`
  - RS/Gabcke: `55d45e98-54c8-435a-9dde-c7fc59926147`

## Overnight 2026-04-29 Second Pass Status

- All four second-pass lane commits were validated serially by the
  coordinator and pushed:
  - Atkinson `ccfe50b` plus coordinator fix `8ff5a67`:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula` passed;
    exposed the corrected Fourier target route and replaced one fragile
    positivity proof with the explicit
    `atkinsonModeWeight_nonneg`/`div_nonneg` argument.
  - Perron/B5a `d499131`:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`
    passed; closed the near-diagonal punctured boundary cardinality atom and
    reduced the estimate to the remaining uniform local kernel bound.
  - Pi/Phase `243e1d9`:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
    and
    `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
    passed; reduced paired tower geometry to the log-scale domination atom
    using `Real.exp` monotonicity.
  - RS/Gabcke `5d29dbc`: focused build set
    `SiegelSaddleExpansionHyp GabckePhaseCouplingInfra GabckePhaseCouplingHyp HardyZFirstMomentBridge`
    passed; reduced the Tabelle first-coefficient bound to the raw
    `standardGabckeRawPsiThirdDerivative` bound on `Ico 0 1`.
- Fresh Aristotle poll shows all four current sidecars in progress:
  - Atkinson `57447356-4c39-4c20-8da2-6096b6243dfe`: in progress.
  - Perron/B5a `ee5694b1-8a5d-4b26-926a-16a38549bfb4`: in progress.
  - Pi/Phase `730f40bc-99a7-49bd-89fa-46039f150c23`: in progress.
  - RS/Gabcke `55d45e98-54c8-435a-9dde-c7fc59926147`: in progress.
- Third-pass live targets:
  - Atkinson: attack the shifted zero-model approximation feeding the
    corrected Fourier-target route, and keep the old target Fourier mismatch
    documented as a genuine coefficient gap unless an exact bridge is found.
  - Perron/B5a: prove the uniform local kernel bound for the near-diagonal
    punctured boundary route; do not reuse the decaying-kernel near-integer
    route.
  - Pi/Phase: prove the paired log-scale tower domination source for target
    and anti-target phase radii.
  - RS/Gabcke: prove either the contour-Taylor first-coefficient identity or
    the raw third-derivative bound that feeds the Tabelle coefficient bound.

## Overnight 2026-04-29 Third Pass Status

- Four third-pass lane commits have been validated serially by the
  coordinator and pushed:
  - Atkinson `cee0acc`:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula` passed;
    reduced the corrected Fourier-target zero-model surface to the exact
    shifted residual atom `atkinsonShiftedQuadraticZeroModelResidual`.
  - Pi/Phase `da02d9f`:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider`
    and
    `lake build Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`
    passed; reduced the paired log tower geometry to the same-height
    `TargetAntiPerronThresholdTowerLogBudgetForPhaseRadiiHyp`.
  - Perron/B5a `e73a902`:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`
    passed; proved the uniform near-diagonal punctured kernel bound and closed
    `small_T_nearDiagonal_punctured_boundary_bound`.
  - RS/Gabcke `15cb908`: focused build set
    `SiegelSaddleExpansionHyp GabckePhaseCouplingInfra GabckePhaseCouplingHyp HardyZFirstMomentBridge`
    passed; split the raw third-derivative bound into regular and removable
    denominator-zero atoms.
- Current follow-up lane assignments:
  - Atkinson: attack the residual atom directly; do not replace it by a
    generic mass/norm estimate that loses the `1 / j` scale.
  - Pi/Phase: attack
    `TargetAntiPerronThresholdTowerLogBudgetForPhaseRadiiHyp` or integrate the
    completed Aristotle packaging endpoint if it fits the newer lane.
  - Perron/B5a: move from the now-closed near-diagonal punctured atom to the
    separated punctured boundary route or next weighted cutoff assembly.
  - RS/Gabcke: attack either
    `StandardGabckeRawPsiRegularThirdDerivativeBoundProp` or
    `StandardGabckeRawPsiRemovableThirdDerivativeBoundProp`.
- Aristotle sidecar `730f40bc-99a7-49bd-89fa-46039f150c23` completed for the
  Pi/Phase lane. It did not close the log-budget atom, but it produced a
  sorry-free packaging file
  `Littlewood/Aristotle/Standalone/RHPiCorrectedPerronOnlyRoute.lean` with
  theorems routing the corrected Perron-only Pi chain from four honest classes
  to `RhPiWitnessData`, including
  `rhPiWitnessData_of_correctedPerronOnlyRoute`,
  `exactSeed_of_correctedPerronOnlyRoute`,
  `correctedPhaseCoupling_of_correctedPerronOnlyRoute`, and
  `rh_pi_7a_7c_pair_of_correctedPerronOnlyRoute`.

## Overnight 2026-04-29 Fourth Pass Status

- The coordinator preserved the one-build rule for this pass. Each focused
  Lean/Lake validation completed before the next one started.
- Aristotle sidecar results were harvested from the ignored temp area
  `/tmp/littlewood_aristotle_20260429`; no raw prompts, logs, downloaded
  archives, or API key material were moved into tracked files.
- Perron/B5a lane validated and pushed through `3a0d351`
  (`proofdebt/20260429-perron-b5a`):
  - Commit: `Reduce separated Perron error to Davenport envelope`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  - Aristotle confirmed the old separated pointwise bounded-height decay route
    is scale-unsafe; the current Davenport-envelope finite weighted-sum route
    is the live route.
  - Halley redeployed to prove or honestly split the pointwise
    Davenport-envelope normalization below
    `small_T_separated_weighted_bound_from_davenport_envelope`.
- Pi/Phase lane validated and pushed through `19d419b`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Expose corrected pi half-budget route`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Planck redeployed to the two honest half-budget leaves:
    `PerronThresholdTowerLogHalfBudgetHyp` and
    `TargetAntiFiniteZeroPhaseRadiusHalfBudgetAtPerronThresholdHyp`.
- RS/Gabcke lane validated and pushed through `bd40a4c`
  (`proofdebt/20260429-rs-gabcke`):
  - Commit: `Split Gabcke denominator zeros into lattice and range`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`.
  - Hume redeployed to the quarter-lattice denominator-zero leaves
    `StandardGabckeRawPsiDenominatorZeroQuarterLatticeProp` and
    `StandardGabckeRawPsiDenominatorZeroQuarterLatticeRangeProp`.
- Atkinson lane was not pushed at local head `6571bfd`
  (`Reduce Atkinson phase error to carrier defect`):
  - The Aristotle Atkinson sidecar proved the two live zero-model route leaves
    scale-false: the mass-coefficient matching leaf has the wrong
    `sqrt(n)/j` versus `sqrt(n)/j^2` scale, and the shifted zero-model
    approximation has too large a carrier phase error on `Ioc j (j+1)`.
  - Hooke was redirected away from the zero-model / mass-coefficient /
    Fourier-corrected / compensated-carrier route.
  - Live Atkinson route is now through `AtkinsonShiftedCorrectionPrefixBoundHyp`
    and the existing
    `atkinson_shiftedInversePhaseCellPrefixBound_of_shiftedCorrectionPrefix`
    handoff. The next useful output is a correction-term prefix bound or a
    clean reduction to the smallest fixed-shift correction atom.
- Current live atoms after this pass:
  - Atkinson: correction-prefix provider path for
    `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`; zero-model route demoted.
  - Perron/B5a: Davenport-envelope pointwise normalization, then weighted
    envelope summation/off-boundary/residue atoms.
  - Pi/Phase: paired same-height Perron-threshold half budget and paired
    finite-zero phase-radius half budget.
  - RS/Gabcke: quarter-lattice denominator-zero classification/range, then
    removable point bounds and the regular raw derivative estimate.
