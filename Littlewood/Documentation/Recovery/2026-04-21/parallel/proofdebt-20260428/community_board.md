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

## Overnight 2026-04-29 Fifth Pass Status

- The coordinator again enforced the one-build rule. Atkinson and RS/Gabcke
  were validated serially after the Perron and Pi heads from the prior pass.
- Perron/B5a lane is validated and pushed through `5198f4b`
  (`proofdebt/20260429-perron-b5a`):
  - Halley commit `4e22d7b` initially failed in
    `PerronTruncationInfra.lean` on separated-set positivity and an unavailable
    `one_lt_div_iff₀` helper.
  - Coordinator fix `5198f4b` added the needed `2 <= T` hypothesis at the
    membership helper, derived the nonzero index contradiction from boundary
    separation, and used the available `one_lt_div` route.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  - Halley is redeployed to the weighted Davenport-envelope summation atom:
    `perronKernelSeparatedDavenportEnvelope x T <= Cd * (Real.log x)^2`
    for `x >= 2`, `2 <= T`, `T <= 16`.
- Pi/Phase lane is validated and pushed through `6e807f4`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Reduce pi half budgets to growth sources`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Planck is redeployed to the two growth-source classes:
    `PerronThresholdTowerExpHalfBudgetGrowthHyp` and
    `TargetAntiFiniteZeroPhaseRadiusHalfBudgetGrowthHyp`.
- Atkinson lane is validated and pushed through `cbd3f6d`
  (`proofdebt/20260429-atkinson-provider`):
  - Commit stack includes the explicit revert of the false zero-model carrier
    route (`a0bca65`) and the new reduction
    `cbd3f6d Reduce Atkinson correction prefix to raw atoms`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Live route is now the correction-prefix route through
    `atkinson_shiftedCorrectionPrefixBound_of_eventual_j3_and_correction_j1_j2`.
  - Hooke is redeployed to prove the large-shift raw correction-prefix atom for
    `3 <= j`.
- RS/Gabcke lane is validated and pushed through `12e7314`
  (`proofdebt/20260429-rs-gabcke`):
  - Commit: `Close Gabcke quarter-lattice range`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`.
  - Hume is redeployed to close the remaining
    `StandardGabckeRawPsiDenominatorZeroQuarterLatticeProp` atom.
- Current live atoms:
  - Atkinson: raw correction-prefix atom for all large shifts `3 <= j`;
    zero-model, Fourier-corrected carrier, and compensated-carrier routes are
    forbidden unless their scale obstruction is explicitly changed.
  - Perron/B5a: weighted Davenport-envelope summation, then separated
    off-boundary/residue assembly.
  - Pi/Phase: two growth-source half-budget providers feeding the corrected
    Perron-only Pi route.
  - RS/Gabcke: quarter-lattice zero atom, then any remaining removable/regular
    raw derivative cleanup needed for the public Gabcke provider.

## Overnight 2026-04-29 Sixth Pass Status

- Perron/B5a lane is validated and pushed through `f66d994`
  (`proofdebt/20260429-perron-b5a`):
  - Commit: `Split Perron Davenport envelope by components`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  - Result: Halley split the Davenport envelope into singular and smooth
    components and banked the scale-correct linear-envelope route.
  - Important guardrail: the pure bounded-height `O((log x)^2)` envelope target
    is scale-incorrect here. The live path keeps the `(x / T)` factor and now
    attacks the singular harmonic-distance component.
- Pi/Phase lane is validated and pushed through `b9e701a`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Split pi growth budgets by majorants`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Result: Planck split the remaining Pi half-budget growth providers into
    the two majorant classes
    `PerronThresholdTowerExpHalfBudgetMajorantHyp` and
    `TargetAntiFiniteZeroPhaseRadiusHalfBudgetMajorantHyp`, with a corrected
    Perron-only majorant-budget route to `RhPiWitnessData`.
- Current live atoms:
  - Perron/B5a: singular harmonic-distance component for the scale-correct
    Davenport envelope route.
  - Pi/Phase: close either majorant class exactly, preferably via a small
    monotonicity/growth provider.
  - Atkinson: Hooke remains assigned to the large-shift raw correction-prefix
    atom for `3 <= j`.
  - RS/Gabcke: Hume remains assigned to
    `StandardGabckeRawPsiDenominatorZeroQuarterLatticeProp`.

## Overnight 2026-04-29 Seventh Pass Status

- Atkinson lane is validated and pushed through `382d32f`
  (`proofdebt/20260429-atkinson-provider`):
  - Commit: `Reduce Atkinson raw correction prefix to row prefix`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Result: the large-shift correction-prefix atom is reduced to a raw
    row-integral prefix atom, with the boundary side extracted from existing
    boundary machinery.
  - Hooke is redeployed to the raw row-integral prefix atom feeding
    `atkinson_largeShiftCorrectionPrefix_bound_of_rowIntegralPrefix` and
    `atkinson_shiftedCorrectionPrefixBound_of_rowIntegralPrefix_and_correction_j1_j2`.
- Current live atoms:
  - Atkinson: raw row-integral prefix atom on the correction-prefix route.
  - Perron/B5a: singular harmonic-distance component for the scale-correct
    Davenport envelope route.
  - Pi/Phase: the two majorant classes for the corrected Perron-only Pi route.
  - RS/Gabcke: `StandardGabckeRawPsiDenominatorZeroQuarterLatticeProp`.

## Overnight 2026-04-29 Eighth Pass Status

- RS/Gabcke lane is validated and pushed through `da48525`
  (`proofdebt/20260429-rs-gabcke`):
  - Commit: `Close Gabcke denominator quarter lattice`.
  - Validation passed after a coordinator over-tactic fix:
    `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`.
  - Result: `StandardGabckeRawPsiDenominatorZeroQuarterLatticeProp` and the
    classified denominator-zero route are now proved.
  - Hume is redeployed to `StandardGabckeRawPsiRemovablePointBoundsProp`, or
    `StandardGabckeRawPsiRegularThirdDerivativeBoundProp` if the removable
    point bounds are already closed.
- Perron/B5a lane is validated and pushed through `acf84ac`
  (`proofdebt/20260429-perron-b5a`):
  - Commit: `Reduce singular Perron envelope to log distance`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  - Result: the singular Davenport component is reduced to a pointwise
    comparison with `x / (T * (x - n))` plus a weighted harmonic-distance
    summation atom, keeping the scale-correct `(x / T)` factor.
  - Halley is redeployed to close one of those two log-distance subatoms.
- Pi/Phase lane is validated and pushed through `37641ae`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Refine pi majorant leaves`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Result: the Pi majorant route now splits to three refined leaves:
    `PerronThresholdTowerExpHalfBudgetCanonicalMajorantHyp`,
    `TargetFiniteZeroPhaseRadiusHalfBudgetMajorantHyp`, and
    `AntiTargetFiniteZeroPhaseRadiusHalfBudgetMajorantHyp`.
  - Planck is redeployed to close one of the three refined majorant leaves.
- Current live atoms:
  - Atkinson: raw row-integral prefix atom on the correction-prefix route.
  - Perron/B5a: one of the two log-distance subatoms.
  - Pi/Phase: one of the three refined majorant leaves.
  - RS/Gabcke: removable point bounds or regular raw third-derivative bound.

## Overnight 2026-04-29 Ninth Pass Status

- Atkinson lane is validated and pushed through `8fd9279`
  (`proofdebt/20260429-atkinson-provider`):
  - Commit: `Reduce Atkinson row prefix to complete-block tail`.
  - Validation passed after a coordinator nonnegativity/empty-branch fix:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Result: the row-integral prefix atom is reduced to two leaves: a weighted
    complete-block tail prefix and the isolated `j - 1` head row-cell bound.
  - Hooke is redeployed to close one of those two leaves while preserving the
    correction-prefix route and scale.
- RS/Gabcke lane is validated and pushed through `130576f`
  (`proofdebt/20260429-rs-gabcke`):
  - Commit: `Isolate Gabcke removable point values`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`.
  - Result: removable point bounds are reduced to exact third-derivative values
    at `1/4` and `3/4`, plus numeric bounds for those values.
  - Hume is redeployed to source those values through the removable/Tabelle
    normalization or to attack the regular raw third-derivative bound.
- Perron/B5a lane is validated and pushed through `bd4010d`
  (`proofdebt/20260429-perron-b5a`):
  - Commit: `Reduce singular Perron pointwise distance`.
  - Validation passed after a coordinator denominator-normalization fix:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  - Result: the pointwise singular comparison now has a proved numerator
    bound and is reduced to the reciprocal-log distance inequality
    `(Real.log (x / (n : ℝ)))⁻¹ <= x / (x - (n : ℝ))`.
  - Halley is redeployed to close that inequality or the weighted harmonic
    distance summation leaf. The false pure bounded-height envelope remains
    forbidden.
- Pi/Phase lane is validated and pushed through `c7339c5`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Canonize pi one-sided radius leaves`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Result: the two finite-zero radius half-budget leaves are canonicalized
    into target and anti-target one-sided classes.
  - Planck is redeployed to one of the three current majorant leaves.
- Current live atoms:
  - Atkinson: weighted complete-block tail prefix or isolated head row-cell
    bound feeding the correction-prefix route.
  - Perron/B5a: reciprocal-log distance inequality or weighted harmonic
    distance summation.
  - Pi/Phase: one of the three canonical majorant leaves.
  - RS/Gabcke: exact removable point values or regular raw third-derivative
    bound.

## Overnight 2026-04-29 Tenth Pass Status

- Atkinson lane is validated and pushed through `af5eb80`
  (`proofdebt/20260429-atkinson-provider`):
  - Commit: `Reduce Atkinson head row cell to finite patch`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Result: the isolated `j - 1` head row-cell side is reduced to a finite
    patch below the eventual cutoff. The main remaining Atkinson obstruction is
    the weighted complete-block tail prefix, plus that finite patch.
  - Hooke is redeployed to the complete-block tail prefix or finite-head patch.
- RS/Gabcke lane is validated and pushed through `127780c`
  (`proofdebt/20260429-rs-gabcke`):
  - Commit: `Split Gabcke removable source bridge`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`.
  - Result: the removable point-value source is reduced to a raw/removable
    bridge plus sourced Tabelle third-derivative values.
  - Hume is redeployed to close the removable source bridge or sourced value
    property.
- Current live atoms:
  - Atkinson: weighted complete-block tail prefix and finite head patch.
  - Perron/B5a: reciprocal-log distance inequality or weighted harmonic
    distance summation.
  - Pi/Phase: one of the three canonical majorant leaves.
  - RS/Gabcke: removable source bridge or sourced Tabelle value property.

## Overnight 2026-04-29 Eleventh Pass Status

- Perron/B5a lane is validated and pushed through `3be3a37`
  (`proofdebt/20260429-perron-b5a`):
  - Commit: `Close singular Perron reciprocal log`.
  - Validation passed after a coordinator normalization fix:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  - Result: the reciprocal-log distance inequality is proved. The singular
    Perron component now points at the weighted harmonic-distance summation
    leaf, still preserving the scale-correct `(x / T)` route.
  - Halley is redeployed to close that weighted summation. The false pure
    bounded-height envelope remains forbidden.
- Pi/Phase lane is validated and pushed through `ebd9c25`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Compare pi canonical budget leaves`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Result: the canonical Pi budget comparisons have advanced; remaining
    pressure stays on the canonical majorant/growth leaves feeding the Pi
    phase route.
  - Planck is redeployed to continue closing those canonical leaves, avoiding
    typeclass loops and the false truncated-Pi shortcut.
- Current live atoms:
  - Atkinson: weighted complete-block tail prefix and finite head patch.
  - Perron/B5a: weighted harmonic-distance summation.
  - Pi/Phase: remaining canonical majorant/growth leaves.
  - RS/Gabcke: removable source bridge or sourced Tabelle value property.

## Overnight 2026-04-29 Twelfth Pass Status

- Atkinson lane is validated and pushed through `cb94ef9`
  (`proofdebt/20260429-atkinson-provider`):
  - Commit: `Close Atkinson finite head patch`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Result: the finite head patch is closed. The Atkinson row-prefix route now
    depends only on the weighted complete-block tail prefix feeding the
    correction-prefix route.
  - Hooke is redeployed to that complete-block tail prefix. Direct raw Abel
    shortcuts remain forbidden.
- RS/Gabcke lane is validated and pushed through `0a3cc55`
  (`proofdebt/20260429-rs-gabcke`):
  - Commit: `Split Gabcke removable source point atoms`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`.
  - Result: the removable source bridge/value route is split pointwise into
    quarter and three-quarter bridge atoms plus sourced third-derivative value
    atoms.
  - Hume is redeployed to close one of those point atoms. Global regularity at
    denominator-zero points and raw `standardGabckeRawPsi = rsPsi` remain
    forbidden routes.
- Current live atoms:
  - Atkinson: weighted complete-block tail prefix.
  - Perron/B5a: weighted harmonic-distance summation.
  - Pi/Phase: remaining canonical majorant/growth leaves.
  - RS/Gabcke: quarter/three-quarter removable source bridge and sourced
    third-derivative value atoms.

## Overnight 2026-04-29 Thirteenth Pass Status

- Perron/B5a lane is validated and pushed through `4dfce73`
  (`proofdebt/20260429-perron-b5a`):
  - Commit: `Reduce Perron harmonic distance to unweighted sum`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  - Result: the weighted harmonic-distance summation is reduced to an
    unweighted finite harmonic-distance bound while keeping the scale-correct
    `(x / T)` factor.
  - Halley is redeployed to prove that unweighted finite bound. The false
    pure bounded-height envelope, public typeclass shortcuts, contour
    providers, and `perron_tail_bound_core` remain forbidden.
- Pi/Phase lane is validated and pushed through `076c424`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Package pi canonical budget exact seeds`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Result: exact seed packaging is in place for paired relative density plus
    canonical budgets.
  - Planck is redeployed to close one canonical budget leaf. Typeclass loops,
    reverse-comparison cycles, and unproved `Classical.choose` radius control
    remain forbidden.
- Current live atoms:
  - Atkinson: weighted complete-block tail prefix.
  - Perron/B5a: unweighted finite harmonic-distance bound.
  - Pi/Phase: three canonical budget leaves.
  - RS/Gabcke: quarter/three-quarter removable source bridge and sourced
    third-derivative value atoms.

## Overnight 2026-04-29 Fourteenth Pass Status

- Atkinson lane is validated and pushed through `bfe18a7`
  (`proofdebt/20260429-atkinson-provider`):
  - Commit: `Reduce Atkinson block tail to target remainder`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Result: the complete-block tail is reduced to the stationary-phase
    complete-block target remainder at `C_err * (atkinsonModeWeight k / j)`
    plus finite fixed-shift weighted complete-block tail patches below the
    eventual cutoff.
  - Hooke is redeployed to those two exact targets. Boundary/correction
    decomposition is forbidden here because it would require the correction
    prefix provider currently being built.
- RS/Gabcke lane is validated and pushed through `bcd870e`
  (`proofdebt/20260429-rs-gabcke`):
  - Commit: `Close Gabcke removable source value atoms`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`.
  - Result: the self-value and point-bound scaffolding for the removable
    source derivative values is closed. The remaining work is to instantiate
    the smooth removable-source derivative `D`, prove the quarter/three-quarter
    raw-removable bridges, and prove the corresponding numeric point bound.
  - Hume is redeployed to the smooth removable-source bridge route. Defining
    `D := standardGabckeRawPsiThirdDerivative`, global regularity at
    denominator-zero points, and raw `standardGabckeRawPsi = rsPsi` remain
    forbidden.
- Current live atoms:
  - Atkinson: stationary-phase complete-block target remainder and finite
    fixed-shift tail patches.
  - Perron/B5a: unweighted finite harmonic-distance bound.
  - Pi/Phase: three canonical budget leaves.
  - RS/Gabcke: smooth removable-source derivative instantiation, point
    bridges, and numeric point bounds.

## Overnight 2026-04-29 Fifteenth Pass Status

- Perron/B5a lane is validated and pushed through `1329939`
  (`proofdebt/20260429-perron-b5a`):
  - Commit: `Factor Perron unweighted harmonic distance`.
  - Validation passed after a coordinator tactic cleanup:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  - Result: the unweighted finite harmonic-distance bound is factored to the
    pure reciprocal-distance envelope. The remaining atom is now the clean
    bounded-height finite harmonic sum:
    `∃ Ch > 0, ∀ x T, x >= 2 -> 2 <= T -> T <= 16 ->
      perronKernelSeparatedReciprocalDistanceEnvelope x T <= Ch * Real.log x`.
  - Halley is redeployed to prove that reciprocal-distance envelope directly.
- Pi/Phase lane is validated and pushed through `7d4b121`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Expose pi growth budget exact seeds`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Result: exact growth-budget seed packaging is exposed for the Pi phase
    route. The remaining Pi work is the same-height `T, ε` domination for the
    canonical majorant and the target/anti-target chosen-radius canonical
    bounds.
  - Planck is redeployed to those canonical-budget leaves. Growth-to-canonical
    cycles and unproved `Classical.choose` control remain forbidden.
- Current live atoms:
  - Atkinson: stationary-phase complete-block target remainder and finite
    fixed-shift tail patches.
  - Perron/B5a: pure reciprocal-distance finite harmonic sum.
  - Pi/Phase: same-height canonical majorant plus target/anti chosen-radius
    canonical bounds.
  - RS/Gabcke: smooth removable-source derivative instantiation, point
    bridges, and numeric point bounds.

## Overnight 2026-04-29 Sixteenth Pass Status

- Atkinson lane is validated and pushed through `633b2d9`
  (`proofdebt/20260429-atkinson-provider`):
  - Commit: `Reduce Atkinson finite block patches to cell patches`.
  - Validation passed after a coordinator normalization patch:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Result: finite weighted complete-block patches are reduced to finite
    fixed-shift inverse-phase cell-prefix patches, and the row-integral
    prefix reduction is now split into the stationary-phase target remainder
    plus those finite cell patches.
  - Hooke is redeployed to the two exact atoms: the complete-block target
    remainder at `C_err * (atkinsonModeWeight k / j)` and native finite
    fixed-shift cell-prefix patches below the eventual cutoff.
- RS/Gabcke lane is validated and pushed through `7cd1500`
  (`proofdebt/20260429-rs-gabcke`):
  - Commit: `Instantiate Gabcke removable source derivative`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`.
  - Result: the smooth removable-source derivative candidate is now
    instantiated without using the circular raw derivative definition. The
    remaining RS/Gabcke atoms are the quarter/three-quarter raw-removable
    bridge for that candidate and the corresponding numeric point bound.
  - Hume is redeployed to close one of those bridge/numeric point-bound atoms.
- Current live atoms:
  - Atkinson: stationary-phase complete-block target remainder and finite
    fixed-shift inverse-phase cell-prefix patches.
  - Perron/B5a: pure reciprocal-distance finite harmonic sum.
  - Pi/Phase: same-height canonical majorant plus target/anti chosen-radius
    canonical bounds.
  - RS/Gabcke: removable-source bridge and numeric point bounds for
    `standardGabckeRemovableSourceThirdDerivative`.

## Overnight 2026-04-29 Seventeenth Pass Status

- Perron/B5a lane is validated and pushed through `0591d7c`
  (`proofdebt/20260429-perron-b5a`):
  - Commit: `Reduce Perron reciprocal distance to harmonic floor`.
  - Validation passed after a coordinator inequality-ordering cleanup:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  - Result: the reciprocal-distance envelope is reduced to the exact finite
    harmonic majorant
    `perronKernelSeparatedReciprocalDistanceEnvelope x T <=
      (harmonic (Nat.floor x) : ℝ)`.
  - Halley is redeployed to close the remaining finite reindexing/injection
    lemma from separated indices to integer distances below `Nat.floor x`.
- Pi/Phase lane is validated and pushed through `fc19c55`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Name pi canonical budget residuals`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Result: the three Pi canonical budget leaves now have explicit residual
    predicates and reduction theorems. This makes the remaining obligations
    inspectable:
    `PerronThresholdTowerExpHalfBudgetCanonicalMajorantResidual`,
    `TargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`, and
    `AntiTargetFiniteZeroPhaseRadiusHalfBudgetCanonicalResidual`.
  - Planck is redeployed to prove one residual directly, with priority on the
    majorant residual if it avoids chosen-radius control.
- Current live atoms:
  - Atkinson: stationary-phase complete-block target remainder and finite
    fixed-shift inverse-phase cell-prefix patches.
  - Perron/B5a: finite reindexing/injection into `harmonic (Nat.floor x)`.
  - Pi/Phase: three named canonical-budget residuals.
  - RS/Gabcke: removable-source bridge and numeric point bounds for
    `standardGabckeRemovableSourceThirdDerivative`.

## Overnight 2026-04-29 Eighteenth Pass Status

- Atkinson lane is validated and pushed through `d4d5985`
  (`proofdebt/20260429-atkinson-provider`):
  - Commit: `Reduce Atkinson finite cell patches to native leaves`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Result: the finite inverse-phase cell-prefix patch now reduces to native
    finite fixed-shift boundary-prefix and correction-prefix leaves, without
    using the global correction provider class. The public/deep path remains
    split into native fixed-shift finite leaves plus the stationary-phase
    complete-block target remainder.
  - Hooke is redeployed to close one native leaf directly.
- RS/Gabcke lane is validated and pushed through `2338200`
  (`proofdebt/20260429-rs-gabcke`):
  - Commit: `Reduce Gabcke quarter bound to Taylor value`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`.
  - Result: the quarter numeric point bound is reduced to the explicit Taylor
    value formula
    `standardGabckeRemovableSourceThirdDerivative (1/4) = -Real.pi ^ 2`.
    The quarter raw-removable bridge remains separate.
  - Hume is redeployed to prove the value formula or the quarter bridge.
- Current live atoms:
  - Atkinson: stationary-phase complete-block target remainder, finite
    fixed-shift boundary-prefix leaf, and finite fixed-shift correction-prefix
    leaf.
  - Perron/B5a: finite reindexing/injection into `harmonic (Nat.floor x)`.
  - Pi/Phase: three named canonical-budget residuals.
  - RS/Gabcke: quarter value formula and quarter raw-removable bridge, with
    analogous three-quarter atoms still available if that route proves easier.

## Overnight 2026-04-29 Nineteenth Pass Status

- Pi/Phase lane is validated and pushed through `936ef57`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Reduce pi Perron residual to transfer`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Result: the Perron-threshold tower half-budget canonical majorant residual
    is reduced to a same-height transfer inequality:
    `perronThreshold hRH T + 1 <=
      max (X + 1) (perronThreshold hRH T0 + 1)`.
  - Planck is redeployed to determine whether this transfer follows from
    existing monotonicity/definition of `perronThreshold`, needs a corrected
    fixed-height residual, or is false as currently stated.
- Current live atoms:
  - Atkinson: stationary-phase complete-block target remainder, finite
    fixed-shift boundary-prefix leaf, and finite fixed-shift correction-prefix
    leaf.
  - Perron/B5a: finite reindexing/injection into `harmonic (Nat.floor x)`.
  - Pi/Phase: Perron transfer inequality plus target/anti chosen-radius
    canonical residuals.
  - RS/Gabcke: quarter value formula and quarter raw-removable bridge, with
    analogous three-quarter atoms still available if that route proves easier.

## Overnight 2026-04-29 Twentieth Pass Status

- Perron/B5a lane is validated and pushed through `21528cd`
  (`proofdebt/20260429-perron-b5a`):
  - Commit: `Close Perron harmonic floor reindexing`.
  - Validation passed after a coordinator injectivity cleanup:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  - Result: the reciprocal-distance envelope is now bounded by the usual
    finite harmonic sum through the exact floor-distance reindexing. The
    branch has the pure small-`T` reciprocal-distance bound down to the
    harmonic/log layer.
  - Halley is redeployed to continue Perron/B5a public-path debt without
    touching the contour-provider duplicate-class route or false tail
    placeholders.
- Atkinson lane is validated and pushed through `4e1ddfb`
  (`proofdebt/20260429-atkinson-provider`):
  - Commit: `Close Atkinson finite boundary patch`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Result: the finite fixed-shift boundary-prefix patch is closed. The native
    shifted inverse-phase/cell-prefix path is now concentrated on the
    stationary-phase complete-block target remainder and finite correction
    prefix patches.
  - Hooke is redeployed to attack the next exact Atkinson leaf directly.
- Current live atoms:
  - Atkinson: stationary-phase complete-block target remainder and finite
    fixed-shift correction-prefix patches.
  - Perron/B5a: inspect whether the small-`T` harmonic/log path discharges the
    public provider; otherwise close the next explicit B5a public-path leaf.
  - Pi/Phase: Perron transfer inequality plus target/anti chosen-radius
    canonical residuals.
  - RS/Gabcke: quarter value formula and quarter raw-removable bridge, with
    analogous three-quarter atoms still available if that route proves easier.

## Overnight 2026-04-29 Twenty-First Pass Status

- Pi/Phase lane is validated and pushed through `0f1ac51`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Analyze pi Perron transfer bound`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Result: the cross-height Perron transfer is now factored into an exact
    selected-threshold bound. The same-height case is proved, and the earlier
    naive monotonicity route is demoted because the `Classical.choose`
    threshold definition does not provide the needed cross-height inequality.
  - Planck is redeployed to either add the missing selected-threshold/cofinality
    bound or revise the canonical majorant statement to a true fixed-height
    residual.
- RS/Gabcke lane is validated and pushed through `fcb17f5`
  (`proofdebt/20260429-rs-gabcke`):
  - Commit: `Reduce Gabcke quarter value to local Taylor atom`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp Littlewood.Aristotle.Standalone.GabckePhaseCouplingInfra Littlewood.Aristotle.Standalone.GabckePhaseCouplingHyp Littlewood.Aristotle.Standalone.HardyZFirstMomentBridge`.
  - Result: the quarter numeric point-bound route is reduced to local Taylor
    coordinate third-derivative atoms, while the raw removable-source bridge
    remains separate and non-circular.
  - Hume is redeployed to close one of the local Taylor atoms or the raw
    quarter removable-source bridge.
- Current live atoms:
  - Atkinson: stationary-phase complete-block target remainder and finite
    fixed-shift correction-prefix patches.
  - Perron/B5a: inspect whether the small-`T` harmonic/log path discharges the
    public provider; otherwise close the next explicit B5a public-path leaf.
  - Pi/Phase: selected-threshold/cofinality bound or corrected fixed-height
    canonical majorant residual, plus target/anti chosen-radius residuals.
  - RS/Gabcke: quarter local Taylor atoms and quarter raw-removable bridge,
    with analogous three-quarter atoms available if easier.

## Overnight 2026-04-29 Twenty-Second Pass Status

- Atkinson lane is validated and pushed through `52831da`
  (`proofdebt/20260429-atkinson-provider`):
  - Commit: `Reduce Atkinson correction patch to fixed shifts`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Result: the finite correction-patch family has been reduced to native
    single-shift correction-prefix leaves for fixed `j >= 3`. The bookkeeping
    cutoff is no longer the live obstruction.
  - Guardrail recorded: do not derive the unweighted correction prefix from the
    phase-weighted correction prefix by dividing through
    `atkinsonShiftedRelativePhase`; this exposes endpoint growth around
    `n / j` and is not scale-safe.
  - Hooke is redeployed to the two remaining Atkinson public-path atoms.
- Current live atoms:
  - Atkinson: shifted-interval stationary-phase target remainder and native
    fixed-shift correction-prefix leaf.
  - Perron/B5a: inspect whether the small-`T` harmonic/log path discharges the
    public provider; otherwise close the next explicit B5a public-path leaf.
  - Pi/Phase: selected-threshold/cofinality bound or corrected fixed-height
    canonical majorant residual, plus target/anti chosen-radius residuals.
  - RS/Gabcke: quarter local Taylor atoms and quarter raw-removable bridge,
    with analogous three-quarter atoms available if easier.

## Overnight 2026-04-29 Twenty-Third Pass Status

- Perron/B5a lane is validated and pushed through `3bfd980`
  (`proofdebt/20260429-perron-b5a`):
  - Commit: `Close Perron linear Davenport route`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  - Result: the separated Davenport boundary contribution is now bounded at
    the scale
    `C * (x / T) * (Real.log x)^2`.
  - Guardrail recorded: the pure separated `O((Real.log x)^2)` route is
    false/demoted. Continue through the off-boundary-compatible assembly or a
    corrected truncation/residue handoff, not by strengthening the separated
    boundary term alone.
  - Halley is redeployed to close the next true B5a public-path leaf under
    this scale.
- Pi/Phase lane is validated and pushed through `4a36945`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Name pi selected-threshold residual`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Result: the canonical majorant route now factors through the exact
    selected-threshold residual
    `perronThreshold hRH T <= max X (perronThreshold hRH T0)`.
  - Guardrail recorded: do not pretend cross-height monotonicity follows from
    the opaque `Classical.choose` threshold definition. Either prove the
    selected residual directly or refactor the provider around a fixed-height
    Perron error witness.
  - Planck is redeployed to this exact residual or the fixed-height refactor.
- Current live atoms:
  - Atkinson: shifted-interval stationary-phase target remainder and native
    fixed-shift correction-prefix leaf.
  - Perron/B5a: assemble the linear Davenport boundary scale into the public
    B5a route or adjust the truncation/residue handoff accordingly.
  - Pi/Phase: selected-threshold/cofinality residual or corrected fixed-height
    canonical majorant residual, plus target/anti chosen-radius residuals.
  - RS/Gabcke: quarter local Taylor atoms and quarter raw-removable bridge,
    with analogous three-quarter atoms available if easier.

## Overnight 2026-04-29 Twenty-Fourth Pass Status

- Atkinson lane is validated and pushed through `a512bc6`
  (`proofdebt/20260429-atkinson-provider`):
  - Commit: `Package Atkinson correction provider from native atoms`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Result: `AtkinsonShiftedCorrectionPrefixBoundHyp` is now packaged from
    the native shifted-interval stationary-phase target remainder, fixed-shift
    correction-prefix leaf for `j >= 3`, and the `j = 1,2` correction patches.
  - Guardrail preserved: no phase-weighted-to-unweighted division, direct
    Abel, zero-model, mass-coefficient, Fourier-corrected, compensated-carrier,
    circular provider, diffuse deweighting, axioms, sorries, or weakening.
  - Hooke is redeployed to use the packaged correction provider toward the
    public/deep `AtkinsonShiftedInversePhaseCellPrefixBoundHyp` leaf.
- RS/Gabcke lane is validated and pushed through `a2226c9`
  (`proofdebt/20260429-rs-gabcke`):
  - Commit: `Reduce Gabcke local Taylor atom to HasDerivAt`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp`.
  - Result: the quarter local Taylor value route is reduced to the local
    second-derivative `HasDerivAt` atom, while the removable-candidate local
    coordinate and raw removable-source bridge remain explicit separate
    targets.
  - Guardrail preserved: do not define the removable candidate by the target
    derivative, assume global raw regularity at the removable point, or assert
    raw `standardGabckeRawPsi = rsPsi`.
  - Hume is redeployed to close one of the exact local Taylor/removable atoms.
- Current live atoms:
  - Atkinson: use the correction provider to close or further reduce
    `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`; if blocked, isolate the
    shifted-interval stationary-phase target remainder as the exact atom.
  - Perron/B5a: assemble the linear Davenport boundary scale into the public
    B5a route or adjust the truncation/residue handoff accordingly.
  - Pi/Phase: selected-threshold/cofinality residual or corrected fixed-height
    canonical majorant residual, plus target/anti chosen-radius residuals.
  - RS/Gabcke: quarter local second-derivative `HasDerivAt`, removable
    candidate local-coordinate third derivative, and raw quarter removable
    bridge.

## Overnight 2026-04-29 Twenty-Fifth Pass Status

- Perron/B5a lane is validated and pushed through `db18924`
  (`proofdebt/20260429-perron-b5a`):
  - Commit: `Route Perron cutoff at linear scale`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  - Result: the small-`T` weighted-kernel cutoff path is routed at the true
    linear scale `C * (x / T) * (Real.log x)^2`, with boundary handling now
    separated from the off-boundary atom.
  - Remaining Perron atom: prove the compatible off-boundary estimate
    `perronKernelWeightedOffBoundaryWindowError x T <=
      Co * (x / T) * (Real.log x)^2` for `x >= 2`, `2 <= T`, `T <= 16`, or
    replace it with a non-circular truncation/residue handoff.
  - Halley is redeployed to that off-boundary atom.
- Pi/Phase lane is validated and pushed through `17b955a`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Expose pi fixed-height Perron error seeds`.
  - Coordinator repair: opened `RHPiZeroSumAlignmentBridge` so the direct
    `piLiErr` / `piMainFromZeros` payload names are in scope.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Result: the route now has fixed-height Perron-error target and anti-target
    exact-seed payloads, avoiding the opaque cross-height
    `Classical.choose` threshold comparison.
  - Remaining Pi atom: connect the fixed-height Perron-error payloads into the
    corrected phase-coupling/provider route, or isolate the smallest remaining
    phase/cofinality payload needed.
  - Planck is redeployed to that fixed-height route.
- Current live atoms:
  - Atkinson: close or further reduce `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`
    using the packaged correction provider.
  - Perron/B5a: compatible off-boundary window bound at linear `x / T` scale.
  - Pi/Phase: wire fixed-height Perron-error exact seeds into the corrected
    provider route, avoiding cross-height threshold monotonicity.
  - RS/Gabcke: quarter local second-derivative `HasDerivAt`, removable
    candidate local-coordinate third derivative, and raw quarter removable
    bridge.

## Overnight 2026-04-29 Twenty-Sixth Pass Status

- Atkinson lane is validated and pushed through `4b336cb`
  (`proofdebt/20260429-atkinson-provider`):
  - Commit: `Package Atkinson inverse provider from native atoms`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Result: `AtkinsonShiftedInversePhaseCellPrefixBoundHyp` is now reduced to
    the native atom package by constructing `AtkinsonShiftedCorrectionPrefixBoundHyp`
    locally, then applying the shifted-correction-prefix bridge.
  - Remaining Atkinson atoms: shifted-interval stationary-phase target
    remainder, native fixed-shift correction-prefix leaf for `j >= 3`, and
    small correction patches `j = 1,2` if immediate provider instantiation
    still needs them.
- Perron/B5a lane is validated and pushed through `7d7cc48`
  (`proofdebt/20260429-perron-b5a`):
  - Commit: `Reduce Perron off-boundary cutoff to Davenport envelope`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  - Result: the off-boundary weighted window error is now bounded by a named
    Davenport envelope, and the small-`T` weighted cutoff route is reduced to
    a single scale-correct envelope estimate.
  - Remaining Perron atom:
    `perronKernelOffBoundaryDavenportEnvelope x T <=
      Cd * (x / T) * (Real.log x)^2`.
- RS/Gabcke lane is validated and pushed through `ea5b66c`
  (`proofdebt/20260429-rs-gabcke`):
  - Commit: `Split Gabcke quarter coordinate bridge`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp`.
  - Result: the removable-candidate quarter local-coordinate third derivative
    is split into a local translation/chain-rule atom plus a local function
    equality atom, avoiding the circular raw-regularity route.
  - Remaining RS/Gabcke atoms:
    `StandardGabckeRemovableCandidateQuarterTranslationThirdDerivativeProp`
    or `StandardGabckeRemovableCandidateQuarterLocalFunctionEqProp`.
- Current live atoms:
  - Atkinson: prove the native stationary-phase/correction-prefix atoms needed
    for immediate provider instantiation.
  - Perron/B5a: prove the named Davenport-envelope bound at linear `x / T`
    scale.
  - Pi/Phase: fixed-height Perron-error exact-seed route is running with
    Planck.
  - RS/Gabcke: close one of the two split removable-candidate quarter atoms.

## Overnight 2026-04-29 Twenty-Seventh Pass Status

- Pi/Phase lane is validated and pushed through `4e04ec6`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Bridge pi fixed-height error route`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Result: the fixed-height Perron-error target and anti-target exact-seed
    payloads now feed the full target/anti arg-approx families, corrected
    phase-coupling, and `RhPiWitnessData`, without constructing
    Perron-threshold exact-seed classes.
  - Remaining Pi atom:
    `InhomogeneousPhaseFitWithFixedHeightPerronErrorHyp`, choosing `x, T, ε`
    with actual fixed-height Perron error, phase approximation, and tower cap
    at the same height.
  - Guardrail preserved: no cross-height `perronThreshold` monotonicity, no
    false truncated-Pi route, no circular provider instances, no axioms/sorries.
- Current live atoms:
  - Atkinson: native stationary-phase/correction-prefix atoms needed for
    immediate provider instantiation.
  - Perron/B5a: named Davenport-envelope bound at linear `x / T` scale.
  - Pi/Phase: `InhomogeneousPhaseFitWithFixedHeightPerronErrorHyp`.
  - RS/Gabcke: one of the split removable-candidate quarter atoms.

## Overnight 2026-04-29 Twenty-Eighth Pass Status

- Atkinson lane is validated and pushed through `9b4dcb5`
  (`proofdebt/20260429-atkinson-provider`):
  - Commit: `Package Atkinson provider from all fixed shifts`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Result: the `j = 1,2` correction patches are no longer separate gates if
    one native fixed-shift correction-prefix family is proved for every
    positive shift. The route remains non-circular: all-fixed-shift correction
    family plus shifted stationary-phase remainder builds
    `AtkinsonShiftedCorrectionPrefixBoundHyp`, then
    `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`.
  - Remaining Atkinson atoms: shifted-interval stationary-phase target
    remainder and native fixed-shift correction-prefix family for every
    positive fixed shift.
- Perron/B5a lane is validated and pushed through `45d39d0`
  (`proofdebt/20260429-perron-b5a`):
  - Commit: `Split Perron off-boundary Davenport envelope`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  - Result: the Davenport envelope is split into singular and smooth
    components with a component-combination theorem feeding the cutoff route.
  - Remaining Perron atoms: prove the smooth component at
    `Cm * (x / T) * (Real.log x)^2`, then close the singular
    reciprocal-log/distance summation.
- RS/Gabcke lane is validated and pushed through `c482eaf`
  (`proofdebt/20260429-rs-gabcke`):
  - Commit: `Close Gabcke shifted fill points`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp`.
  - Result: the local-function equality route is reduced to the
    off-filled-points raw trig identity for `standardGabckeRawPsi (x + 1/4)`.
  - Remaining RS/Gabcke atom:
    `StandardGabckeRemovableCandidateQuarterShiftedRawTrigIdentityProp`.
- Current live atoms:
  - Atkinson: all-positive fixed-shift correction-prefix family or shifted
    stationary-phase target remainder.
  - Perron/B5a: smooth Davenport-envelope component, then singular component.
  - Pi/Phase: `InhomogeneousPhaseFitWithFixedHeightPerronErrorHyp`.
  - RS/Gabcke: shifted raw trig identity.

## Overnight 2026-04-29 Twenty-Ninth Pass Status

- Pi/Phase lane is validated and pushed through `85b1f27`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Reduce pi fixed-height phase fit to window`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Result: `InhomogeneousPhaseFitWithFixedHeightPerronErrorHyp` is reduced
    to `FixedHeightPerronErrorPhaseWideWindowHyp` plus
    `FiniteZeroInhomogeneousPhaseRelativelyDenseHyp`.
  - Interpretation: the arbitrary `targetPhase` quantifier is now exposed as
    the real blocker. The public route should avoid turning arbitrary-target
    finite-zero relative density into a main-chain prerequisite when the
    corrected proof path only needs target/anti-specific phase fits.
  - Next Pi move: build target/anti-specific fixed-height phase-fit
    classes/bridges using the existing relation-compatible target/anti
    finite-zero payloads, then route those into corrected phase-coupling and
    provider construction.
- Current live atoms:
  - Atkinson: all-positive fixed-shift correction-prefix family or shifted
    stationary-phase target remainder.
  - Perron/B5a: smooth Davenport-envelope component, then singular component.
  - Pi/Phase: target/anti-specific fixed-height phase-fit bridge, avoiding
    arbitrary-target relative density as a public-path blocker.
  - RS/Gabcke: shifted raw trig identity.

## Overnight 2026-04-29 Thirtieth Pass Status

- Atkinson lane is validated and pushed through amended commit `4e0ef17`
  (`proofdebt/20260429-atkinson-provider`):
  - Commit: `Reduce Atkinson fixed shifts to absolute correction prefix`.
  - Coordinator repair: removed a redundant `ring` after `field_simp` had
    already closed the fixed-shift scale equality.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Result: the all-positive fixed-shift correction-prefix family now reduces
    to an absolute fixed-shift prefix atom. The `1 / j` scale is preserved
    because the fixed-shift constant may depend on the positive shift `j`,
    avoiding unsafe deweighting or phase-weight division.
  - Remaining Atkinson atoms:
    - shifted-interval stationary-phase target remainder;
    - absolute fixed-shift correction-prefix atom for each positive shift:
      `∑ n ∈ Finset.Ico (j - 1) (m + 1),
        ‖atkinsonResonantShiftedCorrectionTerm n j‖
        ≤ A_j * Real.sqrt (((m + j : ℕ) : ℝ) + 1)`.
- Current live atoms:
  - Atkinson: shifted stationary-phase target remainder and absolute
    fixed-shift correction-prefix atom.
  - Perron/B5a: smooth Davenport-envelope component, then singular component.
  - Pi/Phase: target/anti-specific fixed-height phase-fit bridge.
  - RS/Gabcke: shifted raw trig identity.

## Overnight 2026-04-29 Thirty-First Pass Status

- Perron/B5a lane is validated and pushed through amended commit `3948c63`
  (`proofdebt/20260429-perron-b5a`):
  - Commit: `Close Perron off-boundary smooth envelope`.
  - Coordinator repair: fixed strict denominator positivity, removed a
    redundant post-`field_simp` `ring`, and normalized the nonzero branch of
    the reciprocal-weight nonnegativity proof.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  - Result: the smooth Davenport-envelope component is closed at the honest
    `x / T` scale through `Σ Λ(n) / n`.
  - Remaining Perron atom: singular Davenport-envelope component at
    `Cs * (x / T) * (Real.log x)^2`.
- Pi/Phase lane is validated and pushed through `9617ab1`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Split pi fixed-height target anti route`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Result: the corrected route now uses target/anti-specific fixed-height
    phase-fit classes and relation-compatible target/anti finite-zero data.
    The arbitrary-target fixed-height phase-fit class is no longer the
    preferred public path.
  - Remaining Pi atom: `FixedHeightPerronErrorPhaseWideWindowHyp`, the
    same-height fixed Perron-error/tower window for a supplied radius function.
- RS/Gabcke lane is validated and pushed through `200046a`
  (`proofdebt/20260429-rs-gabcke`):
  - Commit: `Reduce Gabcke shifted raw trig identity`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp`.
  - Result: shifted raw trig identity is reduced to numerator and denominator
    trig atoms plus a proved sign-cancellation bridge.
  - Remaining RS/Gabcke atoms:
    `StandardGabckeQuarterShiftedRawNumeratorTrigProp` and
    `StandardGabckeQuarterShiftedRawDenominatorTrigProp`.
- Current live atoms:
  - Atkinson: shifted stationary-phase target remainder and absolute
    fixed-shift correction-prefix atom.
  - Perron/B5a: singular Davenport-envelope component.
  - Pi/Phase: `FixedHeightPerronErrorPhaseWideWindowHyp`.
  - RS/Gabcke: shifted raw numerator/denominator trig atoms.

## Overnight 2026-04-29 Thirty-Second Pass Status

- Atkinson lane is validated and pushed through `e84388b`
  (`proofdebt/20260429-atkinson-provider`):
  - Commit: `Reduce Atkinson correction atom to pointwise fixed shifts`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Result: the absolute fixed-shift correction-prefix atom now follows from
    a pointwise fixed-shift correction majorant against `atkinsonModeWeight`.
    This keeps the shift-dependent constant explicit and avoids any
    phase-weight-to-unweighted division.
  - Remaining Atkinson atoms:
    - shifted-interval stationary-phase target remainder;
    - pointwise fixed-shift correction majorant:
      `∀ j ≥ 1, ∃ B_j > 0, ∀ n,
        ‖atkinsonResonantShiftedCorrectionTerm n j‖
          ≤ B_j * atkinsonModeWeight (n + j)`.
- Perron/B5a lane is validated and pushed through amended commit `d96ff88`
  (`proofdebt/20260429-perron-b5a`):
  - Commit: `Reduce Perron singular envelope to distance weight`.
  - Coordinator repair: normalized the nonzero branch of the reciprocal-weight
    nonnegativity proof, fixed the finite-sum distribution direction, aligned
    the additive inequality order, and moved the singular-distance wrapper
    below the component helper it calls.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  - Result: the singular Davenport-envelope component is reduced to a
    pointwise reciprocal-log comparison plus a finite off-boundary
    distance-weight summation bound.
  - Remaining Perron atoms:
    - distance-weight summation:
      `perronKernelOffBoundaryDistanceWeight x T ≤ Cd * (Real.log x)^2`
      for `x ≥ 2`, `2 ≤ T`, `T ≤ 16`;
    - pointwise reciprocal-log comparison into the split
      `Λ(n)/n + Λ(n)/(x-n)` term.
- Current live atoms:
  - Atkinson: shifted stationary-phase target remainder and pointwise
    fixed-shift correction majorant.
  - Perron/B5a: distance-weight summation and pointwise reciprocal-log
    comparison.
  - Pi/Phase: `FixedHeightPerronErrorPhaseWideWindowHyp`.
  - RS/Gabcke: shifted raw numerator/denominator trig atoms.

## Overnight 2026-04-29 Thirty-Third Pass Status

- Pi/Phase lane is validated and pushed through `01951b3`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Adapt pi fixed-height window from threshold window`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Result: `FixedHeightPerronErrorPhaseWideWindowHyp` is reduced to the
    same-height `PerronThresholdTowerPhaseWideWindowHyp`, and the corrected
    Perron-only route now packages through this threshold-window adapter.
  - Remaining Pi atom: same-height threshold tower/window source, likely via
    `PerronThresholdTowerWideDominationHyp` or its log-budget leaves.
- RS/Gabcke lane is validated and pushed through `7f6a2e7`
  (`proofdebt/20260429-rs-gabcke`):
  - Commit: `Close Gabcke denominator trig shift`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp`.
  - Result: `StandardGabckeQuarterShiftedRawDenominatorTrigProp` is closed
    by the local quarter-shift trig normalization.
  - Remaining RS/Gabcke atom:
    `StandardGabckeQuarterShiftedRawNumeratorTrigProp`.
- Current live atoms:
  - Atkinson: shifted stationary-phase target remainder and pointwise
    fixed-shift correction majorant.
  - Perron/B5a: distance-weight summation and pointwise reciprocal-log
    comparison.
  - Pi/Phase: same-height `PerronThresholdTowerPhaseWideWindowHyp` source.
  - RS/Gabcke: shifted raw numerator trig atom.

## Overnight 2026-04-29 Thirty-Fourth Pass Status

- Atkinson lane is validated and pushed through `3901947`
  (`proofdebt/20260429-atkinson-provider`):
  - Commit: `Reduce Atkinson pointwise correction to normalized integral`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Result: the pointwise fixed-shift correction majorant now reduces to the
    normalized fixed-shift correction atom
    `∀ j ≥ 1, ∃ D_j > 0, ∀ n,
      ‖atkinsonNormalizedShiftedCorrectionTerm n j‖ ≤ D_j`.
  - Remaining Atkinson atoms:
    - normalized fixed-shift correction bound above;
    - shifted-interval stationary-phase target remainder.
- Perron/B5a lane is validated and pushed through `4fdd92a`
  (`proofdebt/20260429-perron-b5a`):
  - Commit: `Close Perron singular pointwise split`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  - Result: the pointwise reciprocal-log split is closed. The singular
    Davenport route now depends only on the finite distance-weight summation.
  - Remaining Perron atom:
    `∃ Cd > 0, ∀ x T, x ≥ 2 → 2 ≤ T → T ≤ 16 →
      perronKernelOffBoundaryDistanceWeight x T
        ≤ Cd * (Real.log x)^2`.
- Current live atoms:
  - Atkinson: normalized fixed-shift correction bound and shifted
    stationary-phase target remainder.
  - Perron/B5a: finite distance-weight summation bound.
  - Pi/Phase: same-height `PerronThresholdTowerPhaseWideWindowHyp` source.
  - RS/Gabcke: shifted raw numerator trig atom.

## Overnight 2026-04-29 Thirty-Fifth Pass Status

- RS/Gabcke lane is validated and pushed through `a85975c`
  (`proofdebt/20260429-rs-gabcke`):
  - Commit: `Close Gabcke numerator trig shift`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp`.
  - Result: the numerator trig atom is closed, and the raw trig identity plus
    quarter local-function equality are now proved by the local normalization
    route.
  - Remaining RS/Gabcke atom:
    `StandardGabckeRemovableCandidateQuarterTranslationThirdDerivativeProp`.
- Pi/Phase lane is validated and pushed through `90558bd`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Expose pi wide-domination route`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Result: the same-height threshold-window source is reduced to
    `PerronThresholdTowerWideDominationHyp`.
  - Remaining Pi atom:
    same-height arbitrary-radius domination of
    `Real.log (max X (perronThreshold hRH T) + 1) + radius T ε + 1`
    by the selected tower cap.
- Current live atoms:
  - Atkinson: normalized fixed-shift correction bound and shifted
    stationary-phase target remainder.
  - Perron/B5a: finite distance-weight summation bound.
  - Pi/Phase: `PerronThresholdTowerWideDominationHyp`.
  - RS/Gabcke:
    `StandardGabckeRemovableCandidateQuarterTranslationThirdDerivativeProp`.

## Overnight 2026-04-29 Thirty-Sixth Pass Status

- Perron/B5a lane is validated and pushed through `0e72947`
  (`proofdebt/20260429-perron-b5a`):
  - Commit: `Close Perron off-boundary distance weight`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronTruncationInfra`.
  - Result: the finite off-boundary distance-weight summation is no longer
    left as a pure `O((log x)^2)` atom. The branch now proves the
    scale-correct linear handoff through `chebyshevPsi x`, keeping the
    explicit `x / T` scale and avoiding the false macroscopic small-T route.
  - Remaining Perron atom:
    route `small_T_weighted_kernel_cutoff_linear_bound` through the existing
    finite Perron-kernel linear handoff and check downstream truncation/residue
    consumption without reintroducing the false pure `O((log x)^2)` provider.
- Atkinson lane is validated and pushed through `f8ee10b`
  (`proofdebt/20260429-atkinson-provider`):
  - Commit: `Reduce Atkinson normalized correction to eventual bound`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.AtkinsonFormula`.
  - Result: the all-`n` normalized fixed-shift correction atom is reduced to
    the eventual fixed-shift form
    `∀ j ≥ 1, ∃ D_j > 0, ∃ N_j, ∀ n ≥ N_j,
      ‖atkinsonNormalizedShiftedCorrectionTerm n j‖ ≤ D_j`.
  - Remaining Atkinson atoms:
    - eventual normalized fixed-shift correction bound above;
    - shifted-interval stationary-phase target remainder.
- Current live atoms:
  - Atkinson: eventual normalized fixed-shift correction bound and shifted
    stationary-phase target remainder.
  - Perron/B5a: finite Perron-kernel linear handoff from the scale-correct
    small-T weighted cutoff bound.
  - Pi/Phase: `PerronThresholdTowerWideDominationHyp`.
  - RS/Gabcke:
    `StandardGabckeRemovableCandidateQuarterTranslationThirdDerivativeProp`.

## Overnight 2026-04-29 Thirty-Seventh Pass Status

- RS/Gabcke lane is validated and pushed through `0e42226`
  (`proofdebt/20260429-rs-gabcke`):
  - Commit: `Close Gabcke quarter translation derivative`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.SiegelSaddleExpansionHyp`.
  - Result: the quarter-translation third-derivative atom is closed, together
    with the local-coordinate transfer helper.
  - Remaining RS/Gabcke atom:
    `StandardGabckeQuarterLocalSecondDerivativeHasDerivAtProp`, equivalently
    the local third-derivative formula at `x = 0`.
- Pi/Phase lane is validated and pushed through `cd3b46d`
  (`proofdebt/20260429-pi-phase`):
  - Commit: `Split pi wide domination log budget`.
  - Validation passed:
    `lake build Littlewood.Aristotle.Standalone.PerronExplicitFormulaProvider
      Littlewood.Aristotle.Standalone.RHPiCorrectedPerronOnlyRoute
      Littlewood.Aristotle.Standalone.RHPiPhaseCouplingFromExactSeedBridge`.
  - Result: `PerronThresholdTowerWideDominationHyp` is reduced to the
    separated log-budget source `PerronThresholdTowerWideLogBudgetHyp`.
  - Remaining Pi atom:
    for every positive supplied radius function, choose the same `T, ε` so
    both `Real.log (max X (perronThreshold hRH T) + 1)` and `radius T ε + 1`
    fit within half of the same double-exponential tower scale.
- Current live atoms:
  - Atkinson: eventual normalized fixed-shift correction bound and shifted
    stationary-phase target remainder.
  - Perron/B5a: finite Perron-kernel linear handoff from the scale-correct
    small-T weighted cutoff bound.
  - Pi/Phase: `PerronThresholdTowerWideLogBudgetHyp`.
  - RS/Gabcke: local second-derivative differentiability / third-derivative
    formula at `x = 0`.
