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
| 1 | `proofdebt/20260428-atkinson-large-j` | active, pushed through `70078bf` | public import probes after provider closure |
| 2 | `proofdebt/20260428-perron-b5a` | active, pushed through `32eaeea` | public import probes after provider closure |
| 3 | `proofdebt/20260428-pi-phase` | active, pushed through `4a89847` | public import probes after provider closure |
| 4 | `proofdebt/20260428-rs-gabcke` | active, pushed through `d1ff2f9` | public import probes after provider closure |

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
- Coordinator stopped one non-coordinator `lake env lean` process in the
  Atkinson worktree and re-issued the hard rule: agents must not run `lake`,
  `lake env lean`, `lean`, or any focused build/check themselves.
- Current live atoms:
  - Atkinson: zero-model approximation and explicit target matching toward
    `atkinson_blockMode_stationaryPhase_of_zero_model_and_target`, then
    packaging `AtkinsonShiftedInversePhaseCellPrefixBoundHyp`.
  - Perron/B5a: punctured-window decaying kernel estimate, off-boundary
    estimate, and bounded-height residue extraction.
  - Pi/Phase: realized phase-radius tower domination and zeta finite-zero
    compatibility for the target/anti-target leaves.
  - RS/Gabcke: define the correctly phase/parameter-normalized `stdLead`,
    prove `StandardGabckeLocalLeadingNormalizationProp stdLead`, then prove
    `SiegelStationaryPhaseCoefficientIdentityProp C` and
    `SiegelStationaryPhaseCoefficientBoundProp C`.
- Next coordinator action: wait for the redeployed lane agents, validate any
  returning commits serially, and only run public import probes after a lane
  closes a public-path provider rather than another conditional reduction.
