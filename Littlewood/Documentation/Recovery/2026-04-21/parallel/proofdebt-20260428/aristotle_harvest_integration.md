# Aristotle Harvest Integration

Date: 2026-04-28 CDT

Launch ID: `proofdebt-20260428`

This file records the durable findings from the four finished Aristotle
sidecars. Raw result archives, prompt payloads, and runtime logs remain ignored
under `self_drive/` and are not committed.

## Integration Policy

- Treat Aristotle outputs as theorem-shaped sidecar research, not trusted code.
- Integrate exact reductions, failed routes, and smallest next theorem
  statements into the tracked recovery board and lane ledgers.
- Do not add active-source Lean files from the harvest unless they compile
  against the current branch and improve the public proof path.
- Do not commit API keys, raw logs, result zips, or downloaded full-repo
  snapshots.

## Finished Jobs

| Lane | Job | Classification | Integration |
| --- | --- | --- | --- |
| Atkinson | `b895c2cb-ccbc-4edc-b13a-8076b5be5eb6` | audit/reduction | Guardrails and next atoms recorded in the Atkinson ledger. |
| Perron/B5a | `43160ae0-78e7-4d7e-b8af-76332fd6c59f` | non-circular reduction | Guardrails and small-T/large-T split recorded in the Perron ledger. |
| Pi/Phase | `32a1df6a-be94-4cc2-81c3-05623533b222` | interface reduction | Reduction recorded as documentation; delivered Lean file was not added to active source. |
| RS/Gabcke | `381b8764-543a-4024-a84f-9a9f91be9eba` | audit/reduction | Reduction notes and lane guardrails recorded. |

## Atkinson

The direct target `atkinson_inversePhaseCorePrefix_bound_large_j` was not
closed. Aristotle identified four routes and the exact obstruction:

- Contracting induction needs both a log-free boundary row bound and a true
  successor contraction with factor `< 1`. The existing Abel-style successor
  contraction has factor `8`, so it cannot be tuned into a contraction without
  using the multiplicative `1 / stepCoeff` structure.
- Direct Abel decomposition is circular for this target.
- The no-log complete-block route is honest but depends on shifted-interval
  stationary-phase atoms.
- Automated search is not plausible for this oscillatory sum.

Smallest route-1 leaves:

```text
Log-free boundary row:
  ||sum_{n<M} boundary_term(n,j)|| <= C_bdry * sqrt(M+j+1) / j

Successor tail contraction:
  tail(j+1) <= gamma * C_prev * sqrt(N+j+2)/(j+1), with gamma < 1
```

Current coordinator decision: keep Hooke on the no-log complete-block /
stationary-phase route unless a concrete route to the two contraction leaves
appears.

## Perron/B5a

Aristotle confirmed the right public-path shape:

- `shifted_remainder_bound_leaf` should be reduced to two independent
  hypotheses:
  `ShiftedRemainderSegmentBoundLargeTHyp` and
  `HadamardProductZeta.SmallTPerronBoundHyp`.
- Do not derive small-T Perron from `shifted_remainder_bound_atomic`; that is a
  circular provider route.
- Do not attempt to prove `perron_tail_bound_core` as stated.

Current lane work has already pushed past this first reduction and is now
working inside `PerronTruncationInfra.lean`. The live atom is the punctured
boundary-window kernel estimate after the exact-hit obstruction was split out
and validated.

## Pi/Phase

Aristotle delivered a proposed Lean file,
`PerronPhaseCouplingReduction.lean`, giving a direct Perron-to-`RhPiWitnessData`
interface. It was not added as active source:

- It is a sorry-backed reduction, not a provider closure.
- A standalone Lean check against the current branch failed because
  `RiemannHypothesis` is ambiguous between root and `ZetaZeros` namespaces.
- Adding it under `Littlewood/Aristotle/Standalone` would increase active
  source sorry debt without closing a public provider.

Durable reduction:

- Avoid `PerronPiApproxCompatibilityHyp` and `TruncatedExplicitFormulaPiHyp`.
  Their all-epsilon `pi_approx` route is false for the needed strength.
- Avoid the constant-1 `PerronSqrtErrorEventuallyAtHeightHyp` layer.
- The honest route is a pi-scale route: fixed Perron constants are absorbed by
  `piScale x = sqrt(x)/log(x) * lll(x)`.

Honest missing inputs:

```text
PiPerronOBoundHyp:
  for each T >= 2, the pi-level explicit formula error is
  O_T(sqrt(x) / log(x)).

FiniteZeroInhomogeneousPhaseWindowHyp:
  bounded-window Kronecker approximation for the finite zero set.

Tower/lll absorption:
  convert the O_T bound into piScale domination above the Perron threshold.
```

Current coordinator decision: keep Planck on the already-validated
target/anti realized phase-radius geometry and zeta finite-zero compatibility
route; do not introduce a new active module for the harvested reduction yet.

## RS/Gabcke

Aristotle confirmed the RS/Gabcke infrastructure is already maximally
decomposed:

- `SiegelSaddleExpansionHyp` is the open class boundary.
- `GabckePhaseCouplingHyp` is downstream wrapper wiring and is already proved
  from the signed fields of `SiegelSaddleExpansionHyp`.
- Exact k-independence is a false route. The correct route is adjacent
  antitonicity.

Smallest leaves:

```text
SiegelWeightedProfileBoundProp:
  the Gabcke Satz 1 absolute weighted-profile bound.

GabckeNormalizedCoefficientProp:
  nonnegativity and adjacent antitonicity of the normalized signed profile.
```

Current lane work has refined this further to a standard Gabcke normalization
bridge. The live atom is to define the correctly phase/parameter-normalized
`stdLead` and prove `StandardGabckeLocalLeadingNormalizationProp stdLead`.

## Coordinator Actions Completed

- Harvested all four finished sidecars.
- Read and triaged each `ARISTOTLE_SUMMARY.md`.
- Ran a single standalone Lean check on the Pi reduction file; it failed on
  namespace ambiguity, so the file remains out of active source.
- Integrated durable findings into the tracked lane ledgers and community
  board.
- Re-issued lane-specific findings to the active agents so they do not repeat
  failed routes.
