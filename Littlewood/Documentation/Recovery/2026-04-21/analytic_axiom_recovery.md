# Analytic Axiom Recovery Checkpoint

Date: 2026-04-28 CDT

Branch: `recovery/provider-forensics-2026-04-21`

Baseline before de-axiomatization: `bd6c8f3`

## Decision

The analytic provider shim is not part of the final proof policy.  The project
frontier should be Lean standard axioms plus the accepted first-zero witnesses,
with remaining analytic number theory exposed as explicit theorem/class proof
debt.

## Evidence

- `AnalyticAxioms.lean` was introduced by commit `7dcf5d1` as a recovery shim.
- The parent of that commit had `B1B3AnalyticDeepLeaf.lean` using class
  assumptions and documented `sorry` debt, without importing the shim.
- The iCloud `Documents/Git/Littlewood_Proof` copy has a later no-provider stub
  for `AnalyticAxioms.lean`, matching this recovery direction.

## Removed Providers

The stub no longer installs global instances for:

- `SiegelSaddleExpansionHyp`
- `HadamardXiCanonicalProductCriticalZeros`
- `HadamardXiNearZeroSumBound`
- `HadamardXiFarZeroSumBound`
- `ShiftedRemainderContourDecompFromLogDerivLargeTHyp`

These must be proved through the tracked theorem/class leaves.  Temporary
`sorry` is acceptable while recovering the old frontier; hidden private analytic
axioms are not.

## Validation Protocol

Run validations serially.  Do not run more than one Lean/Lake job at a time.

- active axiom scan
- analytic shim import scan
- focused `B1B3AnalyticDeepLeaf.lean`
- focused `DeepBlockersResolved.lean`
- public `LittlewoodPsi` import probe
- public `LittlewoodPi` import probe
- focused Lake module builds for the touched/strict public surfaces

## Validation Result

Completed serially on 2026-04-28:

- active axiom scan: only the accepted first-zero pair plus unimported
  Chebyshev quarantine declarations remain
- analytic shim import scan: no public-path import or qualified use remains
- `lake env lean Littlewood/Aristotle/Standalone/B1B3AnalyticDeepLeaf.lean`
  passed with existing unused-section-variable warnings
- `lake env lean Littlewood/Aristotle/Standalone/DeepBlockersResolved.lean`
  passed with existing unused-section-variable warnings
- `import Littlewood.Main.LittlewoodPsi` passed
- `import Littlewood.Main.LittlewoodPi` passed
- `lake build Littlewood.Aristotle.Standalone.AnalyticAxioms` passed
- `lake build Littlewood.Aristotle.Standalone.B1B3AnalyticDeepLeaf` passed
- `lake build Littlewood.Aristotle.Standalone.DeepBlockersResolved` passed
- `lake build Littlewood.Main.LittlewoodPsi` passed
- `lake build Littlewood.Main.LittlewoodPi` passed

No bare `lake build` was run during this checkpoint.
