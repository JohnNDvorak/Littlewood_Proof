# B2 Scaling Risk Note (March 4, 2026)

## Context
File: `Littlewood/Aristotle/Standalone/B2StationaryWindowLeaves.lean`

Open delegated leaf:
- `hardyCosExpTailBound_sorry` (bridged to `stationaryTailClass_sorry`)

## Critical warning
Avoid spending effort trying to close B2 through the existing class route that
requires
`HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp`.

That class asks for
`|phase'(t)| >= m / sqrt(n+1)` on tail support.

With
- `phase(t) = hardyTheta t - t*log(n+1)`
- tail start `t = hardyStart n + sqrt(n+1)`
- `hardyStart n ~ 2*pi*(n+1)^2`

heuristically
`phase''(t) ~ 1/(2t) ~ 1/(n+1)^2`
and near stationary point
`phase'(t) ~ phase'' * sqrt(n+1) ~ 1/(n+1)^(3/2)`.

So `1/sqrt(n+1)` looks too strong by a factor `(n+1)`.

## Practical implication
For B2, prioritize a **direct stationary-phase tail integral bound**
(`||∫ tail hardyExpPhase|| <= B*sqrt(n+1)`) rather than forcing
class synthesis through `HardyExpPhaseDerivAbsLowerSqrtModeOnTailSupportHyp`.

## Suggested target
Prove directly (in a standalone module):

```lean
∃ B > 0, ∀ n T, T ≥ 2 -> hardyStart n + Real.sqrt (n+1) ≤ T ->
  ‖∫ t in (hardyStart n + Real.sqrt (n + 1))..T,
      HardyFirstMomentWiring.hardyExpPhase n t‖ ≤ B * Real.sqrt (n+1)
```

then instantiate
`HardyExpPhaseStationaryTailIntegralSqrtModeBoundOnSupportHyp` from that.
