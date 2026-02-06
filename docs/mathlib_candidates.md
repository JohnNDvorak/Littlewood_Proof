# Mathlib Contribution Candidates

**Date**: 2026-02-04

## Summary

| File | Lines | Sorries | Readiness | Target Module |
|------|-------|---------|-----------|---------------|
| OmegaNotation.lean | 264 | 0 | HIGH | Mathlib.Analysis.Asymptotics |
| LogarithmicIntegral.lean | 867 | 0 | HIGH | Mathlib.Analysis.SpecialFunctions |
| HardyZRealV2.lean | 322 | 0 | MEDIUM | Mathlib.NumberTheory (with context) |
| ChebyshevFunctions.lean | 147 | 0 | LOW | Already in Mathlib |
| SchmidtTheorem.lean | 227 | 0 | LOW | Hypothesis-based, no actual proofs |

## HIGH Readiness

### OmegaNotation.lean (Littlewood/Basic/)

Defines `IsOmegaPlus`, `IsOmegaMinus`, `IsOmegaPlusMinus` for Omega-plus-minus
asymptotic notation. 4 definitions, 16 theorems, 0 sorries.

**Why Mathlib wants this:** Mathlib has `IsBigO`, `IsLittleO`, but lacks Omega-plus-minus
notation used throughout analytic number theory (Littlewood, Hardy, Schmidt).

**Work needed:** Notation design review (scoped vs global), placement discussion.

### LogarithmicIntegral.lean (Littlewood/Basic/)

Defines `logarithmicIntegral x = integral from 2 to x of dt/log(t)`. 29 theorems including
integration by parts, asymptotic expansion, calculus API (derivative, continuity),
and comparison bounds. 0 sorries.

**Why Mathlib wants this:** Classical special function, essential for PNT statements.
Currently absent from Mathlib.

**Work needed:** Resolve `offsetLogarithmicIntegralConstant` (currently approximate decimal),
remove `PrimeNumberTheoremAnd` dependency for core API.

## MEDIUM Readiness

### HardyZRealV2.lean (Littlewood/Aristotle/)

Defines Hardy Z-function `Z(t) = exp(i*theta(t)) * zeta(1/2 + it)`. 22 theorems including
`hardyZV2_real` (Z(t) is real-valued), zero equivalence with zeta, continuity. 0 sorries.

**Why Mathlib might want this:** Hardy Z-function is important for studying zeta zeros.
`hardyZV2_real` is a non-trivial result.

**Barrier:** Very specialized; needs broader analytic number theory context to justify.

## LOW Readiness

### ChebyshevFunctions.lean

Wrappers around Mathlib's existing `Chebyshev.psi` and `Chebyshev.theta`. Adds asymptotic
lemmas but depends on `PrimeNumberTheoremAnd`. Individual lemmas could be upstreamed
to `Mathlib.NumberTheory.Chebyshev` but the file itself is not a candidate.

### SchmidtTheorem.lean

All 15 theorems are trivial hypothesis wrappers (`simpa using HypClass.field`).
Not contributable until hypotheses are proved.
