# Sorry Closure Log

*Updated 2026-01-31*

## Closed Sorries

| Date | File | Sorry | Method | New Count |
|------|------|-------|--------|-----------|
| 2026-01-31 | ZetaConvexityStrip.lean | `(s-1)·ζ(s) → 1` as s→1 | `exact riemannZeta_residue_one` (Mathlib) | 71 |
| 2026-01-30 | RiemannVonMangoldtV2.lean | Various | Direct proof | 72 |
| 2026-01-30 | PsiThetaBound.lean | Various | Direct proof | — |
| 2026-01-30 | ZeroFreeRegionV2.lean | Various | Direct proof | — |

## Current Sorry Inventory (71 total)

### Assumptions.lean (58 sorries)
Hypothesis class instances for classical analytic number theory theorems.
These are *intentional* — they encode the mathematical structure while
the proofs are developed separately.

### Aristotle Files (12 sorries across 6 files)

| File | Line | Sorry | Nature | Closeable? |
|------|------|-------|--------|------------|
| MeanSquare.lean | 213 | Off-diagonal integral bound | Needs analytic argument | Aristotle |
| MeanSquare.lean | 220 | normSq decomposition | Needs algebraic identity | Aristotle |
| MeanSquare.lean | 237 | Main mean square theorem | Needs above two | Aristotle |
| ZeroCounting.lean | 114 | `xi_Mathlib_differentiable` | **DEPRECATED/FALSE** — xi_Mathlib is not differentiable at s=0,1 | N/A |
| ZeroCounting.lean | 123 | Argument principle for N(T) | Needs Cauchy integral theorem | Aristotle |
| ZeroCounting.lean | 135 | N(T) asymptotic O(log T) | Needs Stirling + arg principle | Aristotle |
| PhragmenLindelof.lean | 138 | Critical line bound | Needs Stirling approximation | Aristotle |
| PhragmenLindelof.lean | 156 | Convexity bound | Needs Phragmén-Lindelöf theory | Aristotle |
| PhragmenLindelof.lean | 170 | Stirling for Gamma | Needs Stirling formula | Aristotle |
| PartialSummation.lean | 225 | ψ→π-li oscillation transfer | Needs Abel summation | Aristotle |
| PerronContourIntegralsV2.lean | 422 | Cauchy integral for rectangle | Needs Mathlib Cauchy integral | Aristotle |
| HardyZConjugation.lean | 111 | Mellin transform identity | Needs Mellin theory | Aristotle |

### Bridge Files (1 sorry)

| File | Line | Sorry | Nature |
|------|------|-------|--------|
| HardyAssemblyAttempt.lean | 161 | Hardy assembly exploration | Intentional placeholder |

### Core Lemmas (1 sorry)

| File | Line | Sorry | Nature |
|------|------|-------|--------|
| LandauLemma.lean | 379 | Pringsheim/identity theorem | Deep analysis |

## Wiring Analysis Results

### Investigated but NOT Closeable

| Assumption | Investigated Source | Why Not |
|------------|-------------------|---------|
| ZetaLogDerivPoleHyp | LaurentExpansion.lean | LaurentExpansion proves -ζ'/ζ residue at s=1 only; assumption needs behavior at *arbitrary* zeros |
| ChebyshevErrorBoundThetaHyp | ThetaLinearBoundV2.lean | ThetaLinearBoundV2 proves θ(n) ≤ Cn; assumption needs \|ψ(x)-x\| bound (different function) |
| ZeroCountingAsymptoticHyp | ZeroCountingNew.lean | ZeroCountingNew uses local NZeros type; needs bridge to zetaZeroCount |
| ZeroCountingTendstoHyp | ZeroCountingNew.lean | Same type mismatch issue |

### Potentially Closeable (Need Investigation)

| Assumption | Source | Issue |
|------------|--------|-------|
| ZeroCountingAsymptoticHyp | NAsymptotic.lean + ZeroCountingBridge.lean | Bridge exists for NZeros types; need to check if full chain compiles |
