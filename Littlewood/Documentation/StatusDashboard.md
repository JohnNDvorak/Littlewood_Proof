# Littlewood Project Status Dashboard

*Updated 2026-01-31 by Claude Code*

## Quick Stats

| Metric | Value |
|--------|-------|
| Total Lean Files | ~148 |
| Total Lines | ~29,000 |
| Total Sorries (lake build) | **72** (58 assumptions + 14 other) |
| Assumption Sorries | 58 |
| Other Sorries | 14 (12 Aristotle + 1 Bridge + 1 CoreLemma) |
| Dependency Sorries | 3 (PrimeNumberTheoremAnd/Wiener.lean, not ours) |

## Aristotle Files

| Status | Count | Percentage |
|--------|-------|------------|
| Total active | 87 | 100% |
| Sorry-free | 81 | 93% |
| With sorries | 6 | 7% |

## Sorry Breakdown (post ZetaConvexityStrip fix)

### Assumptions.lean (58 sorries)
Hypothesis class instances for classical theorems not yet in Mathlib.
See Assumptions.lean for the categorized list.

### Aristotle Files (12 sorries across 6 files)

| File | Sorries | Nature |
|------|---------|--------|
| MeanSquare.lean | 3 | Off-diagonal bound, normSq decomp, main theorem |
| ZeroCounting.lean | 3 | 1 DEPRECATED (xi diff), 2 arg principle + RvM |
| PhragmenLindelof.lean | 3 | Critical line bound, convexity, Stirling |
| PartialSummation.lean | 1 | ψ→π-li oscillation transfer |
| PerronContourIntegralsV2.lean | 1 | Cauchy integral for rectangle |
| HardyZConjugation.lean | 1 | Mellin transform identity |

### Other (1 sorry)

| File | Sorries | Nature |
|------|---------|--------|
| CoreLemmas/LandauLemma.lean | 1 | Pringsheim/identity theorem |

## Recently Closed Sorries

| File | Method | Date |
|------|--------|------|
| ZetaConvexityStrip.lean | riemannZeta_residue_one (Mathlib) | 2026-01-31 |
| RiemannVonMangoldtV2.lean | Direct proof | 2026-01-30 |
| PsiThetaBound.lean | Direct proof | 2026-01-30 |
| ZeroFreeRegionV2.lean | Direct proof | 2026-01-30 |

## Critical Path: Hardy's Theorem

| Component | Status | Source |
|-----------|--------|--------|
| Z real-valued | ✅ | HardyZRealV2.hardyZV2_real |
| Z continuous | ✅ | HardyZRealV2.continuous_hardyZV2 |
| Z zeros ↔ ζ zeros | ✅ | HardyZRealV2.hardyZV2_zero_iff_zeta_zero |
| \|Z\| = \|ζ\| | ✅ | HardyZRealV2.hardyZV2_abs_eq_zeta_abs |
| Completed zeta real on crit line | ✅ | CompletedZetaCriticalLine |
| Z measurable | ✅ | HardyZMeasurability |
| Z integrable | ✅ | HardyZMeasurability.hardyZ_integrable |
| Integral-sum interchange | ✅ | HardyZMeasurability.hardySum_integral_eq |
| Definition map (all variants equiv) | ✅ | HardyZDefinitionMap |
| BuildingBlocks template | ✅ | HardyBuildingBlocksInstance (4/6 fields) |
| Mean square lower bound | ⏳ | **WAITING ON ARISTOTLE** |
| First moment upper bound | ⏳ | **WAITING ON ARISTOTLE** |
| Final assembly | ⏳ | Needs mean square + first moment |

## Bridge Infrastructure

| File | Sorries | Purpose |
|------|---------|---------|
| AristotleBridges.lean | 0 | Bridge lemmas |
| HypothesisInstances.lean | 0 | Proved instances |
| AristotleHypothesisConnections.lean | 0 | Documentation |
| AristotleWiring.lean | 0 | Master wiring |
| ZeroCountingBridge.lean | 0 | NZeros bridges |
| ThetaEquivalence.lean | 0 | theta ℝ→ℝ ↔ ℕ→ℝ |
| WiringTests.lean | 0 | Compilation tests |
| HardyZTransfer.lean | 0 | Hardy Z type transfer |
| HardyAssemblyAttempt.lean | 1 | Hardy assembly exploration |
| HardyBuildingBlocksInstance.lean | 0 | BuildingBlocks template |
| HardyZDefinitionMap.lean | 0 | Definition equivalences |
| HardyCriticalLineWiring.lean | 0 | Pre-wired for Hardy |
| HardyZUnified.lean | 0 | Unified Hardy Z exports |
| HardyChainTest.lean | 0 | Hardy chain integration test |

## Wiring Analysis Results

| Assumption | Investigated Source | Result |
|------------|-------------------|--------|
| ZetaLogDerivPoleHyp | LaurentExpansion.lean | NOT closeable (only s=1, need arbitrary zeros) |
| ChebyshevErrorBoundThetaHyp | ThetaLinearBoundV2.lean | NOT closeable (θ vs ψ mismatch) |
| ZeroCountingAsymptoticHyp | ZeroCountingNew.lean | Needs NZeros type bridge |
| ZeroCountingTendstoHyp | ZeroCountingNew.lean | Same type mismatch |

## Pending Aristotle Returns

| Prompt | Purpose | Priority |
|--------|---------|----------|
| MeanSquareLowerBound | ∫\|Z\|² ≥ c·T·log T | CRITICAL |
| HardyZIntegralBound | \|∫Z\| ≤ C·T^{1/2+ε} | CRITICAL |
| HardyInfiniteZerosComplete | Final assembly | THE PRIZE |
