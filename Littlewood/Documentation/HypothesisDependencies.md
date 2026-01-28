# Hypothesis Class Dependencies

## Critical Path (must prove for full formalization)

### Level 0: Already Proved
- `ZeroConjZeroHyp` ← `riemannZeta_conj` (ZeroCountingFunction.lean)
- `ZeroOneSubZeroHyp` ← `riemannZeta_one_sub` (Mathlib functional equation)

### Level 1: Close to Provable
- `OmegaPsiToThetaHyp` ← needs PartialSummation (2 sorries)
- `OmegaThetaToPiLiHyp` ← needs conversion formulas
- `LambdaFunctionalEqHyp` ← needs FunctionalEquation (1 sorry)

### Level 2: Medium Difficulty
- `ZeroCountingAsymptoticHyp` ← needs ZeroCounting (4 sorries)
- `ZeroCountingMainTermHyp` ← needs Riemann-von Mangoldt formula
- `MeanSquareHyp` ← needs MeanSquare (5 sorries)

### Level 3: Hard (Missing Infrastructure)
- `ExplicitFormulaPsiHyp` ← needs Perron (6 sorries) + contour integration
- `HardyInfiniteZerosHyp` ← needs Hardy theorem (deep)
- `ZeroFreeRegionHyp` ← needs de la Vallée-Poussin bounds

## Dependency Graph
```
littlewood_pi_li
    ├── littlewood_psi
    │       ├── schmidt_oscillation ← trigPoly_zero_iff_coeffs_zero ✅
    │       │       └── SchmidtNew.lean (sorry-free)
    │       ├── psi_explicit_formula ← ExplicitFormulaPsiHyp
    │       │       └── perron_formula ← (6 sorries in PerronFormula.lean)
    │       └── hardy_infinite_zeros ← (assumed)
    │               └── (deep - Hadamard product, functional equation)
    │
    ├── omega_psi_to_theta ← OmegaPsiToThetaHyp
    │       └── partial_summation ← (2 sorries in PartialSummation.lean)
    │
    └── omega_theta_to_pi_li ← OmegaThetaToPiLiHyp
            └── conversion formulas (assumed)
```

## File-to-Hypothesis Mapping

| Hypothesis Class | Primary File | Sorries | Status |
|-----------------|--------------|---------|--------|
| ExplicitFormulaPsiHyp | PerronFormula.lean | 6 | Blocked on contour integration |
| ExplicitFormulaPsiSmoothedHyp | PerronFormula.lean | - | Depends on above |
| ZeroCountingAsymptoticHyp | ZeroCounting.lean | 4 | Partially in ZeroCountingNew.lean |
| ZeroCountingMainTermHyp | ZeroCountingNew.lean | 0 | Assumes RiemannVonMangoldtProperty |
| OmegaPsiToThetaHyp | PartialSummation.lean | 2 | Close to completion |
| OmegaThetaToPiLiHyp | ConversionFormulas.lean | - | Infrastructure exists |
| WeightedAverageFormulaRHHyp | WeightedAverageFormula.lean | - | Assumed |
| AlignedSumLargeHyp | WeightedAverageFormula.lean | - | Assumed |
| ZeroConjZeroHyp | ZeroCountingFunction.lean | 0 | **PROVED** |
| ZeroOneSubZeroHyp | ZeroCountingFunction.lean | 0 | **PROVED** |

## Aristotle Files Supporting Hypotheses

### Sorry-Free Files (can potentially close hypotheses)
- SchmidtNew.lean - Complete Schmidt oscillation theorem
- ZeroCountingNew.lean - N(T) main term, S(T) = O(log T)
- PiLiOscillation.lean - π-li oscillation lemmas
- PsiDominance.lean - ψ dominance lemmas
- TrigPolyIndependence.lean - Trigonometric independence
- HardyZRealV4.lean - Hardy Z function properties
- FunctionalEquationV2.lean - Corrected functional equation

### Files with Sorries (need work)
- PerronFormula.lean (6) - Critical for explicit formula
- MeanSquare.lean (5) - Mean square estimates
- ZeroCounting.lean (4) - Zero counting details
- PhragmenLindelof.lean (3) - Convexity bounds
- PartialSummation.lean (2) - Error term bounds
- FunctionalEquation.lean (1) - ξ properties (use V2 instead)
