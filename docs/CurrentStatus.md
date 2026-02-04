# Littlewood Proof: Current Status

**Date**: 2026-02-03 (audited)

## Sorry Count Summary (from `lake build`)

| Location | Sorries | Notes |
|----------|---------|-------|
| Assumptions.lean | 57 | Hypothesis class instances (classical results not in Mathlib) |
| Bridge/ExplicitFormulaOscillation.lean | 1 | Oscillation extraction from explicit formula + Hardy zeros |
| Aristotle/ | 7 | Analytic number theory proofs across 4 files |
| CoreLemmas/LandauLemma.lean | 1 | Identity theorem (FALSE as stated, unused downstream) |
| **Total (project)** | **66** | Main proof chain: 0 sorries in proof terms |

Additionally: 3 sorries from PrimeNumberTheoremAnd dependency (69 total warnings).
Development/ files (not imported): not counted.

## Complete Dependency Tree

Both main theorems resolve with **no explicit typeclass parameters**:

```
littlewood_psi : ψ(x) - x = Ω±(√x)
  └── Schmidt.psi_oscillation_sqrt
      └── [PsiOscillationSqrtHyp]   ← auto-resolved
          └── PsiOscillationWiring.lean (0 sorry)
              └── [PsiOscillationFromCriticalZerosHyp]   ← auto-resolved
                  └── ExplicitFormulaOscillation.lean (1 SORRY)
                      ├── [HardyCriticalLineZerosHyp]   ← auto-resolved
                      │   └── HardyCriticalLineWiring.lean (0 sorry)
                      │       ├── [ZetaCriticalLineBoundHyp]     (SORRY in Assumptions.lean)
                      │       ├── [HardyFirstMomentUpperHyp]     (SORRY in Assumptions.lean)
                      │       └── HardyInfiniteZerosV2 (Aristotle, 0 sorry)
                      │           └── HardySetupV2Instance (0 sorry)
                      │               └── MeanSquareBridge (0 sorry)
                      │                   └── DiagonalIntegralBound (0 sorry)
                      │                       └── approx_functional_eq (1 SORRY in Aristotle)
                      └── [ExplicitFormulaPsiHyp]        (SORRY in Assumptions.lean)

littlewood_pi_li : π(x) - li(x) = Ω±(√x / log x)
  └── PiLiOscillationSqrtHyp.oscillation
      └── [PiLiOscillationSqrtHyp]   ← auto-resolved
          └── PsiToPiLiOscillation.lean (0 sorry)
              ├── [ThetaOscillationSqrtHyp]    (SORRY in Assumptions.lean)
              └── [OmegaThetaToPiLiHyp]        (SORRY in Assumptions.lean)
```

## Critical Path Sorries

These are the ONLY sorries that the main theorems actually depend on:

### For `littlewood_psi` (4 sorries):
| Sorry | Location | Mathematical Content | Difficulty |
|-------|----------|---------------------|------------|
| `ExplicitFormulaOscillation` | Bridge/ | ∞ critical-line zeros + explicit formula → Ω±(√x) | Hard |
| `ZetaCriticalLineBoundHyp` | Assumptions.lean | \|ζ(1/2+it)\| ≤ C\|t\|^{1/4+ε} (Phragmen-Lindelof) | Hard |
| `HardyFirstMomentUpperHyp` | Assumptions.lean | \|∫₁ᵀ Z(t) dt\| ≤ C·T^{1/2+ε} | Hard |
| `ExplicitFormulaPsiHyp` | Assumptions.lean | ψ₀(x) = x - Σ_ρ x^ρ/ρ + O(log x) | Hard |

Plus 1 Aristotle sorry: `approx_functional_eq` (feeds into Hardy chain).

### For `littlewood_pi_li` (2 sorries):
| Sorry | Location | Mathematical Content | Difficulty |
|-------|----------|---------------------|------------|
| `ThetaOscillationSqrtHyp` | Assumptions.lean | θ(x) - x = Ω±(√x) (from explicit formula for θ) | Hard |
| `OmegaThetaToPiLiHyp` | Assumptions.lean | θ oscillation → π-li oscillation (needs quantitative PNT) | Hard |

## Architecture Fix: COMPLETED

### Problems Fixed
1. **OmegaPsiToThetaHyp** — mathematically FALSE (kept but unused)
2. **OmegaThetaToPiLiHyp** — unprovable from Mathlib (still used as hypothesis, correctly)
3. **PsiOscillationSqrtHyp** — was standalone sorry (now auto-wired through bridge chain)
4. **PsiOscillationFromCriticalZerosHyp** — was standalone sorry (now wired from Hardy + explicit formula)
5. **PiLiOscillationSqrtHyp** — was standalone sorry (now auto-wired through bridge)

### Bridge Chain (all 0 sorries except ExplicitFormulaOscillation)
```
ExplicitFormulaOscillation.lean:
  [HardyCriticalLineZerosHyp] [ExplicitFormulaPsiHyp] → PsiOscillationFromCriticalZerosHyp (1 sorry)

PsiOscillationWiring.lean:
  [PsiOscillationFromCriticalZerosHyp] → PsiOscillationSqrtHyp (0 sorry)

PsiToPiLiOscillation.lean:
  [ThetaOscillationSqrtHyp] [OmegaThetaToPiLiHyp] → PiLiOscillationSqrtHyp (0 sorry)

HardyCriticalLineWiring.lean:
  [ZetaCriticalLineBoundHyp] [HardyFirstMomentUpperHyp] → HardyCriticalLineZerosHyp (0 sorry)
```

## Hardy Chain Status (Structurally Complete)

```
DiagonalIntegralBound: ∫|S_N|² ≥ c·T·log T                (0 sorries)
  → HardyApproxFunctionalEq: ∫Z² ≥ k·∫|S|² - CT           (1 sorry)
  → MeanSquarePartialSumAsymptotic                          (0 sorries)
  → OscillatorySumBound                                     (0 sorries)
  → MeanSquareBridge: ∫Z² ≥ c'·T·log T                     (0 sorries)
  → HardySetupV2Instance: ALL 6 FIELDS PROVED               (0 sorries)
  → HardyInfiniteZerosV2: ALL 5 LEMMAS PROVED               (0 sorries)
  → HardyCriticalLineWiring → HardyCriticalLineZerosHyp     (0 sorries)
  → ExplicitFormulaOscillation → PsiOscillationFromCriticalZerosHyp (1 sorry)
  → PsiOscillationWiring → PsiOscillationSqrtHyp            (0 sorries)
  → littlewood_psi                                          (0 sorries)
```

## Aristotle Module: Active Sorries

| File | Sorries | Topic |
|------|---------|-------|
| PhragmenLindelof.lean | 3 | Convexity bounds, Gamma growth (Stirling) |
| ZeroCounting.lean | 2 | N(T) argument principle + asymptotic |
| HardyApproxFunctionalEq.lean | 1 | Approximate functional equation |
| PartialSummation.lean | 1 | π(x) - li(x) via partial summation |

## Hypothesis Instance Status

### Fully Proved (no sorries)
- `ZeroConjZeroHyp` — conjugation symmetry of nontrivial zeros
- `ZeroOneSubZeroHyp` — functional equation symmetry of nontrivial zeros
- `FunctionalEquationHyp` — zeta functional equation
- `LambdaSymmetryHyp` — completed zeta symmetry
- `ZetaLogDerivPoleHyp` — -zeta'/zeta has poles at zeros

### Auto-Wired via Bridges (fires when dependencies are met)
- `HardyCriticalLineZerosHyp` — from ZetaCriticalLineBoundHyp + HardyFirstMomentUpperHyp
- `PsiOscillationFromCriticalZerosHyp` — from HardyCriticalLineZerosHyp + ExplicitFormulaPsiHyp (1 sorry)
- `PsiOscillationSqrtHyp` — from PsiOscillationFromCriticalZerosHyp
- `PiLiOscillationSqrtHyp` — from ThetaOscillationSqrtHyp + OmegaThetaToPiLiHyp

### Sorry-backed (in Assumptions.lean): 57 instances

## Key Gaps for Progress

1. **ExplicitFormulaOscillation** (1 sorry in Bridge/): Oscillation extraction from
   explicit formula + infinitely many critical-line zeros. Deep analytic number theory.
2. **PhragmenLindelof** (3 sorries): Convexity bounds and Gamma growth.
   Closing these would discharge `ZetaCriticalLineBoundHyp`.
3. **HardyApproxFunctionalEq** (1 sorry): Approximate functional equation.
   Last sorry on the Hardy critical path.
4. **ZeroCounting** (2 sorries): N(T) via argument principle. Not on critical path.
5. **PartialSummation** (1 sorry): Transfer from ψ to π-li oscillation. Not on critical
   path (PsiToPiLiOscillation bridge routes through ThetaOscillationSqrtHyp instead).

## Build Status

- Full `lake build` passes with 69 sorry warnings (66 project + 3 dependency)
- All .lean files compile (8016 jobs)
- ~33,800 lines of Lean code
- Both main theorems resolve with NO explicit typeclass parameters
