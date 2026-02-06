# Littlewood Formalization: Project Snapshot

**Date**: 2026-02-05
**Lean**: 4.27.0-rc1
**Mathlib**: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

## Build Metrics

| Metric | Value |
|--------|-------|
| `lake build Littlewood.Main.Littlewood` | 11 sorry warnings |
| Project sorries | 8 |
| External sorries (Wiener.lean) | 3 |
| Total active .lean files | 198 |
| Deprecated .lean files | 4 |
| Aristotle files | ~117 |

## Build-Visible Sorries

```
# External (NOT on critical path)
PrimeNumberTheoremAnd/Wiener.lean:320:prelim_decay_2
PrimeNumberTheoremAnd/Wiener.lean:339:prelim_decay_3
PrimeNumberTheoremAnd/Wiener.lean:3889:auto_cheby

# Critical Path
Littlewood/CriticalAssumptions.lean:70:ExplicitFormulaPsiHyp
Littlewood/CriticalAssumptions.lean:93:ZetaCriticalLineBoundHyp
Littlewood/CriticalAssumptions.lean:116:HardyFirstMomentUpperHyp
Littlewood/CriticalAssumptions.lean:141:OmegaThetaToPiLiHyp
Littlewood/CriticalAssumptions.lean:163:ExplicitFormulaThetaHyp

# Bridge Wiring
Littlewood/Bridge/ExplicitFormulaOscillation.lean:74:PsiOscillationFromCriticalZerosHyp
Littlewood/Bridge/ThetaExplicitFormulaOscillation.lean:57:ThetaOscillationSqrtHyp

# Aristotle
Littlewood/Aristotle/HardyApproxFunctionalEq.lean:113:approx_functional_eq
```

## Instance Resolution Chain

All instances resolve via `inferInstance`:

```lean
-- Critical hypotheses (5 sorry-backed in CriticalAssumptions.lean)
#check (inferInstance : ExplicitFormulaPsiHyp)      -- ✓
#check (inferInstance : ExplicitFormulaThetaHyp)   -- ✓
#check (inferInstance : ZetaCriticalLineBoundHyp)  -- ✓
#check (inferInstance : HardyFirstMomentUpperHyp)  -- ✓
#check (inferInstance : OmegaThetaToPiLiHyp)       -- ✓

-- Bridge-derived (auto-wired)
#check (inferInstance : PsiOscillationFromCriticalZerosHyp)  -- ✓
#check (inferInstance : ThetaOscillationSqrtHyp)             -- ✓
#check (inferInstance : PiLiOscillationSqrtHyp)              -- ✓
#check (inferInstance : PsiOscillationSqrtHyp)               -- ✓

-- Main theorems typecheck
#check Littlewood.littlewood_psi                   -- ✓
#check LittlewoodPi.littlewood_pi_li               -- ✓
#check LittlewoodPi.pi_gt_li_infinitely_often      -- ✓
#check LittlewoodPi.pi_lt_li_infinitely_often      -- ✓
```

## Critical Path Dependencies

```
ExplicitFormulaPsiHyp + ZetaCriticalLineBoundHyp + HardyFirstMomentUpperHyp
    └─→ Hardy chain (Aristotle files, 0 sorries except approx_functional_eq)
        └─→ HardyCriticalLineZerosHyp (auto-wired)
            └─→ PsiOscillationFromCriticalZerosHyp (1 bridge sorry)
                └─→ PsiOscillationSqrtHyp (0 sorries)
                    └─→ littlewood_psi ✓

ExplicitFormulaThetaHyp + HardyCriticalLineZerosHyp
    └─→ ThetaOscillationSqrtHyp (1 bridge sorry)

ThetaOscillationSqrtHyp + OmegaThetaToPiLiHyp
    └─→ PiLiOscillationSqrtHyp (0 sorries)
        └─→ littlewood_pi_li ✓
```

## Aristotle Files Inventory (Key Files)

| File | Sorries | Status | Notes |
|------|:-------:|--------|-------|
| GammaGrowthBoundsV2.lean | 0 | CLOSED | All 4 exact? sorries fixed |
| ZetaLogDerivInfra.lean | 0 | CLOSED | All 6 sorries fixed |
| ZetaIntegralRep.lean | 0 | CLOSED | 1 exact? sorry fixed |
| ContourIntegrationV2.lean | 0 | PROVED | Cauchy rectangle theorem |
| HardyApproxFunctionalEq.lean | 1 | CRITICAL | approx_functional_eq |
| PhragmenLindelof.lean | 3 | NOT IMPORTED | gamma_growth blocks |
| ZeroCounting.lean | 2 | NOT IMPORTED | Real math |
| PartialSummation.lean | 2 | NOT IMPORTED | Weak hypotheses |
| PsiOscillationPiLi.lean | 0 | STANDALONE | Alt proof (incompatible) |

## What Remains for Completion

1. **approx_functional_eq** (Aristotle) - Closes Hardy chain
2. **gamma_growth** (Aristotle) - Enables ZetaCriticalLineBoundHyp
3. **ExplicitFormulaPsiHyp/ThetaHyp** - Needs Perron's formula + contour integration
4. **OmegaThetaToPiLiHyp** - Architectural issue (see Task 57 analysis)
5. **Bridge sorries** - Need oscillation extraction lemmas

## Session Summary (2026-02-05)

### Completed
- Task 48: GammaGrowthBoundsV2.lean 4→0 sorries
- Task 49: Created GammaGrowthWiring.lean bridge
- Task 50: Documented HardyApproxFunctionalEqV4 hypotheses
- Task 51: Analyzed PartialSummation architectural issues
- Task 52: Updated documentation
- Task 53: ZetaIntegralRep.lean 1→0 sorries
- Task 55: Created WiringSimulation.lean test
- Task 57: Analyzed OmegaThetaToPiLiHyp alternatives

### Key Finding (Task 57)
OmegaThetaToPiLiHyp has architectural issues:
- PsiDominance.lean requires **unbounded oscillation** (∀ K, ∃ x, |ψ-x| > K√x)
- But Ω± notation only gives **bounded limsup/liminf**
- The specific case f = √x might be provable via direct decomposition
- Would require weakening to OmegaThetaToPiLiSqrtHyp
