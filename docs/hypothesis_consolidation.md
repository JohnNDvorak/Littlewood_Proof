# Hypothesis Class Consolidation Report (Task 58)

## Executive Summary

| Metric | Count |
|--------|-------|
| Total hypothesis classes | 42 |
| Classes with sorried instances | 40 |
| Classes with PROVED instances | 2 |
| Classes now provable from Mathlib | 0 |
| Classes potentially reducible | 0 |
| Sorries in Assumptions.lean | 61 |

**Conclusion:** No consolidation possible. All hypothesis classes represent distinct
mathematical theorems that require Mathlib infrastructure not yet available.

## Classes Now Provable from Mathlib

**Count: 0**

Despite recent Mathlib additions (Euler product, non-vanishing on Re ≥ 1), NO hypothesis
classes become directly provable because:

1. **ZeroFreeRegionHyp** requires σ > 1 - c/log|t| (quantitative)
   - Mathlib only has Re(s) ≥ 1 (boundary)
   - Gap: quantitative de la Vallée-Poussin

2. **ExplicitFormula*Hyp** require Perron's formula
   - Mathlib has residues but not contour integrals for ANT
   - Gap: Perron's formula infrastructure

3. **ZeroCountingXxxHyp** require argument principle
   - Mathlib has basic Cauchy but not zero counting
   - Gap: N(T) asymptotic formula

4. **HardyCriticalLineZerosHyp** requires Hardy Z analysis
   - Mathlib has functional equation but not sign change theory
   - Gap: Hardy Z-function infrastructure

## Classes That Could Be Merged

**Count: 0**

All classes are mathematically distinct:

| Domain | Classes | Why Not Mergeable |
|--------|---------|-------------------|
| Explicit Formula | 6 | Different integral representations |
| Weighted Average | 7 | Different summation/bounds |
| Schmidt/Oscillation | 9 | Different oscillation statements |
| Zero Density | 6 | Different density results |
| Zero-Free Region | 4 | Different region types |
| Zero Counting | 10 | Different counting formulas |

## Classes That Are Fundamentally Needed

All 42 classes are fundamentally needed because they represent distinct theorems:

### Tier 1: Foundation (would unlock most progress)
| Class | Mathematical Content | Mathlib Gap |
|-------|---------------------|-------------|
| ExplicitFormulaPsiHyp | ψ(x) = x - Σρ x^ρ/ρ | Perron's formula |
| ZeroCountingAsymptoticHyp | N(T) ~ (T/2π)log(T/2πe) | Argument principle |
| HardyCriticalLineZerosHyp | Infinitely many zeros on Re=1/2 | Hardy Z analysis |
| ZeroFreeRegionHyp | σ > 1 - c/log|t| | Quantitative bounds |

### Tier 2: Consequences (flow from Tier 1)
| Class | Depends On |
|-------|------------|
| PsiErrorBoundHyp | ExplicitFormulaPsiHyp + ZeroFreeRegionHyp |
| ZeroCountingSummabilityHyp | ZeroCountingAsymptoticHyp |
| PsiOscillationFromCriticalZerosHyp | HardyCriticalLineZerosHyp |

### Tier 3: Specialized Results
All WeightedAverage, Schmidt oscillation, and density hypotheses.

## Classes Already Proved

**Count: 2** (in ZeroCountingFunction.lean)

| Class | Proof Source |
|-------|--------------|
| ZeroConjZeroHyp | `riemannZeta_conj` from Mathlib |
| ZeroOneSubZeroHyp | `riemannZeta_one_sub` functional equation |

## Parametric Hypotheses (Design Issue)

The following have instances for ALL functions, which is mathematically incorrect:

| Location | Class Pattern | Issue |
|----------|---------------|-------|
| LandauLemma.lean | `instance (A : ℝ → ℝ) (σ_c : ℝ) : XxxHyp A σ_c` | True only for specific A |

**Recommendation:** These should require hypotheses on A (non-negative, bounded growth, etc.)
rather than being universal instances. This is an architecture issue, not a consolidation
opportunity.

## Instance Sorry Distribution

| File | Sorry Count | Category |
|------|-------------|----------|
| Assumptions.lean | 61 | Centralized instances |
| LandauLemma.lean | 11 | Parametric + specific |
| Various others | ~40 | Distributed |

## Attempted Consolidations

### Attempt 1: Merge ExplicitFormula variants
- **Classes:** ExplicitFormulaPsiHyp, ExplicitFormulaPsiSmoothedHyp, etc.
- **Result:** Cannot merge - represent different mathematical formulas
- **Reason:** Smoothed version uses different kernel

### Attempt 2: Derive ZeroFreeRegionHyp from Mathlib
- **Mathlib has:** `riemannZeta_ne_zero_of_one_le_re`
- **Hyp requires:** σ > 1 - c/log|t| for some c > 0
- **Result:** Cannot derive - Mathlib only has boundary, not interior

### Attempt 3: Merge zero counting variants
- **Classes:** ZeroCountingAsymptoticHyp, ZeroCountingMainTermHyp, etc.
- **Result:** Cannot merge - different precision levels needed for different theorems

## Recommendations

1. **No consolidation possible with current Mathlib**
   - All hypothesis classes are mathematically necessary
   - The 42 classes represent ~42 distinct theorems

2. **Fix parametric hypothesis architecture**
   - LandauLemma.lean instances should have hypotheses on A
   - This is a refactor, not a proof task

3. **Track Mathlib developments**
   - Perron's formula would unlock ~6 classes
   - Zero counting would unlock ~10 classes
   - Hardy's theorem would unlock ~5 classes

## Summary

- **Before consolidation:** 42 classes, 61 sorries in Assumptions.lean
- **After consolidation:** 42 classes, 61 sorries in Assumptions.lean
- **Reduction:** 0 sorries eliminated
- **Reason:** All classes represent distinct, non-derivable mathematical content
