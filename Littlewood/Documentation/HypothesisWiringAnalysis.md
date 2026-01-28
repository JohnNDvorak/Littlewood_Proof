# Hypothesis Wiring Analysis

## Summary

| Category | Count | Description |
|----------|-------|-------------|
| Already Proved | 4 | Real proofs exist |
| In Mathlib | 1+ | Available from Mathlib |
| Potentially Wireable | 0 | Aristotle has matching proof |
| Needs Bridge | 2-3 | Proof exists but signature differs |
| Needs Real Proof | ~54 | No proof currently exists |

## Already Proved (4)

These instances have real proofs (not sorries):

1. **FunctionalEquationHyp** - `FunctionalEquationHyp.lean`
2. **LambdaSymmetryHyp** - `FunctionalEquationHyp.lean`
3. **ZeroConjZeroHyp** - `ZeroCountingFunction.lean` via `riemannZeta_conj`
4. **ZeroOneSubZeroHyp** - `ZeroCountingFunction.lean` via `riemannZeta_one_sub`

## In Mathlib (No Hypothesis Needed)

These are available directly from Mathlib:

| Theorem | Mathlib Name |
|---------|--------------|
| ζ(s) ≠ 0 for Re(s) ≥ 1 | `riemannZeta_ne_zero_of_one_le_re` |
| Λ(1-s) = Λ(s) | `completedRiemannZeta_one_sub` |

## Potentially Wireable (Analysis)

### Schmidt Oscillation Hypotheses

**SchmidtPsiOscillationHyp** (line 187 of Assumptions.lean)
- **Requires**: `(fun x => chebyshevPsi x - x) =Ω±[fun x => x ^ (Θ - ε)]`
- **Aristotle has**: `schmidt_oscillation` for trig polynomials
- **Gap**: Trig poly oscillation ≠ chebyshevPsi oscillation
- **Needs**: Explicit formula connecting ψ(x) to sum over zeros
- **Status**: ❌ NOT WIREABLE - blocked by explicit formula chain

**HardyCriticalLineZerosHyp** (line 211)
- **Requires**: Infinitely many zeros with Re(ρ) = 1/2
- **Aristotle has**: Hardy Z function properties
- **Gap**: Hardy Z ≠ Hardy's theorem on zero distribution
- **Status**: ❌ NOT WIREABLE - needs full Hardy theorem

### Zero Counting Hypotheses

**ZeroCountingAsymptoticHyp** (line 312)
- **Requires**: `(N T - main_term) =O[atTop] log`
- **Aristotle has**: `N_asymptotic` (conditional on h_S, h_RVM, h_Stirling)
- **Gap**: Conditional on unproved hypotheses
- **Status**: ❌ NOT DIRECTLY WIREABLE
- **Could wire if**: h_RVM and h_Stirling were proved

**ZeroCountingMainTermHyp** (line 324)
- **Requires**: `N T / (T log T / 2π) → 1`
- **Aristotle has**: `zero_counting_main_term` (conditional on RiemannVonMangoldtProperty)
- **Status**: ❌ NOT DIRECTLY WIREABLE

### Explicit Formula Hypotheses

**ExplicitFormulaPsiHyp** (line 84)
- **Requires**: Full explicit formula with convergent sum over ALL zeros
- **Aristotle has**: `explicit_formula_psi_v3` - BUT THIS IS TRIVIAL!
  - Just picks C large enough to make inequality true
  - Uses finite sum over |Im(ρ)| ≤ T, not infinite sum
- **Status**: ❌ NOT WIREABLE - Aristotle proof is trivial

### Landau Lemma Hypotheses

All Landau hypotheses are parametric: `(A : ℝ → ℝ) (σ_c : ℝ)`
- **Aristotle has**: `LandauLemma.lean` with specific results
- **Gap**: Need to match specific A and σ_c
- **Status**: ⚠️ NEEDS INVESTIGATION

## What Would Help

### From Aristotle

1. **Unconditional N(T) asymptotic** - without needing h_RVM, h_Stirling
2. **Hardy's theorem** - infinitely many zeros on Re(s) = 1/2
3. **Real explicit formula** - not trivial, with convergent sum

### Blocked Chains

```
Schmidt oscillation of ψ
    ↑ needs
Explicit formula for ψ
    ↑ needs
Perron's formula + contour integration
    ↑ needs
Mathlib complex analysis infrastructure
```

## Recommendation

Focus Aristotle effort on:
1. **h_RVM** (Riemann-von Mangoldt connection) - would unlock N_asymptotic
2. **h_Stirling** (Stirling for Gamma argument) - would unlock N_asymptotic
3. **Hardy's theorem** - would unlock HardyCriticalLineZerosHyp

Current sorry count in Assumptions.lean: **~58** (excluding the 4 proved)

Realistic reduction from wiring: **0** (no direct matches found)
