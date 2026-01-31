# Explicit Formula Component Analysis

**Date:** 2026-01-22
**Task:** 98

## Available in Mathlib

| Component | Status | Location |
|-----------|--------|----------|
| riemannZeta | ✓ | Mathlib.NumberTheory.LSeries.RiemannZeta |
| vonMangoldt | ✓ | Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt |
| chebyshevPsi | ✓ | Mathlib.NumberTheory.Chebyshev |
| chebyshevTheta | ✓ | Mathlib.NumberTheory.Chebyshev |
| logDeriv | ✓ | Mathlib.Analysis.SpecialFunctions.Log.Deriv |
| LSeries | ✓ | Mathlib.NumberTheory.LSeries.Basic |
| Dirichlet character | ✓ | Mathlib.NumberTheory.LSeries.Dirichlet |

## Missing from Mathlib

| Component | Impact | Complexity |
|-----------|--------|------------|
| -ζ'/ζ = ∑ Λ(n)/n^s | HIGH | MEDIUM |
| Perron's formula | HIGH | HIGH |
| Contour integration | HIGH | HIGH |
| Mellin transforms | MEDIUM | HIGH |
| Explicit formula for ψ(x) | HIGH | HIGH |

## Explicit Formula Statement

The explicit formula connects ψ(x) to zeros:

```
ψ(x) = x - ∑_ρ x^ρ/ρ - log(2π) - (1/2)log(1 - 1/x²)
```

where the sum is over non-trivial zeros ρ of ζ(s).

## Gap Analysis

1. **Series representation of -ζ'/ζ**
   - Need: -ζ'/ζ(s) = ∑_{n≥1} Λ(n)/n^s for Re(s) > 1
   - Mathlib has Λ but not this identity
   - Complexity: MEDIUM (needs Dirichlet series theory)

2. **Perron's formula**
   - Need: (1/2πi) ∫_{c-i∞}^{c+i∞} F(s) x^s ds/s
   - Mathlib doesn't have complex contour integration
   - Complexity: HIGH

3. **Truncated explicit formula**
   - Need error bounds for partial sums over zeros
   - Requires detailed zero density estimates
   - Complexity: HIGH

## Conclusion

The explicit formula cannot be fully formalized without substantial
additions to Mathlib's complex analysis infrastructure.
Current approach: Use hypothesis instances for explicit formula results.
