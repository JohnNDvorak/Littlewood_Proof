# Definition Conflicts and Resolution Plan

## chebyshevPsi

| File | Definition | Notes |
|------|------------|-------|
| Basic/ChebyshevFunctions | `Chebyshev.psi` (Mathlib) | Canonical |
| TruncatedExplicitFormula | `chebyshevPsi` (namespaced) | Local, compatible |
| ChebyshevTheta | `psi` | Standalone, commented out |
| PartialSummation | imports Basic | Uses canonical |
| ExplicitFormulaInfrastructure | `chebyshevPsi` (namespaced) | Local |

**Resolution**: Use `Chebyshev.psi` from Mathlib where possible. Namespaced local definitions are OK.

## xi (Riemann Xi Function)

| File | Definition | Entire? |
|------|------------|---------|
| ZeroCounting | `xi_Mathlib = s(s-1)·completedRiemannZeta s` | ❌ NO (discontinuous at 0,1) |
| ZeroCounting | `xi_Mathlib_corrected = s(s-1)·Λ₀(s) + 1` | ✅ YES |
| ZeroCountingXi | `xi = s(s-1)·completedRiemannZeta₀ s + 1` | ✅ YES |
| RiemannXi | `xi = (1/2)s(s-1)·completedRiemannZeta s` | ❌ NO |
| XiDifferentiability | `xi_Literal`, `xi_LiteralCorrected` | Both documented |

**Resolution**: Use `ZeroCountingXi.xi` as canonical entire xi function.

## NZeros / Zero Counting

| File | Definition | Type | Notes |
|------|------------|------|-------|
| ZeroCounting | `zetaZeroCount` | ℕ | Uses ncard, wrong xi |
| ZeroCountingXi | `zetaZeroCount` | ℕ | Uses ncard, correct xi |
| NAsymptotic | `N` | ℝ | Conditional on hypotheses |
| RiemannVonMangoldt | `NZeros` | ℕ | Different formulation |
| NZerosStirling | `NZeros` | ℝ | Via arg Γ formula |

**Resolution**: Need equivalence lemmas. ZeroCountingXi.zetaZeroCount is most correct.

## partialZeta

| File | Definition | Notes |
|------|------------|-------|
| MeanSquare | `partialZeta N s = Σ_{n∈Icc 1 N} n^{-s}` | 1-indexed |
| PartialZetaNormSqV2 | `Σ_{n∈range N} (n+1)^{-s}` | 0-indexed, equivalent |

**Resolution**: Mathematically equivalent (both sum n=1 to N of n^{-s}).

## offDiagSsq

| File | Definition |
|------|------------|
| MeanSquare | `offDiagSsq t = Σ_{n≠m} (nm)^{-1/2} (n/m)^{-it}` |
| OffDiagonalBound | `offDiagSsqReal` (similar) |

**Resolution**: Check exact type compatibility for wiring.

## Wiring Priority

1. **High**: Wire OffDiagonalBound → MeanSquare (norm_integral_offDiagSsq_le)
2. **Medium**: Bridge PartialZetaNormSqV2 → MeanSquare (need diagonal/off-diagonal split)
3. **Low**: Definition alignment for N(T) variants
