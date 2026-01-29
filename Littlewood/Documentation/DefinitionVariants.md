# Definition Variants Across Files

Updated: 2026-01-29

Multiple files define the same mathematical objects differently.
This causes type mismatches when wiring.

## chebyshevPsi

| File | Definition | Type |
|------|------------|------|
| Basic/ChebyshevFunctions | chebyshevPsi | ℝ → ℝ |
| ChebyshevThetaV2 | psi (local, namespaced) | ℕ → ℝ |
| TruncatedExplicitFormula | chebyshevPsi (namespaced) | ℝ → ℝ |
| ChebyshevTheta (commented) | psi | ℕ → ℝ |

## chebyshevTheta / theta

| File | Definition | Type |
|------|------------|------|
| ThetaLinearBound | theta | ℝ → ℝ (via ⌊x⌋₊, Nat.primesBelow) |
| ThetaLinearBoundV2 | theta (namespaced) | ℕ → ℝ (via Finset.range.filter) |
| ChebyshevThetaV2 | theta (namespaced) | ℕ → ℝ (via Finset.range.filter) |
| ChebyshevTheta (commented) | theta | ℕ → ℝ |
| Basic/ChebyshevFunctions | chebyshevTheta | ℝ → ℝ |

## NZeros / zeroCountingFunction / N

| File | Name | Type | Notes |
|------|------|------|-------|
| ZeroCountingFunction | zeroCountingFunction | ℝ → ℕ | Project canonical |
| ZeroCountingFunction | N | ℝ → ℕ (abbrev) | Shorthand |
| ZeroCountingNew | NZeros | ℝ → ℕ | Global, Set.ncard |
| RiemannVonMangoldt | NZeros (in module) | ℝ → ℕ | Nat.card |
| NAsymptotic | N (in ZetaZeroCount) | ℝ → ℕ | Namespaced |
| NZerosStirling | NZeros (namespaced) | ℝ → ℕ | |
| ZeroCounting | zetaZeroCount | ℝ → ℕ | |
| Bridge/ZeroCountingBridge | Proved equivalences | — | NZeros = zeroCountingFunction |

## Resolution Strategy

1. Choose canonical definition (prefer project's own or Mathlib when available)
2. Prove equivalence lemmas: local_def = canonical_def
3. Use equivalence to transfer theorems
4. ZeroCountingBridge already handles NZeros ↔ zeroCountingFunction
