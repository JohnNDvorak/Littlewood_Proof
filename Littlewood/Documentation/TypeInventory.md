# Complete Type Inventory

## Part A: Canonical Types (used in Assumptions.lean class definitions)

The assumption classes reference types from three layers:

### Layer 0: Mathlib
- `riemannZeta : ℂ → ℂ`
- `completedRiemannZeta : ℂ → ℂ`
- `Chebyshev.psi : ℝ → ℝ`, `Chebyshev.theta : ℝ → ℝ`
- `Nat.primeCounting : ℕ → ℕ`
- `ArithmeticFunction.vonMangoldt : ℕ → ℝ`

### Layer 1: ZetaZeros/ (project-defined)
- `zetaNontrivialZeros : Set ℂ` — `{s | ζ(s)=0 ∧ 0 < Re(s) < 1}`
- `zetaNontrivialZerosPos : Set ℂ` — positive imaginary part
- `zetaZeroOrdinates : Set ℝ` — imaginary parts of zeros
- `zeroCountingFunction : ℝ → ℕ` — N(T), uses `Set.ncard`
- `riemannXi : ℂ → ℂ` — s(s-1)Λ(s)
- `RiemannHypothesis' : Prop`
- `ZeroOrdinate` — subtype `{γ : ℝ // γ ∈ zetaZeroOrdinates}`
- `zetaZeroSupRealPart : ℝ` — Θ = sup Re(ρ)

### Layer 2: Basic/ (project-defined)
- `chebyshevPsi : ℝ → ℝ` — wraps `Chebyshev.psi`
- `chebyshevTheta : ℝ → ℝ` — wraps `Chebyshev.theta`
- `logarithmicIntegral : ℝ → ℝ` — `∫ t ∈ Ioc 2 x, 1/log t`
- `IsOmegaPlusMinus : (ℝ→ℝ) → (ℝ→ℝ) → Prop`

### Layer 3: Module-local definitions
- `chebyshevPsi0 : ℝ → ℝ` — normalized at jumps (ExplicitFormulaPsi)
- `weightedAverage : ℝ → ℝ → ℝ` (WeightedAverageFormula)
- `dirichletIntegral : (ℝ→ℝ) → ℂ → ℂ` (LandauLemma)

## Part B: Aristotle Local Definitions

### `chebyshevPsi` — 7 Aristotle files redefine it

All use `Σ n ∈ range(⌊x⌋+1), vonMangoldt(n)` which equals Mathlib's `Chebyshev.psi`.
One uses `Finset.Icc 1 ⌊x⌋₊` (equivalent since vonMangoldt(0) = 0).

**Verdict: MATHEMATICALLY EQUIVALENT to canonical, but different Lean expressions.**

### `theta` — 5 Aristotle files

3 files: `(x : ℝ) → ℝ` using `Σ p ∈ range(⌊x⌋+1).filter Prime, log p`
2 files: `(n : ℕ) → ℝ` using `Σ p ∈ range(n+1).filter Prime, log p`

**Verdict: ℝ→ℝ versions EQUIVALENT to canonical; ℕ→ℝ versions INCOMPATIBLE type.**

### `NZeros` — 5 Aristotle files

3 files: `ℕ`-returning, counting same set as canonical `zeroCountingFunction`
  - RiemannVonMangoldt uses `Nat.card`, others use `Set.ncard`
2 files: `ℝ`-returning (analytic formula, not a count)

**Verdict: ℕ versions EQUIVALENT (Nat.card vs Set.ncard on finite sets); ℝ versions INCOMPATIBLE.**

### `hardyZ` — 4 Aristotle files + 1 Development

3 Aristotle: `(t : ℝ) → ℝ` via `.re` — all IDENTICAL
1 Development: `(t : ℝ) → ℂ` — INCOMPATIBLE return type

**Verdict: Aristotle versions consistent with each other but no canonical definition exists.**

### `li` — 5 Aristotle files

All use `∫ t in (2)..x, 1/Real.log t` (interval integral).
Canonical uses `∫ t in Ioc 2 x, 1/log t` (Lebesgue integral).

**Verdict: EQUIVALENT (same math, different integral API).**

### `primeCountingReal` — 4 Aristotle files

All compute `Nat.primeCounting(⌊x⌋) : ℝ`.
No canonical definition exists (Main/ uses the expression inline).

**Verdict: Consistent across Aristotle, no canonical to match against.**

## Part C: The Bridging Problem

| Canonical Type | Aristotle Equivalent | Gap |
|---------------|---------------------|-----|
| `chebyshevPsi x` = `Chebyshev.psi x` | `Σ n ∈ range(⌊x⌋+1), vonMangoldt n` | Need: `Chebyshev.psi x = Σ vonMangoldt` (may be `rfl` or `simp` in Mathlib) |
| `chebyshevTheta x` = `Chebyshev.theta x` | `Σ p ∈ range(⌊x⌋+1).filter Prime, log p` | Need: same as above for theta |
| `zeroCountingFunction T` (Set.ncard) | `NZeros T` (Nat.card or Set.ncard) | Need: `Set.ncard` = `Nat.card` for finite sets |
| `logarithmicIntegral x` (Lebesgue) | `li x` (interval integral) | Need: `∫ t ∈ Ioc 2 x = ∫ t in 2..x` for positive integrands |
| `zetaNontrivialZeros` (canonical) | local zero sets | No Aristotle file uses the canonical name |
| No canonical `hardyZ` | 3 consistent Aristotle defs | Need to pick one as canonical |

## Part D: What Can Actually Be Bridged

### Tier 1: Likely `rfl` or `simp` (verify by compilation)
- `chebyshevPsi x` ↔ Aristotle `chebyshevPsi x` (if Mathlib's `Chebyshev.psi` unfolds to the sum)
- `theta (n : ℕ)` across Aristotle files (identical definitions)

### Tier 2: Need a short proof
- `zeroCountingFunction T` ↔ `NZeros T` (Nat.card vs Set.ncard on finite sets)
- `logarithmicIntegral x` ↔ `li x` (Lebesgue vs interval integral)
- `theta (x : ℝ)` ↔ `theta (n : ℕ)` for natural number inputs

### Tier 3: Fundamental mismatch
- `hardyZ : ℝ → ℂ` (Development) vs `hardyZ : ℝ → ℝ` (Aristotle)
- `NZeros : ℝ → ℝ` (analytic formula) vs `zeroCountingFunction : ℝ → ℕ` (counting)
- Any Aristotle theorem using structures/typeclasses as assumptions
