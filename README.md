# Littlewood's Oscillation Theorem - Lean 4 Formalization

## Overview

This project formalizes Littlewood's theorem that π(x) - Li(x) changes sign
infinitely often, along with quantitative oscillation bounds for ψ(x) - x.

## Status: Architecture Complete, Core Analysis ~15-20% Formalized

### What's Complete ✓

- **Theorem statements**: All main theorems compile without sorry
- **Logical architecture**: 304 proved theorems/lemmas
- **Modular structure**: Clean hypothesis-based design
- **Mathlib integration**: Connected to Euler product, non-vanishing on Re ≥ 1, LSeries

### What's In Progress

| Gap | Status | Notes |
|-----|--------|-------|
| Euler Product (#1) | 90% | Mathlib has core results |
| LSeries Bridge (#5) | 95% | TypeBridge infrastructure built |

### What's Blocked

| Gap | Description | Mathlib Status | Est. Hours |
|-----|-------------|----------------|------------|
| #2 | Perron's Formula | NOT IN MATHLIB | 100-200 |
| #3 | Zero Counting | NOT IN MATHLIB | 100-200 |
| #4 | Hardy's Theorem | NOT IN MATHLIB | 200-400 |
| #6 | Quantitative Zero-Free | PARTIAL | 80-150 |

### Honest Numbers

| Metric | Count |
|--------|-------|
| Total sorries | ~113 |
| Hypothesis classes | 42 |
| Hypothesis instances with sorry | 40 |
| Proved instances | 2 |
| Main theorem sorries | 0 |

## Main Theorems

All compile and type-check, parameterized by hypothesis classes:

```lean
-- π(x) - Li(x) changes sign infinitely often
theorem littlewood_pi_li : ∃ᶠ x in atTop, π(x) > Li(x) ∧ ∃ᶠ x in atTop, π(x) < Li(x)

-- Quantitative oscillation for ψ(x) - x
theorem littlewood_psi :
    limsup (fun x => (ψ(x) - x) / (√x · log log log x)) atTop = +∞ ∧
    liminf (fun x => (ψ(x) - x) / (√x · log log log x)) atTop = -∞
```

## Building

```bash
lake build
```

Requires Lean 4 and Mathlib. See `lakefile.lean` for dependencies.

## Project Structure

```
Littlewood/
├── Main/                    # Main theorem statements (0 sorries)
│   ├── Littlewood.lean
│   ├── LittlewoodPi.lean
│   └── LittlewoodPsi.lean
├── Assumptions.lean         # Hypothesis instances (61 sorries)
├── CoreLemmas/              # Supporting infrastructure
│   ├── LandauLemma.lean
│   ├── WeightedAverageFormula.lean
│   └── DirichletApproximation.lean
├── Development/             # New Mathlib-connected work
│   ├── ZeroFreeRegion.lean  # 8 sorries, 6 new theorems
│   ├── TypeBridge.lean      # LSeries infrastructure
│   ├── HardyTheorem.lean    # 11 sorries, blocked on slitPlane
│   └── LandauLemma.lean     # Proved vonMangoldt identity
├── ExplicitFormulas/        # Perron/Mellin (blocked)
├── Oscillation/             # Schmidt theorem
├── ZetaZeros/               # Zero counting, density
└── Basic/                   # Chebyshev, Li, notation
```

## Documentation

- [`docs/blocking_analysis.md`](docs/blocking_analysis.md) - Gap analysis
- [`docs/development_audit.md`](docs/development_audit.md) - File-by-file status
- [`docs/hypothesis_consolidation.md`](docs/hypothesis_consolidation.md) - Hypothesis class analysis
- [`docs/mathlib_pr_specs/`](docs/mathlib_pr_specs/) - Specifications for needed Mathlib PRs
- [`docs/sorry_analysis/`](docs/sorry_analysis/) - Detailed sorry audits

## Contributing

### Easy (Current Mathlib)

Review files in `Development/` for sorries that might be fillable:
- `ZeroFreeRegion.lean` - 8 sorries, some might be closable
- `TypeBridge.lean` - LSeries infrastructure

### Medium (Small Mathlib PRs)

See [`docs/mathlib_pr_specs/`](docs/mathlib_pr_specs/) for needed PRs:
1. **Quantitative zero-free region** - Most prerequisites exist
2. **Perron's formula** - High impact, unlocks explicit formulas

### Hard (Major Mathlib Work)

- Zero counting infrastructure (100-200 hours)
- Hardy's theorem (200-400 hours)

## Architecture Design

The project uses **hypothesis classes** to separate:
1. **Logical structure** (complete) - How theorems depend on each other
2. **Mathematical content** (partial) - The actual analytic proofs

This allows Main theorems to compile while Development work proceeds.

Example:
```lean
class ExplicitFormulaPsiHyp : Prop where
  formula : ∀ x ≥ 2, ψ(x) = x - Σρ x^ρ/ρ - log(2π) - ...

-- Main theorem uses the hypothesis
theorem littlewood_psi [ExplicitFormulaPsiHyp] : ...

-- Instance with sorry (requires Perron's formula)
instance : ExplicitFormulaPsiHyp := ⟨by sorry⟩
```

## References

- Littlewood, J.E. "Sur la distribution des nombres premiers." 1914
- Ingham, A.E. "The Distribution of Prime Numbers." 1932
- Montgomery & Vaughan, "Multiplicative Number Theory I"
- Titchmarsh, "The Theory of the Riemann Zeta Function"

## License

Apache 2.0
