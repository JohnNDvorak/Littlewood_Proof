# Mathlib Feature Requests for Littlewood Formalization

## Overview

This document identifies Mathlib gaps blocking progress on the Littlewood formalization.
Each item includes a minimal context and potential MCP (Mathlib Contribution Project) scope.

## Priority 1: Dirichlet Character Specialization

### Gap
`DirichletCharacter.norm_LSeries_product_ge_one` provides:
```
‖L(χ⁰, 1+x)³ · L(χ, 1+x+iy)⁴ · L(χ², 1+x+2iy)‖ ≥ 1
```
But specializing to trivial character (χ = 1, L = ζ) requires boilerplate.

### What's Needed
```lean
theorem riemannZeta_product_lower_bound (σ : ℝ) (t : ℝ) (hσ : 1 < σ) :
    ‖riemannZeta σ‖ ^ 3 * ‖riemannZeta (σ + t * I)‖ ^ 4 *
    ‖riemannZeta (σ + 2 * t * I)‖ ≥ 1
```

### Files Affected
- `Littlewood/Development/ZeroFreeRegion.lean`: mertens_inequality_stub, zeta_product_lower_bound

### Potential Approach
Extract from `DirichletCharacter.norm_LSeries_product_ge_one` by showing `LSeries 1 = riemannZeta`.

---

## Priority 2: Laurent Expansion Infrastructure

### Gap
No general mechanism for extracting Laurent series coefficients from `MeromorphicAt`.

### What's Needed
```lean
-- Given MeromorphicAt ℂ f z₀ with a simple pole:
-- Extract residue and regular part
theorem MeromorphicAt.simple_pole_expansion (hf : MeromorphicAt ℂ f z₀)
    (hpole : MeromorphicAt.order hf = -1) :
    ∃ (r : ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g z₀ ∧
    ∀ z ≠ z₀, f z = r / (z - z₀) + g z
```

### Files Affected
- `Littlewood/Development/LaurentExpansion.lean`: neg_zeta_logderiv_laurent
- `Littlewood/Development/ZeroFreeRegion.lean`: neg_zeta_logderiv_expansion

---

## Priority 3: Complex.arg Continuity

### Gap
`Complex.arg` is discontinuous on negative real axis.
For Hardy's theorem, need continuity of `arg ∘ Gamma` on specific curves.

### What's Needed
```lean
-- arg is continuous where the value doesn't hit the branch cut
theorem Complex.continuousAt_arg_of_ne_neg_real (z : ℂ) (hz : ¬(z.re < 0 ∧ z.im = 0)) :
    ContinuousAt Complex.arg z
```

Or:
```lean
-- Gamma doesn't hit negative real axis on the line 1/4 + it/2
theorem Gamma_ne_neg_real_on_quarter_line (t : ℝ) :
    ¬(Complex.Gamma (1/4 + t/2 * I)).re < 0 ∨ (Complex.Gamma (1/4 + t/2 * I)).im ≠ 0
```

### Files Affected
- `Littlewood/Development/HardyTheorem.lean`: hardyZ_continuous

---

## Priority 4: Ω± Transfer Lemmas

### Gap
No lemmas for transferring Ω± through addition of bounded errors.

### What's Needed
```lean
-- If g =Ω±[f] and |h| = o(f), then g + h =Ω±[f]
theorem IsOmegaPlusMinus.add_o (hg : g =Ω±[f]) (hh : h =o[atTop] f) :
    (fun x => g x + h x) =Ω±[f]
```

### Files Affected
- `Littlewood/ExplicitFormulas/ConversionFormulas.lean`: OmegaPsiToThetaHyp, OmegaThetaToPiLiHyp

---

## Priority 5: Filter Coercion ℝ → ℂ

### Gap
Working with `nhdsWithin` for real σ → 1+ while functions are defined on ℂ.

### What's Needed
```lean
-- Tendsto for real filter when function is on ℂ
theorem tendsto_ofReal_nhdsWithin (f : ℂ → ℂ) (a b : ℝ) :
    Tendsto (fun σ : ℝ => f σ) (nhdsWithin a (Set.Ioi a)) (𝓝 b) ↔
    Tendsto (fun s : ℂ => f s) (nhdsWithin a (Set.Ioi (a : ℂ))) (𝓝 b)
```

### Files Affected
- `Littlewood/Development/ZeroFreeRegion.lean`: zeta_pole_behavior
- `Littlewood/Development/TypeBridge.lean`: lseries_real_tendsto_top_of_nonneg_divergent

---

## Summary Table

| Gap | Complexity | Blocking |
|-----|------------|----------|
| Dirichlet char specialization | MEDIUM | 3 sorries |
| Laurent expansion | HARD | 4 sorries |
| Complex.arg continuity | MEDIUM | 2 sorries |
| Ω± transfer lemmas | MEDIUM | 2 sorries |
| Filter coercion | EASY | 2 sorries |

---

## Contributing

If you're interested in contributing any of these features to Mathlib, please:
1. Open an issue on mathlib4 referencing this document
2. Ping the analytic number theory working group
3. Consider starting with Priority 5 (easiest) or Priority 1 (most impact)
