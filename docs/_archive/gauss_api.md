# Gauss (PrimeNumberTheoremAnd) API Reference

This document catalogs the theorems and definitions from the PrimeNumberTheoremAnd project
(the "Gauss" project) that are relevant to the Littlewood sign change theorem formalization.

## Import Path
```lean
import PrimeNumberTheoremAnd
-- Or import specific modules:
import PrimeNumberTheoremAnd.Consequences
import PrimeNumberTheoremAnd.StrongPNT
import PrimeNumberTheoremAnd.ZetaDefinitions
```

---

## Prime Number Theorem Variants

### Weak PNT

| Theorem | Type Signature | File |
|---------|---------------|------|
| `WeakPNT` | `Tendsto (fun N => cumsum Λ N / N) atTop (nhds 1)` | Wiener.lean:2438 |
| `WeakPNT'` | `Tendsto (fun N => (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1)` | Consequences.lean:83 |
| `WeakPNT''` | `ψ ~[atTop] (fun x => x)` | Consequences.lean:103 |
| `WeakPNT_AP` | Weak PNT in arithmetic progressions | Wiener.lean:4036 |

### Medium Strength PNT

| Theorem | Type Signature | File |
|---------|---------------|------|
| `MediumPNT` | `∃ c > 0, (ψ - id) =O[atTop] (fun x => x * exp (-c * (log x)^(1/10)))` | MediumPNT.lean:3804 |

---

## Chebyshev Functions

### Definitions

| Definition | Type | File |
|------------|------|------|
| `ψ` | `ℝ → ℝ` (equals `Chebyshev.psi`) | PrimaryDefinitions.lean:24 |
| `θ` | `ℝ → ℝ` (equals `Chebyshev.theta`) | SecondaryDefinitions.lean:42 |
| `R` | `ℝ → ℝ` (equals `Psi x - x`) | Consequences.lean:1734 |

### Chebyshev Asymptotics

| Theorem | Type Signature | File |
|---------|---------------|------|
| `chebyshev_asymptotic` | `θ ~[atTop] id` | Consequences.lean:175 |
| `chebyshev_asymptotic'` | (alternate form) | Consequences.lean:215 |
| `chebyshev_asymptotic''` | (alternate form) | Consequences.lean:245 |
| `chebyshev_asymptotic_finsum` | finsum version | Consequences.lean:185 |
| `chebyshev_asymptotic_pnt` | PNT form | Consequences.lean:2452 |
| `SmoothedChebyshevClose` | smoothed version | MediumPNT.lean:717 |
| `SmoothedChebyshevPull1/2/3` | contour integral forms | MediumPNT.lean, StrongPNT.lean |

### Psi-Theta Relations

| Theorem | Type Signature | File |
|---------|---------------|------|
| `psi_eq_sum_range` | `ψ x = ∑ in range, Λ` | MediumPNT.lean:33 |

---

## Zeta Function

### Definitions

| Definition | Description | File |
|------------|-------------|------|
| `riemannZeta.zeroes` | `{s : ℂ | riemannZeta s = 0}` | ZetaDefinitions.lean:19 |
| `riemannZeta.zeroes_rect` | Zeroes in rectangle `I × J` | ZetaDefinitions.lean:23 |
| `riemannZeta.order` | Multiplicity at a point | ZetaDefinitions.lean:28 |
| `riemannZeta.zeroes_sum` | Sum over zeroes | ZetaDefinitions.lean:32 |
| `riemannZeta.RH_up_to` | RH verified up to height `T` | ZetaDefinitions.lean:42 |
| `riemannZeta.classicalZeroFree` | Zero-free region with param `R` | ZetaDefinitions.lean:52 |
| `riemannZeta.N` | Zero counting function `N(T)` | ZetaDefinitions.lean:62 |
| `riemannZeta.N'` | Zero counting `N(σ,T)` | ZetaDefinitions.lean:71 |

### Zero-Free Region

| Theorem | Description | File |
|---------|-------------|------|
| `ZeroInequality` | `∃ E ∈ (0,1), ...` (zero-free region exists) | StrongPNT.lean:860 |
| `ZeroInequalitySpecialized` | Specialized form | StrongPNT.lean:874 |

### Riemann-von Mangoldt

| Definition/Theorem | Description | File |
|---------|-------------|------|
| `riemannZeta.RvM` | Error term function | ZetaDefinitions.lean:75 |
| `riemannZeta.Riemann_vonMangoldt_bound` | Bound definition | ZetaDefinitions.lean:85 |

### Log Derivative Bounds

| Theorem | Description | File |
|---------|-------------|------|
| `LogDerivZetaUniformLogSquaredBound` | `∃ C ≥ 0, ...` | StrongPNT.lean:1032 |
| `LogDerivZetaLogSquaredBoundSmallt` | Small `t` version | StrongPNT.lean:1057 |
| `dlog_riemannZeta_bdd_on_vertical_lines_explicit` | Explicit bound | MediumPNT.lean:1034 |

---

## Mertens Theorems (mostly sorry)

| Theorem | Status | File |
|---------|--------|------|
| `mertens_first_theorem` | **sorry** | RosserSchoenfeldPrime.lean:336 |
| `mertens_second_theorem` | **sorry** | RosserSchoenfeldPrime.lean:312 |
| `mertens_first_theorem'` | **sorry** | RosserSchoenfeldPrime.lean:355 |
| `mertens_second_theorem'` | **sorry** | RosserSchoenfeldPrime.lean:331 |

### Mertens Constants

| Definition | Description | File |
|------------|-------------|------|
| `meisselMertensConstant` | Meissel-Mertens constant B | SecondaryDefinitions.lean:92 |
| `mertensConstant` | Mertens constant E | SecondaryDefinitions.lean:100 |

---

## Mellin Calculus and Perron Formula

| Module | Description |
|--------|-------------|
| `PrimeNumberTheoremAnd.MellinCalculus` | Mellin transform theory |
| `PrimeNumberTheoremAnd.PerronFormula` | Perron's formula |
| `PrimeNumberTheoremAnd.ResidueCalcOnRectangles` | Residue calculus |

Key theorems in these modules include smoothed approximation identities and
contour integral representations.

---

## Auxiliary Results

### Asymptotics

| Theorem | Description | File |
|---------|-------------|------|
| `isLittleO_sqrt_mul_log` | `√x · log x = o(x)` | Consequences.lean:130 |
| `tendsto_floor_add_one_div_self` | `(⌊x⌋₊ + 1) / x → 1` | Consequences.lean:139 |

### Integral Results

| Lemma | Description | File |
|-------|-------------|------|
| `th43_b` | `π(⌊x⌋₊) = θ(x)/log(x) + ∫...` | Consequences.lean:30 |

---

## Borel-Carathéodory

| Theorem | Description | File |
|---------|-------------|------|
| `BorelCaratheodoryDeriv` | Derivative bound from real part | StrongPNT.lean:153 |
| `DerivativeBound` | General derivative bound | StrongPNT.lean:77 |

---

## Brun-Titchmarsh and Sieve Methods

| Module | Description |
|--------|-------------|
| `PrimeNumberTheoremAnd.BrunTitchmarsh` | Brun-Titchmarsh inequality |
| `PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.*` | Selberg sieve |

---

## Hadamard Factorization

| Module | Description |
|--------|-------------|
| `PrimeNumberTheoremAnd.HadamardFactorization` | Factorization of zeta |
| `PrimeNumberTheoremAnd.GeneralMeromorphic` | General meromorphic functions |

---

## Known Gaps (theorems with sorry)

The following important theorems exist but are not yet proven in Gauss:

1. **Mertens theorems** (first and second) - RosserSchoenfeldPrime.lean
2. **Various explicit bounds** in FKS2.lean
3. **Some secondary summary results** in SecondarySummary.lean

---

## Notes for Littlewood Integration

### Directly Usable
- `WeakPNT''` (`ψ ~[atTop] id`) - matches Chebyshev asymptotic needs
- `chebyshev_asymptotic` (`θ ~[atTop] id`) - theta asymptotic
- `riemannZeta.classicalZeroFree` - zero-free region definition
- Zero counting function definitions

### Need Adaptation
- Gauss uses `Chebyshev.psi` from Mathlib; Littlewood may need wrapper
- Zero sum definitions differ in structure
- Explicit formula representations may need translation

### Not in Gauss
- Landau's oscillation lemma machinery
- Schmidt's theorem infrastructure
- Weighted average formulas for sign changes
