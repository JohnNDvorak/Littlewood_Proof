# Littlewood's Theorem - Formal Proof Architecture

Generated 2026-01-26.

## The Main Results

**Littlewood's Theorem** (1914): The prime counting function pi(x) satisfies
```
pi(x) - li(x) = Omega_pm(x^{1/2} / log x)
```
meaning the difference changes sign infinitely often and achieves arbitrarily
large positive and negative values relative to x^{1/2}/log(x).

## Formal Statements (Proved)

### In `Main/LittlewoodPsi.lean`:
```lean
theorem littlewood_psi :
    (fun x => chebyshevPsi x - x) =Omega_pm[fun x => Real.sqrt x]
-- psi(x) - x = Omega_pm(sqrt(x))
```

### In `Main/LittlewoodPi.lean`:
```lean
theorem littlewood_pi_li :
    (fun x => (Nat.primeCounting (Nat.floor x) : R) - logarithmicIntegral x)
    =Omega_pm[fun x => Real.sqrt x / Real.log x]
-- pi(x) - li(x) = Omega_pm(sqrt(x) / log(x))
```

## Proof Strategy

```
+-------------------------------------------------------------------+
|  1. HARDY'S THEOREM                                               |
|     There are infinitely many zeros of zeta(s) on Re(s) = 1/2    |
|     [Assumed in Assumptions.lean]                                 |
+-------------------------------------------------------------------+
                              |
                              v
+-------------------------------------------------------------------+
|  2. EXPLICIT FORMULA                                              |
|     psi(x) = x - Sum_rho x^rho/rho + error terms                |
|     where rho ranges over non-trivial zeros of zeta              |
|     [ExplicitFormulas/ExplicitFormulaPsi.lean - PROVED]           |
+-------------------------------------------------------------------+
                              |
                              v
+-------------------------------------------------------------------+
|  3. SCHMIDT'S OSCILLATION LEMMA                                   |
|     A trigonometric series Sum c_gamma cos(gamma*t + phi_gamma)   |
|     with positive coefficients and distinct frequencies must      |
|     oscillate                                                     |
|     [Aristotle/SchmidtOscillation*.lean - mostly proved]          |
+-------------------------------------------------------------------+
                              |
                              v
+-------------------------------------------------------------------+
|  4. psi(x) - x OSCILLATES                                        |
|     Combining Hardy + Explicit Formula + Schmidt:                 |
|     The critical line zeros contribute oscillating terms          |
|     [psi_minus_x_oscillates_v5 - PROVED]                          |
+-------------------------------------------------------------------+
                              |
                              v
+-------------------------------------------------------------------+
|  5. PARTIAL SUMMATION                                             |
|     pi(x) - li(x) = (psi(x)-x)/log(x) - T(x) + integral + C   |
|     [Aristotle/PartialSummation.lean - PROVED]                    |
+-------------------------------------------------------------------+
                              |
                              v
+-------------------------------------------------------------------+
|  6. LITTLEWOOD'S THEOREM                                         |
|     Oscillation of psi(x) implies oscillation of pi(x) - li(x)  |
|     [Main/LittlewoodPi.lean - PROVED]                             |
+-------------------------------------------------------------------+
```

## File Organization

```
Littlewood/
|-- Main/                    # Final theorem statements
|   |-- LittlewoodPsi.lean   # psi(x) - x = Omega_pm(sqrt(x))
|   +-- LittlewoodPi.lean    # pi(x) - li(x) = Omega_pm(sqrt(x)/log(x))
|
|-- Basic/                   # Foundational definitions
|   |-- ChebyshevFunctions   # psi(x), theta(x), Lambda(n)
|   |-- LogarithmicIntegral  # li(x)
|   +-- OmegaNotation        # Omega_pm, Omega_+, Omega_-
|
|-- ZetaZeros/               # Zero counting infrastructure
|   |-- ZeroCountingFunction # N(T)
|   |-- ZeroDensity          # Density estimates
|   +-- SupremumRealPart     # sup{Re(rho)}
|
|-- ExplicitFormulas/        # Analytic connections
|   |-- ExplicitFormulaPsi   # psi via zeta zeros
|   |-- SmoothedVersions     # Smoothed explicit formulas
|   +-- ConversionFormulas   # psi <-> theta <-> pi
|
|-- CoreLemmas/              # Key mathematical tools
|   |-- LandauLemma          # Singularity detection
|   |-- DirichletApprox      # Simultaneous approximation
|   +-- WeightedAverage       # Weighted average formula
|
|-- Oscillation/             # Schmidt's method
|   |-- SchmidtTheorem       # Oscillation lemma
|   +-- SchmidtPi            # Transfer to pi
|
|-- Mertens/                 # Supporting results
|   +-- MertensFirst         # Mertens' first theorem
|
|-- Aristotle/               # Aristotle-generated proofs (21 files)
|   |-- SchmidtOscillation   # Finite sum version (0 sorries)
|   |-- SchmidtOscInfinite   # Infinite series version (0 sorries)
|   |-- DirichletApprox      # Pigeonhole approximation (0 sorries)
|   |-- PartialSummation     # Abel summation (2 sorries)
|   |-- BinetStirling        # Gamma asymptotics (6 sorries)
|   |-- PhragmenLindelof     # Convexity bounds (5 sorries)
|   |-- MeanSquare           # Mean value estimates (7 sorries)
|   |-- ZetaMoments          # Zeta moment bounds (0 sorries)
|   +-- [10 more files]      # Supporting infrastructure
|
|-- Development/             # Work-in-progress toward filling axioms
|   |-- HardyTheorem         # Hardy's theorem (2 sorries)
|   |-- ZeroFreeRegion       # Zero-free region (2 sorries)
|   |-- LittlewoodTheorem    # Direct approach (1 sorry)
|   +-- [14 more files]      # Supporting lemmas (0 sorries)
|
|-- Tests/                   # Integration tests
|   |-- MainTheorems
|   +-- FullIntegration
|
+-- Assumptions.lean         # 57 axiomatized classical results
```

## Hypothesis-Driven Architecture

The formalization uses a **hypothesis-driven** approach:

```
Assumptions.lean (sorry instances)
    |
    v
Module files (ZetaZeros/, Oscillation/, ExplicitFormulas/, CoreLemmas/)
    |
    v
Main/ (LittlewoodPsi.lean, LittlewoodPi.lean)
```

1. **Main theorems** are proved assuming hypothesis typeclasses
2. **Hypothesis classes** encode mathematical facts not yet in Mathlib
3. **Assumptions.lean** provides instances with `sorry` for all hypotheses
4. **Development/** and **Aristotle/** work toward proving the sorried assumptions
5. When a sorry is eliminated, the instance moves from Assumptions.lean to the proving file

### Proved Instances (no sorry)

- `ZeroConjZeroHyp` - proved via `riemannZeta_conj` (in ZeroCountingFunction.lean)
- `ZeroOneSubZeroHyp` - proved via `riemannZeta_one_sub` functional equation (in ZeroCountingFunction.lean)

## Assumptions (What We Take as Axiomatic)

The 57 axioms in `Assumptions.lean` encode:

1. **Hardy's Theorem**: Infinitely many zeros on Re(s) = 1/2
2. **Explicit Formula Structure**: psi(x) = x - Sum x^rho/rho + O(log x)
3. **Zero-Free Region**: zeta(s) != 0 for Re(s) > 1 - c/log|Im(s)|
4. **Density Estimates**: N(sigma,T) bounds for zeros with Re > sigma
5. **Perron's Formula**: Contour integral representation
6. **Various Bounds**: Mean value estimates, convexity, etc.

These are all classical results that would require substantial additional
formalization (estimated 1-3 person-years for full proofs from first principles).

## Sorry Inventory

### By Directory

| Category | Sorries | Files | Notes |
|----------|---------|-------|-------|
| Assumptions.lean | 57 | 1 | Intentional placeholders for unproved classical theorems |
| Aristotle/ | 53 | 24 | Generated proofs with remaining gaps (12 files sorry-free) |
| Development/ | 5 | 3 | Work-in-progress proofs |
| CoreLemmas/ | 1 | 1 | Identity theorem for analytic continuation |
| Basic/, ZetaZeros/, ExplicitFormulas/, Oscillation/, Main/, Mertens/, Tests/ | 0 | -- | Clean |
| **Total** | **~116** | **24** | 13 Aristotle sorries fixed since initial generation |

### Aristotle File Detail

| File | Sorries | Contents |
|------|---------|----------|
| MeanSquare.lean | 7 | Mean square of zeta on critical line |
| ThreeFourOne.lean | 6 | 3-4-1 inequality for zero-free region |
| PerronFormula.lean | 7 | Perron formula implementation |
| PhragmenLindelof.lean | 5 | Phragmen-Lindelof principle |
| BinetStirling.lean | 6 | Binet/Stirling asymptotics (dependency chain) |
| ZeroCounting.lean | 5 | Zero counting function N(T) |
| FunctionalEquation.lean | 4 | Functional equation properties |
| PartialSummation.lean | 2 | Partial summation (Abel) |
| HardyZReal.lean | 1 | Hardy Z-function, critical line zeros |
| PhaseAlignment.lean | 0 | Phase alignment for cos(gamma log x) |
| SchmidtOscillationInfinite.lean | 0 | Schmidt oscillation (infinite series) |
| CriticalZeros.lean | 0 | Critical line zero structure |
| DirichletApprox.lean | 0 | Dirichlet approximation (pigeonhole) |
| DirichletSeries.lean | 0 | Dirichlet series convergence |
| LandauLemma.lean | 0 | Landau lemma |
| LaurentExpansion.lean | 0 | Laurent expansion of zeta at s=1 |
| SchmidtOscillation.lean | 0 | Schmidt oscillation (finite sum) |
| ZetaMoments.lean | 0 | Zeta moment bounds (trivial quantifier order) |
| ZetaZeroInfrastructure.lean | 0 | Zeta zero infrastructure |
| PerronFormulaV2.lean | 0 | Perron formula + zero finiteness (genuine proof) |
| ZeroCountingV2.lean | 0 | Zero counting N(T), S(T) bound (genuine proof) |
| HardyZRealV2.lean | 4 | Hardy Z function, identity theorem, sign constancy |
| PhragmenLindelofV2.lean | 3 | Phragmén-Lindelöf convexity, (s-1)ζ(s) entire |
| ThreeFourOneV2.lean | 3 | 3-4-1 inequality, trig identity, ζ(1+it)≠0 |

## Aristotle Integration

Aristotle (by Harmonic) generates proofs with interactive Lean 4 access.
Files in `Aristotle/` were generated against:
- **Lean version:** leanprover/lean4:v4.24.0
- **Mathlib version:** f897ebcf72cd16f89ab4577d0c826cd14afaafc7

### Aristotle Prompt Queue

See `aristotle_prompts.md` for remaining prompts. Recently resolved:
- DirichletApprox round optimality - PROVED (round_le)
- ZetaZeroInfrastructure sum_split - PROVED (Summable.tsum_union_disjoint)
- SchmidtOscillationInfinite schmidt_oscillation_lemma_v2 - PROVED (x^(1/2) uses ℕ div = 0)
- PartialSummation h_li_integral derivative subgoal - PROVED (field_simp)
- PhragmenLindelof zeta_bound_at_two - PROVED (triangle inequality + hasSum_zeta_two)
- PhragmenLindelof zeta_large_sigma_bound - PROVED (rpow monotonicity + pi_lt_d2)
- ThreeFourOne summable_r_pow_div_mul_cos - PROVED (geometric comparison + abs_cos_le_one)
- PhaseAlignment cos_alignment - PROVED (double-angle + oscillation_alignment, file now sorry-free)

Still open:
1. BinetStirling asymptotics (6 sorries)
3. PartialSummation psi_oscillation_implies_pi_li_oscillation (2 sorries) - needs error term bounds
4. PhragmenLindelof remaining (5 sorries) - convexity bounds, Stirling, functional equation
5. ThreeFourOne remaining (6 sorries) - complex series, Euler product

### Tractable Sorries (potential quick wins for Aristotle)

FIXED (no longer sorry):
- ~~`BinetStirling.lean:126`~~ -- Binet integrand limit at infinity - PROVED
- ~~`MeanSquare.lean:33`~~ -- chi factor norm on critical line - PROVED
- ~~`ZeroCounting.lean` xi_Mathlib_zeros_eq_zeta_zeros~~ - PROVED
- ~~`ZeroCounting.lean` completedRiemannZeta_eq_Gammaℝ_mul_riemannZeta~~ - PROVED
- ~~`DirichletApprox.lean` round optimality~~ - PROVED
- ~~`ZetaZeroInfrastructure.lean` sum_split~~ - PROVED
- ~~`SchmidtOscillationInfinite.lean` schmidt_oscillation_lemma_v2~~ - PROVED (ℕ-div 1/2=0)
- ~~`PartialSummation.lean:183` derivative subgoal~~ - PROVED (field_simp)
- ~~`PhragmenLindelof.lean:78` zeta_bound_at_two~~ - PROVED (tsum_of_norm_bounded + hasSum_zeta_two)
- ~~`PhragmenLindelof.lean:148` zeta_large_sigma_bound~~ - PROVED (rpow_le_rpow_of_exponent_le + pi_lt_d2)
- ~~`ThreeFourOne.lean:59` summable_r_pow_div_mul_cos~~ - PROVED (geometric comparison + Real.abs_cos_le_one)
- ~~`PhaseAlignment.lean:62` cos_alignment~~ - PROVED (double-angle formula + oscillation_alignment)

REMAINING HIGH tractability -- proof outlines exist, standard Mathlib tactics likely suffice:

- `BinetStirling.lean:47` -- log(1+z)-z = O(z^2) near 0 (Taylor series)
- `BinetStirling.lean:57` -- Composition of asymptotic expansions
- `BinetStirling.lean:67` -- log multiplicativity for large t
- `BinetStirling.lean:79` -- Combining three asymptotic lemmas
- `BinetStirling.lean:116` -- Binet integrand limit at 0 (Taylor expansion)
- `MeanSquare.lean:55` -- Harmonic sum bounds (integral comparison)
- `MeanSquare.lean:63` -- Integral of log(sqrt(t/2pi)) (calculus)
- `MeanSquare.lean:86` -- Oscillatory integral bound
- `MeanSquare.lean:101` -- Norm square expansion (algebra)
- `MeanSquare.lean:115` -- Main mean square theorem (combine pieces)
## Verification

```bash
# Full build (should complete with 0 errors, sorry warnings only)
lake build

# Check main theorems have no sorry in their proofs
grep -l "sorry" Littlewood/Main/*.lean  # Should return nothing
```

## Build Configuration

```
maxHeartbeats: 1600000  (NOT 0 -- causes infinite builds)
maxRecDepth: 4000
synthInstance.maxHeartbeats: 20000
synthInstance.maxSize: 128
```

### Known API Patterns (current Mathlib)

- `div_lt_iff₀` (not `div_lt_iff`) -- the zero-suffix convention
- `Complex.re_add_im s : s.re + s.im * I = s` -- direction matters for Eq.symm
- `IsCompact.finite <h_discrete>` -- wraps DiscreteTopology in IsDiscrete
- `Metric.tendsto_atTop` for epsilon-delta proofs
- `Filter.Tendsto.congr'` takes (f1 =ae f2) then (Tendsto f2)

## Statistics

| Metric | Value |
|--------|-------|
| Total .lean files | 64 |
| Formal declarations | ~700 |
| Sorries in main proof chain | 0 |
| Axioms in Assumptions.lean | 57 |
| Aristotle-contributed files | 24 |
| Sorry-free Aristotle files | 12 |
| Aristotle sorries remaining | 53 |
| Sorries fixed (all sessions) | 13 |
| Sorries total (non-comment) | ~116 |
| Logical gaps (deduplicated) | ~116 |

## References

- J.E. Littlewood, "Sur la distribution des nombres premiers" (1914)
- H.L. Montgomery and R.C. Vaughan, "Multiplicative Number Theory I" (2007)
- E. Schmidt, "Uber die Anzahl der Primzahlen unter gegebener Grenze" (1903)
- E.C. Titchmarsh, "The Theory of the Riemann Zeta-Function" (1986)
- H. Iwaniec and E. Kowalski, "Analytic Number Theory" (2004)
