# Remaining Sorries - Categorized by Difficulty

## SORRY-FREE FILES (7 total, no action needed)
- CriticalZeros.lean
- DirichletApprox.lean
- DirichletSeries.lean
- LandauLemma.lean
- LaurentExpansion.lean
- SchmidtOscillation.lean
- ZetaZeroInfrastructure.lean

## FALSE THEOREMS (cannot be proved as stated)
These theorems have incorrect hypotheses and need statement changes:
- `zeta_functional_equation` (FunctionalEquation.lean) - fails at s=-2
- `completed_zeta_zeros_eq_zeta_zeros` (FunctionalEquation.lean) - fails at s=-2
- `xi_Mathlib_eq_RiemannXi` (ZeroCounting.lean) - fails at s=-2
See docs/FALSE_THEOREMS.md for details.

## POSSIBLY TRACTABLE (medium difficulty)
Worth another attempt with Aristotle or interactive Lean:

1. **cos_alignment** (PhaseAlignment.lean, 1 sorry)
   - Requires Dirichlet simultaneous approximation for arbitrarily large aligned times
   - `align_phases` only gives small t > 0; need import of DirichletApprox or reproof
   - Proof sketch in comments

2. **schmidt_oscillation_lemma_v2** (SchmidtOscillationInfinite.lean, 1 sorry)
   - Proof structure exists, partially complete

### Recently Fixed
- **sum_split** (ZetaZeroInfrastructure.lean) - PROVED via `Summable.tsum_union_disjoint`

## NEEDS ARISTOTLE (deep analytic number theory)
All remaining sorries require substantial mathematical infrastructure:

### BinetStirling.lean (6 sorries)
- Complex logarithm asymptotics and Stirling approximation
- Taylor expansion analysis near z=0
- Requires: HasDerivAt, series manipulation, real/imaginary part tracking

### MeanSquare.lean (7 sorries)
- Harmonic sum asymptotics (Euler-Mascheroni)
- Oscillatory integral bounds
- Mean square decomposition (diagonal + off-diagonal)
- Requires: integral estimates, asymptotic analysis

### PerronFormula.lean (7 sorries)
- Contour integration and residue calculus
- Horizontal/vertical segment bounds
- Perron's formula main statement
- Requires: complex contour integration (not in Mathlib)

### ThreeFourOne.lean (7 sorries)
- Complex logarithm series representations
- Euler product for log|zeta(s)|
- 3-4-1 inequality application to zeta product
- Requires: Euler product, series manipulation

### PhragmenLindelof.lean (7 sorries)
- Zeta bounds for sigma > 1 and on critical line
- Gamma function growth (Stirling's formula)
- Convexity bounds (Phragmen-Lindelof principle)
- Requires: Dirichlet series triangle inequality, Stirling

### FunctionalEquation.lean (4 sorries, 2 are FALSE)
- Poisson summation for theta
- Gamma-cosine identity
- 2 false theorems (see above)

### ZeroCounting.lean (5 sorries)
- RiemannXi differentiability (entire function)
- Argument principle for zero counting
- Riemann-von Mangoldt formula
- 1 false theorem (see above)

### HardyZReal.lean (2 sorries)
- Completed zeta conjugation (identity theorem)
- Hardy Z function phase calculation

### PartialSummation.lean (3 sorries)
- Integration by parts for Dirichlet series
- Domination arguments for oscillation

## SUMMARY
| Category | Count | Action |
|----------|-------|--------|
| Sorry-free files | 7 | None needed |
| False theorems | 3 | Fix hypotheses |
| Possibly tractable | 2 | Try with Aristotle |
| Needs Aristotle | 45 | Submit prompts |
| **Total remaining sorries** | **50** | |
