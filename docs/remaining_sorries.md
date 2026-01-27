# Remaining Sorries - Categorized by Difficulty

## SORRY-FREE FILES (8 total, no action needed)
- CriticalZeros.lean
- DirichletApprox.lean
- DirichletSeries.lean
- LandauLemma.lean
- LaurentExpansion.lean
- SchmidtOscillation.lean
- SchmidtOscillationInfinite.lean
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

### Recently Fixed
- **schmidt_oscillation_lemma_v2** (SchmidtOscillationInfinite.lean) - PROVED (ℕ-div 1/2=0, file now sorry-free)
- **h_li_integral derivative** (PartialSummation.lean) - PROVED (field_simp)
- **zeta_bound_at_two** (PhragmenLindelof.lean) - PROVED (tsum_of_norm_bounded + hasSum_zeta_two)
- **zeta_large_sigma_bound** (PhragmenLindelof.lean) - PROVED (rpow monotonicity + pi_lt_d2)
- **summable_r_pow_div_mul_cos** (ThreeFourOne.lean) - PROVED (geometric comparison + abs_cos_le_one)
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

### ThreeFourOne.lean (6 sorries)
- Complex logarithm series representations
- Euler product for log|zeta(s)|
- 3-4-1 inequality application to zeta product
- Requires: Euler product, series manipulation
- Fixed: summable_r_pow_div_mul_cos (geometric comparison)

### PhragmenLindelof.lean (5 sorries)
- Zeta bounds for sigma > 1 and on critical line
- Gamma function growth (Stirling's formula)
- Convexity bounds (Phragmen-Lindelof principle)
- Requires: Stirling, functional equation, Phragmen-Lindelof interpolation
- Fixed: zeta_bound_at_two (π²/6 bound), zeta_large_sigma_bound (σ≥2 bound)

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

### PartialSummation.lean (2 sorries)
- Domination arguments for oscillation transfer (psi → pi-li)
- Fixed: h_li_integral derivative subgoal (field_simp)

## SUMMARY
| Category | Count | Action |
|----------|-------|--------|
| Sorry-free files | 8 | None needed |
| False theorems | 3 | Fix hypotheses |
| Possibly tractable | 1 | Try with Aristotle |
| Needs Aristotle | 41 | Submit prompts |
| **Total remaining sorries** | **45** | |
