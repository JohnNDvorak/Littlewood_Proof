# Remaining Sorries - Categorized by Difficulty

## SORRY-FREE FILES (12 total, no action needed)
- CriticalZeros.lean
- DirichletApprox.lean
- DirichletSeries.lean
- LandauLemma.lean
- LaurentExpansion.lean
- PerronFormulaV2.lean
- PhaseAlignment.lean
- SchmidtOscillation.lean
- SchmidtOscillationInfinite.lean
- ZeroCountingV2.lean
- ZetaMoments.lean
- ZetaZeroInfrastructure.lean

## FALSE THEOREMS (cannot be proved as stated)
These theorems have incorrect hypotheses and need statement changes:
- `zeta_functional_equation` (FunctionalEquation.lean) - fails at s=-2
- `completed_zeta_zeros_eq_zeta_zeros` (FunctionalEquation.lean) - fails at s=-2
- `xi_Mathlib_eq_RiemannXi` (ZeroCounting.lean) - fails at s=-2
See docs/FALSE_THEOREMS.md for details.

## POSSIBLY TRACTABLE (medium difficulty)
No currently identified tractable targets. All remaining sorries require deep infrastructure.

### Recently Fixed
- **completedRiemannZeta_conj** (HardyZReal.lean) - PROVED (identity theorem for entire functions via completedRiemannZeta₀)
- **cos_alignment** (PhaseAlignment.lean) - PROVED (double-angle + oscillation_alignment, file now sorry-free)
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

### HardyZReal.lean (1 sorry)
- ~~Completed zeta conjugation~~ - PROVED (identity theorem for entire functions)
- Hardy Z function phase calculation

### PartialSummation.lean (2 sorries)
- Domination arguments for oscillation transfer (psi → pi-li)
- Fixed: h_li_integral derivative subgoal (field_simp)

### HardyZRealV2.lean (4 sorries)
- Hardy Z function real-valuedness (Gamma phase argument)
- Gamma duplication formula at 1/4+it/2
- Continuity of Z(t) (arg(Γ) continuity)
- Sign constancy between zeros (IVT)
- Proved: identity_theorem_extension_v2, hardyZV2_zero_iff_zeta_zero, hardyZV2_abs_eq_zeta_abs

### PhragmenLindelofV2.lean (3 sorries)
- (s-1)ζ(s) differentiability at s=1 (removable singularity)
- Polynomial-to-exponential growth condition
- Zeta growth estimate in critical strip
- Proved: phragmen_lindelof_convexity_v2 (Hadamard three-lines), polynomial_growth_implies_bounded_of_boundary_bounded_v2

### ThreeFourOneV2.lean (3 sorries)
- log‖ζ(s)‖ as Euler product tsum
- 3-4-1 log combination non-negativity
- ζ(1+it) ≠ 0 (limit argument)
- Proved: trig_ineq_v2 (nlinarith), three_four_one_v2 (conditional on log combination)

## SUMMARY
| Category | Count | Action |
|----------|-------|--------|
| Sorry-free files | 12 | None needed |
| False theorems | 3 | Fix hypotheses |
| Possibly tractable | 0 | -- |
| Needs Aristotle | 50 | Submit prompts |
| **Total remaining sorries** | **53** | |
