# Hardy Theorem Chain Status

## Goal
Prove: `∀ T : ℝ, ∃ t : ℝ, t > T ∧ riemannZeta (1/2 + t * I) = 0`

## Available Building Blocks (all sorry-free)

| Component | File | Key Theorem |
|-----------|------|-------------|
| Z is real | HardyZRealV4 | `hardyZV4_real` |
| Z is real (alt) | HardyZReal | `completedRiemannZeta_real_on_critical_line` |
| Z continuous | HardyZRealV2 | `continuous_hardyZV2` |
| Z zeros ↔ ζ zeros | HardyZRealV2 | `hardyZV2_zero_iff_zeta_zero` |
| |Z| = |ζ| | HardyZRealV2 | `hardyZV2_abs_eq_zeta_abs` |
| Sign constancy | HardyZRealV2 | `hardyZV2_constant_sign_between_zeros` |
| |e^{iθ}| = 1 | HardyEstimatesPartial | `exp_iTheta_norm` |
| Cauchy-Schwarz | HardyZContradiction | `Z_integral_cauchy_schwarz` |
| Constant sign → |integral| | HardyZContradiction | `Z_constant_sign_implies_integral_eq_abs` |
| Asymptotic contradiction | HardyZContradiction | `asymptotic_contradiction` |
| Contradiction final step | HardyZContradiction | `contradiction_final_step` |
| Sign change → zero (IVT) | HardyTheorem (Dev) | `sign_change_implies_zero` |
| Sign changes → ∀T ∃t | HardyTheorem (Dev) | `hardy_from_sign_changes` |
| Z not identically zero | HardyTheorem (Dev) | `hardyZ_not_zero` |
| Z growth bound | HardyTheorem (Dev) | `hardyZ_growth_bound` (uses PhragmenLindelof sorry) |
| Mean square ∫|ζ|² | ZetaMeanSquare | `zeta_second_moment` (via typeclass) |
| ζ conjugation | HardyZConjugation | `completedRiemannZeta_conj` (1 sorry in alt proof) |
| Zeros finite in strip | CriticalZeros | `critical_zeros_finite` |
| ζ on Re=1.1 bounded | HardyZContradiction | `riemannZeta_bound_1` |

## Assumption Structures (4 variants)

| Structure | File | Fields |
|-----------|------|--------|
| `BuildingBlocks` | HardyZContradiction | completed_real, Z_real, Z=norm, mean_sq, integral, continuous |
| `BuildingBlocksExtended` | HardyZContradiction | + convexity_bound |
| `HardyHypotheses'` | HardyInfrastructure | completed_real, Z_continuous, integral_bound, sq_lower |
| `HardyEstimates` | HardyEstimatesPartial | mean_sq_lower, first_moment_upper, Z_continuous |
| `HardyAssumptions` | HardyAssumptions | Z_real, continuous, mean_sq, integral, convexity |

## The Gap (1 critical sorry + 1 minor sorry in Dev)

### Critical: `hardyZ_sign_change_in_interval` (Dev/HardyTheorem.lean:539)

Two possible proof strategies:

### Strategy A: Schmidt Oscillation (via explicit formula)
1. Riemann-Siegel approximate functional equation: Z(t) = 2Σ n^{-1/2} cos(θ(t) - t log n) + O(t^{-1/4})
2. This is a trigonometric sum with non-vanishing coefficients
3. Apply `schmidt_oscillation_lemma_finite` (already proved in SchmidtNew.lean)
4. Get sign changes of Z → zeros on critical line

**Status:** BLOCKED — needs Riemann-Siegel formula (not in any Aristotle file)

### Strategy B: Contradiction (via mean square vs first moment)
1. If Z has constant sign eventually → |∫Z| = ∫|Z| (PROVED)
2. By convexity bound |Z(t)| ≤ C(1+|t|)^{1/4+ε}: ∫Z² ≤ sup|Z| · ∫|Z|
3. So c·T·log(T) ≤ C·T^{1/4+ε} · C'·T^{1/2+ε} = O(T^{3/4+2ε})
4. For ε < 1/8, this is a contradiction for large T (PROVED)
5. Therefore Z changes sign infinitely often

**Status:** BLOCKED — needs to instantiate `BuildingBlocks`/`BuildingBlocksExtended`:
- `mean_square_lower_bound`: Available via ZetaMeanSquare typeclass (needs instantiation)
- `hardyZ_integral_bound`: NO direct proof available — needs new Aristotle submission
- `convexity_bound`: PhragmenLindelof `zeta_critical_line_bound` has sorry
- `completed_real`: PROVED in multiple files (HardyZReal, HardyZConjugation)
- `hardyZ_continuous`: PROVED in HardyZRealV2

### Minor: `gamma_quarter_in_slitPlane` (Dev/HardyTheorem.lean:268)
For t ≠ 0: show Γ(1/4 + it/2) ∈ slitPlane (not a non-positive real).
Proved at t = 0. Needs reflection formula analysis for t ≠ 0.

## New Aristotle File (1de9e757)

HardyEstimatesPartial.lean — budget reached, 81 lines. Provides:
- `HardyEstimates` structure (3 fields: mean_sq_lower, first_moment_upper, Z_continuous)
- `exp_iTheta_norm` lemma (proved)
- Definitions of hardyTheta (via Complex.log.im), hardyZ, signChanges

**Assessment:** Adds little over existing HardyInfrastructure/HardyAssumptions.
The main theorem was NOT reached before budget exhaustion.

## What Would Close the Chain

**Minimum needed for Strategy B (contradiction):**
1. `hardyZ_integral_bound`: ∀ ε > 0, ∃ C, ∀ T ≥ 1, |∫₀ᵀ Z(t) dt| ≤ C · T^{1/2+ε}
2. `zeta_critical_line_bound`: ‖ζ(1/2+it)‖ ≤ C · |t|^{1/2} for |t| ≥ 1
3. `mean_square_lower_bound`: ∃ c > 0, ∫₀ᵀ |ζ(1/2+it)|² dt ≥ c · T · log T
4. Wire these into `BuildingBlocksExtended` and invoke `contradiction_final_step`

Items 2 and 3 could be Aristotle prompts. Item 1 typically follows from
the approximate functional equation.

**Minimum needed for Strategy A (Schmidt):**
1. Riemann-Siegel approximate functional equation for Z(t)
2. Non-vanishing of leading coefficients (from existence of zeros)
3. Tail bound matching o(x^{1/2})

## Downstream Chain (once Hardy is proved)
```
Hardy infinite zeros (Set.Infinite)
  → nonzero coefficients in explicit formula
  → Schmidt oscillation (already proved: trigPoly_zero_iff_coeffs_zero)
  → ψ(x) - x = Ω±(√x) (LittlewoodPsi.lean)
  → π(x) - li(x) = Ω±(√x / log x) (LittlewoodPi.lean)
  → MAIN THEOREM COMPLETE
```
