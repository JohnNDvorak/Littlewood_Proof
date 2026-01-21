# LandauLemma.lean Sorry Analysis (Task 57)

## Summary
- **Total sorries:** 11
- **Fillable now:** 0
- **Might be provable with effort:** 1 (ZetaLogDerivPoleHyp)
- **Fundamentally unprovable (parametric):** 10

## Categorization

### Category A: Might Be Fillable with TypeBridge/Mathlib
**Count: 1**

#### Sorry 11: Line 437 - `ZetaLogDerivPoleHyp` instance
- **Statement:** If ζ(ρ) = 0, then -ζ'/ζ is not analytic at ρ
- **Mathlib has this?** PARTIAL
- **Key Mathlib tools:**
  - `analyticOrderAt` - order of vanishing of analytic function
  - `AnalyticAt.analyticOrderAt_eq_natCast` - characterization of order
  - `differentiableAt_riemannZeta` - ζ is differentiable away from 1
  - `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` - isolated zeros
- **Proof sketch:**
  1. ζ is analytic at ρ (since ρ ≠ 1 for zeros in critical strip)
  2. ζ(ρ) = 0, so analyticOrderAt ζ ρ ≥ 1
  3. ζ(s) = (s - ρ)^n · g(s) locally, with g(ρ) ≠ 0
  4. -ζ'/ζ = -n/(s-ρ) - g'/g has a pole at ρ
  5. Pole implies not analytic
- **Fillable now?** MAYBE with ~20-40 lines of work
- **Complexity:** MEDIUM

### Category B: Needs Additional LSeries Work
**Count: 0**

(TypeBridge provides LSeries infrastructure, but the Landau lemma hypotheses
need the full singularity detection theorem, not just convergence/analyticity)

### Category C: Fundamentally Unprovable (Parametric Hypotheses)
**Count: 10**

These sorries are in instances that claim to prove properties for ALL functions A : ℝ → ℝ:

| Line | Instance | Why Unprovable |
|------|----------|----------------|
| 396, 398 | `LandauLemmaHyp A σ_c` | Claims Landau for ANY A |
| 403 | `DirichletIntegralConvergesHyp A σ_c` | Claims convergence for ANY A |
| 408 | `DirichletIntegralAnalyticHyp A σ_c` | Claims analyticity for ANY A |
| 413 | `DirichletIntegralDerivHyp A σ_c` | Claims deriv exists for ANY A |
| 418 | `DirichletIntegralPowerSeriesHyp A σ_c` | Claims power series for ANY A |
| 423 | `RadiusExceedsAbscissaHyp A σ_c` | Claims radius bound for ANY A |
| 428 | `LandauExtensionHyp A σ₀` | Claims extension for ANY A |
| 432 | `LandauLemmaSeriesHyp a σ_c` | Claims series version for ANY a |

**Why these are unprovable:**
The Landau lemma only applies to functions with specific properties:
- Non-negative for large x
- Monotone or bounded growth
- The integral actually converges somewhere

These instances claim the properties hold for ALL functions A, which is FALSE.
For example, A(x) = 0 is analytic everywhere, contradicting Landau's conclusion.

### Category D: Blocked on Prior Work
**Count: 1**

#### Sorry 1: Line 387 - `zeta_zero_implies_vonMangoldt_singularity`
- **Statement:** If ζ(ρ) = 0, von Mangoldt LSeries is not analytic at ρ
- **Depends on:** `ZetaLogDerivPoleHyp` instance AND analytic continuation
- **Fillable now?** NO
- **Blocker:** Needs to connect L(Λ,s) = -ζ'/ζ(s) for Re(s) > 1 to behavior at ρ

## TypeBridge Connection Analysis

TypeBridge.lean provides:
- `lseries_analytic_from_mathlib` - LSeries analyticity
- `neg_zeta_logderiv_eq_vonMangoldt` - L(Λ,s) = -ζ'/ζ(s) for Re(s) > 1
- `partial_sums_monotone` - monotonicity of partial sums
- `landau_lseries_not_analytic_at_boundary` - boundary singularity (has sorry)

**Key insight:** TypeBridge's `landau_lseries_not_analytic_at_boundary` is the
LSeries version of Landau's lemma, but it also has a sorry for the same reason:
the singularity detection theorem is not in Mathlib.

## Recommendations

1. **ZetaLogDerivPoleHyp (Sorry 11) is the only actionable item**
   - Uses `analyticOrderAt` from Mathlib
   - Proof: zeros of analytic functions give poles in log derivative
   - Estimated: 20-40 lines, MEDIUM complexity

2. **The 10 parametric instances should be REDESIGNED**
   - Current design: `instance (A : ℝ → ℝ) (σ_c : ℝ) : LandauLemmaHyp A σ_c`
   - Better design: Add hypotheses on A, e.g., `[NonNegEventually A] [HasAbscissa A σ_c]`
   - This is an architecture change, not a proof task

3. **TypeBridge work helps but doesn't close sorries**
   - The LSeries → dirichletIntegral bridge exists
   - But the core singularity detection theorem is still missing

## Conclusion

- **0 sorries fillable immediately**
- **1 sorry (ZetaLogDerivPoleHyp) potentially provable with Mathlib's analyticOrderAt**
- **10 sorries fundamentally unprovable due to overly general parametric design**
- TypeBridge provides infrastructure but not the final theorem
