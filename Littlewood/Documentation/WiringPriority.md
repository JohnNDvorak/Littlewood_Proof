# Hypothesis Wiring Priority

Updated: 2026-01-29

## Summary (revised after deep type analysis)

| Category | Count | Notes |
|----------|-------|-------|
| ALREADY PROVED | 4 | ZeroConjZero, ZeroOneSub, FunctionalEq, LambdaSymmetry |
| DIRECTLY WIREABLE | 0 | No exact type matches found |
| BRIDGE NEEDED (feasible) | ~5-8 | ZeroCounting classes via NAsymptotic, with constant manipulation |
| BRIDGE NEEDED (hard) | ~10 | Landau (real→complex upcast), Schmidt (trig poly→ψ application) |
| MISSING (no Aristotle proof) | ~40+ | Explicit formula, weighted average, RH-conditional, etc. |
| **Total hypothesis classes** | **~62** |

### Key finding
Most hypothesis classes need **application-specific proofs**, not just the
abstract mathematical ingredients. For example:
- SchmidtNew proves trig poly oscillation, but SchmidtPsiOscillationHyp needs
  the result **applied to chebyshevPsi** via the explicit formula
- LandauLemma proves real Dirichlet series singularity, but LandauLemmaSeriesHyp
  needs complex coefficients with type upcasting
- NAsymptotic proves N(T) asymptotics, but ZeroCountingAsymptoticHyp needs
  constant term adjustment and definition bridging

## Tier 1: Ready to Wire (types likely match)

| Hypothesis | Aristotle Source | Key Theorem | Notes |
|------------|------------------|-------------|-------|
| ZeroCountingAsymptoticHyp | ZeroCountingNew | zero_counting_main_term | Constant term adjustment needed |
| ZeroCountingCrudeBoundHyp | NAsymptotic / ZeroCountingNew | Derive from asymptotic | Extract explicit C |
| ZeroCountingTendstoHyp | ZeroCountingNew | Derive from main term | N(T) ~ T log T → ∞ |
| ZeroCountingRvmExplicitHyp | NZerosStirling | N_from_S_and_Stirling | Explicit formula |
| ZeroCountingMainTermHyp | ZeroCountingNew | zero_counting_main_term | Ratio limit |
| ZeroCountingAsymptoticRatioHyp | ZeroCountingNew | Derive | Limit form |
| SchmidtPsiOscillationHyp | SchmidtNew | schmidt_oscillation | Core oscillation |
| PsiOscillationSqrtHyp | SchmidtNew | Consequence | √x lower bound |
| OmegaMinusNecessityHyp | SchmidtNew | Consequence | Lower bound |
| OmegaPlusNecessityHyp | SchmidtNew | Consequence | Upper bound |
| HardyCriticalLineZerosHyp | HardyZRealV4 | hardyZ_infinitely_many_zeros | Check if proved |
| ZeroCountingSummabilityHyp | ZeroDensity | Explicit convergence | Lines 103-206 |
| ZeroCountingSumInvGammaAsymptoticHyp | ZeroDensity | Asymptotic | Sum 1/γ ~ log T |
| ZeroCountingTailSqAsymptoticHyp | ZeroDensity | Tail estimate | ∑_{γ>T} 1/γ² = O(1/T) |
| ZeroSumTailHyp | ZeroDensity | Tail bound | ∑_{γ>T} 1/γ² |
| LandauLemmaHyp | LandauLemma | landau_dirichlet_singularity | Lines 150-199 |
| LandauLemmaSeriesHyp | LandauLemma | Applied to zeta | Lines 261-272 |
| DirichletIntegralConvergesHyp | LandauLemma | Convergence | Implicit |
| DirichletIntegralAnalyticHyp | LandauLemma | Analyticity | Implicit |
| DirichletIntegralDerivHyp | LandauLemma | Differentiation | Standard |
| RadiusExceedsAbscissaHyp | LandauLemma | Singularity | Implicit |
| LandauExtensionHyp | LandauLemma | Extension | Lines 206-256 |
| ZetaLogDerivPoleHyp | LandauLemma | Pole structure | Follows from FE |

## Tier 2: Need Definition Bridge

| Hypothesis | Aristotle Source | Gap |
|------------|------------------|-----|
| OmegaPsiToThetaHyp | PsiThetaBound / ChebyshevThetaV2 | theta def mismatch |
| OmegaThetaToPiLiHyp | SchmidtNew | pi/li def mismatch |
| ThetaBoundHyp | ThetaLinearBoundV2.theta_O_n | theta: ℕ→ℝ vs ℝ→ℝ |
| PsiErrorBoundHyp | ChebyshevThetaV2 | Bounds in different form |
| ChebyshevErrorBoundThetaHyp | SupremumRealPart | Different constants |
| PsiOscillationFromCriticalZerosHyp | Need connection theorem | Hardy → ψ oscillation |
| ZeroCountingSpecialValuesHyp | ZeroCountingNew | Computational bounds |
| FirstZeroOrdinateHyp | ZeroCountingNew | Specific ordinates |
| DirichletIntegralPowerSeriesHyp | LandauLemma | Power series from analyticity |
| SumOverPositiveOrdinatesHyp | ZeroDensity | Zero sum theory |
| ZeroCountingSumOneEqHyp | ZeroCountingNew | N(T) = specific formula |
| ThetaOscillationMinusHyp | Derive from psi | θ from ψ |
| DensityRiemannHypothesisInvRhoAsymptoticHyp | Needs RH | RH-conditional |

## Tier 3: Need New Aristotle Proof

| Hypothesis | What's Missing |
|------------|----------------|
| ExplicitFormulaPsiHyp | Full explicit formula for ψ₀(x) |
| ExplicitFormulaPsiSmoothedHyp | Smoothed version |
| ExplicitFormulaIntegralHyp | Integrated form |
| ExplicitFormulaDoubleIntegralHyp | Double integrated form |
| PsiMellinHyp | Mellin transform connectivity |
| MellinContourShiftHyp | Contour integral shift |
| ZeroSumBoundRHHyp | RH-conditional bounds |
| PsiErrorBoundRHHyp | RH-conditional ψ error |
| WeightedAverageFormulaRHHyp | Weighted averaging technique |
| IntegralPsiMinusXHyp | ∫(ψ-x) bound |
| RhoToGammaErrorHyp | RH oscillation bounds |
| MainSumBoundHyp | Weighted sum bound |
| AlignedSumLargeHyp | Alignment result |
| MellinPsiIdentityHyp | Mellin identity |
| ZeroFreeRegionHyp | De la Vallée Poussin region |
| ZetaZeroSupRealPartDichotomyHyp | Θ dichotomy |
| ChebyshevErrorBoundZeroFreeHyp | Zero-free region bound |
| ThetaOscillationRHHyp | RH theta oscillation |
| ZeroCountingFifteenHyp | Computational N(15) |
| ZeroCountingLowerBoundHyp | Lower bound form |
| ZeroCountingLocalDensityHyp | Local distribution |
| ZeroGapsLowerBoundHyp | Gap lower bound |
| ZeroCountingSummableXPowRhoDivHyp | Conditional convergence |

## Already Proved (4 instances)

1. ZeroConjZeroHyp ✓
2. ZeroOneSubZeroHyp ✓
3. FunctionalEquationHyp ✓
4. LambdaSymmetryHyp ✓
