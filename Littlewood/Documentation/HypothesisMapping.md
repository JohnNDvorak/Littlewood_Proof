# Hypothesis to Aristotle Mapping

Updated: 2026-01-29

## Legend
- PROVED: Instance has a real proof (no sorry)
- WIREABLE: Aristotle theorem exists, bridge code needed
- PARTIAL: Aristotle has related result, type mismatch or gap
- BLOCKED: Requires multi-step chain or missing Aristotle proof
- MISSING: No Aristotle coverage yet

---

## SECTION 1: Explicit Formula Hypotheses (11 classes)

### ExplicitFormulaPsiHyp
**Status**: PARTIAL
**Requires**: `forall x, 1 < x -> exists E, ||E|| <= log x /\ psi_0(x) = x - sum rho x^rho/rho - log(2pi) - ... + E`
**Aristotle source**: `TruncatedExplicitFormula.psi_as_trig_sum`
**Gap**: Aristotle's version is truncated (sum over zeros in box, not tsum), and uses `TruncatedExplicitFormula.chebyshevPsi` not `chebyshevPsi`. Bridge `chebyshevPsiV3_eq_chebyshevPsi` helps but truncation vs full sum is a real mathematical gap.

### ExplicitFormulaPsiSmoothedHyp
**Status**: MISSING
**Requires**: Smoothed explicit formula for psi
**Aristotle source**: None

### ExplicitFormulaIntegralHyp
**Status**: MISSING
**Requires**: Integral of psi explicit formula
**Aristotle source**: None

### ExplicitFormulaDoubleIntegralHyp
**Status**: MISSING
**Requires**: Double integral of psi explicit formula
**Aristotle source**: None

### PsiMellinHyp
**Status**: MISSING
**Requires**: Mellin transform representation of psi
**Aristotle source**: None

### MellinContourShiftHyp
**Status**: MISSING
**Requires**: Contour shift for Mellin transform
**Aristotle source**: None

### ZeroSumBoundRHHyp
**Status**: MISSING
**Requires**: ||sum rho x^rho/rho|| <= 10 sqrt(x) log^2(x) under RH
**Aristotle source**: None

### PsiErrorBoundHyp
**Status**: MISSING
**Requires**: |psi(x) - x| <= 10 x^Theta log(x)
**Aristotle source**: None directly (ChebyshevTheta has related bounds but different form)

### PsiErrorBoundRHHyp
**Status**: MISSING
**Requires**: |psi(x) - x| <= 10 sqrt(x) log^2(x) under RH
**Aristotle source**: None

### OmegaPsiToThetaHyp
**Status**: PARTIAL
**Requires**: psi = Omega_pm(f) implies theta = Omega_pm(f)
**Aristotle source**: PsiThetaBound.psi_theta_bound proves |psi-theta| <= C*sqrt(x), which is the key ingredient. But the Omega transfer needs more.
**Gap**: Need to show that if psi oscillates at scale f(x) >> sqrt(x), then theta also oscillates at that scale since |psi-theta| = O(sqrt(x)).

### OmegaThetaToPiLiHyp
**Status**: PARTIAL
**Requires**: theta = Omega_pm(f) implies pi-li = Omega_pm(f/log)
**Aristotle source**: PartialSummationPiLi (commented out - conflicts) has partial summation results
**Gap**: Needs partial summation formula connecting theta to pi(x)

---

## SECTION 2: Weighted Average Hypotheses (7 classes)

### WeightedAverage.WeightedAverageFormulaRHHyp
**Status**: MISSING - No Aristotle coverage

### WeightedAverage.IntegralPsiMinusXHyp
**Status**: MISSING

### WeightedAverage.RhoToGammaErrorHyp
**Status**: MISSING

### WeightedAverage.SumOverPositiveOrdinatesHyp
**Status**: MISSING

### WeightedAverage.ZeroSumTailHyp
**Status**: MISSING

### WeightedAverage.MainSumBoundHyp
**Status**: MISSING

### WeightedAverage.AlignedSumLargeHyp
**Status**: MISSING

---

## SECTION 3: Schmidt/Oscillation Hypotheses (9 classes)

### Schmidt.SchmidtPsiOscillationHyp
**Status**: BLOCKED
**Requires**: psi(x) - x = Omega_pm(x^(Theta-epsilon))
**Aristotle source**: SchmidtNew.schmidt_oscillation (trig poly oscillation)
**Gap**: Multi-step chain: explicit formula -> zero sum is trig poly -> oscillation. Needs full explicit formula + Theta > 0.

### Schmidt.PsiOscillationSqrtHyp
**Status**: BLOCKED
**Requires**: psi(x) - x = Omega_pm(sqrt(x))
**Depends on**: SchmidtPsiOscillationHyp + Theta = 1/2 or 1

### Schmidt.MellinPsiIdentityHyp
**Status**: MISSING

### Schmidt.OmegaMinusNecessityHyp
**Status**: BLOCKED (depends on Schmidt chain)

### Schmidt.OmegaPlusNecessityHyp
**Status**: BLOCKED (depends on Schmidt chain)

### Schmidt.HardyCriticalLineZerosHyp
**Status**: BLOCKED - WAITING ON ARISTOTLE
**Requires**: Set.Infinite { rho in zetaNontrivialZeros | rho.re = 1/2 }
**Aristotle source**: Hardy's theorem prompt submitted, awaiting result
**Note**: CRITICAL BLOCKER for main theorem

### Schmidt.PsiOscillationFromCriticalZerosHyp
**Status**: BLOCKED (depends on Hardy + Schmidt chain)

### Schmidt.ThetaOscillationMinusHyp
**Status**: BLOCKED

### Schmidt.ThetaOscillationRHHyp
**Status**: BLOCKED

---

## SECTION 4: Zero Density Hypotheses (6 classes)

### ZetaZeros.Density.ZeroCountingSummabilityHyp
**Status**: MISSING - No Aristotle coverage
**Requires**: Summable (gamma^(-alpha)) for alpha > 1, and Summable (1/|rho|^2)
**Note**: Follows from N(T) ~ (T/2pi) log T asymptotic + summation by parts

### ZetaZeros.Density.ZeroCountingSumInvGammaAsymptoticHyp
**Status**: MISSING

### ZetaZeros.Density.ZeroCountingSumOneEqHyp
**Status**: PARTIAL
**Requires**: sum_{gamma <= T} 1 = N(T)
**Note**: Essentially tautological if definitions match

### ZetaZeros.Density.ZeroCountingTailSqAsymptoticHyp
**Status**: MISSING

### ZetaZeros.Density.RiemannHypothesisInvRhoAsymptoticHyp
**Status**: MISSING

### ZetaZeros.Density.ZeroCountingSummableXPowRhoDivHyp
**Status**: MISSING

---

## SECTION 5: Zeta Zero Supremum Hypotheses (4 classes)

### ZetaZeros.ZeroFreeRegionHyp
**Status**: PARTIAL
**Requires**: exists c > 0, forall rho, rho.re < 1 - c/log(|rho.im| + 2)
**Aristotle source**: ThreeFourOneV2 proves 3-4-1 inequality (zeta_ne_zero_re_one_v2), but not the full de la Vallee-Poussin zero-free region
**Gap**: Need quantitative zero-free region, not just Re(s) = 1

### ZetaZeros.ZetaZeroSupRealPartDichotomyHyp
**Status**: MISSING
**Requires**: Theta = 1 or Theta = 1/2

### ZetaZeros.ChebyshevErrorBoundZeroFreeHyp
**Status**: MISSING

### ZetaZeros.ChebyshevErrorBoundThetaHyp
**Status**: MISSING

---

## SECTION 6: Zero Counting Hypotheses (12 classes + 2 proved)

### ZetaZeros.ZeroConjZeroHyp
**Status**: PROVED in ZeroCountingFunction.lean:1618
**Proof**: riemannZeta_conj from Aristotle/HardyZReal.lean

### ZetaZeros.ZeroOneSubZeroHyp
**Status**: PROVED in ZeroCountingFunction.lean:1640
**Proof**: Functional equation

### ZetaZeros.ZeroCountingTendstoHyp
**Status**: PARTIAL
**Requires**: N(T) -> infinity
**Aristotle source**: Follows from N(T) ~ (T/2pi) log T (RiemannVonMangoldt)
**Gap**: Need to extract tendsto from asymptotic

### ZetaZeros.ZeroCountingCrudeBoundHyp
**Status**: PARTIAL
**Requires**: N(T) <= C * T * log T
**Aristotle source**: RiemannVonMangoldt.riemann_von_mangoldt gives N(T) = main + O(log T)
**Gap**: Definition mismatch (NZeros vs zeroCountingFunction)

### ZetaZeros.ZeroCountingSpecialValuesHyp
**Status**: MISSING (N(14) = 0)

### ZetaZeros.ZeroCountingFifteenHyp
**Status**: MISSING (N(15) = 1)

### ZetaZeros.FirstZeroOrdinateHyp
**Status**: MISSING (first zero at gamma ~= 14.134)

### ZetaZeros.ZeroCountingAsymptoticHyp
**Status**: PARTIAL
**Requires**: N(T) - (T/2pi) log(T/2pie) + T/2pi = O(log T)
**Aristotle source**: NAsymptotic.N_asymptotic (conditional), RiemannVonMangoldt.riemann_von_mangoldt
**Bridge**: zeroCountingFunction_eq_NAsymptotic_N proved
**Gap**: RiemannVonMangoldt uses NZeros (local def), need bridge to zeroCountingFunction

### ZetaZeros.ZeroCountingRvmExplicitHyp
**Status**: PARTIAL (same gap as ZeroCountingAsymptoticHyp)

### ZetaZeros.ZeroCountingAsymptoticRatioHyp
**Status**: PARTIAL (follows from asymptotic)

### ZetaZeros.ZeroCountingMainTermHyp
**Status**: PARTIAL (follows from asymptotic)

### ZetaZeros.ZeroCountingLowerBoundHyp
**Status**: PARTIAL (follows from asymptotic)

### ZetaZeros.ZeroCountingLocalDensityHyp
**Status**: MISSING

### ZetaZeros.ZeroGapsLowerBoundHyp
**Status**: MISSING

---

## SECTION 7: Landau Lemma Hypotheses (9 classes)

### Landau.LandauLemmaHyp
**Status**: MISSING - No Aristotle coverage
**Note**: Requires Dirichlet series analyticity theory

### Landau.DirichletIntegralConvergesHyp
**Status**: MISSING

### Landau.DirichletIntegralAnalyticHyp
**Status**: MISSING

### Landau.DirichletIntegralDerivHyp
**Status**: MISSING

### Landau.DirichletIntegralPowerSeriesHyp
**Status**: MISSING

### Landau.RadiusExceedsAbscissaHyp
**Status**: MISSING

### Landau.LandauExtensionHyp
**Status**: MISSING

### Landau.LandauLemmaSeriesHyp
**Status**: MISSING

### Landau.ZetaLogDerivPoleHyp
**Status**: MISSING

---

## SUMMARY

| Status | Count | Classes |
|--------|-------|---------|
| PROVED | 4 | ZeroConjZeroHyp, ZeroOneSubZeroHyp, FunctionalEquationHyp, LambdaSymmetryHyp |
| WIREABLE | 0 | (none ready without bridge work) |
| PARTIAL | ~12 | ZeroCountingAsymptoticHyp, ExplicitFormulaPsiHyp, OmegaPsiToThetaHyp, ... |
| BLOCKED | ~9 | Schmidt chain, Hardy theorem |
| MISSING | ~37 | Weighted Average, Zero Density, Landau, ... |
