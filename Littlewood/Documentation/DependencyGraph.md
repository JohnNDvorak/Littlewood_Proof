# Hypothesis Class Dependency Graph

Updated: 2026-01-29

## Main Theorem Proof Paths

```
                    littlewood_pi_li
                   /        |        \
        littlewood_psi  OmegaPsiTo  OmegaThetaTo
              |          ThetaHyp    PiLiHyp
    PsiOscillationSqrtHyp
              |
    SchmidtPsiOscillationHyp
         /         \
   ExplicitFormula  HardyCriticalLine
     PsiHyp          ZerosHyp
                        |
                   (Hardy's theorem)
```

## Instance-Level Dependencies (proved in source)

These are cases where one hypothesis class has an `instance` declaration
that derives it from another:

| Derived Class | Depends On | Location |
|---------------|-----------|----------|
| ZeroCountingSpecialValuesHyp | FirstZeroOrdinateHyp | ZeroCountingFunction.lean:522 |
| ZeroCountingAsymptoticHyp | ZeroCountingRvmExplicitHyp | ZeroCountingFunction.lean:589 |

## Multi-Hypothesis Theorems

| Theorem | Required Hypotheses | File |
|---------|-------------------|------|
| littlewood_psi | PsiOscillationSqrtHyp | Main/LittlewoodPsi.lean |
| littlewood_pi_li | littlewood_psi + OmegaPsiToThetaHyp + OmegaThetaToPiLiHyp | Main/LittlewoodPi.lean |
| omega_psi_to_pi_li | OmegaPsiToThetaHyp + OmegaThetaToPiLiHyp | ConversionFormulas.lean:227 |
| tsum_inv_gamma_sq_pos | ZeroCountingSummabilityHyp + FirstZeroOrdinateHyp | ZeroDensity.lean:222 |
| chebyshev_error_bound_Theta | FirstZeroOrdinateHyp + ChebyshevErrorBoundThetaHyp | SupremumRealPart.lean:279 |

## Logical Dependency Chains

### Chain 1: Main Theorem Path (CRITICAL)
```
HardyCriticalLineZerosHyp
  -> PsiOscillationFromCriticalZerosHyp  [blocked: needs explicit formula chain]
  -> SchmidtPsiOscillationHyp            [blocked: needs Hardy + explicit formula]
  -> PsiOscillationSqrtHyp               [blocked: needs Schmidt + Theta dichotomy]
  -> littlewood_psi                       [blocked: needs PsiOscillationSqrtHyp]
  -> littlewood_pi_li                     [blocked: needs littlewood_psi + transfers]
```

### Chain 2: Zero Counting Path
```
RiemannVonMangoldt (Aristotle)
  -> ZeroCountingRvmExplicitHyp          [PARTIAL: definition bridge needed]
  -> ZeroCountingAsymptoticHyp           [derived from RvmExplicit]
  -> ZeroCountingCrudeBoundHyp           [follows from asymptotic]
  -> ZeroCountingTendstoHyp              [follows from asymptotic]
  -> ZeroCountingSummabilityHyp          [follows from crude bound]
```

### Chain 3: Explicit Formula Path
```
ExplicitFormulaPsiHyp                    [PARTIAL: truncated formula available]
  -> PsiErrorBoundHyp                    [needs explicit formula + zero-free region]
  -> SchmidtPsiOscillationHyp            [needs explicit formula + trig poly]
```

### Chain 4: Transfer Path
```
PsiOscillationSqrtHyp
  + OmegaPsiToThetaHyp                  [PARTIAL: PsiThetaBound available]
  + OmegaThetaToPiLiHyp                 [PARTIAL: partial summation available]
  -> littlewood_pi_li
```

## Hypothesis Classes by Independence Level

### Foundation Layer (no dependencies, ~55 classes)
All Explicit Formula classes (11), all Weighted Average classes (7),
all Landau classes (9), all Zero Density classes (6-7),
ZeroFreeRegionHyp, ZetaZeroSupRealPartDichotomyHyp,
ChebyshevErrorBoundZeroFreeHyp, ChebyshevErrorBoundThetaHyp,
ZeroConjZeroHyp (PROVED), ZeroOneSubZeroHyp (PROVED),
FunctionalEquationHyp (PROVED), LambdaSymmetryHyp (PROVED),
ZeroCountingSpecialValuesHyp, ZeroCountingFifteenHyp,
FirstZeroOrdinateHyp, ZeroCountingLocalDensityHyp,
ZeroGapsLowerBoundHyp, HardyCriticalLineZerosHyp,
MellinPsiIdentityHyp, OmegaMinusNecessityHyp, OmegaPlusNecessityHyp,
ThetaOscillationMinusHyp, ThetaOscillationRHHyp

### Derived Layer (depends on foundation, ~5 classes)
- ZeroCountingAsymptoticHyp <- ZeroCountingRvmExplicitHyp
- ZeroCountingCrudeBoundHyp <- (logically from asymptotic, but independent in code)
- ZeroCountingTendstoHyp <- (logically from asymptotic, but independent in code)
- ZeroCountingAsymptoticRatioHyp <- (logically from asymptotic)
- ZeroCountingMainTermHyp <- (logically from asymptotic)

### Result Layer (depends on derived + transfers)
- PsiOscillationSqrtHyp <- SchmidtPsiOscillationHyp (+ more)
- PsiOscillationFromCriticalZerosHyp <- HardyCriticalLineZerosHyp (+ more)
- littlewood_psi <- PsiOscillationSqrtHyp
- littlewood_pi_li <- littlewood_psi + OmegaPsiToThetaHyp + OmegaThetaToPiLiHyp

## Aristotle Coverage Map

```
                              Aristotle Available?
ZeroCountingRvmExplicitHyp    YES (riemann_von_mangoldt, def bridge needed)
ZeroCountingAsymptoticHyp     YES (derived from RvmExplicit)
ZeroCountingCrudeBoundHyp     YES (follows from asymptotic)
ZeroCountingTendstoHyp        YES (follows from asymptotic)
ExplicitFormulaPsiHyp         PARTIAL (truncated version only)
OmegaPsiToThetaHyp            PARTIAL (PsiThetaBound key ingredient)
OmegaThetaToPiLiHyp           PARTIAL (partial summation, conflicts)
HardyCriticalLineZerosHyp     WAITING (Aristotle batch submitted)
SchmidtPsiOscillationHyp      BLOCKED (needs Hardy + explicit formula)
PsiOscillationSqrtHyp         BLOCKED (needs Schmidt + Theta)
ZeroFreeRegionHyp             PARTIAL (3-4-1 proved, not full region)
All Landau classes             MISSING
All WeightedAverage classes    MISSING
```
