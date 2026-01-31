# Ready to Wire Report

Updated: 2026-01-29

## Confirmed Wired (4 instances)

| Hypothesis | Location | Proof |
|------------|----------|-------|
| FunctionalEquationHyp | FunctionalEquationHyp.lean:70 | Mathlib riemannZeta_eq_chiFE_mul |
| LambdaSymmetryHyp | FunctionalEquationHyp.lean:80 | Mathlib completedRiemannZeta_one_sub |
| ZeroConjZeroHyp | ZeroCountingFunction.lean:1618 | Aristotle riemannZeta_conj |
| ZeroOneSubZeroHyp | ZeroCountingFunction.lean:1640 | Functional equation |

## Near-Term Wiring Candidates

### 1. ZeroCountingAsymptoticHyp (MOST PROMISING)

**What it needs**: `N(T) - (T/2pi) log(T/2pie) + T/2pi = O(log T)`

**Available from Aristotle**:
- `RiemannVonMangoldtModule.riemann_von_mangoldt`: `|NZeros(T) - main| <= C log T` for T >= 2
- `NAsymptotic.N_asymptotic`: conditional on h_S, h_RVM, h_Stirling
- `NZerosStirling.N_from_S_and_Stirling`: N from S bound + Stirling

**Bridge needed**:
- `RiemannVonMangoldtModule.NZeros` -> `zeroCountingFunction` (project's N)
- These count the same set but definitions differ
- Bridge lemma `zeroCountingFunction_eq_NAsymptotic_N` connects to NAsymptotic's N
- Need similar bridge for RiemannVonMangoldt's NZeros

**Difficulty**: MEDIUM - definition bridging + Big-O reformulation

### 2. OmegaPsiToThetaHyp (PROMISING after Hardy)

**What it needs**: psi = Omega_pm(f) -> theta = Omega_pm(f) for f >> sqrt(x)

**Available from Aristotle**:
- `PsiThetaBound.psi_theta_bound`: |psi(x) - theta(x)| <= 10*sqrt(x) for x >= 2

**Bridge needed**:
- Show that if psi(x) - x oscillates at scale f(x) where f(x)/sqrt(x) -> infinity,
  then theta(x) - x also oscillates at that scale
- Key: |psi - theta| = O(sqrt(x)) << f(x), so psi and theta have same oscillation

**Difficulty**: MEDIUM - needs Omega_pm transfer lemma

### 3. ZeroCountingCrudeBoundHyp (follows from asymptotic)

**What it needs**: N(T) <= C * T * log T

**Available**: Follows directly from ZeroCountingAsymptoticHyp once wired

**Difficulty**: LOW (once asymptotic is wired)

### 4. ZeroCountingTendstoHyp (follows from asymptotic)

**What it needs**: N(T) -> infinity

**Available**: (T/2pi) log(T/2pie) -> infinity, and N(T) = this + O(log T)

**Difficulty**: LOW (once asymptotic is wired)

### 5. ZeroCountingRvmExplicitHyp (closely related to asymptotic)

**What it needs**: exists C T0, |N(T) - main| <= C * log T for T >= T0

**Available**: Aristotle's riemann_von_mangoldt proves this directly

**Difficulty**: LOW (once definition bridge exists)

## After Hardy Arrives

| Hypothesis | Source | Difficulty |
|------------|--------|------------|
| HardyCriticalLineZerosHyp | HardyInfiniteZeros (pending) | LOW (direct) |
| PsiOscillationFromCriticalZerosHyp | Hardy + Schmidt chain | HIGH |

## Need New Aristotle Proofs

| Hypothesis | What's needed | Priority |
|------------|---------------|----------|
| All 9 Landau Lemma classes | Dirichlet series singularity theory | MEDIUM |
| All 7 Weighted Average classes | Averaging inequalities for ψ | MEDIUM |
| ZeroFreeRegionHyp | de la Vallee-Poussin zero-free region | HIGH |
| 6 Zero Density classes | Summability over zeros | MEDIUM |
| ZeroCountingSpecialValuesHyp | N(14) = 0 (computational) | LOW |
| ZeroCountingFifteenHyp | N(15) = 1 (computational) | LOW |
| FirstZeroOrdinateHyp | gamma_1 in (14.13, 14.14) | LOW |

## Definition Bridge Status

| Project Definition | Aristotle Definition | Bridge |
|-------------------|---------------------|--------|
| chebyshevPsi (Basic/) | chebyshevPsiV3 (ExplicitFormulaV3) | PROVED: chebyshevPsiV3_eq_chebyshevPsi |
| zeroCountingFunction (ZeroCountingFunction.lean) | ZetaZeroCount.N (NAsymptotic) | PROVED: zeroCountingFunction_eq_NAsymptotic_N |
| zeroCountingFunction | RiemannVonMangoldtModule.NZeros | NEEDED |
| zeroCountingFunction | ZeroCounting.NZeros | NEEDED |
| chebyshevPsi | PsiThetaBound.psi | NEEDED |
| chebyshevTheta (Basic/) | PsiThetaBound.theta | NEEDED |
| zetaNontrivialZeros | zetaZerosBelowSet (ZetaZerosFiniteBelow) | PARTIAL |
