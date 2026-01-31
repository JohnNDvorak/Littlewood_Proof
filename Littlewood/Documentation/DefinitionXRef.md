# Definition Cross-Reference

All definitions and where they're used.

## Definitions by File

### BinetStirling
```
noncomputable def riemannSiegelTheta (t : ℝ) : ℝ :=
noncomputable def stirlingApprox (t : ℝ) : ℂ :=
noncomputable def binetIntegrand (t : ℝ) : ℝ :=
noncomputable def binetIntegral (z : ℂ) : ℂ :=
```

### CriticalZeros
```
noncomputable def critical_zeros_set (T : ℝ) : Set ℂ :=
noncomputable def critical_zeros_upto (T : ℝ) : Finset ℂ :=
noncomputable def sum_recip_zeros (T : ℝ) : ℝ :=
def ExplicitFormulaApprox (C : ℝ) : Prop :=
```

### ExplicitFormulaV3
```
noncomputable def chebyshevPsiV3 (x : ℝ) : ℝ :=
def zetaZerosUpToV3 (T : ℝ) : Set ℂ :=
```

### FunctionalEquationHyp
```
noncomputable def chiFE (s : ℂ) : ℂ :=
```

### FunctionalEquationV2
```
noncomputable def chiV2 (s : ℂ) : ℂ :=
noncomputable def LambdaV2 (s : ℂ) : ℂ :=
```

### HardyAssumptions
```
def riemannSiegelThetaAssump (t : ℝ) : ℝ :=
def hardyZAssump (t : ℝ) : ℝ :=
```

### HardyZComplete
```
def riemannSiegelThetaV3 (t : ℝ) : ℝ :=
def hardyZV3 (t : ℝ) : ℂ :=
def hardyCompletedZeta (s : ℂ) : ℂ :=
```

### HardyZReal
```
noncomputable def riemannSiegelTheta' (t : ℝ) : ℝ :=
noncomputable def hardyZ' (t : ℝ) : ℂ :=
```

### HardyZRealV2
```
noncomputable def hardyThetaV2 (t : ℝ) : ℝ :=
noncomputable def hardyZV2 (t : ℝ) : ℂ :=
```

### HardyZRealV4
```
noncomputable def hardyThetaV4 (t : ℝ) : ℝ :=
noncomputable def hardyZV4 (t : ℝ) : ℂ :=
```

### HarmonicSumIntegral
```
noncomputable def N_truncation (t : ℝ) : ℕ := Nat.floor (Real.sqrt (t / (2 * Real.pi)))
noncomputable def harmonicSum (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1)
```

### LaurentExpansion
```
def zetaMulSubOne (s : ℂ) : ℂ := if s = 1 then 1 else (s - 1) * riemannZeta s
def sqZeta (s : ℂ) : ℂ := if s = 1 then 0 else (s - 1)^2 * riemannZeta s
```

### MeanSquare
```
noncomputable def chi (s : ℂ) : ℂ :=
noncomputable def partialZeta (x : ℝ) (s : ℂ) : ℂ :=
noncomputable def N_t (t : ℝ) : ℕ := Nat.floor (Real.sqrt (t / (2 * Real.pi)))
noncomputable def offDiagSsq (t : ℝ) : ℂ :=
```

### NAsymptotic
```
noncomputable def N (T : ℝ) : ℝ := (Set.ncard {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T} : ℝ)
noncomputable def S (T : ℝ) : ℝ := (1 / Real.pi) * Complex.arg (riemannZeta (1 / 2 + T * Complex.I))
noncomputable def argGamma (T : ℝ) : ℝ := Complex.arg (Complex.Gamma (1 / 4 + (T / 2) * Complex.I))
```

### NZerosStirling
```
noncomputable def S (T : ℝ) : ℝ := (1/Real.pi) * Complex.arg (riemannZeta (1/2 + Complex.I * T))
noncomputable def NZeros (T : ℝ) : ℝ := (1/Real.pi) * (Complex.arg (Complex.Gamma (1/4 + Complex.I * T / 2)) - (T/2) * Real.log Real.pi) + 1 + S T
```

### OffDiagonalBound
```
noncomputable def offDiagSsqReal (N : ℕ) (t : ℝ) : ℝ :=
```

### PartialSummation
```
noncomputable def primeCountingReal (x : ℝ) : ℝ :=
noncomputable def li (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t
def IsOmegaPlusFilter (f g : ℝ → ℝ) (l : Filter ℝ) : Prop :=
def IsOmegaMinusFilter (f g : ℝ → ℝ) (l : Filter ℝ) : Prop :=
def IsOmegaOscillationFilter (f g : ℝ → ℝ) (l : Filter ℝ) : Prop :=
noncomputable def sumLambdaDivLog (x : ℝ) : ℝ :=
noncomputable def sumPrimePowers (x : ℝ) : ℝ :=
```

### PartialSummationPiLi
```
noncomputable def chebyshevPsi (x : ℝ) : ℝ :=
noncomputable def primeCountingReal (x : ℝ) : ℝ :=
noncomputable def li (x : ℝ) : ℝ := ∫ t in (2)..x, 1 / Real.log t
noncomputable def primePowerCorrection (x : ℝ) : ℝ :=
noncomputable def primePowerCorrectionSum (x : ℝ) : ℝ :=
```

### PartialZetaNormSq
```
def partialZetaSum (N : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Finset.range N, (n + 1 : ℂ) ^ (-s)
```

### PerronContourIntegrals
```
def verticalIntegralPerron (f : ℂ → ℂ) (c : ℝ) (T : ℝ) : ℂ :=
def perronIntegralTrunc (F : ℂ → ℂ) (x c T : ℝ) : ℂ :=
noncomputable def chebyshevPsiPerronLocal (x : ℝ) : ℝ :=
noncomputable def perron_integrand_ext (x : ℝ) (s : ℂ) : ℂ :=
noncomputable def exp_sub_one_div_z (z : ℂ) : ℂ :=
```

### PerronFormulaV2
```
noncomputable def chebyshevPsiPerron (x : ℝ) : ℝ :=
def zetaZerosInStrip (T : ℝ) : Set ℂ :=
noncomputable def zetaZerosFinset (T : ℝ) : Finset ℂ :=
```

### PerronNew
```
noncomputable def chebyshevPsi (x : ℝ) : ℝ :=
def zetaZerosInStrip : Set ℂ :=
noncomputable def zetaZerosFinset (T : ℝ) : Finset ℂ :=
noncomputable def sumOverZeros (x T : ℝ) : ℂ :=
noncomputable def perronIntegrand (x : ℝ) (s : ℂ) : ℂ :=
noncomputable def perronVerticalIntegral (x c T : ℝ) : ℂ :=
noncomputable def perronHorizontalIntegral (x T σ₁ σ₂ : ℝ) : ℂ :=
noncomputable def delta (y : ℝ) : ℝ :=
noncomputable def perronAuxIntegrand (y c t : ℝ) : ℂ :=
noncomputable def perronErrorBound (y c T : ℝ) : ℝ :=
```

### PhragmenLindelof
```
noncomputable def convexity_exponent (σ : ℝ) : ℝ :=
```

### PhragmenLindelofStrip
```
noncomputable def mu (σ : ℝ) : ℝ := sInf {α : ℝ | Asymptotics.IsBigO Filter.atTop (fun t : ℝ ↦ riemannZeta (↑σ + ↑t * Complex.I)) (fun t ↦ |t| ^ α)}
```

### PhragmenLindelofV2
```
noncomputable def lindelof_mu_v2 (σ : ℝ) : ℝ :=
noncomputable def convexity_mu_v2 (σ : ℝ) : ℝ := (1 - σ) / 2
noncomputable def zeta_entire_v2 (s : ℂ) : ℂ :=
```

### PiLiOscillation
```
noncomputable def chebyshevPsi (x : ℝ) : ℝ := (Finset.range (Nat.floor x + 1)).sum (fun n => ArithmeticFunction.vonMangoldt n)
noncomputable def primeCountingReal (x : ℝ) : ℝ := (primeCounting (Nat.floor x) : ℝ)
noncomputable def li (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t
noncomputable def T_error (x : ℝ) : ℝ := (Finset.range (Nat.floor x + 1)).sum (fun n => if IsPrimePow n ∧ ¬ n.Prime then 1 / ((Nat.factorization n) n.minFac : ℝ) else 0)
noncomputable def integral_error (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, (chebyshevPsi t - t) / (t * (Real.log t)^2)
```

### PsiDominance
```
def chebyshevPsi (x : ℝ) : ℝ := ∑ n ∈ Finset.range (Nat.floor x + 1), (ArithmeticFunction.vonMangoldt n : ℝ)
def primeCountingReal (x : ℝ) : ℝ := (Nat.primeCounting (Nat.floor x) : ℝ)
def li (x : ℝ) : ℝ := ∫ t in (2)..x, 1 / Real.log t
def sumPrimePowers (x : ℝ) : ℝ := 
def errorTerm (x : ℝ) : ℝ := sumPrimePowers x - (∫ t in (2)..x, (chebyshevPsi t - t) / (t * (Real.log t)^2)) - 2 / Real.log 2
```

### RiemannVonMangoldt
```
noncomputable def NZeros (T : ℝ) : ℕ :=
noncomputable def Xi (s : ℂ) : ℂ :=
noncomputable def S_T (T : ℝ) : ℝ :=
noncomputable def Theta (T : ℝ) : ℝ :=
noncomputable def Theta_approx (T : ℝ) : ℝ :=
noncomputable def Theta_cont (T : ℝ) : ℝ :=
```

### RiemannVonMangoldtV2
```
noncomputable def xi (s : ℂ) : ℂ := (1/2) * s * (s - 1) * (Real.pi ^ (-s/2)) * Complex.Gamma (s/2) * riemannZeta s
noncomputable def ImLogGamma (s : ℂ) : ℝ := s.im * Real.log s.im - s.im - Real.pi/8
noncomputable def S (T : ℝ) : ℝ := (1/Real.pi) * Complex.arg (riemannZeta (1/2 + Complex.I * T))
noncomputable def NZeros (T : ℝ) : ℝ :=
```

### RiemannXi
```
noncomputable def xi (s : ℂ) : ℂ := (1 / 2) * s * (s - 1) * completedRiemannZeta s
noncomputable def RiemannXi (s : ℂ) : ℂ := (1 / 2) * s * (s - 1) * completedRiemannZeta₀ s + 1 / 2
```

### RiemannXiEntire
```
noncomputable def RiemannXiAlt (s : ℂ) : ℂ := (1/2) * (s * (s - 1) * completedRiemannZeta₀ s + 1)
```

### StirlingGammaBounds
```
noncomputable def stirling_proxy (z : ℂ) : ℂ :=
```

### TruncatedExplicitFormula
```
noncomputable def chebyshevPsi (x : ℝ) : ℝ := ∑ n ∈ Finset.range (Nat.floor x + 1), ArithmeticFunction.vonMangoldt n
def zetaZerosInBoxSet (T : ℝ) : Set ℂ := {s | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T}
noncomputable def zetaZerosInBox (T : ℝ) : Finset ℂ :=
```

### XiDifferentiability
```
noncomputable def xi_Literal (s : ℂ) := s * (s - 1) * completedRiemannZeta s
noncomputable def xi_LiteralCorrected (s : ℂ) := s * (s - 1) * completedRiemannZeta₀ s + 1
```

### ZeroCounting
```
noncomputable def zetaZeroCount (T : ℝ) : ℕ :=
noncomputable def RiemannXi (s : ℂ) : ℂ :=
noncomputable def xi_Mathlib (s : ℂ) : ℂ :=
noncomputable def xi_Mathlib_corrected (s : ℂ) : ℂ :=
```

### ZeroCountingNew
```
noncomputable def NZeros (T : ℝ) : ℕ :=
noncomputable def MainTerm (T : ℝ) : ℝ :=
noncomputable def S_term (T : ℝ) : ℝ := (1 / Real.pi) * (riemannZeta (1 / 2 + T * Complex.I)).arg
def RiemannVonMangoldtProperty : Prop :=
```

### ZeroCountingV2
```
noncomputable def NZeros (T : ℝ) : ℕ :=
noncomputable def SArg (T : ℝ) : ℝ :=
noncomputable def GammaArg (T : ℝ) : ℝ :=
noncomputable def digamma (s : ℂ) : ℂ := deriv Complex.Gamma s / Complex.Gamma s
```

### ZeroCountingXi
```
def xi (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1
def zetaZeroCount (T : ℝ) : ℕ :=
```

### ZetaMeanSquare
```
noncomputable def mean_square_zeta (σ T : ℝ) : ℝ :=
noncomputable def chi_zeta (s : ℂ) : ℂ :=
```

### ZetaZeroInfrastructure
```
def isNontrivialZero (s : ℂ) : Prop :=
def zetaZerosUpTo (T : ℝ) : Set ℂ :=
def criticalLineZeros (T : ℝ) : Set ℂ :=
def C : ℝ := 1
def c_zero_free : ℝ := 1
def DensityEstimateConsequence (x T : ℝ) : Prop :=
def CriticalLineSumBound (T : ℝ) : Prop :=
def ZeroFreeRegion (T : ℝ) : Prop :=
def criticalBox (T : ℝ) : Set ℂ :=
def offCriticalZeros (T : ℝ) : Set ℂ :=
```


## Potential Definition Conflicts

- **NZeros**: defined 5 times
- **chebyshevPsi**: defined 5 times
- **primeCountingReal**: defined 4 times
- **li**: defined 4 times
- **xi**: defined 3 times
- **S**: defined 3 times
- **zetaZerosInStrip**: defined 2 times
- **zetaZerosFinset**: defined 2 times
- **zetaZeroCount**: defined 2 times
- **sumPrimePowers**: defined 2 times
- **RiemannXi**: defined 2 times
