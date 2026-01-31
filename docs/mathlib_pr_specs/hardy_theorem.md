# Mathlib PR Specification: Hardy's Theorem on Critical Line Zeros

## Mathematical Statement

**Hardy's Theorem (1914):** The Riemann zeta function has infinitely many zeros
on the critical line Re(s) = 1/2.

More precisely, if N₀(T) counts zeros on the critical line up to height T:
```
N₀(T) = #{ρ : ζ(ρ) = 0, Re(ρ) = 1/2, 0 < Im(ρ) ≤ T}
```
then N₀(T) → ∞ as T → ∞.

**Stronger form (Hardy-Littlewood, 1921):** N₀(T) ≥ cT for some c > 0.

**Selberg (1942):** A positive proportion of zeros are on the critical line:
N₀(T) ≥ c · N(T) for some c > 0.

## Prerequisites in Mathlib

### Already Available
- [x] `riemannZeta : ℂ → ℂ` - Riemann zeta function
- [x] `riemannZeta_one_sub` - Functional equation ξ(s) = ξ(1-s)
- [x] `completedRiemannZeta` - Completed zeta ξ(s)
- [x] `completedRiemannZeta_one_sub` - ξ(s) = ξ(1-s)
- [x] `Complex.Gamma` - Gamma function
- [x] `Complex.continuousAt_arg` - Arg continuity (needs slitPlane)

### Missing (Need to Develop)
- [ ] Hardy Z-function Z(t)
- [ ] Riemann-Siegel theta function θ(t)
- [ ] Z(t) is real-valued for real t
- [ ] Sign changes of Z(t)
- [ ] Gamma slitPlane membership for ζ arguments

## Proposed File Structure

```
Mathlib/NumberTheory/ZetaFunction/HardyZFunction.lean
Mathlib/NumberTheory/ZetaFunction/HardyTheorem.lean
```

## Key Lemmas Needed

### 1. Riemann-Siegel Theta Function
```lean
/-- The Riemann-Siegel theta function -/
noncomputable def riemannSiegelTheta (t : ℝ) : ℝ :=
  arg (Complex.Gamma (1/4 + t/2 * I)) - t/2 * log π

/-- Asymptotic: θ(t) ~ (t/2) log(t/2πe) - π/8 -/
theorem riemannSiegelTheta_asymptotic (t : ℝ) (ht : t ≥ 2) :
    |riemannSiegelTheta t - ((t/2) * log(t/(2*π)) - t/2 - π/8)| ≤ C/t
```

### 2. Hardy Z-Function
```lean
/-- The Hardy Z-function: Z(t) = e^{iθ(t)} ζ(1/2 + it) -/
noncomputable def hardyZ (t : ℝ) : ℂ :=
  Complex.exp (I * riemannSiegelTheta t) * riemannZeta (1/2 + t * I)

/-- Z(t) is real for real t -/
theorem hardyZ_real (t : ℝ) : (hardyZ t).im = 0

/-- Z(t) = 0 iff ζ(1/2 + it) = 0 -/
theorem hardyZ_zero_iff (t : ℝ) : hardyZ t = 0 ↔ riemannZeta (1/2 + t * I) = 0
```

### 3. Sign Changes
```lean
/-- Z is continuous on ℝ -/
theorem hardyZ_continuous : Continuous (fun t => (hardyZ t).re)

/-- If Z changes sign on [a,b], there's a zero in (a,b) -/
theorem hardyZ_sign_change_implies_zero (a b : ℝ) (hab : a < b)
    (ha : (hardyZ a).re > 0) (hb : (hardyZ b).re < 0) :
    ∃ t ∈ Set.Ioo a b, riemannZeta (1/2 + t * I) = 0
```

### 4. Hardy's Theorem
```lean
/-- Hardy's theorem: infinitely many zeros on the critical line -/
theorem hardy_infinitely_many_critical_zeros :
    Set.Infinite {t : ℝ | 0 < t ∧ riemannZeta (1/2 + t * I) = 0}

/-- Counting form: N₀(T) → ∞ -/
theorem hardy_N0_tendsto_top :
    Tendsto (fun T => #{t : ℝ | 0 < t ∧ t ≤ T ∧ riemannZeta (1/2 + t*I) = 0}.toFinset.card)
    atTop atTop
```

### 5. Key Technical Lemma (THE BLOCKER)
```lean
/-- Gamma(1/4 + t/2 * I) lies in the slit plane for all real t -/
theorem gamma_quarter_plus_half_t_slitPlane (t : ℝ) :
    Complex.Gamma (1/4 + t/2 * I) ∈ Complex.slitPlane
```

## Estimated Complexity

- **Lines of code:** 1500-2500
- **Dependencies:** Gamma function, functional equation, complex analysis
- **Difficulty:** VERY HIGH
- **Estimated time:** 200-400 hours

## Technical Challenges

1. **slitPlane membership:** Proving Γ(1/4 + it/2) ∈ slitPlane for all real t
   - Gamma can take negative real values
   - Need to show this doesn't happen for these specific inputs

2. **Theta asymptotics:** Stirling-type formulas for arg(Gamma)
   - Mathlib has limited Stirling support
   - Need arg(Γ(s)) asymptotics, not just |Γ(s)|

3. **Sign change detection:** Proving Z actually changes sign
   - Need explicit numerical bounds or asymptotic arguments
   - Hardy's original proof uses Fourier analysis

4. **Continuity of Z:** Requires continuity of arg ∘ Gamma on the relevant domain

## Alternative Approach: Numerical Verification

For a partial result, one could:
1. Verify numerically that Z changes sign in small intervals
2. Use interval arithmetic to make this rigorous
3. This gives finitely many verified zeros, not infinitely many

## References

- Hardy, "Sur les zéros de la fonction ζ(s) de Riemann", 1914
- Titchmarsh, "The Theory of the Riemann Zeta Function", Chapter 10
- Edwards, "Riemann's Zeta Function", Chapter 8
- Ivić, "The Riemann Zeta-Function", Chapter 7
