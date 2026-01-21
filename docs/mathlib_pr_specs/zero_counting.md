# Mathlib PR Specification: Riemann Zeta Zero Counting

## Mathematical Statement

The zero counting function N(T) counts zeros of ζ(s) in the critical strip:
```
N(T) = #{ρ : ζ(ρ) = 0, 0 < Re(ρ) < 1, 0 < Im(ρ) ≤ T}
```

Main asymptotic:
```
N(T) = (T/2π) log(T/2πe) + O(log T)
```

More precisely (Riemann-von Mangoldt formula):
```
N(T) = (T/2π) log(T/2π) - T/2π + 7/8 + S(T) + O(1/T)
```
where S(T) = (1/π) arg ζ(1/2 + iT).

## Prerequisites in Mathlib

### Already Available
- [x] `riemannZeta : ℂ → ℂ` - Riemann zeta function
- [x] `differentiableAt_riemannZeta` - Differentiability away from s=1
- [x] `riemannZeta_ne_zero_of_one_le_re` - Non-vanishing for Re ≥ 1
- [x] `riemannZeta_one_sub` - Functional equation
- [x] `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` - Isolated zeros
- [x] Basic argument principle setup

### Missing (Need to Develop)
- [ ] Zeros of ζ are discrete (follow from analyticity)
- [ ] Rectangular contour integration
- [ ] Bounds on ζ'/ζ on contours
- [ ] S(T) bounds
- [ ] Connection between arg ζ and N(T)

## Proposed File Structure

```
Mathlib/NumberTheory/ZetaFunction/ZeroCounting.lean
```

## Key Lemmas Needed

### 1. Zero Set Properties
```lean
/-- The set of zeros of ζ in the critical strip is discrete -/
theorem riemannZeta_zeros_discrete :
    DiscreteTopology {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0}

/-- All nontrivial zeros have 0 < Re(ρ) < 1 -/
theorem riemannZeta_zero_re_bounds {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h1 : ρ ≠ 1) :
    0 < ρ.re ∧ ρ.re < 1
```

### 2. Zero Counting Function
```lean
/-- N(T) = number of zeros with 0 < Im(ρ) ≤ T -/
noncomputable def riemannZeta_N (T : ℝ) : ℕ :=
  #{ρ : zetaNontrivialZeros | 0 < ρ.val.im ∧ ρ.val.im ≤ T}.toFinset.card

/-- N(T) is finite for all T -/
theorem riemannZeta_N_finite (T : ℝ) : (riemannZeta_N T).Finite
```

### 3. Argument Principle Application
```lean
/-- The argument principle for ζ on a rectangular contour -/
theorem riemannZeta_argument_principle (T : ℝ) (hT : 0 < T) :
    riemannZeta_N T = (1/2πi) * ∮ ∂R, ζ'/ζ(s) ds
    -- where R is the rectangle [1/2-ε, 3/2] × [-ε, T]
```

### 4. Main Asymptotic
```lean
/-- The Riemann-von Mangoldt formula -/
theorem riemannZeta_N_asymptotic :
    ∃ C, ∀ T ≥ 2, |riemannZeta_N T - (T/(2*π)) * log(T/(2*π*e))| ≤ C * log T

/-- Explicit version with S(T) -/
theorem riemannZeta_N_explicit (T : ℝ) (hT : T ≥ 2) :
    riemannZeta_N T = (T/2π) * log(T/2π) - T/(2*π) + 7/8 +
                      (1/π) * arg (riemannZeta (1/2 + T*I)) + O(1/T)
```

### 5. Density Results
```lean
/-- There are roughly T log T / 2π zeros up to height T -/
theorem riemannZeta_zero_density (T : ℝ) (hT : 2 ≤ T) :
    T / (4 * π) * log T ≤ riemannZeta_N T ∧ riemannZeta_N T ≤ T * log T
```

## Estimated Complexity

- **Lines of code:** 800-1500
- **Dependencies:** Complex analysis, argument principle, zeta function
- **Difficulty:** HIGH
- **Estimated time:** 100-200 hours

## Technical Challenges

1. **Rectangular contours:** Need to set up integration over rectangle boundaries
2. **ζ'/ζ bounds:** Showing log derivative is bounded on vertical lines away from zeros
3. **S(T) estimates:** The oscillatory term S(T) = O(log T) requires careful analysis
4. **Corner contributions:** Handling the corners of the rectangular contour
5. **Pole at s=1:** The zeta pole requires special treatment in contour arguments

## References

- Titchmarsh, "The Theory of the Riemann Zeta Function", Chapter 9
- Edwards, "Riemann's Zeta Function", Chapter 6
- Ivić, "The Riemann Zeta-Function", Chapter 1
