# Remaining Sorry Analysis

## Summary
| File | Sorries | Difficulty | Blocking Main Proof |
|------|---------|------------|---------------------|
| PartialSummation.lean | 2 | EASY | No (alternative path exists) |
| FunctionalEquation.lean | 1 | DEPRECATED | No (use V2) |
| ZeroCounting.lean | 4 | MEDIUM | Partially |
| PhragmenLindelof.lean | 3 | MEDIUM | No |
| MeanSquare.lean | 5 | MEDIUM | No |
| PerronFormula.lean | 6 | HARD | No (use PerronNew) |

## PartialSummation.lean (2 sorries)

### Lines 238, 241: psi_oscillation_implies_pi_li_oscillation
```lean
theorem psi_oscillation_implies_pi_li_oscillation
    (h_psi_pos : ∀ M : ℝ, ∃ x > M, chebyshevPsi x - x > 0)
    (h_psi_neg : ∀ M : ℝ, ∃ x > M, chebyshevPsi x - x < 0) :
    (∀ M : ℝ, ∃ x > M, primeCountingReal x - li x > 0) ∧
    (∀ M : ℝ, ∃ x > M, primeCountingReal x - li x < 0)
```

**What's needed**:
- Show that when ψ(x) - x is large, π(x) - li(x) has the same sign
- Error terms T(x) and integral are lower order
- Standard partial summation argument

**Difficulty**: EASY - mainly arithmetic manipulation
**Blocking**: No - LittlewoodPi uses a different conversion path

---

## FunctionalEquation.lean (1 sorry)

### Line 23: poisson_theta
```lean
theorem poisson_theta (t : ℝ) (ht : 0 < t) :
    jacobi_theta t = t^(-(1:ℝ)/2) * jacobi_theta (1/t)
```

**What's needed**:
- Poisson summation formula
- Fourier transform of Gaussians

**Difficulty**: MEDIUM (but deprecated)
**Blocking**: No - use FunctionalEquationV2.lean instead which uses Mathlib's completedRiemannZeta directly

---

## ZeroCounting.lean (4 sorries)

### Line 86: xi_Mathlib_differentiable
```lean
theorem xi_Mathlib_differentiable : Differentiable ℂ xi_Mathlib
```
**Needs**: Show s(s-1)completedZeta is entire
**Difficulty**: EASY - follows from Mathlib's completedRiemannZeta theory

### Lines 92, 97, 103: Riemann-von Mangoldt machinery
- `zetaZeroCount_via_argument` - argument principle
- `riemann_von_mangoldt` - N(T) ~ (T/2π) log(T/2πe)
- `zetaZeroCount_asymp` - asymptotic form

**Needs**: Argument principle (not in Mathlib), Stirling approximation
**Difficulty**: MEDIUM-HARD
**Blocking**: Partially - provides zero counting estimates

---

## PhragmenLindelof.lean (3 sorries)

### Line 153: zeta_critical_line_bound
```lean
∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
    ‖riemannZeta ((1:ℂ)/2 + t * I)‖ ≤ C * |t| ^ (1/2 : ℝ)
```
**Needs**: Functional equation + Stirling for χ factor
**Difficulty**: MEDIUM

### Line 167: zeta_convexity_bound
General convexity bound in critical strip
**Needs**: Phragmén-Lindelöf interpolation
**Difficulty**: MEDIUM

### Line 177: gamma_growth (Stirling)
```lean
∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ t : ℝ, 1 ≤ |t| →
    C₁ * |t|^(σ - 1/2) * exp(-π|t|/2) ≤ ‖Γ(σ+it)‖ ∧ ...
```
**Needs**: Stirling approximation for Gamma
**Difficulty**: MEDIUM (Mathlib has asymptotic but not explicit bounds)

**Blocking**: No - these are growth bounds, not core logic

---

## MeanSquare.lean (5 sorries)

### Line 90: integral_log_sqrt_asymp (TRACTABLE)
```lean
(fun T => ∫ t in (1:ℝ)..T, Real.log (Real.sqrt (t / (2 * Real.pi))))
    =Θ[atTop] (fun T => T * Real.log T)
```
**Needs**: Basic calculus - ∫ log√(t/2π) dt = (T/2)log(T/2πe) + O(1)
**Difficulty**: EASY

### Line 98: integral_harmonic_sum_asymp
```lean
(fun T => ∫ t in (1:ℝ)..T, ∑ n ∈ Finset.Icc 1 (N_t t), (1:ℝ)/n) =Θ[atTop] (fun T => T * Real.log T)
```
**Needs**: Harmonic sum bounds, dominated convergence
**Difficulty**: EASY-MEDIUM

### Line 184: norm_integral_offDiagSsq_le
Off-diagonal sum bound
**Needs**: Oscillatory integral bounds (done in file)
**Difficulty**: MEDIUM

### Line 192: normSq_partialZeta_eq (TRACTABLE)
```lean
Complex.normSq (partialZeta ...) = (∑ 1/n) + (offDiagSsq t).re
```
**Needs**: Expand |Σ n^{-1/2-it}|² and collect terms
**Difficulty**: EASY-MEDIUM

### Line 206: mean_square_partial_zeta_asymp
Main mean square result
**Needs**: Combines above lemmas
**Difficulty**: MEDIUM (once dependencies proved)

**Blocking**: No - mean square is auxiliary for sign changes

---

## PerronFormula.lean (6 sorries)

### Lines 39, 44: Contour segment limits
```lean
horizontal_segment_bound, vertical_segment_limit
```
**Needs**: Contour integration, dominated convergence
**Difficulty**: HARD (infrastructure missing in Mathlib)

### Line 82: integral_real_part_arctan
```lean
∫ t in Icc (-R) R, (1/(c+it)).re = 2 arctan(R/c)
```
**Needs**: Direct calculation
**Difficulty**: EASY

### Lines 97, 102, 109: Perron formula machinery
- perron_term_integral_bound
- cauchy_integral_zero
- perron_formula_counting

**Needs**: Residue theorem (not in Mathlib), Cauchy's theorem for rectangles
**Difficulty**: HARD

**Blocking**: No - use PerronNew.lean which has infrastructure

---

## Priority Order for Proving

### High Priority (Easy wins)
1. `integral_log_sqrt_asymp` - direct calculus
2. `normSq_partialZeta_eq` - algebraic expansion
3. `integral_real_part_arctan` - direct calculation
4. `xi_Mathlib_differentiable` - follows from Mathlib

### Medium Priority (Would help)
5. `integral_harmonic_sum_asymp` - uses harmonic bounds
6. `gamma_growth` - Stirling approximation
7. `zeta_critical_line_bound` - functional equation + Stirling

### Low Priority (Infrastructure gaps)
8. Perron formula sorries - need contour integration
9. Argument principle results - need complex analysis

---

## What Would Close the Proof?

The main theorems in `Main/` have 0 sorries. The proof chain is:

```
Assumptions.lean (58 sorries as hypothesis placeholders)
    ↓
ExplicitFormulas/ (uses hypotheses)
    ↓
Oscillation/ (Schmidt theorem)
    ↓
Main/LittlewoodPsi.lean (0 sorries - complete)
    ↓
Main/LittlewoodPi.lean (0 sorries - complete)
```

To eliminate Assumptions.lean sorries, we need:
1. Infinitely many zeros on critical line (Hardy's theorem - needs analytic continuation)
2. Explicit formula convergence (needs Perron + contour integration)
3. Zero density estimates (needs argument principle)

Current Mathlib gaps:
- Argument principle for meromorphic functions
- Residue theorem with explicit contours
- Completed proofs of Hardy's theorem
