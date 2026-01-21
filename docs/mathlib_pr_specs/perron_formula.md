# Mathlib PR Specification: Perron's Formula

## Mathematical Statement

For f : ℕ → ℂ with associated Dirichlet series F(s) = ∑ f(n) n^{-s},
and for x > 0, c > σ_a (abscissa of absolute convergence):

```
∑_{n≤x} f(n) = (1/2πi) ∫_{c-i∞}^{c+i∞} F(s) x^s / s ds
```

More precisely, for x not an integer:
```
∑_{n<x} f(n) + (1/2)f(⌊x⌋) = lim_{T→∞} (1/2πi) ∫_{c-iT}^{c+iT} F(s) x^s / s ds
```

## Prerequisites in Mathlib

### Already Available
- [x] `LSeries` - L-series/Dirichlet series definition
- [x] `LSeries.abscissaOfAbsConv` - Abscissa of absolute convergence
- [x] `LSeriesSummable` - Summability conditions
- [x] `LSeries_analyticOnNhd` - Analyticity in half-plane
- [x] Complex contour integration basics (`CauchyIntegral`)
- [x] `riemannZeta_residue_one` - Residue calculation

### Missing (Need to Develop)
- [ ] Vertical line integrals `∫_{c-iT}^{c+iT}`
- [ ] Truncation error estimates
- [ ] Perron kernel `x^s/s` bounds
- [ ] Connection between truncated and infinite integrals

## Proposed File Structure

```
Mathlib/NumberTheory/LSeries/PerronFormula.lean
```

## Key Lemmas Needed

### 1. Perron Kernel Definition and Bounds
```lean
/-- The Perron kernel x^s/s -/
def perronKernel (x : ℝ) (s : ℂ) : ℂ := x ^ s / s

/-- Bound on Perron kernel for Re(s) = c > 0 -/
lemma perronKernel_bound (x : ℝ) (hx : 0 < x) (c : ℝ) (hc : 0 < c) (t : ℝ) :
    ‖perronKernel x (c + t * I)‖ ≤ x ^ c / |t|
```

### 2. Truncated Perron Integral
```lean
/-- Truncated Perron integral -/
def perronIntegralTruncated (F : ℂ → ℂ) (x c T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ∫ t in Icc (-T) T, F (c + t * I) * perronKernel x (c + t * I)

/-- The truncated integral converges to the sum for non-integer x -/
lemma perronIntegralTruncated_tendsto (f : ℕ → ℂ) (x c : ℝ)
    (hx_pos : 0 < x) (hx_nonint : x ∉ range Nat.cast)
    (hc : LSeries.abscissaOfAbsConv f < c) :
    Tendsto (perronIntegralTruncated (LSeries f) x c) atTop
      (nhds (∑ n in Finset.filter (· < x) (Finset.range ⌈x⌉₊), f n))
```

### 3. Main Perron Formula
```lean
/-- Perron's formula: the sum ∑_{n≤x} f(n) equals a contour integral -/
theorem perron_formula (f : ℕ → ℂ) (x c : ℝ)
    (hx_pos : 0 < x) (hx_nonint : x ∉ range Nat.cast)
    (hc : LSeries.abscissaOfAbsConv f < c) :
    ∑ n in Finset.filter (fun n => (n : ℝ) < x) (Finset.range ⌈x⌉₊), f n =
    -- (Appropriate limit of truncated integrals)
```

### 4. Application to von Mangoldt / ψ(x)
```lean
/-- Explicit formula for ψ(x) via Perron -/
theorem chebyshevPsi_perron (x c : ℝ) (hx : 2 ≤ x) (hc : 1 < c) :
    chebyshevPsi x = x - ∑' ρ : zetaNontrivialZeros, x ^ ρ.val / ρ.val - log (2 * π) - ...
```

## Estimated Complexity

- **Lines of code:** 500-1000
- **Dependencies:** Complex analysis, LSeries, number theory
- **Difficulty:** HIGH
- **Estimated time:** 100-200 hours

## Technical Challenges

1. **Contour integration:** Mathlib has `circleIntegral` but not general vertical line integrals
2. **Truncation estimates:** Need careful bounds on ∫_{|t|>T} terms
3. **Pole contributions:** Extracting residues from shifting contours
4. **Non-integer x:** Handling the half-contribution at integer points

## References

- Montgomery & Vaughan, "Multiplicative Number Theory I", Chapter 5
- Iwaniec & Kowalski, "Analytic Number Theory", Section 5.1
- Davenport, "Multiplicative Number Theory", Chapter 17
