# Mathlib PR Specification: Quantitative Zero-Free Region

## Mathematical Statement

**De la Vallée Poussin Zero-Free Region (1899):**
There exists c > 0 such that ζ(s) ≠ 0 for all s with:
```
Re(s) > 1 - c / log(|Im(s)| + 2)
```

This is the classical zero-free region that implies the Prime Number Theorem
with error term O(x exp(-c√(log x))).

## Prerequisites in Mathlib

### Already Available
- [x] `riemannZeta_ne_zero_of_one_le_re` - Non-vanishing for Re(s) ≥ 1
- [x] `riemannZeta_eulerProduct` - Euler product formula
- [x] `riemannZeta_eulerProduct_exp_log` - Log form of Euler product
- [x] `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` - Log derivative = L(Λ,s)
- [x] `DirichletCharacter.norm_LSeries_product_ge_one` - |L³L⁴L| ≥ 1
- [x] `re_log_comb_nonneg'` - 3 + 4cos(θ) + cos(2θ) ≥ 0 (private)
- [x] `riemannZeta_residue_one` - Residue at s=1

### Missing (Need to Develop)
- [ ] Extraction of trivial character case from Dirichlet results
- [ ] Quantitative bounds from the 3-4-1 inequality
- [ ] Extension from Re = 1 boundary to interior region
- [ ] Explicit constant c

## Proposed File Structure

```
Mathlib/NumberTheory/ZetaFunction/ZeroFreeRegion.lean
```

## Key Lemmas Needed

### 1. The 3-4-1 Inequality for Zeta
```lean
/-- The Mertens/de la Vallée Poussin inequality for ζ -/
theorem riemannZeta_341_inequality (σ t : ℝ) (hσ : 1 < σ) :
    3 * Real.log ‖riemannZeta σ‖ + 4 * Real.log ‖riemannZeta (σ + t * I)‖ +
    Real.log ‖riemannZeta (σ + 2 * t * I)‖ ≥ 0
```

### 2. Product Lower Bound
```lean
/-- |ζ(σ)|³ |ζ(σ+it)|⁴ |ζ(σ+2it)| ≥ 1 for σ > 1 -/
theorem riemannZeta_product_ge_one (σ t : ℝ) (hσ : 1 < σ) :
    ‖riemannZeta σ‖ ^ 3 * ‖riemannZeta (σ + t * I)‖ ^ 4 *
    ‖riemannZeta (σ + 2 * t * I)‖ ≥ 1
```

### 3. Pole Behavior
```lean
/-- |ζ(σ)| ~ 1/(σ-1) as σ → 1⁺ -/
theorem riemannZeta_pole_behavior :
    Tendsto (fun σ : ℝ => (σ - 1) * ‖riemannZeta σ‖)
    (nhdsWithin 1 (Set.Ioi 1)) (nhds 1)
```

### 4. Zero-Free Region
```lean
/-- De la Vallée Poussin zero-free region -/
theorem riemannZeta_zero_free_region :
    ∃ c > 0, ∀ s : ℂ, s.re > 1 - c / Real.log (|s.im| + 2) → riemannZeta s ≠ 0

/-- Explicit constant version -/
theorem riemannZeta_zero_free_region_explicit :
    ∀ s : ℂ, s.re > 1 - (1/58) / Real.log (|s.im| + 2) → riemannZeta s ≠ 0
```

### 5. Consequences for PNT
```lean
/-- Zero-free region implies PNT error bound -/
theorem chebyshevPsi_error_from_zero_free [ZeroFreeRegionHyp] :
    ∃ c C > 0, ∀ x ≥ 2, |chebyshevPsi x - x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))
```

## Proof Strategy

### From Mathlib's Re = 1 to Quantitative Interior

**Step 1:** Use Mathlib's `riemannZeta_ne_zero_of_one_le_re` for the boundary

**Step 2:** For 1 - c/log|t| < σ < 1, use the 3-4-1 argument:
1. If ζ(β + iγ) = 0 with β < 1, then from product inequality:
   ```
   |ζ(σ)|³ · |ζ(σ + 2iγ)| ≥ 1
   ```
2. As σ → 1⁺:
   - |ζ(σ)| ~ 1/(σ-1) (pole)
   - |ζ(σ + 2iγ)| ≤ C log|γ| (standard bound)
3. This gives: 1/(σ-1)³ · C log|γ| ≥ 1
4. So: (σ-1)³ ≤ C log|γ|
5. Taking cube root and relating to β: β ≥ 1 - c/log|γ|

**Step 3:** The key missing piece is bounding |ζ(σ + 2iγ)| away from zero

## Estimated Complexity

- **Lines of code:** 300-600
- **Dependencies:** Existing Mathlib zeta infrastructure
- **Difficulty:** MEDIUM-HIGH
- **Estimated time:** 80-150 hours

## Technical Challenges

1. **Extracting from Dirichlet characters:** Mathlib's 3-4-1 is for L-functions,
   need to specialize to ζ = L(1, ·)

2. **|ζ(σ+it)| bounds:** Need to show |ζ| is bounded on vertical lines away from 1

3. **Quantitative constant:** Getting an explicit c requires careful tracking

4. **Real-valuedness:** ζ(σ) is real for real σ > 1 (positive Dirichlet series)

## Why This Is Closer Than Other PRs

1. **Most prerequisites exist:** The hard analysis (3-4-1 inequality, Euler product) is done
2. **Clear proof strategy:** The classical argument is well-understood
3. **Mathlib has the boundary:** Just need to extend inward
4. **Medium complexity:** Not as hard as Perron or Hardy

## References

- de la Vallée Poussin, "Recherches analytiques...", 1899
- Montgomery & Vaughan, "Multiplicative Number Theory I", Chapter 12
- Titchmarsh, "The Theory of the Riemann Zeta Function", Chapter 3
- Iwaniec & Kowalski, "Analytic Number Theory", Chapter 5
