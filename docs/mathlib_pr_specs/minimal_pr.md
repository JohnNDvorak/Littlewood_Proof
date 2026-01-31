# Mathlib PR Specification: Minimal High-Impact Additions

## Overview

This spec identifies the **smallest possible Mathlib additions** that would unlock the most
sorries in the Littlewood formalization. Unlike the larger PR specs (quantitative_zero_free,
perron_formula, etc.), these are 1-2 lemma PRs that could be contributed independently.

## Priority 1: Riemann Zeta Real-Valued on Real Axis

### Mathematical Statement

For real σ > 1, the Riemann zeta function takes real values:
```
ζ(σ) ∈ ℝ  for σ ∈ ℝ, σ > 1
```

More specifically, ζ(σ) > 0 for σ > 1 (positive Dirichlet series with positive terms).

### Proposed Lean Statement

```lean
/-- ζ(σ) is real for real σ > 1 -/
theorem riemannZeta_ofReal_eq_re (σ : ℝ) (hσ : 1 < σ) :
    riemannZeta σ = ↑(riemannZeta σ).re := by
  -- ζ(σ) = ∑ 1/n^σ is a sum of positive reals
  sorry

/-- ζ(σ) > 0 for real σ > 1 -/
theorem riemannZeta_pos (σ : ℝ) (hσ : 1 < σ) :
    0 < (riemannZeta σ).re := by
  -- Each term 1/n^σ > 0 for n ≥ 1
  sorry

/-- ζ(σ) is real (alternative form) -/
theorem riemannZeta_im_eq_zero (σ : ℝ) (hσ : 1 < σ) :
    (riemannZeta σ).im = 0 := by
  have h := riemannZeta_ofReal_eq_re σ hσ
  simp only [Complex.ofReal_re, Complex.ofReal_im] at h
  sorry
```

### Proof Strategy

1. Use the definition `riemannZeta s = ∑' n, 1/(n+1)^s` for Re(s) > 1
2. For real σ, each term `1/(n+1)^σ = 1/(n+1)^σ` is real
3. The tsum of reals is real
4. Positivity follows from all terms being positive

### Prerequisites (Already in Mathlib)

- `riemannZeta_eq_tsum_one_div_nat_cpow` (or similar)
- `Complex.cpow_ofReal_ofReal` - real^real = real
- `tsum_coe_ne_top_iff_summable` and real tsum properties

### Impact

**Sorries Unlocked:** 2-3 directly
- `zeta_pole_behavior` (ZeroFreeRegion.lean:341-350)
- Helps with `neg_zeta_logderiv_re_bound` (simplifies real part extraction)

**Estimated Effort:** 5-15 hours

---

## Priority 2: Trivial Dirichlet Character ↔ Riemann Zeta

### Mathematical Statement

The L-series of the trivial Dirichlet character (N=1) equals the Riemann zeta function:
```
L(χ₁, s) = ζ(s)  for Re(s) > 1
```

where χ₁ is the principal character modulo 1 (which is 1 for all positive integers).

### Proposed Lean Statement

```lean
/-- The trivial Dirichlet character is identically 1 on positive integers -/
theorem DirichletCharacter.one_apply_pos {n : ℕ} (hn : n ≠ 0) :
    (1 : DirichletCharacter ℂ 1) n = 1 := by
  -- In ZMod 1, every element is a unit
  have heq : (n : ZMod 1) = 0 := Subsingleton.elim _ _
  have hunit : IsUnit (0 : ZMod 1) := by
    have : (0 : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [this]; exact isUnit_one
  simp only [DirichletCharacter, heq]
  exact MulChar.one_apply hunit

/-- LSeries of trivial character equals riemannZeta -/
theorem LSeries_one_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (1 : DirichletCharacter ℂ 1) n) s = riemannZeta s := by
  -- Both equal ∑_{n≥1} 1/n^s
  -- Use LSeries_zeta_eq_riemannZeta and the fact that χ₁(n) = 1 for n ≥ 1
  have h : ∀ n : ℕ, n ≠ 0 → (1 : DirichletCharacter ℂ 1) n = ↑(ArithmeticFunction.zeta n) := by
    intro n hn
    simp [DirichletCharacter.one_apply_pos hn, ArithmeticFunction.zeta_apply_ne hn]
  -- LSeries only cares about n ≥ 1 (term at 0 is 0)
  sorry
```

### Proof Strategy

1. Show `(1 : DirichletCharacter ℂ 1) n = 1` for n ≥ 1 (done above)
2. Note that `ArithmeticFunction.zeta n = 1` for n ≥ 1
3. Since LSeries.term ignores n=0, the L-series are equal
4. Apply `ArithmeticFunction.LSeries_zeta_eq_riemannZeta`

### Prerequisites (Already in Mathlib)

- `ArithmeticFunction.LSeries_zeta_eq_riemannZeta`
- `ArithmeticFunction.zeta_apply_ne`
- `MulChar.one_apply`
- `Subsingleton (ZMod 1)`

### Impact

**Sorries Unlocked:** 1-2 directly, enables specialization of many Dirichlet results
- Enables specializing `DirichletCharacter.norm_LSeries_product_ge_one` to ζ
- Would help with `mertens_inequality_stub` (if combined with log-derivative results)

**Estimated Effort:** 10-20 hours

---

## Priority 3: L-Series Real Part for Real Arguments

### Mathematical Statement

For a Dirichlet series with non-negative real coefficients, the L-series value at a real
point equals its real part:

```
If a(n) ≥ 0 for all n, then L(a, σ) ∈ ℝ for σ > σ_a
```

### Proposed Lean Statement

```lean
/-- L-series of non-negative function at real point is real -/
theorem LSeries_nonneg_ofReal_re (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (σ : ℝ)
    (hs : LSeriesSummable (fun n => (f n : ℂ)) σ) :
    (LSeries (fun n => (f n : ℂ)) σ).im = 0 := by
  -- Each term f(n)/n^σ is real (non-negative real / positive real)
  -- Sum of reals is real
  sorry

/-- L-series of non-negative function at real point is non-negative -/
theorem LSeries_nonneg_nonneg (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (σ : ℝ)
    (hs : LSeriesSummable (fun n => (f n : ℂ)) σ) :
    0 ≤ (LSeries (fun n => (f n : ℂ)) σ).re := by
  -- Each term is non-negative, sum of non-negatives is non-negative
  sorry
```

### Impact

**Sorries Unlocked:** Helps with real-part arguments in multiple places
- Simplifies `zetaLogDeriv` analysis for real σ
- Helps with Landau-type lemmas about real Dirichlet series

**Estimated Effort:** 15-25 hours

---

## Summary Table

| Priority | Lemma | Effort | Sorries Unlocked | Dependencies |
|----------|-------|--------|------------------|--------------|
| 1 | `riemannZeta_ofReal_eq_re` | 5-15 hrs | 2-3 | tsum of reals |
| 2 | `LSeries_one_eq_riemannZeta` | 10-20 hrs | 1-2 + enabling | LSeries_zeta_eq_riemannZeta |
| 3 | `LSeries_nonneg_ofReal_re` | 15-25 hrs | Multiple | tsum properties |

## Recommendation

**Start with Priority 1** (`riemannZeta_ofReal_eq_re`) because:
1. Simplest proof (just tsum of positive reals)
2. Directly unlocks `zeta_pole_behavior`
3. Self-contained - no complex dependencies
4. Stepping stone for Priority 2 and 3

## References

- Mathlib: `Mathlib.NumberTheory.LSeries.RiemannZeta`
- Mathlib: `Mathlib.NumberTheory.LSeries.DirichletContinuation`
- Mathlib: `Mathlib.Analysis.Normed.Field.Basic` (tsum properties)
