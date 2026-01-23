/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Basic
import Littlewood.CoreLemmas.LandauLemma
import Littlewood.Development.LSeriesRealBridge

/-!
# Type Bridge: LSeries ↔ dirichletIntegral

This file bridges the gap between:
1. Mathlib's `LSeries` (discrete sums)
2. Our `dirichletIntegral` (continuous integrals)

## Discovery (Task 36)

Mathlib already has the key theorem connecting these!

**`LSeries_eq_mul_integral`** (in `Mathlib.NumberTheory.LSeries.SumCoeff`):

For `f : ℕ → ℂ`, if the partial sums are `O(n ^ r)` and the L-series converges at `s`
with `r < s.re`, then:
```
LSeries f s = s * ∫ t in Set.Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * t ^ (-(s + 1))
```

This IS the Abel summation / Dirichlet series ↔ integral equivalence!

## Type Analysis

### Mathlib LSeries
```
LSeries : (ℕ → ℂ) → ℂ → ℂ
LSeries f s = ∑' n, term f s n
  where term f s n = if n = 0 then 0 else f n / n ^ s
```

### Our dirichletIntegral
```
dirichletIntegral : (ℝ → ℝ) → ℂ → ℂ
dirichletIntegral A s = ∫ x in Set.Ioi 1, A x * (x : ℂ) ^ (-s)
```

### The Summatory Function Bridge
The summatory function `S(x) = ∑_{n ≤ x} a(n)` connects these:
- Mathlib: `fun t ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k`
- This is step-function version of our `A : ℝ → ℝ`

### The Abel Summation Connection
From `LSeries_eq_mul_integral`:
```
LSeries f s = s * ∫_{1}^{∞} S(t) * t^{-(s+1)} dt
```

## References
- Montgomery-Vaughan, "Multiplicative Number Theory I", Chapter 5
- Apostol, "Introduction to Analytic Number Theory", Chapter 11
- Mathlib.NumberTheory.LSeries.SumCoeff
- Mathlib.NumberTheory.AbelSummation
-/

namespace Littlewood.Development.TypeBridge

open Complex Real Filter Topology Set MeasureTheory Finset Asymptotics

-- ============================================================
-- SECTION 1: Type Signatures
-- ============================================================

-- Mathlib's LSeries
#check @LSeries
-- LSeries : (ℕ → ℂ) → ℂ → ℂ

#check @LSeries.term
-- LSeries.term : (ℕ → ℂ) → ℂ → ℕ → ℂ

-- Our dirichletIntegral
#check @Landau.dirichletIntegral
-- Landau.dirichletIntegral : (ℝ → ℝ) → ℂ → ℂ

-- ============================================================
-- SECTION 2: Mathlib's LSeries ↔ Integral Theorem
-- ============================================================

-- The KEY theorem that bridges discrete and continuous!
#check @LSeries_eq_mul_integral
/-
LSeries_eq_mul_integral :
  ∀ (f : ℕ → ℂ) {r : ℝ}, 0 ≤ r →
  ∀ {s : ℂ}, r < s.re →
  LSeriesSummable f s →
  (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ ↑n ^ r →
  LSeries f s = s * ∫ t in Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * ↑t ^ (-(s + 1))
-/

-- Specialized version for nonnegative functions
#check @LSeries_eq_mul_integral_of_nonneg
/-
LSeries_eq_mul_integral_of_nonneg :
  ∀ (f : ℕ → ℝ) {r : ℝ}, 0 ≤ r →
  ∀ {s : ℂ}, r < s.re →
  (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ ↑n ^ r →
  (∀ (n : ℕ), 0 ≤ f n) →
  LSeries (fun n ↦ ↑(f n)) s = s * ∫ t in Ioi 1, (∑ k ∈ Icc 1 ⌊t⌋₊, ↑(f k)) * ↑t ^ (-(s + 1))
-/

-- ============================================================
-- SECTION 3: Summatory Function
-- ============================================================

/-- The summatory function: S(x) = ∑_{1 ≤ n ≤ x} a(n)

This is the bridge between discrete LSeries and continuous integrals.
Mathlib uses `∑ k ∈ Icc 1 ⌊x⌋₊, f k` which is exactly this. -/
noncomputable def summatory (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Icc 1 (Nat.floor x), a k

/-- Alternative: summatory starting from 0 -/
noncomputable def summatory₀ (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Icc 0 (Nat.floor x), a k

-- ============================================================
-- SECTION 4: Basic Summatory Lemmas
-- ============================================================

/-- Summatory at 0 is 0 (since Icc 1 0 = ∅) -/
lemma summatory_zero (a : ℕ → ℂ) : summatory a 0 = 0 := by
  unfold summatory
  simp only [Nat.floor_zero]
  rfl  -- Icc 1 0 = ∅ for Finset

/-- Summatory at positive integers -/
lemma summatory_nat (a : ℕ → ℂ) (n : ℕ) :
    summatory a n = ∑ k ∈ Icc 1 n, a k := by
  unfold summatory
  simp only [Nat.floor_natCast]

/-- Summatory is constant on [n, n+1) for integer n -/
lemma summatory_const_on_Ico (a : ℕ → ℂ) (n : ℕ) (x : ℝ) (hx : x ∈ Ico (n : ℝ) (n + 1)) :
    summatory a x = ∑ k ∈ Icc 1 n, a k := by
  unfold summatory
  have hfloor : Nat.floor x = n := Nat.floor_eq_on_Ico n x hx
  rw [hfloor]

/-- Summatory step: S(n+1) - S(n) = a(n+1) for n ≥ 1

NOTE: This is a basic Finset.Icc manipulation that should be provable but
requires careful handling of the ℕ → ℝ coercion and Nat.floor.
The proof strategy is: Icc 1 (n+1) = insert (n+1) (Icc 1 n), then use sum_insert.
-/
lemma summatory_step (a : ℕ → ℂ) (n : ℕ) (hn : 1 ≤ n) :
    summatory a (n + 1) - summatory a n = a (n + 1) := by
  -- Key floor simplification: ⌊↑n + 1⌋₊ = n + 1
  have hfloor : Nat.floor ((n : ℝ) + 1) = n + 1 := by
    rw [Nat.floor_add_one (Nat.cast_nonneg n), Nat.floor_natCast]
  -- Establish the key facts
  have hnotin : n + 1 ∉ Finset.Icc 1 n := by simp only [Finset.mem_Icc]; omega
  have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  -- Unfold summatory and simplify
  simp only [summatory, Nat.floor_natCast, hfloor, hIcc, Finset.sum_insert hnotin]
  abel

/-- Our summatory equals Mathlib's partial sum form -/
lemma summatory_eq_mathlib_form (a : ℕ → ℂ) (x : ℝ) :
    summatory a x = ∑ k ∈ Icc 1 (Nat.floor x), a k := rfl

-- ============================================================
-- SECTION 5: Connection to Mathlib's Form
-- ============================================================

/-- The LSeries integral form uses our summatory -/
theorem lseries_integral_uses_summatory (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
    (hS : LSeriesSummable f s)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    LSeries f s = s * ∫ t in Ioi (1 : ℝ), (summatory f t) * (t : ℂ) ^ (-(s + 1)) := by
  rw [LSeries_eq_mul_integral f hr hs hS hO]
  -- The integrands are definitionally equal since summatory f t = ∑ k ∈ Icc 1 ⌊t⌋₊, f k
  rfl

-- ============================================================
-- SECTION 6: Bridge to Our dirichletIntegral
-- ============================================================

/-- Our dirichletIntegral definition (for reference) -/
example (A : ℝ → ℝ) (s : ℂ) : Landau.dirichletIntegral A s =
    ∫ x in Ioi 1, A x * (x : ℂ) ^ (-s) := rfl

/-!
## The Key Difference

Mathlib's `LSeries_eq_mul_integral`:
  LSeries f s = s * ∫ t, S(t) * t^{-(s+1)} dt

Our `dirichletIntegral`:
  dirichletIntegral A s = ∫ x, A(x) * x^{-s} dx

These are related by integration by parts:
  s * ∫ S(t) * t^{-(s+1)} dt = [S(t) * t^{-s}]_1^∞ + ∫ S'(t) * t^{-s} dt

For S the summatory function, S' is a sum of delta functions at integers:
  S'(t) = ∑_n a(n) δ(t - n)

So formally:
  ∫ S'(t) * t^{-s} dt = ∑_n a(n) * n^{-s} = LSeries a s

The boundary term [S(t) * t^{-s}]_1^∞ = 0 for Re(s) > abscissa of convergence.
-/

-- ============================================================
-- SECTION 7: Key Mathlib Theorems
-- ============================================================

-- The real bridge: LSeries analyticity from Mathlib
-- LSeries_analyticOnNhd : For f with convergent L-series, the function is analytic in the half-plane
#check @LSeries_analyticOnNhd

-- Von Mangoldt function and zeta connection
-- -ζ'/ζ(s) = LSeries Λ s for Re(s) > 1
#check @ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div

/-!
## Conclusion: Gap #5 Analysis

### Key Discovery
Mathlib ALREADY has the LSeries ↔ integral bridge:
- `LSeries_eq_mul_integral` in `Mathlib.NumberTheory.LSeries.SumCoeff`
- `AbelSummation` in `Mathlib.NumberTheory.AbelSummation`

### What This Means
1. The "gap" is smaller than thought - Mathlib has the core machinery
2. Our `dirichletIntegral` is redundant for discrete coefficient cases
3. The Landau hypotheses could be reformulated to use LSeries

### Remaining Work
1. Verify Landau lemma applications use discrete coefficients (likely yes)
2. Reformulate hypotheses to use `LSeries` instead of `dirichletIntegral`
3. Connect to existing Mathlib analyticity results

### Estimated Remaining: 10-20 hours (down from 40-80)
The hard work (Abel summation) is done in Mathlib!
-/

-- ============================================================
-- SECTION 8: Task 40 - Bridge to Landau Hypotheses
-- ============================================================

/-!
## Task 40: Reformulating Landau Hypotheses

### Current Problem
Our Landau hypotheses use `dirichletIntegral : (ℝ → ℝ) → ℂ → ℂ`:
```
dirichletIntegral A s = ∫ x in Ioi 1, A(x) * x^{-s} dx
```

But Mathlib's infrastructure works with `LSeries : (ℕ → ℂ) → ℂ → ℂ`:
```
LSeries f s = ∑' n, f(n) * n^{-s}
```

### Solution: Two Approaches

**Approach A: Use LSeries Directly**
For discrete coefficient sequences (like von Mangoldt Λ):
- Use `LSeries Λ s` instead of `dirichletIntegral (summatory Λ) s`
- Leverage `LSeries_analyticOnNhd` for analyticity
- Leverage `LSeries_eq_mul_integral` when integral form needed

**Approach B: Keep dirichletIntegral for Continuous Functions**
For truly continuous functions A(x):
- dirichletIntegral remains the right tool
- But such cases are rare in our application

### Key Insight: Most Applications Are Discrete
The main uses of Landau lemma in analytic number theory involve:
1. Von Mangoldt function Λ(n) → -ζ'/ζ
2. Chebyshev ψ(x) = ∑_{n≤x} Λ(n) → summatory of Λ
3. Various arithmetic functions

All of these are DISCRETE, so LSeries is the right abstraction!
-/

-- ============================================================
-- SECTION 9: LSeries-Based Landau Hypothesis (Proposed)
-- ============================================================

/--
PROPOSED HYPOTHESIS: Landau's lemma for LSeries.

For arithmetic function f : ℕ → ℂ with f(n) ≥ 0 for all n > 0,
if LSeries f converges for Re(s) > σ_c, then
LSeries f is NOT analytic at s = σ_c.

This is equivalent to our current LandauLemmaHyp but uses LSeries
instead of dirichletIntegral.
-/
class LandauLemmaLSeriesHyp (f : ℕ → ℂ) (σ_c : ℝ) : Prop where
  analytic_right : ∀ s : ℂ, σ_c < s.re → AnalyticAt ℂ (LSeries f) s
  not_analytic_at : ¬AnalyticAt ℂ (LSeries f) σ_c

/--
Key observation: For LSeries, we get analytic_right nearly for free!
`LSeries_analyticOnNhd` gives analyticity in the convergence half-plane.
-/
theorem lseries_analytic_from_mathlib (f : ℕ → ℂ) (s : ℂ)
    (hs : LSeries.abscissaOfAbsConv f < s.re) :
    AnalyticAt ℂ (LSeries f) s := by
  have h := LSeries_analyticOnNhd f
  have hmem : s ∈ {s | LSeries.abscissaOfAbsConv f < s.re} := by
    simp only [Set.mem_setOf_eq]; exact hs
  exact h s hmem

/-
The main remaining content of Landau's lemma for LSeries:
If f(n) ≥ 0 for n > 0 and σ_c is the abscissa of convergence,
then LSeries f is NOT analytic at σ_c.

This is the "singularity at boundary" part that needs work.

## Proof Strategy (BLOCKED - needs Mathlib extension)

The classical proof uses:
1. AnalyticAt implies ContinuousAt (Mathlib has this: `AnalyticAt.continuousAt`)
2. For non-negative real series, if not summable at σ_c, then L(σ) → +∞ as σ → σ_c⁺
3. But ContinuousAt implies bounded in neighborhood, contradiction

The blocker is step 2: proving LSeries → +∞ for non-negative divergent series.
This requires showing partial sums are unbounded, which needs:
- Monotone convergence for non-negative terms
- Connection between series divergence and sum divergence to +∞

## Status: PARTIALLY ADDRESSED (Task 48)
Needs theorem: For f : ℕ → ℝ≥0, ¬Summable f → partial sums → +∞
-/

-- ============================================================
-- SECTION 10: Divergent Non-Negative Series (Task 48)
-- ============================================================

/--
For non-negative real sequences, partial sums are monotone increasing.
-/
theorem partial_sums_monotone (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) :
    Monotone (fun N => ∑ n ∈ Finset.range N, a n) := by
  intro n m hnm
  -- Use Finset.sum_le_sum_of_subset_of_nonneg with range_mono
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono hnm
  · intro i _ _
    exact ha i

/--
**KEY LEMMA (Task 48):** Non-negative divergent series have partial sums → +∞.

This is the missing piece for the Landau boundary theorem.

**Proof Strategy:**
1. Partial sums are monotone (adding non-negative terms)
2. If bounded above, would be Cauchy, hence convergent
3. But series diverges, so must be unbounded
4. Monotone + unbounded ⟹ tends to +∞

Uses `tendsto_atTop_atTop_of_monotone` from Mathlib.
-/
theorem nonneg_divergent_partial_sums_tendsto_top
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hdiv : ¬Summable a) :
    Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, a n) Filter.atTop Filter.atTop := by
  -- Use Mathlib's tendsto_atTop_atTop_of_monotone: monotone + unbounded ⟹ tends to atTop
  apply Filter.tendsto_atTop_atTop_of_monotone
  · -- Monotone: adding non-negative terms
    exact partial_sums_monotone a ha
  · -- Unbounded: if bounded, would be summable (contrapositive)
    intro b
    by_contra h
    push_neg at h
    -- h : ∀ N, ∑ n ∈ range N, a n < b (strictly less)
    -- Bounded monotone ⟹ convergent ⟹ summable
    have hsummable : Summable a := by
      apply summable_of_sum_range_le ha
      intro n
      exact le_of_lt (h n)
    exact hdiv hsummable

/-!
## Landau Theorem Specializations (REMOVED - had sorries, not imported)

The following were removed because they had sorries and weren't used:
- lseries_real_tendsto_top_of_nonneg_divergent
- landau_lseries_not_analytic_at_boundary

These require: monotone unbounded → tendsto atTop filter argument
-/

-- ============================================================
-- SECTION 11: Euler Product ↔ PNT Connection (Task 49)
-- ============================================================

/-!
## Euler Product ↔ Prime Number Theorem Connection

### Overview

The Euler product formula connects the Riemann zeta function to primes:
  ζ(s) = ∏_{p prime} (1 - p^{-s})^{-1}

This is the fundamental bridge between ζ(s) and the distribution of primes.

### Mathlib Infrastructure (discovered Task 43-49)

**Euler Product Theorems:**
```
riemannZeta_eulerProduct : 1 < s.re →
    HasProd (fun p : Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s)

riemannZeta_eulerProduct_tprod : 1 < s.re →
    ∏' p : Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s

riemannZeta_eulerProduct_exp_log : 1 < s.re →
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = riemannZeta s
```

**Von Mangoldt ↔ Zeta Logarithmic Derivative:**
```
LSeries_vonMangoldt_eq_deriv_riemannZeta_div : 1 < s.re →
    L ↗Λ s = - deriv riemannZeta s / riemannZeta s

-- Which says: ∑_{n≥1} Λ(n)/n^s = -ζ'(s)/ζ(s)
```

**Key Convolution Identity:**
```
vonMangoldt_mul_zeta : Λ * ζ = log
-- Where ζ is the arithmetic zeta function, and * is Dirichlet convolution
-- This says: ∑_{d|n} Λ(d) = log(n)
```

### Connection to Prime Number Theorem

The PNT states: π(x) ~ x/log(x), equivalently ψ(x) ~ x where ψ(x) = ∑_{n≤x} Λ(n).

**Path through Euler product:**
1. **Euler product** ⟹ ζ(s) ≠ 0 for Re(s) ≥ 1 (from log form)
2. **Log derivative** ⟹ -ζ'/ζ(s) = L(Λ, s) is analytic for Re(s) > 1
3. **Non-vanishing** ⟹ -ζ'/ζ extends to Re(s) ≥ 1 except simple pole at s = 1
4. **Perron's formula** ⟹ ψ(x) = (residue at s=1) + (error from zeros)
5. **Zero-free region** ⟹ Error is o(x), so ψ(x) ~ x

**What Mathlib provides:**
- Steps 1-3: COMPLETE (Euler product, log derivative, non-vanishing on Re = 1)
- Step 4: MISSING (Perron's formula, contour integration)
- Step 5: PARTIAL (non-vanishing on Re = 1, but not quantitative region)

### Key Theorem Available in This Project

From ZeroFreeRegion.lean:
```
theorem neg_zeta_logderiv_eq_vonMangoldt (s : ℂ) (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s = LSeries (↗vonMangoldt) s
```

This bridges ZeroFreeRegion.lean's work with Mathlib's LSeries infrastructure.

### What's Still Needed for Full PNT Path

1. **Perron's formula:** ψ(x) = (1/2πi) ∫ -ζ'/ζ(s) · x^s/s ds
   Status: NOT IN MATHLIB

2. **Quantitative zero-free region:** σ > 1 - c/log(|t|)
   Status: NOT IN MATHLIB (only Re = 1 boundary)

3. **Contour shifting:** Move integration contour left
   Status: NOT IN MATHLIB (basic residue theory exists)

### Connection to Littlewood Oscillation Theorem

Littlewood's theorem says π(x) - li(x) changes sign infinitely often.
This requires:
- PNT: π(x) ~ li(x) (baseline)
- Critical zeros: ζ(ρ) = 0 with Re(ρ) = 1/2 contribute oscillations
- These oscillations don't cancel ⟹ sign changes

The Euler product provides the PNT part; Hardy's theorem provides the critical zeros.
-/

/-!
## Gap #5 Final Status

### Fully Closed
- Mathlib has Abel summation: `Mathlib.NumberTheory.AbelSummation`
- Mathlib has LSeries ↔ integral: `LSeries_eq_mul_integral`
- Mathlib has analyticity: `LSeries_analyticOnNhd`

### Remaining (1 theorem)
- `landau_lseries_not_analytic_at_boundary`: singularity detection

### Recommendation
Reformulate our Landau hypotheses to use `LSeries` instead of `dirichletIntegral`.
This leverages Mathlib's existing infrastructure and reduces the gap to
a single theorem about singularity at the boundary.

### Estimated Work: 5-10 hours for full closure
Down from original 40-80 hours!
-/

end Littlewood.Development.TypeBridge
