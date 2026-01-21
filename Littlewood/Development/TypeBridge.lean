/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Basic
import Littlewood.CoreLemmas.LandauLemma

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

/-- Summatory step: S(n+1) - S(n) = a(n+1) for n ≥ 1 -/
lemma summatory_step (a : ℕ → ℂ) (n : ℕ) (hn : 1 ≤ n) :
    summatory a (n + 1) - summatory a n = a (n + 1) := by
  simp only [summatory, Nat.floor_natCast]
  -- Proof: Finset.Icc 1 (n+1) = insert (n+1) (Finset.Icc 1 n), then use sum_insert
  sorry

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

end Littlewood.Development.TypeBridge
