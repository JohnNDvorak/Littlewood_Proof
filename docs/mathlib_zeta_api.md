# Mathlib Zeta Function API

Comprehensive audit of Mathlib lemmas relevant to the Littlewood formalization.

## Summary

| Category | Count | Notes |
|----------|-------|-------|
| Basic Properties | 8 | Definition, special values |
| Differentiability | 3 | Away from s=1 |
| Functional Equation | 2 | ξ(s) = ξ(1-s) |
| Non-vanishing | 4 | Re(s) ≥ 1 |
| Euler Product | 4 | Re(s) > 1 |
| Special Values | 8 | ζ(0), ζ(2), ζ(-n) |
| Residue/Asymptotics | 4 | Pole at s=1 |
| L-series Connection | 5 | LSeries = ζ |

---

## 1. Basic Properties

### Definition
```lean
riemannZeta : ℂ → ℂ
-- Mathlib/NumberTheory/LSeries/RiemannZeta.lean
```

### Differentiability
```lean
theorem differentiableAt_riemannZeta {s : ℂ} (hs' : s ≠ 1) :
    DifferentiableAt ℂ riemannZeta s
-- ζ is differentiable (hence continuous) everywhere except s = 1

theorem differentiable_completedZeta₀ : Differentiable ℂ completedRiemannZeta₀
-- The completed zeta ξ₀(s) is entire

theorem differentiableAt_completedZeta {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    DifferentiableAt ℂ completedRiemannZeta s
```

---

## 2. Functional Equation

```lean
theorem completedRiemannZeta_one_sub (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s
-- ξ(1-s) = ξ(s) where ξ(s) = π^(-s/2) Γ(s/2) ζ(s)

theorem riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = 2 * (2 * π) ^ (-s) * Γ s * Real.cos (s * π / 2) * riemannZeta s
-- Standard functional equation
```

---

## 3. Non-vanishing Results

```lean
theorem riemannZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ≠ 0
-- ζ(s) ≠ 0 for Re(s) > 1 (Euler product region)

lemma riemannZeta_ne_zero_of_one_le_re ⦃s : ℂ⦄ (hs : 1 ≤ s.re) :
    s ≠ 1 → riemannZeta s ≠ 0
-- ζ(s) ≠ 0 for Re(s) ≥ 1, s ≠ 1 (includes critical line!)
-- This is the de la Vallée Poussin result on Re(s) = 1

theorem riemannZeta_one_ne_zero : riemannZeta 1 ≠ 0
-- ζ(1) ≠ 0 (though it has a pole, the value is defined)
```

**IMPORTANT:** `riemannZeta_ne_zero_of_one_le_re` gives non-vanishing on Re(s) = 1,
which is key for the zero-free region!

---

## 4. Special Values

```lean
theorem riemannZeta_zero : riemannZeta 0 = -1 / 2

theorem riemannZeta_two : riemannZeta 2 = (π : ℂ) ^ 2 / 6

theorem riemannZeta_four : riemannZeta 4 = π ^ 4 / 90

theorem riemannZeta_two_mul_nat {k : ℕ} (hk : k ≠ 0) :
    riemannZeta (2 * k) = (-1) ^ (k + 1) * (2 * π) ^ (2 * k) * bernoulli (2 * k) / (2 * (2 * k)!)

theorem riemannZeta_neg_nat_eq_bernoulli (k : ℕ) :
    riemannZeta (-k) = (-1) ^ k * bernoulli (k + 1) / (k + 1)
-- ζ(-n) in terms of Bernoulli numbers

theorem riemannZeta_neg_two_mul_nat_add_one (n : ℕ) :
    riemannZeta (-2 * (n + 1)) = 0
-- Trivial zeros at s = -2, -4, -6, ...
```

---

## 5. Residue and Pole Behavior

```lean
lemma riemannZeta_residue_one :
    Tendsto (fun s ↦ (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1)
-- lim_{s→1} (s-1)ζ(s) = 1 (simple pole with residue 1)

lemma completedRiemannZeta_residue_one :
    Tendsto (fun s ↦ s * (s - 1) * completedRiemannZeta s) (𝓝 1) (𝓝 1)
```

**USEFUL:** `riemannZeta_residue_one` is exactly the pole behavior we need
for the zero-free region analysis.

---

## 6. Euler Product

```lean
theorem riemannZeta_eulerProduct_hasProd (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s)

theorem riemannZeta_eulerProduct (hs : 1 < s.re) :
    riemannZeta s = ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹

theorem riemannZeta_eulerProduct_exp_log {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = exp (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s)))
-- Euler product via exponential form
```

---

## 7. L-series Connection

```lean
lemma LSeries_zeta_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    L ↗ζ s = riemannZeta s
-- L-series of arithmetic ζ equals Riemann ζ

lemma LSeries_vonMangoldt_eq_deriv_riemannZeta_div {s : ℂ} (hs : 1 < s.re) :
    L ↗Λ s = -deriv riemannZeta s / riemannZeta s
-- -ζ'/ζ(s) = Σ Λ(n) n^(-s) (von Mangoldt)
```

**USEFUL:** `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` connects
the logarithmic derivative to the von Mangoldt function!

---

## 8. Series Representations

```lean
theorem zeta_eq_tsum_one_div_nat_cpow {s : ℂ} (hs : 1 < re s) :
    riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s
-- ζ(s) = Σ n^(-s) for Re(s) > 1

theorem zeta_nat_eq_tsum_of_gt_one {k : ℕ} (hk : 1 < k) :
    riemannZeta k = ∑' n : ℕ, 1 / (n : ℝ) ^ k
-- Real version for natural k > 1
```

---

## What's Missing for Littlewood

### Critical for Zero-Free Region
1. **Log-derivative bounds:** Need `-Re(ζ'/ζ(σ+it))` bounds for σ near 1
2. **Product inequality from trig:** |ζ(σ)|³|ζ(σ+it)|⁴|ζ(σ+2it)| ≥ 1

### Critical for Hardy's Theorem
1. **Hardy Z-function:** Not defined
2. **Riemann-Siegel theta:** Not defined
3. **Sign change analysis:** No oscillation theorems

### Critical for Explicit Formula
1. **Contour integration:** Limited Perron-type formulas
2. **Zero sum formulas:** No Σ x^ρ/ρ representations
3. **Zero counting N(T):** Not defined

### Nice to Have
1. **Zero density estimates:** N(σ,T) bounds
2. **Zero spacing:** γ_{n+1} - γ_n bounds
3. **Lindelöf hypothesis:** Not formalized

---

## Usage in Littlewood Project

### Currently Used
- `riemannZeta` - Basic definition
- `riemannZeta_ne_zero_of_one_lt_re` - Non-vanishing for Re(s) > 1
- `differentiableAt_riemannZeta` - Continuity away from s=1

### Should Use More
- `riemannZeta_ne_zero_of_one_le_re` - Non-vanishing for Re(s) ≥ 1!
- `riemannZeta_residue_one` - Pole behavior at s=1
- `riemannZeta_one_sub` - Functional equation
- `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` - Log derivative = -ζ'/ζ

### Key Insight
Mathlib has `riemannZeta_ne_zero_of_one_le_re` which gives non-vanishing
on the entire line Re(s) = 1 (except at s=1). This is the main ingredient
for the classical zero-free region!
