/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Littlewood.Development.ZetaPositivity
import Littlewood.Aristotle.LaurentExpansion

/-!
# Zero-Free Region Development

Working toward the classical de la Vallée Poussin zero-free region:
ζ(s) ≠ 0 for Re(s) > 1 - c/log(|Im(s)| + 2)

## The Classical Approach

The de la Vallée Poussin zero-free region uses:
1. The trigonometric identity: 3 + 4cos(θ) + cos(2θ) ≥ 0
2. Applied to: Re(log ζ(σ)³ ζ(σ+it)⁴ ζ(σ+2it))
3. This forces zeros away from Re(s) = 1

## References
- Titchmarsh, "Theory of the Riemann Zeta Function", Chapter 3
- Montgomery-Vaughan, "Multiplicative Number Theory I", Chapter 6
-/

namespace Littlewood.Development.ZeroFreeRegion

open Complex Real Topology

-- ============================================================
-- SECTION 1: What Mathlib provides
-- ============================================================

#check riemannZeta
-- riemannZeta : ℂ → ℂ

#check riemannZeta_ne_zero_of_one_lt_re
-- ζ(s) ≠ 0 for Re(s) > 1 (Euler product region)

#check riemannZeta_ne_zero_of_one_le_re
-- ζ(s) ≠ 0 for Re(s) ≥ 1 (non-vanishing on critical line!)

#check differentiableAt_riemannZeta
-- ζ is differentiable away from s = 1

#check riemannZeta_residue_one
-- (s - 1) * ζ(s) → 1 as s → 1

#check riemannZeta_eulerProduct
-- Euler product formula

#check ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
-- L(Λ, s) = -ζ'/ζ(s)

/-
## What Mathlib Provides (Updated Task 46):

1. **Basic zeta function:** `riemannZeta : ℂ → ℂ`
2. **Non-vanishing for Re(s) > 1:** `riemannZeta_ne_zero_of_one_lt_re`
3. **Non-vanishing for Re(s) ≥ 1:** `riemannZeta_ne_zero_of_one_le_re` ✓ NEW!
4. **Functional equation:** `riemannZeta_one_sub`
5. **Differentiability:** `differentiableAt_riemannZeta`
6. **Residue at 1:** `riemannZeta_residue_one` ✓ USEFUL!
7. **Euler product:** `riemannZeta_eulerProduct`, `riemannZeta_eulerProduct_exp_log` ✓ NEW!
8. **Product bound:** `DirichletCharacter.norm_LSeries_product_ge_one` ✓ NEW!
9. **3-4-1 inequality:** `DirichletCharacter.re_log_comb_nonneg` ✓ NEW!
10. **Log derivative:** `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` ✓ NEW!

## What's Still Missing:

1. **Quantitative zero-free region:** σ > 1 - c/log|t| (de la Vallée Poussin)
   - We have Re(s) = 1 non-vanishing, but not the interior region
-/

-- ============================================================
-- SECTION 2: The trigonometric inequality
-- ============================================================

/-- The key trigonometric identity: 3 + 4cos(θ) + cos(2θ) ≥ 0.

This is equivalent to 2(1 + cos(θ))² ≥ 0, which is obviously true.
This inequality is the foundation of de la Vallée Poussin's zero-free region.

**Proof:** Using cos(2θ) = 2cos²(θ) - 1, we get:
  3 + 4cos(θ) + cos(2θ) = 3 + 4cos(θ) + 2cos²(θ) - 1 = 2(1 + cos(θ))² ≥ 0
-/
theorem trig_inequality (θ : ℝ) : 3 + 4 * Real.cos θ + Real.cos (2 * θ) ≥ 0 := by
  -- Using the double angle formula: cos(2θ) = 2cos²(θ) - 1
  have h : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  calc 3 + 4 * Real.cos θ + Real.cos (2 * θ)
      = 3 + 4 * Real.cos θ + (2 * Real.cos θ ^ 2 - 1) := by rw [h]
    _ = 2 * (1 + Real.cos θ) ^ 2 := by ring
    _ ≥ 0 := by positivity

/-- Variant: the identity equals 2(1 + cos θ)² -/
theorem trig_identity (θ : ℝ) : 3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ) ^ 2 := by
  have h : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  rw [h]; ring

-- ============================================================
-- SECTION 2.3: Connection to Mathlib's re_log_comb_nonneg (Task 47)
-- ============================================================

/-
## Connection: trig_inequality ↔ Mathlib's re_log_comb_nonneg

Our `trig_inequality`: 3 + 4cos(θ) + cos(2θ) ≥ 0

Mathlib's `re_log_comb_nonneg'` (private, but we explain the connection):
  0 ≤ 3·Re(-log(1-a)) + 4·Re(-log(1-az)) + Re(-log(1-az²))

**Key Insight:**
Using the Taylor series -log(1-x) = Σₙ xⁿ/n for |x| < 1:
  -log(1-a) = a + a²/2 + a³/3 + ...
  -log(1-az) = az + (az)²/2 + ...
  -log(1-az²) = az² + (az²)²/2 + ...

Taking the combination with coefficients 3, 4, 1:
  3·(-log(1-a)) + 4·(-log(1-az)) + (-log(1-az²))
  = Σₙ (aⁿ/n) · [3 + 4·Re(zⁿ) + Re(z²ⁿ)]

When z = e^(iθ), we get Re(zⁿ) = cos(nθ), so the bracket becomes:
  3 + 4·cos(nθ) + cos(2nθ) ≥ 0  (by trig_inequality with argument nθ)

Since each term in the sum is non-negative, the sum is non-negative.
This is exactly how Mathlib proves `re_log_comb_nonneg'`!

**Public Access:**
While `re_log_comb_nonneg'` is private in Mathlib, its consequence
`DirichletCharacter.norm_LSeries_product_ge_one` is public and gives:
  ‖L(χ⁰, 1+x)³ · L(χ, 1+x+iy)⁴ · L(χ², 1+x+2iy)‖ ≥ 1

This is the product bound that implies non-vanishing on Re(s) = 1.
-/

/-- The coefficients 3, 4, 1 in trig_inequality come from Mertens's insight:
    using (1+z)² = 1 + 2z + z² expands as:
    (3 + 4cos(θ) + cos(2θ)) = 2(1 + cos(θ))² ≥ 0.

    This same pattern appears in Mathlib's non-vanishing proof. -/
theorem trig_coefficients_explanation (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) =
    2 * (1 + Real.cos θ) ^ 2 := trig_identity θ

/-- For completeness: another proof of trig_inequality using norm bound.
    If |z| = 1, then |1 + z|² = (1 + Re(z))·2 when z = e^(iθ). -/
theorem trig_inequality_via_norm (θ : ℝ) : 3 + 4 * Real.cos θ + Real.cos (2 * θ) ≥ 0 := by
  rw [trig_identity θ]
  apply mul_nonneg (by norm_num : (2 : ℝ) ≥ 0)
  exact sq_nonneg _

-- ============================================================
-- SECTION 2.5: Mathlib-derived non-vanishing results (Task 46)
-- ============================================================

/-- **PROVED FROM MATHLIB**: ζ(s) ≠ 0 for Re(s) ≥ 1.

This is the KEY result that was missing! Mathlib now has this via
the 3-4-1 inequality applied to Dirichlet L-functions.
-/
theorem zeta_ne_zero_on_one_line (s : ℂ) (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- **PROVED FROM MATHLIB**: ζ(1 + it) ≠ 0 for all t ∈ ℝ.

This is the critical line non-vanishing that's crucial for PNT.
-/
theorem zeta_ne_zero_on_critical_line (t : ℝ) : riemannZeta (1 + t * I) ≠ 0 := by
  apply zeta_ne_zero_on_one_line
  simp [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im]

/-- **PROVED FROM MATHLIB**: The residue of ζ at s = 1 is 1.

(s - 1) * ζ(s) → 1 as s → 1.
-/
theorem zeta_residue_at_one : Filter.Tendsto (fun s => (s - 1) * riemannZeta s)
    (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds 1) :=
  riemannZeta_residue_one

/-- **PROVED FROM MATHLIB**: The Euler product formula for ζ(s), Re(s) > 1. -/
theorem zeta_euler_product (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ :=
  (riemannZeta_eulerProduct_tprod hs).symm

/-- **PROVED FROM MATHLIB**: The log of Euler product. -/
theorem zeta_euler_product_log (s : ℂ) (hs : 1 < s.re) :
    Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s))) = riemannZeta s :=
  riemannZeta_eulerProduct_exp_log hs

/-- **PROVED FROM MATHLIB**: The von Mangoldt identity -ζ'/ζ = L(Λ, s). -/
theorem neg_zeta_logderiv_eq_vonMangoldt (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
    -deriv riemannZeta s / riemannZeta s :=
  ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

-- ============================================================
-- SECTION 3: The classical argument (outline)
-- ============================================================

/-
## De la Vallée Poussin's Argument

The key idea is to apply the trigonometric inequality to the Euler product.

### Step 1: For σ > 1, the Euler product gives
  log ζ(s) = Σ_p Σ_k p^(-ks)/k

### Step 2: Taking real parts
  -Re(ζ'/ζ(σ)) = Σ_p Σ_k (log p) p^(-kσ) cos(kt log p)

### Step 3: Form the combination
  -3 Re(ζ'/ζ(σ)) - 4 Re(ζ'/ζ(σ+it)) - Re(ζ'/ζ(σ+2it))
  = Σ_p Σ_k (log p) p^(-kσ) (3 + 4cos(kt log p) + cos(2kt log p))
  ≥ 0  (by the trig inequality)

### Step 4: Analyze behavior as σ → 1+
  -ζ'/ζ(σ) ~ 1/(σ-1) as σ → 1+

### Step 5: If ζ(1+it) = 0 for some t ≠ 0, then
  -ζ'/ζ(σ+it) ~ -1/(σ-1+it-ρ) for zeros ρ near 1+it
  This leads to a contradiction with the non-negativity from Step 3.

### Conclusion
  There exists c > 0 such that ζ(s) ≠ 0 for Re(s) > 1 - c/log(|Im(s)|+2)
-/

-- ============================================================
-- SECTION 4: Stubs for development
-- ============================================================

/-- The logarithmic derivative of zeta (placeholder).

In the region Re(s) > 1, we have -ζ'/ζ(s) = Σ Λ(n) n^(-s)
where Λ is the von Mangoldt function.
-/
noncomputable def zetaLogDeriv (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s

/-- Stub: The combination 3·Re(-ζ'/ζ(σ)) + 4·Re(-ζ'/ζ(σ+it)) + Re(-ζ'/ζ(σ+2it)) ≥ 0
for σ > 1.

This is the key non-negativity that implies the zero-free region.

**NOTE (Task 46):** Mathlib has `DirichletCharacter.re_log_comb_nonneg` which proves
this for Dirichlet L-functions. The proof uses this to derive non-vanishing on Re(s) = 1.
We inherit the result via `riemannZeta_ne_zero_of_one_le_re`.
-/
theorem mertens_inequality_stub (σ : ℝ) (t : ℝ) (hσ : 1 < σ) :
    3 * (zetaLogDeriv σ).re + 4 * (zetaLogDeriv (σ + t * I)).re +
    (zetaLogDeriv (σ + 2 * t * I)).re ≥ 0 := by
  -- This follows from DirichletCharacter.re_log_comb_nonneg for trivial character
  -- The key insight is that Mathlib already uses this to prove non-vanishing
  -- See DirichletCharacter.norm_LSeries_product_ge_one
  sorry -- BLOCKED: Need to specialize DirichletCharacter.norm_LSeries_product_ge_one to trivial char
         -- Mathlib PR needed: Trivial character specialization (MEDIUM complexity)

/-- Stub: Zero-free region.

There exists c > 0 such that ζ(s) ≠ 0 for Re(s) > 1 - c/log(|Im(s)|+2).

**NOTE (Task 46):** Mathlib proves ζ(s) ≠ 0 for Re(s) ≥ 1 via `riemannZeta_ne_zero_of_one_le_re`.
This is STRONGER than the boundary case but does not give the quantitative interior region.
The de la Vallée Poussin region σ > 1 - c/log|t| requires additional analysis.
-/
theorem zero_free_region_stub :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s.re > 1 - c / Real.log (|s.im| + 2) →
    riemannZeta s ≠ 0 := by
  -- For the boundary case Re(s) = 1, we have Mathlib's result
  -- For the interior region, we need quantitative bounds from the 3-4-1 argument
  -- The qualitative version is: use riemannZeta_ne_zero_of_one_le_re for Re(s) ≥ 1
  use 0.001 -- placeholder
  constructor
  · norm_num
  · intro s hs
    by_cases h : 1 ≤ s.re
    · exact riemannZeta_ne_zero_of_one_le_re h
    · -- Interior region: need de la Vallée Poussin analysis
      sorry -- BLOCKED: quantitative zero-free region

-- ============================================================
-- SECTION 4.5: Building from trig_inequality (Task 16)
-- ============================================================

/-
## Strategy: From Trigonometric to Zero-Free

The key insight is that the trigonometric inequality, applied to the
Euler product, gives a lower bound on a combination of log|ζ|.

For σ > 1 and primes p, we have:
  log|ζ(σ)| = Σ_p Σ_k p^(-kσ)/k (from Euler product)

Applying the trig inequality with θ = t log p:
  3 log|ζ(σ)| + 4 log|ζ(σ+it)| + log|ζ(σ+2it)| ≥ 0

This means: |ζ(σ)|³ |ζ(σ+it)|⁴ |ζ(σ+2it)| ≥ 1
-/

/-- The product inequality from applying trig_inequality to Euler product.

For σ > 1 and any t, we have: |ζ(σ)|³ |ζ(σ+it)|⁴ |ζ(σ+2it)| ≥ 1

This is the key inequality that prevents zeros near σ = 1.

**NOTE (Task 46):** Mathlib has `DirichletCharacter.norm_LSeries_product_ge_one` for
L-functions of Dirichlet characters. For trivial character N=1, this gives exactly
this inequality for the Riemann zeta function!
-/
theorem zeta_product_lower_bound (σ : ℝ) (t : ℝ) (hσ : 1 < σ) :
    ‖riemannZeta σ‖ ^ 3 * ‖riemannZeta (σ + t * I)‖ ^ 4 *
    ‖riemannZeta (σ + 2 * t * I)‖ ≥ 1 := by
  -- Use Mathlib's DirichletCharacter.norm_LFunction_product_ge_one for N = 1
  -- For N = 1: LFunctionTrivChar 1 s = riemannZeta s (since 1 has no prime factors)
  -- Setting x = σ - 1, y = t gives our result
  have hx : 0 < σ - 1 := by linarith
  -- Get the product bound from Mathlib
  have hbound := DirichletCharacter.norm_LFunction_product_ge_one (N := 1) (χ := 1) hx t
  -- Key: 1 + ↑(σ - 1) = ↑σ (in ℂ)
  have hconv : (1 : ℂ) + ((σ - 1 : ℝ) : ℂ) = (σ : ℂ) := by
    push_cast; ring
  -- For N = 1: LFunctionTrivChar 1 s = riemannZeta s (1 has no prime factors)
  have hσ_ne : (1 : ℂ) + (σ - 1 : ℝ) ≠ 1 := by
    rw [hconv]
    intro h
    have : σ = 1 := by exact_mod_cast h
    linarith
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hσ_ne,
      Nat.primeFactors_one, Finset.prod_empty, one_mul] at hbound
  -- LFunction 1 for N=1 equals riemannZeta by LFunction_modOne_eq
  -- Note: 1^2 = 1, so (1^2 : DirichletCharacter ℂ 1) = 1
  simp only [one_pow, DirichletCharacter.LFunction_modOne_eq] at hbound
  -- Convert the arguments: 1 + (σ-1) → σ, 1 + (σ-1) + I*t → σ + t*I, etc.
  -- Also: ‖a * b * c‖ = ‖a‖ * ‖b‖ * ‖c‖ and ‖a^n‖ = ‖a‖^n
  rw [hconv] at hbound
  -- Fix argument order: I * t = t * I
  have ht_comm : (I : ℂ) * t = t * I := mul_comm I t
  have ht_comm2 : (2 : ℂ) * I * t = 2 * t * I := by ring
  simp only [ht_comm, ht_comm2] at hbound
  -- Now use norm properties
  rw [norm_mul, norm_mul, norm_pow, norm_pow] at hbound
  exact hbound

/-- Consequence: If ζ(σ + it) = 0 with t ≠ 0, then |ζ(σ)| → ∞ as σ → 1+.

More precisely: |ζ(σ + it)| = 0 implies |ζ(σ)|³ |ζ(σ + 2it)| ≥ 1,
but |ζ(σ)| has a pole of order 1 at σ = 1, so this limits how close
zeros can be to σ = 1.
-/
lemma zero_forces_zeta_large (σ : ℝ) (t : ℝ) (hσ : 1 < σ) (ht : t ≠ 0)
    (hzero : riemannZeta (σ + t * I) = 0) :
    ‖riemannZeta σ‖ ^ 3 * ‖riemannZeta (σ + 2 * t * I)‖ ≥ 1 := by
  have h := zeta_product_lower_bound σ t hσ
  simp only [hzero, map_zero, zero_pow (by norm_num : 4 ≠ 0), mul_zero] at h
  -- h : 0 ≥ 1 which is false
  norm_num at h

/-- The pole behavior: |ζ(σ)| ~ 1/(σ-1) as σ → 1+.

More precisely: (σ-1)|ζ(σ)| → 1 as σ → 1+.
-/
lemma zeta_pole_behavior :
    Filter.Tendsto (fun σ : ℝ => (σ - 1) * ‖riemannZeta σ‖)
    (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  -- Strategy: Use riemannZeta_residue_one plus the fact that ζ(σ) is positive real for σ > 1
  -- Step 1: For σ > 1, ‖ζ(σ)‖ = (ζ(σ)).re since ζ(σ) is positive real
  have hzeta_real : ∀ σ : ℝ, 1 < σ → ‖riemannZeta σ‖ = (riemannZeta σ).re := by
    intro σ hσ
    have him := ZetaPositivity.riemannZeta_im_zero_of_real σ hσ
    have hpos := ZetaPositivity.riemannZeta_pos_of_real_gt_one σ hσ
    -- |z.re| = ‖z‖ when z.im = 0
    rw [← Complex.abs_re_eq_norm.mpr him]
    -- |z.re| = z.re when z.re > 0
    exact abs_of_pos hpos
  -- Step 2: Restrict riemannZeta_residue_one to real line
  -- (s-1)*ζ(s) → 1 as s → 1 in ℂ\{1} implies it tends to 1 along reals > 1
  have hres := riemannZeta_residue_one
  -- Step 2a: Show coe : ℝ → ℂ maps nhdsWithin 1 (Ioi 1) into nhdsWithin 1 {1}ᶜ
  have hmap : Filter.Tendsto (fun σ : ℝ => (σ : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhdsWithin 1 {(1 : ℂ)}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · apply eventually_nhdsWithin_of_forall
      intro σ hσ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      exact ne_of_gt hσ (Complex.ofReal_injective h)
  -- Step 2b: Restrict hres to real line
  have hres_real : Filter.Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * riemannZeta σ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := hres.comp hmap
  -- Step 3: Take real part (since limit is real)
  have hres_re : Filter.Tendsto (fun σ : ℝ => (((σ : ℂ) - 1) * riemannZeta σ).re)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 : ℂ).re) :=
    (Complex.continuous_re.tendsto 1).comp hres_real
  -- Step 4: Simplify ((σ - 1) * ζ(σ)).re = (σ - 1) * (ζ(σ)).re
  have hsimpl : ∀ σ : ℝ, (((σ : ℂ) - 1) * riemannZeta σ).re = (σ - 1) * (riemannZeta σ).re := by
    intro σ
    rw [Complex.mul_re]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re,
               Complex.sub_im, Complex.ofReal_im, Complex.one_im, sub_zero, zero_mul, sub_zero]
  -- Step 5: For σ > 1, (ζ(σ)).re = ‖ζ(σ)‖, so the functions are equal eventually
  have heq : (fun σ : ℝ => (((σ : ℂ) - 1) * riemannZeta σ).re) =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
             (fun σ : ℝ => (σ - 1) * ‖riemannZeta σ‖) := by
    apply eventually_nhdsWithin_of_forall
    intro σ hσ
    simp only
    rw [hsimpl, ← hzeta_real σ hσ]
  -- Step 6: Combine
  simp only [Complex.one_re] at hres_re
  exact hres_re.congr' heq

-- ============================================================
-- SECTION 4.4: Multiplicative bounds from LaurentExpansion (Task 47)
-- ============================================================

/-- For σ ∈ (1, 1+r), the product (σ-1)*Re(-ζ'/ζ(σ)) is bounded and near 1.
    This uses neg_zeta_logDeriv_principal_part from LaurentExpansion.lean. -/
theorem sigma_times_neg_logderiv_bounded :
    ∃ r > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + r →
      |(σ - 1) * (-deriv riemannZeta σ / riemannZeta σ).re - 1| ≤ M := by
  obtain ⟨r, hr_pos, M, hM⟩ := neg_zeta_logDeriv_principal_part
  use r, hr_pos, M
  constructor
  · -- Show M ≥ 0
    by_contra h
    push_neg at h
    -- Pick some σ ∈ (1, 1+r)
    have hσ := (Set.nonempty_Ioo.mpr (by linarith : 1 < 1 + r)).some_mem
    set σ := (Set.nonempty_Ioo.mpr (by linarith : 1 < 1 + r)).some
    have hσ_gt : 1 < σ := hσ.1
    have hσ_lt : σ < 1 + r := hσ.2
    have hσ_ne : (σ : ℂ) ≠ 1 := by
      intro heq; exact ne_of_gt hσ_gt (Complex.ofReal_injective heq)
    have hdist : ‖(σ : ℂ) - 1‖ < r := by
      have h1 : (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : σ - 1 > 0)]
      linarith
    have hbound := hM σ hσ_ne hdist
    have hpos : 0 ≤ ‖((σ : ℂ) - 1) * (-deriv riemannZeta ↑σ / riemannZeta ↑σ) - 1‖ := norm_nonneg _
    linarith
  · intro σ hσ_gt hσ_lt
    have hσ_ne : (σ : ℂ) ≠ 1 := by
      intro heq; exact ne_of_gt hσ_gt (Complex.ofReal_injective heq)
    have hdist : ‖(σ : ℂ) - 1‖ < r := by
      have h1 : (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : σ - 1 > 0)]
      linarith
    have hbound := hM σ hσ_ne hdist
    -- Extract real part bound from norm bound
    -- For real σ, ((σ-1)*f).re = (σ-1)*f.re
    have hre : ((↑σ - 1 : ℂ) * (-deriv riemannZeta ↑σ / riemannZeta ↑σ)).re =
               (σ - 1) * (-deriv riemannZeta ↑σ / riemannZeta ↑σ).re := by
      rw [Complex.mul_re]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re,
                 Complex.sub_im, Complex.ofReal_im, Complex.one_im, sub_zero]
      ring
    calc |(σ - 1) * (-deriv riemannZeta ↑σ / riemannZeta ↑σ).re - 1|
        = |((↑σ - 1 : ℂ) * (-deriv riemannZeta ↑σ / riemannZeta ↑σ) - 1).re| := by
          rw [Complex.sub_re, hre, Complex.one_re]
      _ ≤ ‖((↑σ : ℂ) - 1) * (-deriv riemannZeta ↑σ / riemannZeta ↑σ) - 1‖ := Complex.abs_re_le_norm _
      _ ≤ M := hbound

/-- Upper bound: Re(-ζ'/ζ(σ)) ≤ (1+M)/(σ-1) for σ near 1.
    This is the multiplicative form of the bound. -/
theorem neg_zeta_logderiv_re_upper :
    ∃ r > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + r →
      (-deriv riemannZeta σ / riemannZeta σ).re ≤ (1 + C) / (σ - 1) := by
  obtain ⟨r, hr_pos, M, hM_nonneg, hM⟩ := sigma_times_neg_logderiv_bounded
  use r, hr_pos, M, hM_nonneg
  intro σ hσ_gt hσ_lt
  have hσ_pos : 0 < σ - 1 := by linarith
  have hbound := hM σ hσ_gt hσ_lt
  -- From |x - 1| ≤ M, we get x ≤ 1 + M (since h.1 gives x - 1 ≤ M)
  have h := abs_sub_le_iff.mp hbound
  have hupper : (σ - 1) * (-deriv riemannZeta ↑σ / riemannZeta ↑σ).re ≤ 1 + M := by linarith [h.1]
  rw [le_div_iff₀ hσ_pos]
  linarith

/-- Lower bound: Re(-ζ'/ζ(σ)) ≥ (1-M)/(σ-1) for σ near 1 -/
theorem neg_zeta_logderiv_re_lower :
    ∃ r > 0, ∃ C : ℝ, ∀ σ : ℝ, 1 < σ → σ < 1 + r →
      (1 - C) / (σ - 1) ≤ (-deriv riemannZeta σ / riemannZeta σ).re := by
  obtain ⟨r, hr_pos, M, _, hM⟩ := sigma_times_neg_logderiv_bounded
  use r, hr_pos, M
  intro σ hσ_gt hσ_lt
  have hσ_pos : 0 < σ - 1 := by linarith
  have hbound := hM σ hσ_gt hσ_lt
  have h := abs_sub_le_iff.mp hbound
  -- h.2 gives 1 - x ≤ M, so x ≥ 1 - M
  have hlower : 1 - M ≤ (σ - 1) * (-deriv riemannZeta ↑σ / riemannZeta ↑σ).re := by linarith [h.2]
  rw [div_le_iff₀ hσ_pos]
  linarith

-- ============================================================
-- SECTION 4.45: Analyticity of (s-1)*(-ζ'/ζ) at s = 1 (Task 47)
-- ============================================================

/-- The function (s-1)²ζ'(s) extended analytically to s = 1.
    This equals deriv sqZeta s - 2*zetaMulSubOne s, which is analytic. -/
noncomputable def subSqMulZetaDeriv (s : ℂ) : ℂ :=
  deriv sqZeta s - 2 * zetaMulSubOne s

/-- subSqMulZetaDeriv is analytic at s = 1. -/
theorem subSqMulZetaDeriv_analyticAt_one : AnalyticAt ℂ subSqMulZetaDeriv 1 := by
  unfold subSqMulZetaDeriv
  apply AnalyticAt.sub
  · exact sqZeta_analyticAt_one.deriv
  · exact analyticAt_const.mul zetaMulSubOne_analyticAt_one

/-- subSqMulZetaDeriv equals (s-1)²*ζ'(s) for s ≠ 1. -/
theorem subSqMulZetaDeriv_eq (s : ℂ) (hs : s ≠ 1) :
    subSqMulZetaDeriv s = (s - 1)^2 * deriv riemannZeta s := by
  unfold subSqMulZetaDeriv
  rw [deriv_sqZeta_eq s hs]
  simp only [zetaMulSubOne, if_neg hs, mul_comm 2, two_mul]
  ring

/-- subSqMulZetaDeriv(1) = -1. -/
theorem subSqMulZetaDeriv_at_one : subSqMulZetaDeriv 1 = -1 := by
  unfold subSqMulZetaDeriv
  rw [deriv_sqZeta_at_one]
  simp only [zetaMulSubOne, ↓reduceIte]
  norm_num

/-- The function (s-1)*(-ζ'/ζ(s)) extended analytically to s = 1.
    This equals -subSqMulZetaDeriv s / zetaMulSubOne s. -/
noncomputable def negLogDerivTimesSubOne (s : ℂ) : ℂ :=
  -subSqMulZetaDeriv s / zetaMulSubOne s

/-- negLogDerivTimesSubOne is analytic at s = 1 (key result!). -/
theorem negLogDerivTimesSubOne_analyticAt_one : AnalyticAt ℂ negLogDerivTimesSubOne 1 := by
  unfold negLogDerivTimesSubOne
  apply AnalyticAt.div
  · exact subSqMulZetaDeriv_analyticAt_one.neg
  · exact zetaMulSubOne_analyticAt_one
  · simp only [zetaMulSubOne, if_pos rfl]
    exact one_ne_zero

/-- negLogDerivTimesSubOne(1) = 1. -/
theorem negLogDerivTimesSubOne_at_one : negLogDerivTimesSubOne 1 = 1 := by
  unfold negLogDerivTimesSubOne
  rw [subSqMulZetaDeriv_at_one]
  simp only [zetaMulSubOne, ↓reduceIte, neg_neg, div_one]

/-- negLogDerivTimesSubOne equals (s-1)*(-ζ'/ζ(s)) for s ≠ 1 where ζ(s) ≠ 0. -/
theorem negLogDerivTimesSubOne_eq (s : ℂ) (hs : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    negLogDerivTimesSubOne s = (s - 1) * (-deriv riemannZeta s / riemannZeta s) := by
  unfold negLogDerivTimesSubOne
  rw [subSqMulZetaDeriv_eq s hs]
  simp only [zetaMulSubOne, if_neg hs]
  have hs_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hprod_ne : (s - 1) * riemannZeta s ≠ 0 := mul_ne_zero hs_ne hζ
  field_simp [hζ, hs_ne, hprod_ne]

/-- The logarithmic derivative has a simple pole at s = 1.

-ζ'(s)/ζ(s) = 1/(s-1) + holomorphic part

### Infrastructure (PROVED above):
- `negLogDerivTimesSubOne_analyticAt_one`: (s-1)*(-ζ'/ζ(s)) is analytic at s = 1
- `negLogDerivTimesSubOne_at_one`: Value at s = 1 is 1

### Proof Strategy:
1. h(s) = negLogDerivTimesSubOne(s) - 1 is analytic at 1 with h(1) = 0.
2. By `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`, h(s) = (s-1)*k(s)
   for some analytic k (since h(1) = 0, the order of vanishing is ≥ 1).
3. So negLogDerivTimesSubOne(s) = 1 + (s-1)*k(s).
4. For s ≠ 1: -ζ'/ζ(s) = negLogDerivTimesSubOne(s)/(s-1) = 1/(s-1) + k(s).
5. Take f = k (analytic at 1).
-/
lemma neg_zeta_logderiv_expansion :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f 1 ∧
    ∀ᶠ s in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ,
      zetaLogDeriv s = 1 / (s - 1) + f s := by
  -- Infrastructure is in place (negLogDerivTimesSubOne_analyticAt_one, etc.)
  -- Requires extracting the zero factorization: h = (s-1)*k for analytic k.
  sorry

/-- The bound on -Re(ζ'/ζ) for σ > 1.

-Re(ζ'/ζ(σ)) ≤ 1/(σ-1) + C for some constant C.

### Infrastructure (PROVED above):
- `negLogDerivTimesSubOne_analyticAt_one`: (s-1)*(-ζ'/ζ(s)) is analytic at s = 1
- `negLogDerivTimesSubOne_at_one`: Value at s = 1 is 1
- `negLogDerivTimesSubOne_eq`: Equals (s-1)*(-ζ'/ζ(s)) for s ≠ 1

### Proof Strategy:
1. Since negLogDerivTimesSubOne is analytic at 1 with value 1, the function
   h(s) = negLogDerivTimesSubOne(s) - 1 is analytic with h(1) = 0.
2. By `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`, h(s) = (s-1)^n * g(s)
   for some n ≥ 1 and analytic g with g(1) ≠ 0.
3. For s near 1: negLogDerivTimesSubOne(s) = 1 + (s-1)*k(s) for analytic k.
4. Hence (s-1)*|Re(-ζ'/ζ(σ))| - 1 ≤ (σ-1)*|k(σ)| ≤ K*(σ-1).
5. This gives Re(-ζ'/ζ(σ)) ≤ 1/(σ-1) + K for σ near 1.
6. For σ ∈ [1+δ, 2], use continuity on compact set.

### What Remains:
- Extract the factorization from analyticity
- Combine near-1 and away-from-1 bounds
-/
lemma neg_zeta_logderiv_re_bound :
    ∃ C : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (zetaLogDeriv σ).re ≤ 1 / (σ - 1) + C := by
  -- Infrastructure is in place (negLogDerivTimesSubOne_analyticAt_one, etc.)
  -- Full proof requires extracting the zero factorization from analyticity.
  sorry

/-- The classical de la Vallée Poussin zero-free region.

Combining the product inequality with the pole behavior, we get:
ζ(s) ≠ 0 for Re(s) ≥ 1 - c/log(|Im(s)| + 2)

**Proof outline:**
1. Suppose ζ(β + iγ) = 0 with β close to 1
2. From zeta_product_lower_bound: |ζ(σ)|³ |ζ(σ+2iγ)| ≥ 1 for σ > 1
3. As σ → 1+: |ζ(σ)| ~ 1/(σ-1), bounded |ζ(σ+2iγ)|
4. Get: 1/(σ-1)³ · M ≥ 1, so (σ-1)³ ≤ M
5. The zero β pushes this bound, giving β ≤ 1 - c/log|γ|

**NOTE (Task 46):** Mathlib proves the BOUNDARY case ζ(s) ≠ 0 for Re(s) ≥ 1.
The quantitative interior region requires extracting the constant c from the
3-4-1 argument. This is the remaining gap for zero-free regions.
-/
theorem de_la_vallee_poussin_zero_free :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, 0 < s.im →
      s.re ≥ 1 - c / Real.log (s.im + 2) →
      riemannZeta s ≠ 0 := by
  -- For s.re ≥ 1, use Mathlib's riemannZeta_ne_zero_of_one_le_re
  -- For 1 - c/log(t) < s.re < 1, need quantitative analysis
  use 0.001 -- placeholder for actual constant
  constructor
  · norm_num
  · intro s hpos hre
    by_cases h : 1 ≤ s.re
    · exact riemannZeta_ne_zero_of_one_le_re h
    · sorry -- BLOCKED: quantitative interior region

-- ============================================================
-- SECTION 5: Gap Analysis (Updated Task 46)
-- ============================================================

/-
## Gap Analysis for Zero-Free Region (Updated Task 46)

### What We CAN Prove Now (from Mathlib):
1. ✓ Trigonometric inequality (proved above)
2. ✓ ζ(s) ≠ 0 for Re(s) > 1 (from Mathlib)
3. ✓ ζ(s) ≠ 0 for Re(s) ≥ 1 (NEW! `riemannZeta_ne_zero_of_one_le_re`)
4. ✓ ζ(1 + it) ≠ 0 for all t (NEW! `zeta_ne_zero_on_critical_line`)
5. ✓ Euler product formula (from Mathlib)
6. ✓ Euler product log form (from Mathlib)
7. ✓ -ζ'/ζ = L(Λ,s) identity (from Mathlib)
8. ✓ Residue at s=1 (from Mathlib)
9. ✓ Product bound |ζ|³|ζ|⁴|ζ| ≥ 1 (in Mathlib as DirichletCharacter theorem)
10. ✓ 3-4-1 inequality (in Mathlib as re_log_comb_nonneg)
11. ✓ Differentiability of ζ (from Mathlib)

### NEW THEOREMS PROVED (Task 46):
- `zeta_ne_zero_on_one_line` - Direct wrapper for Mathlib result
- `zeta_ne_zero_on_critical_line` - ζ(1+it) ≠ 0 for all t
- `zeta_residue_at_one` - Residue wrapper
- `zeta_euler_product` - Euler product wrapper
- `zeta_euler_product_log` - Log Euler product wrapper
- `neg_zeta_logderiv_eq_vonMangoldt` - Log derivative identity wrapper

### What's Still Blocked:

1. **Quantitative Zero-Free Region:**
   - Mathlib proves Re(s) = 1 non-vanishing (boundary)
   - Missing: σ > 1 - c/log|t| (interior region with explicit c)

2. **Extraction from Dirichlet Framework:**
   - Mathlib's results are in DirichletCharacter namespace
   - Need to specialize `norm_LSeries_product_ge_one` to riemannZeta

3. **Real-Valued Zeta on Reals:**
   - For σ > 1, ζ(σ) is real and positive
   - Blocks converting residue to norm form

### Summary of Sorries (8 total, down from needing full proofs):
- mertens_inequality_stub: BLOCKED (Dirichlet extraction)
- zero_free_region_stub: PARTIAL (boundary OK, interior blocked)
- zeta_product_lower_bound: BLOCKED (Dirichlet extraction)
- zero_forces_zeta_large: BLOCKED (depends on above)
- zeta_pole_behavior: BLOCKED (real-valued zeta)
- neg_zeta_logderiv_expansion: BLOCKED (Laurent extraction)
- neg_zeta_logderiv_re_bound: BLOCKED
- de_la_vallee_poussin_zero_free: PARTIAL (boundary OK, interior blocked)

### Progress: 6 new theorems proved from Mathlib! Key result: ζ(1+it) ≠ 0 ∀t
-/

end Littlewood.Development.ZeroFreeRegion
