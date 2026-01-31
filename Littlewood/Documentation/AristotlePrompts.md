# Aristotle Prompt Queue

Priority-ordered prompts for closing the Hardy theorem chain.

## PROMPT 1: Mean Square Lower Bound (Highest Value)

```
Prove the mean square lower bound for the Riemann zeta function on the critical line.

THIS MUST BE UNCONDITIONAL - no typeclasses, no structures, no hypotheses.
Only Mathlib imports allowed.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

THEOREM TO PROVE:

theorem zeta_mean_square_lower :
    ∃ c : ℝ, c > 0 ∧ ∃ T₀ : ℝ, T₀ > 0 ∧
      ∀ T : ℝ, T ≥ T₀ →
        c * T * Real.log T ≤ ∫ t in Set.Ioc 1 T, ‖riemannZeta (1/2 + Complex.I * t)‖^2

This is a classical result of Hardy-Littlewood (1918).

PROOF APPROACH:

Method: Approximate Functional Equation
1. ζ(1/2+it) = Σ_{n≤N} n^{-1/2-it} + χ(1/2+it) Σ_{n≤M} n^{-1/2+it} + error
   where NM ≈ t/2π
2. ∫|ζ|² = ∫|Σ n^{-1/2-it}|² + cross terms + error
3. Diagonal terms give:
   ∫₁ᵀ Σ_{n≤√(t/2π)} n⁻¹ dt ≈ (1/2) T log T
4. Off-diagonal and cross terms are lower order.
5. Therefore ∫|ζ|² ≥ c T log T for some c > 0.

If the full proof is too hard, prove a WEAKER version:

theorem zeta_mean_square_growth :
    ¬ (∃ C : ℝ, ∀ T ≥ 1, ∫ t in Set.Ioc 1 T, ‖riemannZeta (1/2 + I * t)‖^2 ≤ C)

REQUIREMENTS:
- No sorry in the final theorem statement
- No typeclasses like ZetaMeanSquareHalfBound
- Import only from Mathlib
```

## PROMPT 2: Critical Line Bound (High Value)

```
Prove a bound for |ζ(1/2+it)| - UNCONDITIONALLY.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

THEOREM:

theorem zeta_critical_bound :
    ∃ C : ℝ, C > 0 ∧ ∃ T₀ : ℝ, T₀ > 0 ∧
      ∀ t : ℝ, |t| ≥ T₀ →
        ‖riemannZeta (1/2 + Complex.I * t)‖ ≤ C * |t|^(1/2 : ℝ)

This is the convexity bound μ(1/2) ≤ 1/4 (we prove the weaker exponent 1/2).

PROOF SKETCH:

Use the functional equation + Stirling:
1. ζ(s) = χ(s) ζ(1-s) where χ involves Γ
2. At s = 1/2 + it: bound |χ(1/2+it)| using Stirling
3. |ζ(1/2+it)|² = |χ(1/2+it)| · |ζ(1/2+it)| (from func eq + symmetry)
4. Bound |ζ(1/2+it)| using |ζ(σ+it)| for σ > 1 and Phragmén-Lindelöf

REQUIREMENTS:
- UNCONDITIONAL - no typeclasses, no structures
- Import only from Mathlib
- No sorry in final statement
```

## PROMPT 3: First Moment Upper Bound (High Value)

```
Prove an upper bound for the integral of the Hardy Z function.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

THEOREM:

theorem hardyZ_integral_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, C > 0 ∧ ∀ T : ℝ, T ≥ 1 →
      |∫ t in (0 : ℝ)..T,
        (Complex.exp (Complex.I * (Complex.log (Complex.Gamma (1/4 + Complex.I * (t/2)))).im
          - Complex.I * (t/2) * Real.log Real.pi)
        * riemannZeta (1/2 + Complex.I * t)).re|
      ≤ C * T^(1/2 + ε)

PROOF APPROACH:

This follows from the approximate functional equation for Z(t):
Z(t) = 2 Σ_{n≤√(t/2π)} n^{-1/2} cos(θ(t) - t log n) + O(t^{-1/4})

The integral of each cosine term is bounded (each oscillates), giving O(1) per term.
There are O(√T) terms, so the total integral is O(√T).
The error integral contributes O(T^{3/4}).

REQUIREMENTS:
- UNCONDITIONAL
- Import only from Mathlib
- No sorry in final statement
```

## PROMPT 4: Riemann-von Mangoldt Formula (Foundation)

```
Prove the Riemann-von Mangoldt formula UNCONDITIONALLY.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

THEOREM:

-- Define the zero counting function
noncomputable def NZeros (T : ℝ) : ℕ :=
  Set.ncard {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T}

theorem riemann_von_mangoldt_uniform :
    ∃ C : ℝ, C > 0 ∧ ∃ T₀ : ℝ, T₀ ≥ 2 ∧
      ∀ T : ℝ, T ≥ T₀ →
        |(NZeros T : ℝ) - ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1)))| ≤ C * Real.log T

IMPORTANT: The constant C must be UNIFORM (not depend on T).
Do NOT use the trivial trick of setting C = |LHS|/log T.

PROOF APPROACH:
1. Use the argument principle: N(T) = (1/2π) Δ arg ξ(s) around rectangle
2. ξ(s) = s(s-1)/2 · π^{-s/2} · Γ(s/2) · ζ(s)
3. Stirling's formula for arg Γ
4. Bound the S(T) = (1/π) arg ζ(1/2+iT) term
5. Combine for the asymptotic

REQUIREMENTS:
- UNCONDITIONAL
- UNIFORM C (the proof is FALSE if C depends on T)
- Import only from Mathlib
```

## PROMPT 5: Zero-Free Region (Foundation)

```
Prove the de la Vallée Poussin zero-free region for the Riemann zeta function.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

THEOREM:

theorem zero_free_region :
    ∃ c : ℝ, c > 0 ∧
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
        ρ.re < 1 - c / Real.log (|ρ.im| + 2)

PROOF APPROACH:

The classical proof uses the 3-4-1 inequality:
  3 log|ζ(σ)| + 4 log|ζ(σ+it)| + log|ζ(σ+2it)| ≥ 0

Already proved in Aristotle as `zeta_product_ge_one` in ThreeFourOne.lean.

From this:
1. Take σ = 1 + 1/log(|t|+2)
2. Use log|ζ(σ)| = -log(σ-1) + O(1) near σ=1
3. Use log|ζ(σ+it)| ≤ log log(|t|+2) + O(1) if ζ(β+iγ)=0 with β close to 1
4. Combine to get β < 1 - c/log(|γ|+2)

REQUIREMENTS:
- UNCONDITIONAL
- Import only from Mathlib
- May reference results from ThreeFourOne.lean if helpful
```
