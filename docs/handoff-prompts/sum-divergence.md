# Handoff Prompt: Divergence of Sum Re(I/rho) over Positive-Imaginary Zeros

> **STATUS**: This prompt is now **OPTIONAL** for the main Littlewood proof.
> The B5b sorry was originally planned to use the Ingham phase-alignment
> approach, which required this divergent sum as a sub-result. After
> discovering that phase alignment to w=I requires the Linear Independence
> conjecture for zeta ordinates (an open problem), B5b was restructured
> to use Landau's indirect argument instead (see `inhomogeneous-dirichlet.md`).
>
> This sum divergence result remains **valid standalone infrastructure**
> and is independently interesting. It would become relevant again if
> the LI conjecture were assumed or proved, enabling the stronger
> Ω±(√x · log log log x) quantitative result.

## Task

Prove in Lean 4 / Mathlib that under the Riemann Hypothesis, the sum of `Re(I/ρ)` over critical zeros with positive imaginary part diverges to `+∞`.

## Target File

Create a **new standalone file**:
```
Littlewood/Aristotle/Standalone/ZeroSumDivergence.lean
```

## Exact Signature

```lean
theorem posImZeroSum_re_I_div_diverges
    (hRH : ZetaZeros.RiemannHypothesis) :
    ∀ B : ℝ, ∃ T : ℝ, T ≥ 2 ∧
      ∑ ρ ∈ (ZerosBelow T).filter (fun ρ => 0 < ρ.im), (I / ρ).re > B
```

## File Template

```lean
/-
Divergence of ∑_{Im(ρ)>0} Re(I/ρ) under RH.

Under RH, every critical zero has the form ρ = 1/2 + iγ with γ real.
For γ > 0: Re(I/ρ) = Re(I/(1/2+iγ)) = γ/(1/4+γ²) ≥ 1/(2γ).
Combined with N(T) ≥ (T/3π)·log T, partial summation gives
∑_{0<γ≤T} 1/γ ≥ c·(log T)², which diverges.

Reference: Backlund (1918), Titchmarsh §9.4.
-/

import Littlewood.Aristotle.DirichletPhaseAlignment
import Littlewood.ZetaZeros.ZeroCountingFunction

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Aristotle.Standalone.ZeroSumDivergence

open Filter Complex Real
open Aristotle.DirichletPhaseAlignment (ZerosBelow CriticalZeros)
open ZetaZeros

-- Your code here

end Aristotle.Standalone.ZeroSumDivergence
```

## Critical Mathematical Warning

**The full `ZerosBelow T` sum CANCELS.** Zeros come in conjugate pairs `ρ = 1/2 ± iγ`, and:
```
Re(I/ρ) + Re(I/ρ̄) = γ/(1/4+γ²) + (-γ)/(1/4+γ²) = 0
```

The divergence comes from restricting to **positive-imaginary zeros only**. This is why the filter `(fun ρ => 0 < ρ.im)` is essential in the statement.

## Available Infrastructure

### From `DirichletPhaseAlignment.lean`

```lean
-- The set of non-trivial zeros (line 38)
def CriticalZeros : Set ℂ := {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

-- Finset of critical zeros with |Im| ≤ T (line 41)
def ZerosBelow (T : ℝ) : Finset ℂ :=
  if h : (CriticalZeros ∩ {ρ | |ρ.im| ≤ T}).Finite then h.toFinset else ∅
```

### From `ZeroCountingFunction.lean`

```lean
-- The zero counting function (counts zeros with 0 < Im ≤ T)
noncomputable def N (T : ℝ) : ℕ := ...

-- Lower bound hypothesis (line 584)
class ZeroCountingLowerBoundHyp : Prop where
  lower_bound : ∃ T0 : ℝ, ∀ T ≥ T0, T / (3 * π) * Real.log T ≤ N T
```

### From `ZetaZeros` namespace

```lean
-- The Riemann Hypothesis
class RiemannHypothesis : Prop  -- ∀ ρ ∈ CriticalZeros, ρ.re = 1/2
```

### From `PsiZeroSumOscillationFromIngham.lean` (already proved)

```lean
-- Positive-Im zero subset (line 65)
def PositiveImZerosBelow (T : ℝ) : Finset ℂ :=
  (ZerosBelow T).filter (fun ρ => 0 < ρ.im)

-- Under RH, all zeros in PositiveImZerosBelow have re = 1/2 (line 72)
lemma positiveImZerosBelow_re_half (T : ℝ) (hRH : ZetaZeros.RiemannHypothesis) :
    ∀ ρ ∈ PositiveImZerosBelow T, ρ.re = 1 / 2

-- Re(I/ρ) ≤ 1/‖ρ‖ for nonzero ρ (line 89)
lemma re_I_div_le_inv_norm (ρ : ℂ) (_hρ : ρ ≠ 0) :
    (I / ρ).re ≤ 1 / ‖ρ‖
```

**NOTE on `ZeroCountingLowerBoundHyp`:** This is a typeclass with a sorry-backed instance only in `Assumptions.lean`. The Standalone directory does NOT import `Assumptions.lean`. You have two options:
1. Add `[ZeroCountingLowerBoundHyp]` as a class parameter to your theorem (clean but changes signature)
2. Sorry the N(T) lower bound locally as a `have` (keeps the stated signature exact)

**Recommended: Option 2** — sorry the N(T) lower bound as a local lemma. The statement `posImZeroSum_re_I_div_diverges` should take only `hRH` as hypothesis.

## Mathematical Strategy

### Step 1: Compute Re(I/(1/2+iγ)) explicitly

For `ρ = 1/2 + iγ` with `γ > 0`:
```
I/(1/2 + iγ) = I·(1/2 - iγ) / (1/4 + γ²) = (γ + i/2) / (1/4 + γ²)
```
So `Re(I/ρ) = γ/(1/4 + γ²)`.

**Lean proof idea:** Use `Complex.ext_iff` to compute real and imaginary parts of `I / (1/2 + I*γ)`. The key identity is:
```lean
have : (I / (1/2 + I * γ)).re = γ / (1/4 + γ^2) := by
  rw [Complex.div_re]; ring_nf; ...
```

### Step 2: Lower bound for γ ≥ 1

For `γ ≥ 1`: `γ/(1/4 + γ²) ≥ γ/(2γ²) = 1/(2γ)`.

Proof: `1/4 + γ² ≤ γ² + γ² = 2γ²` when `γ ≥ 1` (since `1/4 ≤ γ² ≤ γ²`). Actually more carefully: `1/4 ≤ γ²` when `γ ≥ 1/2`, so `1/4 + γ² ≤ 2γ²`.

### Step 3: Connect Finset.card to N(T)

The cardinality of `PositiveImZerosBelow T` equals `N T` (or is at least `N T` minus a bounded correction). The zero counting function `N(T)` counts zeros with `0 < Im(ρ) ≤ T`, which is exactly what `PositiveImZerosBelow T` contains.

**Warning:** The exact relationship between `Finset.card (PositiveImZerosBelow T)` and `N T` may require careful argument about the definition alignment. If this is too hard to formalize exactly, sorry it as a local `have`.

### Step 4: Partial summation argument

From `N(T) ≥ (T/3π)·log T` (for large T):

```
∑_{0<γ≤T} 1/γ ≥ N(T)/T + ∫₁ᵀ N(t)/t² dt
                ≥ (log T)/(3π) + ∫₁ᵀ (log t)/(3π·t) dt
                = (log T)/(3π) + (log T)²/(6π)
```

For any bound `B`, choosing `T` with `(log T)² > 12πB` gives the sum exceeding `B`.

### Simplified approach (recommended for Lean)

Rather than formalizing full partial summation, consider this simpler argument:

1. Sorry locally: `have hN_lb : ∃ T₀, ∀ T ≥ T₀, (PositiveImZerosBelow T).card ≥ ⌊T / (3*π) * log T⌋₊`
2. Sorry locally: `have hRe_lb : ∀ ρ ∈ PositiveImZerosBelow T, ρ.im ≤ T → (I/ρ).re ≥ 1/(2*T)` (since γ ≤ T ⟹ γ/(1/4+γ²) ≥ γ/(2T²) ... actually this bound is too weak)

**Better simplified approach:**

1. For the finite sum, use: `∑_{ρ : γ∈(T/2, T]} Re(I/ρ) ≥ |{ρ : γ∈(T/2,T]}| · 1/(2T)` since each `γ ≤ T` gives `Re(I/ρ) ≥ γ/(2γ²) ≥ (T/2)/(2T²) = 1/(4T)` ... This is getting tangled.

**Cleanest Lean approach:** Prove a helper that for any `C > 0`, for large enough `T`, the sum over positive-Im zeros exceeds `C`. Use:
- Each positive-Im zero with `1 ≤ γ ≤ T` contributes `Re(I/ρ) ≥ 1/(2T)`
- There are `≥ cT·log T` such zeros
- Product: `≥ c·log T / 2 → ∞`

This gives:
```
∑ Re(I/ρ) ≥ N(T) · 1/(2T) ≥ (T·log T)/(3π) · 1/(2T) = log T / (6π)
```

Since `log T → ∞`, for any `B` we can find `T` with `log T > 6πB`.

## Lean-Specific Gotchas

1. **`Finset.filter` decidability:** `(fun ρ => 0 < ρ.im)` needs a `DecidablePred` instance. On `Finset ℂ`, this should work via `Classical.dec`.

2. **`Complex.div_re`:** This is the key lemma for computing the real part of a quotient:
   ```
   Complex.div_re : (z / w).re = z.re * w.re / (w.re^2 + w.im^2) + z.im * w.im / (w.re^2 + w.im^2)
   ```
   Alternatively, multiply numerator and denominator by conjugate and use `Complex.mul_conj`.

3. **`relaxedAutoImplicit false`:** All variables must be explicitly typed.

4. **Sum lower bounds:** `Finset.sum_le_sum` gives pointwise bounds:
   ```lean
   Finset.sum_le_sum (fun ρ hρ => h_lb ρ hρ)  -- ∑ f ≤ ∑ g from f ≤ g pointwise
   ```
   For lower bounds, use `Finset.le_sum_of_subset` or flip the inequality.

5. **`Finset.card_filter_le_iff`:** Useful for relating cardinality to sums.

6. **`Complex.normSq_mk`:** `normSq (a + bi) = a² + b²` — needed to simplify denominator.

## Estimated Size

~200-300 lines:
- ~40 lines: infrastructure / helpers
- ~50 lines: `Re(I/(1/2+iγ))` explicit computation
- ~30 lines: lower bound `γ/(1/4+γ²) ≥ 1/(2T)` for `γ ≤ T`
- ~50 lines: connecting `card` of filtered finset to `N(T)` (may need sorry)
- ~50 lines: main divergence argument

## Acceptance Criteria

```bash
# Build just this file
lake build Littlewood.Aristotle.Standalone.ZeroSumDivergence

# Check sorry count — should have at most 1-2 (N(T) lower bound, card-N bridge)
lake build Littlewood.Aristotle.Standalone.ZeroSumDivergence 2>&1 | grep "sorry"

# Verify the theorem exists
lake env lean --run -c 'import Littlewood.Aristotle.Standalone.ZeroSumDivergence; #check @Aristotle.Standalone.ZeroSumDivergence.posImZeroSum_re_I_div_diverges'
```

The downstream consumer is `PsiZeroSumOscillationFromIngham.lean` (line 122-141), which needs this divergence to choose `T₀` with an arbitrarily large sum (Step 1 of the Ingham argument).

**Ideal outcome:** 0 sorry. **Acceptable outcome:** ≤ 2 sorry (the N(T) lower bound and/or the card-N bridge), with the main divergence logic fully proved.

## References

- Backlund, R. (1918). "Über die Nullstellen der Riemannschen Zetafunktion"
- Titchmarsh, E. C. (1986). *The Theory of the Riemann Zeta-Function*, §9.4
- Montgomery & Vaughan (2007). *Multiplicative Number Theory I*, §14.1
