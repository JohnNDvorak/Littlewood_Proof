# Aristotle Prompt: approx_functional_eq (Attempt 2)

## What to prove

Prove `approx_functional_eq` in Lean 4 with `import Mathlib`. This is the approximate functional equation integral bound for the Hardy Z-function.

## Exact statement needed

```lean
import Mathlib

noncomputable section

namespace HardyApproxFunctional

def hardyZ (t : ℝ) : ℝ := ‖riemannZeta (1 / 2 + t * Complex.I)‖

def partial_sum (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, (n + 1 : ℂ) ^ (-(1 / 2 : ℂ) - t * Complex.I)

def partial_sum_approx (t : ℝ) : ℂ :=
  partial_sum (Nat.floor (Real.sqrt (t / (2 * Real.pi)))) t

theorem approx_functional_eq :
    ∃ k > 0, ∃ C ≥ 0, ∃ T₁ ≥ 2, ∀ T : ℝ, T ≥ T₁ →
      ∫ t in Set.Ioc 1 T, (hardyZ t)^2 ≥
        (k * ∫ t in Set.Ioc 1 T, ‖partial_sum_approx t‖^2) - C * T := by
  sorry

end HardyApproxFunctional
```

## Critical details about the statement

1. **`hardyZ` is REAL-VALUED** — defined as `‖ζ(1/2+it)‖`. So `(hardyZ t)^2 = ‖ζ(1/2+it)‖²`.

2. **Integration is over `Set.Ioc 1 T`** (half-open interval (1,T]), NOT `Set.Icc`.

3. **The `- C * T` is OUTSIDE the integral** — it's subtracted from `k * ∫...`, not from each integrand value. The parentheses matter: `(k * ∫ ...) - C * T`.

4. **`partial_sum_approx t`** is the Dirichlet partial sum `S_N(t) = Σ_{n=1}^{N(t)} n^{-1/2-it}` where `N(t) = ⌊√(t/2π)⌋`. It returns `ℂ`, so `‖partial_sum_approx t‖^2` is its squared complex norm.

5. **Quantifier structure:** `∃ k > 0, ∃ C ≥ 0, ∃ T₁ ≥ 2, ∀ T ≥ T₁, ...` — note `C ≥ 0` (not `C > 0`) and explicit `T₁` (not `∀ᶠ`).

## Why the previous attempt failed

The previous proof (uuid 721a165a) used `k=1, C=1` and showed the RHS ≤ 0 by proving the subtracted integral is non-positive. This makes the bound trivially true (since `∫ ‖ζ‖² ≥ 0`) but completely vacuous — it says nothing about the relationship between the mean square and the partial sum. The bridge that consumes this theorem (`MeanSquareBridge.lean`) multiplies `k` by the partial-sum integral and needs `k > 0` to propagate the lower bound `∫ ‖S_N‖² = Θ(T log T)` into `∫ Z² ≥ c·T·log T`.

**Do NOT prove this by making the RHS trivially ≤ 0.** The constant `k` must be genuinely positive and must multiply a non-trivial lower bound on the partial-sum integral.

## Mathematical approach

The standard proof uses the approximate functional equation pointwise:

For `t ≥ t₀`, the Riemann-Siegel formula gives:
```
ζ(1/2 + it) = S_N(t) + χ(1/2+it) · conj(S_N(t)) + O(t^{-1/4})
```
where `χ(s) = π^{s-1/2} Γ((1-s)/2) / Γ(s/2)` satisfies `|χ(1/2+it)| = 1`.

Taking norms squared:
```
|ζ(1/2+it)|² = |S_N(t) + χ·conj(S_N)|² + O(t^{-1/4} · |S_N(t)|)
             ≥ |S_N(t)|² + ... cross terms ... - error
```

But a simpler approach suffices for the integral bound. Since `|χ| = 1` on the critical line:

**Step 1:** From the AFE, `|ζ(1/2+it)| ≥ |S_N(t)| - |S_N(t)| - |error| = |2·Re(...)| - error`. Actually, the cleanest route:

Since `ζ(1/2+it) = S_N(t) + χ·conj(S_N(t)) + R(t)` with `|R(t)| = O(t^{-1/4})`:
```
|ζ|² = |S_N + χ·conj(S_N) + R|²
     ≥ (|S_N + χ·conj(S_N)| - |R|)²
     ≥ |S_N + χ·conj(S_N)|² - 2|S_N + χ·conj(S_N)|·|R|
```

Now `|S_N + χ·conj(S_N)| ≤ 2|S_N|` and `|S_N + χ·conj(S_N)|² ≥ ... ` involves oscillatory cross terms. But for the integral, the key fact is:

**The diagonal terms give `∫ |S_N|²`** and the cross terms `∫ Re(χ·S_N²)` are bounded by O(T) (they oscillate and mostly cancel over [1,T]).

So: `∫₁ᵀ |ζ|² ≥ ∫₁ᵀ |S_N|² - O(T)`.

Take `k = 1` (or any positive constant ≤ 1) and `C` absorbing the oscillatory and error contributions.

**Step 2:** The error integral `∫₁ᵀ |R(t)|·|S_N(t)| dt` is `O(T)` because `|R| = O(t^{-1/4})` and `|S_N| = O(t^{1/4})` (the partial sum has `N ~ √(t/2π)` terms each of size `n^{-1/2}`, so `|S_N| ≤ 2√N ~ O(t^{1/4})`).

## Useful proved results available

The following are already proved (0 sorries) in the project:

1. **`∑_{n=1}^N n^{-1/2} ≤ 2√N`** — proved via induction in `HardyApproxFunctionalEqV2.lean`

2. **`‖S_N(t)‖ ≤ C_S · t^{1/4}`** — `hardySum_bound` in `HardyApproxFunctionalEqV2.lean`

3. **`‖ζ(1/2+it)‖ = hardyZ t`** — by definition (rfl)

4. **`|χ(1/2+it)| = 1`** — `norm_chi_critical_line` in `MeanSquare.lean`

## What NOT to do

- Do NOT use `maxHeartbeats 0`. Use `maxHeartbeats 1600000` (project standard).
- Do NOT define your own `hardyZ` or `partial_sum` — use the exact definitions above.
- Do NOT make the proof vacuous by showing RHS ≤ 0. The bridge needs `k` to carry a genuine lower bound.
- Do NOT change the quantifier structure or switch `Ioc` to `Icc`.
- Do NOT use `exact?` as a proof step — it may time out. Use explicit proof terms.

## Proof strategy recommendation

The simplest viable approach:

1. **Assume the pointwise AFE as an axiom** (via a hypothesis or an auxiliary axiom `sorry`), then derive the integral bound from it. This is acceptable — the project already has the pointwise AFE as an assumption in `HardyConjectureData`.

2. Alternatively, prove the bound `∫ |ζ|² ≥ ∫ |S_N|² - C·T` directly using:
   - The identity `|ζ|² ≥ |S_N|² - 2|S_N|·|R| + something` pointwise
   - Integration of the error: `∫ |S_N|·|R| ≤ ∫ O(t^{1/4})·O(t^{-1/4}) = O(T)`
   - This gives `k = 1, C = (some constant)`.

3. The measurability/integrability obligations will need:
   - `MeasureTheory.Integrable` for `t ↦ ‖ζ(1/2+it)‖²` on `Ioc 1 T`
   - `MeasureTheory.Integrable` for `t ↦ ‖S_N(t)‖²` on `Ioc 1 T`
   - These follow from continuity of `riemannZeta` (available in Mathlib) and finiteness of the partial sum.

## References

- Titchmarsh, "Theory of the Riemann Zeta-Function", Chapter 4 (approximate functional equation)
- Ivić, "The Riemann Zeta-Function", Chapter 4
- Montgomery-Vaughan, "Multiplicative Number Theory I", Chapter 5
