# Handoff Prompt: AFE Mean Square Bridge (B1 Atomic Sorry)

## Task

Prove the approximate functional equation mean-square bridge in Lean 4 / Mathlib: the integral of `|ζ(1/2+it)|²` equals twice the integral of `|S_N(1/2+it)|²` plus `O(T)`, where `S_N` is the partial Dirichlet series with `N = ⌊√(t/2π)⌋` terms.

This is the **last remaining sorry** (Blocker B1) on the Hardy mean-square chain.

## Target File

**Replace the sorry** at line 205 of:
```
Littlewood/Aristotle/Standalone/HardyMeanSquareAsymptoticFromZetaMoment.lean
```

## Exact Signature (already in the file)

```lean
private theorem afe_mean_square_bridge :
    (fun T => (∫ t in (1:ℝ)..T, ‖riemannZeta (↑(1/2 : ℝ) + Complex.I * ↑t)‖^2) -
      2 * (∫ t in (1:ℝ)..T, Complex.normSq
        (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1/2 + Complex.I * t))))
    =O[atTop] (fun T => T)
```

## File Context

The file already has these imports:
```lean
import Littlewood.Aristotle.ZetaMeanSquare
import Littlewood.Aristotle.HardyMeanSquareAsymptoticLeaf
import Littlewood.Bridge.HardyZTransfer
import Littlewood.Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp
import Littlewood.Aristotle.MeanSquare

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section
namespace Aristotle.Standalone.HardyMeanSquareAsymptoticFromZetaMoment
open Filter Asymptotics MeasureTheory Set Real
```

## What This Theorem Says (in plain math)

```
∫₁ᵀ |ζ(1/2+it)|² dt = 2 · ∫₁ᵀ |S_N(t)(1/2+it)|² dt + O(T)
```

where `S_N(t)(s) = ∑_{n=1}^{N(t)} n^{-s}` with `N(t) = ⌊√(t/(2π))⌋`, implemented as `partialZeta`.

## Available Infrastructure (all proved, 0 sorry)

### In the same file

**`partial_zeta_mean_square_half_coeff` (line 52):** The coefficient extraction — PROVED:
```lean
private lemma partial_zeta_mean_square_half_coeff :
    (fun T => (∫ t in (1:ℝ)..T,
        Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1/2 + Complex.I * t)))
      - 2⁻¹ * T * Real.log T)
    =O[atTop] (fun T => T)
```

**`integral_log_exact` (line 41):** `∫₁ᵀ log t = T·log T - T + 1`

### From imported files

- **`partialZeta`** — The partial Dirichlet series `∑_{n=1}^{⌊N⌋} n^{-s}`
- **`normSq_partialZeta_eq`** — Decomposition of `|S_N|²` into harmonic sum + off-diagonal
- **`harmonicSum`**, **`offDiagSsq`** — Components of the normSq decomposition
- **`norm_integral_offDiagSsq_le`** — Off-diagonal integral bounded by `8·N²`
- **`mean_square_zeta`** — The cumulative mean-square function `∫₀ᵀ |ζ(1/2+it)|² dt`

### From Mathlib

- `riemannZeta` — The Riemann zeta function
- `Complex.normSq` — `|z|² = z.re² + z.im²`
- `Asymptotics.IsBigO` — Big-O notation with filter
- `MeasureTheory.integral` — Bochner/Lebesgue integral
- `intervalIntegral` — `∫ t in a..b, f t`

## Mathematical Strategy (Titchmarsh §7.2, Ingham 1926)

### The Approximate Functional Equation on the Critical Line

On `Re(s) = 1/2`, the AFE gives:
```
ζ(s) = S_N(s) + χ(s) · S̄_N(1-s) + R(s)
```
where:
- `S_N(s) = ∑_{n≤N} n^{-s}` is the partial Dirichlet series
- `χ(s) = π^{s-1/2} · Γ((1-s)/2) / Γ(s/2)` is the chi function from the functional equation
- `|χ(1/2+it)| = 1` on the critical line
- `S̄_N(1-s) = conj(S_N(s))` when `s = 1/2+it` and `N = ⌊√(t/2π)⌋`
- `|R(t)| = O(t^{-1/4})` — the AFE remainder

### Expanding |ζ|²

```
|ζ(1/2+it)|² = |S_N + χ·S̄_N + R|²
             = |S_N|² + |χ·S̄_N|² + 2·Re(S_N · conj(χ·S̄_N)) + cross-terms with R
             = |S_N|² + |S_N|² + 2·Re(conj(χ)·S_N²) + O(|S_N|·|R|) + O(|R|²)
             = 2|S_N|² + 2·Re(conj(χ)·S_N²) + O(|S_N|·t^{-1/4} + t^{-1/2})
```

### Integrating

1. **Main term:** `∫₁ᵀ 2|S_N|²` — this is `2 · ∫₁ᵀ |S_N|²` (the RHS of our goal)

2. **Oscillatory term:** `∫₁ᵀ Re(conj(χ)·S_N²) = O(T)` by:
   - Cauchy-Schwarz: `|∫ Re(conj(χ)·S_N²)| ≤ ∫ |S_N|² = O(T·log T)`
   - Actually need: the oscillation of `χ(1/2+it) = exp(-2iϑ(t))` where `ϑ(t) = Im(log Γ(1/4+it/2)) - (t/2)·log π` causes cancellation
   - **Simpler bound:** `|∫ Re(conj(χ)·S_N²)| ≤ ∫ |S_N|² ≤ C·T·log T`, but this gives `O(T·log T)` not `O(T)`
   - **The key insight (Ingham 1926):** The oscillatory integral cancels to `O(T)` by the mean-value theorem for Dirichlet polynomials. Reference: Titchmarsh Theorem 7.2.

3. **Remainder terms:** `∫₁ᵀ |S_N|·t^{-1/4} ≤ (∫|S_N|²)^{1/2}·(∫ t^{-1/2})^{1/2} = O(√(T·log T)·√T) = O(T·√(log T)) = o(T·log T)`
   Actually: we need `O(T)`, and `∫ |S_N|·t^{-1/4} ≤ √(∫|S_N|²)·√(∫ t^{-1/2}) ≤ √(cT·log T)·√T = O(T·√(log T))` which is `o(T·log T)` but NOT `O(T)`.

### Recommended Lean Approach

Given the difficulty of formalizing the full AFE + oscillatory cancellation, **sorry the AFE decomposition as a local lemma** and prove the integration argument:

```lean
-- Sorry the pointwise AFE decomposition as a local hypothesis
have hAFE : ∃ C : ℝ, ∀ t : ℝ, t ≥ 2 →
    |‖riemannZeta (↑(1/2 : ℝ) + Complex.I * ↑t)‖^2 -
     2 * Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1/2 + Complex.I * t))| ≤
    C * (1 + Complex.normSq (partialZeta (Real.sqrt (t / (2 * Real.pi))) (1/2 + Complex.I * t)) ^ (1/2 : ℝ)) := by
  sorry
```

Then prove the integration: a pointwise bound `|f(t) - 2g(t)| ≤ C·(1 + √g(t))` integrated over `[1,T]` gives `|∫f - 2∫g| ≤ C·T + C·∫√g ≤ C·T + C·√T·√(∫g)` using Cauchy-Schwarz, and `∫g = O(T·log T)` gives `C·√(T²·log T) = O(T·√(log T)) = o(T·log T)` ... which is still not `O(T)`.

**Actually, the cleanest approach:** Sorry the entire oscillatory integral bound directly:

```lean
-- The AFE mean-value consequence: Ingham 1926, Titchmarsh §7.2
-- This encodes the full oscillatory cancellation argument
sorry
```

**If you want partial progress:** Factor the proof into:
1. A sorry'd local lemma stating the pointwise AFE remainder bound
2. Proved integration of the remainder bound using Cauchy-Schwarz + integrability
3. Proved assembly using triangle inequality

## Lean-Specific Gotchas

1. **Integral notation is GREEDY:** `∫ t in a..b, f t - g t` parses as `∫ t in a..b, (f t - g t)`. The statement carefully parenthesizes: `(∫ t in ...) - 2 * (∫ t in ...)` with the subtraction OUTSIDE both integrals.

2. **`integral_ofReal`** is `@[norm_cast]` not `@[simp]` — use `rw` not `simp`. Also doesn't match through set integral notation — use intermediate `have`.

3. **`Complex.normSq` vs `‖·‖^2`:** Equal via `Complex.normSq_eq_norm_sq` but Lean treats them as distinct terms. Be explicit about which one you use.

4. **`IsBigO` at `atTop`:** The goal type is `=O[atTop]`. Prove via `IsBigO.of_bound C (eventually_ge_atTop T₀ ▸ ...)` or `.of_bound`:
   ```lean
   refine .of_bound C ?_
   filter_upwards [eventually_ge_atTop T₀] with T hT
   ```

5. **`intervalIntegral.integral_add`:** For splitting `∫(f+g) = ∫f + ∫g`, both `f` and `g` must be `IntervalIntegrable`. The existing code at lines 117-119 demonstrates this pattern.

6. **Norm vs abs:** `‖(r : ℝ)‖ = |r|` is via `Real.norm_eq_abs`. Use `simp only [Real.norm_eq_abs]` to convert.

## Risk Assessment

This is the **hardest** of the three handoff tasks. The mathematical content requires:
- The approximate functional equation itself (a non-trivial identity)
- Oscillatory integral cancellation (Ingham's mean-value theorem)
- Integration of remainder terms via Cauchy-Schwarz

**Realistic expectations:**
- **Best case:** Full proof with 0 sorry (~400 lines, unlikely without AFE in Mathlib)
- **Good case:** 1 sorry for the pointwise AFE, integration argument proved (~200-300 lines)
- **Acceptable case:** Clean factoring into 2-3 atomic sorry lemmas with the assembly logic proved (~150 lines)

## Estimated Size

~300-400 lines total for a good-case result.

## Acceptance Criteria

```bash
# Build just this file
lake build Littlewood.Aristotle.Standalone.HardyMeanSquareAsymptoticFromZetaMoment

# Check sorry count — should be ≤ 2 (ideally 1)
lake build Littlewood.Aristotle.Standalone.HardyMeanSquareAsymptoticFromZetaMoment 2>&1 | grep "sorry"

# Full project build to verify no regressions
lake build 2>&1 | grep "declaration uses 'sorry'" | sort -u | wc -l
# Current baseline: 5 sorry warnings. Should remain ≤ 5 (ideally drop to 4).
```

**Key constraint:** The `afe_mean_square_bridge` theorem is `private`, so its proof is self-contained within the file. Downstream consumers (`zeta_mean_square_half`, `hardyMeanSquareAsymptoticHyp_proved`) are already proved and depend only on this theorem's *statement*, not its proof.

## References

- Ingham, A. E. (1926). "Mean-value theorems in the theory of the Riemann zeta-function." *Proc. London Math. Soc.* 27, 273-300.
- Titchmarsh, E. C. (1986). *The Theory of the Riemann Zeta-Function*, §7.2, Theorem 7.2.
- Siegel, C. L. (1932). "Über Riemanns Nachlaß zur analytischen Zahlentheorie." *Quellen Studien zur Geschichte der Math.* 2, 45-80.
- Ivić, A. (2003). *The Riemann Zeta-Function*, Ch. 4 (mean-value theorems).
