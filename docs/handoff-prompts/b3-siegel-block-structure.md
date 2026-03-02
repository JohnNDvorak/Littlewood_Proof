# Handoff Prompt: B3 Unified RS Block Analysis (1 Sorry)

## Overview

B3 (`RSCompleteBlockAsymptotic.lean`) has been consolidated from 3 sub-sorries into **1 unified atomic sorry** (`rs_block_analysis`). The assembly from the atom to `RSCompleteBlockWithResidualHyp` (all 3 clauses) is **fully proved**, using `alternating_antitone_sum_le_first` from `AbelSummation.lean` for the cumulative cancellation bound.

## Target File

```
Littlewood/Aristotle/Standalone/RSCompleteBlockAsymptotic.lean
```

## The Single Sorry

```lean
private theorem rs_block_analysis :
    ∃ (A : ℝ) (c : ℕ → ℝ) (C₂ : ℝ),
      A > 0 ∧
      (∀ k, 0 ≤ c k) ∧
      AntitoneOn c (Ici (1 : ℕ)) ∧
      (∀ k : ℕ,
        (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)), ErrorTerm t)
          = (-1 : ℝ) ^ k * (A * Real.sqrt ((k : ℝ) + 1) + c k)) ∧
      C₂ ≥ 0 ∧
      (∀ k : ℕ, ∀ T : ℝ, hardyStart k ≤ T → T ≤ hardyStart (k + 1) →
        ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
          |(∫ t in Ioc (hardyStart k) T, ErrorTerm t)
            - β * (∫ t in Ioc (hardyStart k) (hardyStart (k + 1)),
                     ErrorTerm t)| ≤ C₂) := by
  sorry
```

### What Must Be Proved (5 conjuncts)

1. **A > 0**: The Fresnel constant from the leading RS term. `A = ∫₀¹ Ψ(p) dp · (geometric factor)`.

2. **∀ k, 0 ≤ c k** (sign-definite corrections): Define `c(k) := (-1)^k · (∫_{block k} ErrorTerm) - A·√(k+1)`. The sign analysis shows `c(k) ≥ 0` because the `O(t^{-3/4})` remainder has the same sign as the leading term within each block (from the Ψ-function's constant-sign property on [0,1]).

3. **AntitoneOn c (Ici 1)** (corrections decay for k ≥ 1): The remainder `c(k) = O(k^{-1/2})` from the `O(t^{-3/4})` RS remainder integrated over block length `O(k)` at height `t ~ 2πk²`. The decay is strict for k ≥ 1; block k = 0 is excluded to avoid edge cases.

4. **Block integral equality**: `∫_{block k} ErrorTerm = (-1)^k (A √(k+1) + c_k)`. This is the core RS asymptotic: the integral splits into leading term `(-1)^k A √(k+1)` (Fresnel evaluation) plus correction `(-1)^k c_k` (from `O(t^{-3/4})` remainder). The equality is exact because `c_k` is defined as the difference.

5. **Partial-block interpolation**: For any sub-interval `(hardyStart k, T] ⊆ (hardyStart k, hardyStart(k+1)]`, the partial integral is β times the full integral (β ∈ [0,1]) with bounded error C₂. This follows from the Ψ-function having constant sign on [0,1], making the integrand monotone within each block.

### Why Equality (Not Bounds) for Conjunct 4

The exact equality is essential for the downstream proof. The assembly proves Clause 2 (cumulative cancellation) by extracting `e_k = (-1)^k c_k` and applying `alternating_antitone_sum_le_first`, which needs the errors to be EXACTLY `(-1)^k c_k`. An approximate version `|e_k - (-1)^k c_k| ≤ ε` would only give `O(N)` growth.

The equality is not restrictive: `c_k` is existentially quantified.

## Mathematical Content

### Leading Term (Fresnel Evaluation)

On block k, `ErrorTerm(t) = (-1)^{N-1} · Ψ(p(t)) · t^{-1/4} + O(t^{-3/4})` where:
- `Ψ` is the Riemann-Siegel Ψ-function (Siegel 1932 §3)
- `p(t) = √(t/2π) - N(t)` is the fractional part
- `N(t) = hardyN t = ⌊√(t/2π)⌋` is constant on block k (equals k+1, proved: `hardyN_constant_on_block`)

The leading integral evaluates via Fresnel:
```
∫_{block k} (-1)^k Ψ(p(t)) t^{-1/4} dt = (-1)^k · A · √(k+1)
```
where `A > 0` comes from the Fresnel constant.

### Correction Term (Sign + Decay)

`c(k) = (-1)^k · ∫_{block k} O(t^{-3/4}) dt`. On block k:
- Block length: `hardyStart(k+1) - hardyStart(k) = 2π(2k+3) = O(k)`
- Block height: `t ~ 2πk² = O(k²)`
- So `∫ O(t^{-3/4}) dt ~ O(k) · O(k^{-3/2}) = O(k^{-1/2})`

The sign `(-1)^k · ∫ R(t) dt ≥ 0` comes from the Ψ-function's constant-sign property on [0,1]:
within block k, the remainder inherits the same sign as the leading term.

AntitoneOn for k ≥ 1 follows from the `O(k^{-1/2})` decay being strict.

### Partial-Block Interpolation

Within block k, the integrand has constant sign (from Ψ monotonicity on [0,1]). So:
- `F(T) = ∫_{hardyStart k}^T ErrorTerm dt` is monotone in T
- `F(hardyStart k) = 0`, `F(hardyStart(k+1)) = I_full`
- Set `β = F(T) / I_full` (or 0 if `I_full = 0`). Then `0 ≤ β ≤ 1`.
- The error `C₂` absorbs the `O(t^{-3/4})` remainder contribution.

### References

- Siegel, "Über Riemanns Nachlaß zur analytischen Zahlentheorie" (1932), §3
- Titchmarsh, "The Theory of the Riemann Zeta-Function", §4.16-4.17
- Edwards, "Riemann's Zeta Function", §7.7

## Assembly (Fully Proved)

The theorem `rsCompleteBlockWithResidual_sorry` proves all 3 clauses of `RSCompleteBlockWithResidualHyp` from `rs_block_analysis`:

- **Clause 1** (per-block bound): `|e_k| = c_k ≤ max(c 0, c 1) ≤ B`
- **Clause 2** (cumulative cancellation): Split at k=0, apply `alternating_antitone_sum_le_first` to `fun j => c(j+1)`. Result: `|∑ e_k| ≤ c 0 + c 1 = R`.
- **Clause 3** (partial interpolation): Triangle inequality on `(∫_{partial} - β · ∫_{full}) + β · (-1)^k c_k`. Bounded by `C₂ + max(c 0, c 1) = B`.

The downstream wiring to `PerBlockSignedBoundHyp` (unchanged, fully proved) is also in this file.

## Available Infrastructure (proved, 0 sorry)

| Lemma | File | What it gives |
|---|---|---|
| `alternating_antitone_sum_le_first` | `AbelSummation.lean` | `\|∑_{k≤n} (-1)^k a_k\| ≤ a 0` for antitone nonneg `a` |
| `alternating_sum_le_last` | `AbelSummation.lean` | `\|∑_{k≤n} (-1)^k a_k\| ≤ a n` for monotone nonneg `a` |
| `hardyN_constant_on_block` | `HardyNProperties.lean` | `hardyN t = k+1` on block k |
| `errorTerm_integrable` | `HardyZFirstMoment.lean` | `ErrorTerm` is integrable on bounded intervals |
| `errorTerm_block_sum` | `RSBlockDecomposition.lean` | `∫₁ᵀ ErrorTerm = head + ∑ blocks + partial` |
| `cos_pi_mul_nat_sq` | `CosPiSqSign.lean` | `cos(πn²) = (-1)^n` |
| Fresnel integrals | `FresnelIntegrals.lean` | Gaussian / Fresnel integral evaluations |

## Common Pitfalls

1. **`0^(-1/2)` is undefined in Lean.** Use `1/√(k+1)` not `k^(-1/2)` for decay bounds.
2. **Block 0 edge case.** `AntitoneOn c (Ici 1)` deliberately excludes k = 0.
3. **`Set.Ioc` vs `Ioc`.** The codebase opens `MeasureTheory Set`, so write `Ioc`.
4. **Integral notation is greedy.** Parenthesize: `(∫ t in Ioc a b, f t) - c`.
5. **Division by zero in β construction.** When `I_full = 0`, set `β = 0` via `if/else` + `split_ifs`.
