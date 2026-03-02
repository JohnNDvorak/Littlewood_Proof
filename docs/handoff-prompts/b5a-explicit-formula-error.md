# Handoff Prompt: Truncated Explicit Formula Error (B5a Atomic Sorry)

## Task

Prove the truncated explicit formula error bound in Lean 4 / Mathlib:

$$|\psi(x) - x + \sum_{|\gamma| \le T} \operatorname{Re}(x^\rho/\rho)| \le C_2 \cdot \frac{\sqrt{x} \cdot (\log T)^2}{\sqrt{T}}$$

for all $x \ge 2$, $T \ge 2$. This is the **sole remaining sorry** (Blocker B5a) on the ψ explicit formula chain.

## Target File

**Replace the sorry** at line 112 of:
```
Littlewood/Aristotle/Standalone/ExplicitFormulaPsiSkeleton.lean
```

## Exact Signature (already in the file)

```lean
theorem shifted_contours_bound :
    ∃ C₂ > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |shiftedRemainderRe x T| ≤ C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T) := by
  sorry
```

where `shiftedRemainderRe` is defined concretely as:

```lean
def shiftedRemainderRe (x T : ℝ) : ℝ :=
  Aristotle.DirichletPhaseAlignment.chebyshevPsi x - x + zeroSumRe x T

def zeroSumRe (x T : ℝ) : ℝ :=
  (∑ ρ ∈ ZerosBelow T, ((x : ℂ) ^ ρ) / ρ).re
```

So the sorry asserts: `|chebyshevPsi x - x + ∑_{|γ|≤T} Re(x^ρ/ρ)| ≤ C₂ · (√x · (log T)² / √T)`

## Mathematical Content

This is the classical truncated explicit formula for ψ(x), proved via:

1. **Perron's formula**: ψ(x) = (1/2πi) ∫_{c-i∞}^{c+i∞} (-ζ'/ζ)(s) · x^s/s ds
   for c > 1, with truncation at height T giving error O(x·log²(xT)/T).
   Reference: Davenport Ch. 17, Theorem 17.1.

2. **Residue extraction**: Inside a rectangle with vertices c±iT and -U±iT,
   the integrand has poles at:
   - s = 1 (simple pole of ζ'/ζ, residue = x)
   - s = ρ with |Im(ρ)| ≤ T (zeros of ζ, residue = -x^ρ/ρ)
   - s = -2n (trivial zeros, contributions O(1))
   Reference: Davenport Ch. 17, equation (4).

3. **Contour bound**: The horizontal segments at Im(s) = ±T contribute
   O(x^c · log²T / T), and the shifted vertical at Re(s) = -U contributes O(x^{-U}).
   Taking c = 1 + 1/log x and letting U → ∞:
   |remainder| ≤ C · (√x · (log T)² / √T)
   Reference: Davenport Ch. 17, Lemma 17.2; Ingham 1932, Ch. IV.

## Available Infrastructure (DO use these)

### Proved (0 sorry) — horizontal segment bounds:
- `Littlewood/Aristotle/HorizontalSegmentBounds.lean`:
  `horizontal_segment_bound` — bounds ∫ x^s/s · (-ζ'/ζ) on horizontal segments
- `Littlewood/Aristotle/PerronContourIntegralsV2.lean`:
  `perron_horizontal_bound_pointwise` — pointwise Perron integral bound
  `integral_norm_bound_large_y` — tail integral bound

### Zeta function (Mathlib):
- `differentiableAt_riemannZeta (hs : s ≠ 1)` — ζ differentiable away from s=1
- `riemannZeta_ne_zero_of_one_le_re` — nonvanishing for Re(s) ≥ 1

### Definitions already in scope:
- `ZerosBelow T : Finset ℂ` — finite set of zeros with |Im(ρ)| ≤ T
- `chebyshevPsi x : ℝ` — Chebyshev ψ function (sum of von Mangoldt)

## What's Missing (you need to build or sorry-factor)

1. **Meromorphic residue theorem**: Cauchy's theorem for meromorphic functions
   inside a rectangle. Mathlib has `cauchy_goursat_rectangle` for holomorphic functions
   but not the residue-counting version. File `RectangleCauchy.lean` is a placeholder.

2. **Perron truncation error**: The error from truncating the Perron integral at height T.
   This is the difference between (1/2πi)∫_{c-iT}^{c+iT} and ψ(x).

3. **Zeta growth estimates**: |ζ'/ζ(σ+iT)| = O(log²T) for σ bounded below.
   Not proved in Mathlib or this project.

## Recommended Strategy

### Option A: Single atomic sorry (keep as-is)
The sorry is already well-localized and mathematically clear. Each component
(Perron formula, residue theorem, contour bounds) is a substantial formalization.

### Option B: Factor into 3 sub-sorry's
```lean
-- Sub-sorry 1: Perron truncation connects ψ to contour integral
private theorem perron_truncation_error :
    ∃ C > 0, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |chebyshevPsi x - perronIntegral x T| ≤ C * x * (Real.log x)^2 / T
  := sorry

-- Sub-sorry 2: Residue extraction for (-ζ'/ζ)(s)·x^s/s
private theorem residue_extraction :
    ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      perronIntegral x T = x - zeroSumRe x T + contourRemainder x T
  := sorry

-- Sub-sorry 3: Contour remainder bound (uses HorizontalSegmentBounds)
private theorem contour_remainder_bound :
    ∃ C > 0, ∀ x T : ℝ, x ≥ 2 → T ≥ 2 →
      |contourRemainder x T| ≤ C * (√x * (log T)^2 / √T)
  := sorry
```
Then wire via triangle inequality (similar to existing `explicitFormulaPsiGeneral_proved`).

### Option C: Direct proof (most ambitious)
Build the full Perron formula chain using existing `HorizontalSegmentBounds.lean`.
Estimated: 300-500 lines.

## Build Commands

```bash
lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiSkeleton
lake build Littlewood.Aristotle.Standalone.DeepBlockersResolved
lake build 2>&1 | grep "declaration uses 'sorry'" | sort -u
```

## File Context

```lean
import Littlewood.Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.Standalone.ExplicitFormulaPsiSkeleton

open Aristotle.DirichletPhaseAlignment (ZerosBelow)
open Aristotle.Standalone.ExplicitFormulaAndOscillationFromSubSorries
open ZetaZeros
```

## Constraints

- Do NOT modify files outside `ExplicitFormulaPsiSkeleton.lean`
- Do NOT add new imports unless absolutely necessary
- Do NOT touch the wiring block (`explicitFormulaPsiGeneral_proved`) — it's already proved
- The `shiftedRemainderRe` definition MUST stay as-is (concrete, not sorry)
- Build must pass: `lake build Littlewood.Aristotle.Standalone.ExplicitFormulaPsiSkeleton`

## References

- Davenport, H. (2000). *Multiplicative Number Theory*, 3rd ed., Chapter 17.
- Montgomery & Vaughan (2007). *Multiplicative Number Theory I*, §12.5.
- Ingham, A. E. (1932). *The Distribution of Prime Numbers*, Chapter IV.
- Titchmarsh, E. C. (1986). *The Theory of the Riemann Zeta-Function*, 2nd ed., §3.12.
