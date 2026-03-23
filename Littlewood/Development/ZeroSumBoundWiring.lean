/-
Zero Sum Bound Wiring: HadamardXiCore + RvM → ShiftedRemainderSegmentBoundLargeTHyp

## Architecture

This file wires the Hadamard factorization (HadamardXiCore) and the Riemann–von
Mangoldt multiplicity formula through the existing class hierarchy to produce an
instance of `ShiftedRemainderSegmentBoundLargeTHyp`.

### Chain:
1. HadamardXiResidualStripBoundHyp (zero sum bound, assumed as typeclass)
2. → zeta_logderiv_zero_avoiding_bound (from ZetaLogDerivBound.lean)
3. → zeta_logderiv_pointwise_bound (absorb into C·(log|t|)², from PerronContourShift)
4. → ZetaLogDerivPointwiseLargeTHyp (handle zeros via Lean div-by-zero)
5. → ShiftedRemainderSegmentBoundFromLogDerivLargeTHyp.bound (Perron closure)
6. → ShiftedRemainderSegmentBoundLargeTHyp

### Zero sum bound
The Hadamard zero sum bound ‖B + Σ(1/(s-ρ)+1/ρ)‖ ≤ C·(log|t|)²
is assumed via the typeclass `HadamardXiResidualStripBoundHyp`. Formally,
the bound requires s to be bounded away from zeros of ξ (the condition
∀ n, s ≠ zeros n). On contours chosen to avoid zero ordinates (standard in
the Perron formula approach), this bound follows from partial summation
with the RvM formula N(T) = (T/2π)log(T/2π) + O(log T) and the gap
between consecutive zeros being ≥ c/log T.

## References

- Titchmarsh, "Theory of the Riemann Zeta Function", §§3.20, 9.6
- Davenport, "Multiplicative Number Theory", Chapter 12
-/

import Mathlib
import Littlewood.Development.ZetaLogDerivBound
import Littlewood.Development.ShiftedRemainderInterface

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Littlewood.Development.ZeroSumBoundWiring

open Complex Real Set MeasureTheory Topology Filter HadamardXi

/-! ## Part 1: Unconditional ZetaLogDerivPointwiseLargeTHyp from HadamardXiCore

Given:
  - HadamardXiCore: partial fraction for ξ
  - HadamardXiResidualStripBoundHyp: zero sum bound (on-contour)
  - zeros_are_zeta_zeros: the zeros in the enumeration are ζ-zeros

We derive the unconditional pointwise -ζ'/ζ bound:
  ‖-ζ'/ζ(σ+it)‖ ≤ C · (log|t|)²
for ALL s in the strip, including at ζ-zeros (where LHS = 0 by Lean convention). -/

/-- **Unconditional pointwise -ζ'/ζ bound** from the Hadamard chain.

    The three cases:
    1. ζ(s) = 0: the quotient is 0 in Lean, bound holds trivially
    2. ζ(s) ≠ 0 and s ≠ zeros n: use the zero-avoiding bound
    3. ζ(s) ≠ 0 and s = zeros n: contradicts zeros being ζ-zeros -/
theorem zeta_logderiv_pointwise_from_hadamard
    [h : HadamardXiCore]
    [ZetaLogDerivBound.HadamardXiResidualStripBoundHyp]
    (hzeros_zeta : ∀ n, riemannZeta (h.zeros n) = 0) :
    ShiftedRemainderInterface.ZetaLogDerivPointwiseLargeTHyp := by
  -- Extract zero-avoiding bound with A0+A1·log+A2·log² shape
  obtain ⟨A0, A1, A2, hA0, hA1, hA2, hza⟩ :=
    ZetaLogDerivBound.zeta_logderiv_zero_avoiding_bound (h := h)
  -- Absorb into C·(log|t|)² using the algebraic reduction
  exact PerronContourShift.zeta_logderiv_pointwise_bound A0 A1 A2 hA0 hA1 hA2
    (fun σ t hσlo hσhi ht => by
      by_cases hzeta : riemannZeta (↑σ + ↑t * I) = 0
      · -- Case 1: ζ(s) = 0 → -ζ'/ζ = 0 → bound holds
        have hq : -deriv riemannZeta (↑σ + ↑t * I) / riemannZeta (↑σ + ↑t * I) = 0 := by
          simp [hzeta]
        simp only [hq, norm_zero]
        have hlog_pos : 0 < Real.log |t| := Real.log_pos (by linarith)
        have h1 : 0 ≤ A0 := hA0
        have h2 : 0 ≤ A1 * Real.log |t| := by positivity
        have h3 : 0 ≤ A2 * (Real.log |t|) ^ 2 := by positivity
        linarith
      · -- ζ(s) ≠ 0
        by_cases hall : ∀ n, (↑σ + ↑t * I : ℂ) ≠ h.zeros n
        · -- Case 2: s ≠ zeros n → use zero-avoiding bound
          exact hza σ t hσlo hσhi ht hzeta hall
        · -- Case 3: ∃ n, s = zeros n, but ζ(s) ≠ 0 — contradiction
          push_neg at hall
          obtain ⟨n, hn⟩ := hall
          exact absurd (hn ▸ hzeros_zeta n) hzeta)

/-! ## Part 2: ShiftedRemainderSegmentBoundLargeTHyp wiring

With the unconditional pointwise bound in hand, the segment-form bound
follows from the Perron/contour closure class. -/

/-- **ShiftedRemainderSegmentBoundLargeTHyp** from the full Hadamard + RvM chain.

    Typeclass assumptions encode the analytic inputs:
    - `HadamardXiCore`: Hadamard partial fraction for ξ
    - `HadamardXiResidualStripBoundHyp`: zero sum bound on contours
    - `ShiftedRemainderSegmentBoundFromLogDerivLargeTHyp`: Perron/contour closure

    The explicit hypothesis `hzeros_zeta` links the abstract zero enumeration
    to actual ζ-zeros, bridging the Hadamard world to the ζ world. -/
theorem segment_bound_from_hadamard_chain
    [h : HadamardXiCore]
    [ZetaLogDerivBound.HadamardXiResidualStripBoundHyp]
    [ShiftedRemainderInterface.ShiftedRemainderSegmentBoundFromLogDerivLargeTHyp]
    (hzeros_zeta : ∀ n, riemannZeta (h.zeros n) = 0) :
    ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |ShiftedRemainderInterface.shiftedRemainderRe x T| ≤
        P * (Real.sqrt x * (Real.log T) ^ 3 / T) +
        2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T) :=
  ShiftedRemainderInterface.ShiftedRemainderSegmentBoundFromLogDerivLargeTHyp.bound
    (zeta_logderiv_pointwise_from_hadamard hzeros_zeta)

/-- The full chain exported as a downstream-facing theorem: the standard
    large-`T` contour bound follows once all three analytic inputs are
    available. -/
theorem contour_bound_from_hadamard_chain
    [h : HadamardXiCore]
    [ZetaLogDerivBound.HadamardXiResidualStripBoundHyp]
    [ShiftedRemainderInterface.ShiftedRemainderSegmentBoundFromLogDerivLargeTHyp]
    (hzeros_zeta : ∀ n, riemannZeta (h.zeros n) = 0) :
    ∃ A > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |ShiftedRemainderInterface.shiftedRemainderRe x T| ≤
        A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
  obtain ⟨P, hP, hseg⟩ := segment_bound_from_hadamard_chain hzeros_zeta
  exact PerronContourShift.contour_bound_from_pointwise
    ShiftedRemainderInterface.shiftedRemainderRe P hP hseg

end Littlewood.Development.ZeroSumBoundWiring
