/-
  Segment bound for the shifted remainder: ShiftedRemainderSegmentBoundLargeTHyp

  This file completes the chain from the Hadamard product factorization of ξ(s)
  to the explicit-formula contour remainder bound. The three analytic inputs are:

  1. **HadamardXiCore** — the partial-fraction decomposition of ξ(s), proved in
     `HadamardFactorizationXi.lean`;
  2. **HadamardXiResidualStripBoundHyp** — the strip bound on the Hadamard
     remainder `B + Σ(1/(s−ρ) + 1/ρ)` away from zeros, encoding the zero-sum
     partial summation with the Riemann–von Mangoldt formula;
  3. **ShiftedRemainderSegmentBoundFromLogDerivLargeTHyp** — the Perron/contour
     closure that converts a pointwise −ζ'/ζ bound into the segment-form bound
     on the concrete shifted remainder.

  Given these three inputs plus the arithmetic bridge `hzeros_zeta` (which says
  the Hadamard zero enumeration lists genuine ζ-zeros), the wiring produces:

    −ζ'/ζ pointwise bound → segment bound → ShiftedRemainderSegmentBoundLargeTHyp

  ## References

  - Titchmarsh, "Theory of the Riemann Zeta Function", §§3.20, 9.6
  - Davenport, "Multiplicative Number Theory", Chapter 12
-/

import Littlewood.Development.ZeroSumBoundWiring

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Littlewood.Aristotle.Standalone.ZetaLogDerivBound

open Complex Real HadamardXi

/-! ## Instance: ShiftedRemainderSegmentBoundLargeTHyp from the full chain

The three analytic inputs are taken as typeclass assumptions. The arithmetic
bridge `hzeros_zeta` is derived from `HadamardXiCanonicalProductCriticalZeros`
when that stronger class is available, or can be supplied explicitly.
-/

/-- **ShiftedRemainderSegmentBoundLargeTHyp** — the full wiring from Hadamard
product to contour segment bound.

Given:
  - `HadamardXiCore` (Hadamard partial fraction for ξ),
  - `HadamardXiResidualStripBoundHyp` (zero-sum strip bound),
  - `ShiftedRemainderSegmentBoundFromLogDerivLargeTHyp` (Perron closure),
  - `hzeros_zeta` (the zeros are genuine ζ-zeros),

the instance follows by the chain:
  1. Extract the zero-avoiding −ζ'/ζ bound from the Hadamard remainder,
  2. Absorb pole + digamma background into C·(log|t|)²,
  3. Handle the ζ-zero singularity via Lean's div-by-zero convention,
  4. Apply the Perron contour closure to get the segment-form bound.
-/
theorem shiftedRemainderSegmentBound_of_hadamard
    [h : HadamardXiCore]
    [Development.ZetaLogDerivBound.HadamardXiResidualStripBoundHyp]
    [Development.ShiftedRemainderInterface.ShiftedRemainderSegmentBoundFromLogDerivLargeTHyp]
    (hzeros_zeta : ∀ n, riemannZeta (h.zeros n) = 0) :
    ∃ P > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |Development.ShiftedRemainderInterface.shiftedRemainderRe x T| ≤
        P * (Real.sqrt x * (Real.log T) ^ 3 / T) +
        2 * P * (Real.sqrt x * (Real.log T) ^ 2 / T) :=
  Development.ZeroSumBoundWiring.segment_bound_from_hadamard_chain hzeros_zeta

/-- Typeclass packaging the arithmetic bridge: every zero in the Hadamard
enumeration is a genuine ζ-zero. This allows the bridge to participate in
typeclass resolution. -/
class HadamardZerosAreZetaZerosHyp [h : HadamardXiCore] : Prop where
  /-- Every zero in the Hadamard enumeration is a genuine ζ-zero. -/
  zeros_zeta : ∀ n, riemannZeta (h.zeros n) = 0

/-- The instance of `ShiftedRemainderSegmentBoundLargeTHyp` from a bare
`HadamardXiCore` plus the three auxiliary inputs. This is the most general
form. -/
instance instFromCore
    [h : HadamardXiCore]
    [HadamardZerosAreZetaZerosHyp]
    [Development.ZetaLogDerivBound.HadamardXiResidualStripBoundHyp]
    [Development.ShiftedRemainderInterface.ShiftedRemainderSegmentBoundFromLogDerivLargeTHyp] :
    Development.ShiftedRemainderInterface.ShiftedRemainderSegmentBoundLargeTHyp where
  bound := shiftedRemainderSegmentBound_of_hadamard
    HadamardZerosAreZetaZerosHyp.zeros_zeta

/-- The `HadamardXiCanonicalProductCriticalZeros` class packages the arithmetic
bridge automatically, since `zeros_spec` provides `riemannZeta (zeros n) = 0`. -/
instance instFromCriticalZeros
    [h : HadamardXiCanonicalProductCriticalZeros]
    [Development.ZetaLogDerivBound.HadamardXiResidualStripBoundHyp]
    [Development.ShiftedRemainderInterface.ShiftedRemainderSegmentBoundFromLogDerivLargeTHyp] :
    Development.ShiftedRemainderInterface.ShiftedRemainderSegmentBoundLargeTHyp where
  bound := shiftedRemainderSegmentBound_of_hadamard
    (fun n => (h.zeros_spec n).1)

/-- The standard large-T contour bound as a corollary: once
`ShiftedRemainderSegmentBoundLargeTHyp` is available, the generic Perron
contour algebra normalizes the segment-form bound to the
`sqrt(x) · (log T)² / sqrt(T) + (log x)²` shape. -/
theorem contour_bound_from_hadamard
    [HadamardXiCore]
    [HadamardZerosAreZetaZerosHyp]
    [Development.ZetaLogDerivBound.HadamardXiResidualStripBoundHyp]
    [Development.ShiftedRemainderInterface.ShiftedRemainderSegmentBoundFromLogDerivLargeTHyp] :
    ∃ A > (0 : ℝ), ∀ x T : ℝ, x ≥ 2 → T ≥ 16 →
      |Development.ShiftedRemainderInterface.shiftedRemainderRe x T| ≤
        A * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) :=
  Development.ShiftedRemainderInterface.contour_bound_from_segment_hyp

end Littlewood.Aristotle.Standalone.ZetaLogDerivBound
