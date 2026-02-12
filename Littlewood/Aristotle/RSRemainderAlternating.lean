/-
Riemann-Siegel remainder alternating-structure decomposition.

This module isolates the deep analytic input used by
`RiemannSiegelFirstMoment.lean`: the signed first-moment integral of the
Riemann-Siegel remainder can be decomposed into an alternating
`sqrt (k+1)` sum plus bounded error.

The decomposition is then consumed by
`RiemannSiegelSignCancellation.errorTerm_firstMoment_quarter_of_alternatingSqrt`
to deduce the `O(T^(1/4))` bound.

Co-authored-by: Codex (OpenAI)
-/

import Mathlib
import Littlewood.Aristotle.RSBreakpointDecomposition
import Littlewood.Aristotle.HardyZFirstMoment

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.RSRemainderAlternating

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

/-- **Atomic sorry**: Alternating-sqrt decomposition for the
Riemann-Siegel remainder first moment.

MATHEMATICAL CONTENT:
1. Split `∫_1^T ErrorTerm` at breakpoints `2π(k+1)^2` where
   `hardyN t = floor(sqrt(t/(2π)))` jumps.
2. On each interval, the leading RS remainder term carries sign `(-1)^k`.
3. Interval integrals have size `O(sqrt(k+1))`.
4. Summing gives:
   `|∫ ErrorTerm| ≤ A * |∑ (-1)^k sqrt(k+1)| + B` with `N+1 ≤ T^(1/2)`.

REFERENCES:
- Titchmarsh, *The Theory of the Riemann Zeta-Function*, §4.16
- Edwards, *Riemann's Zeta Function*, §7.7 -/
theorem errorTerm_alternatingSqrt_decomposition :
    ∃ A B : ℝ, A > 0 ∧ B ≥ 0 ∧
      ∀ T : ℝ, T ≥ 2 →
        ∃ N : ℕ,
          ((N : ℝ) + 1) ≤ T ^ (1 / 2 : ℝ) ∧
          |∫ t in Ioc 1 T, ErrorTerm t|
            ≤ A * |∑ k ∈ Finset.range (N + 1), (-1 : ℝ) ^ k * Real.sqrt ((k : ℝ) + 1)| + B := by
  exact Aristotle.RSBreakpointDecomposition.errorTerm_alternatingSqrt_decomposition

end Aristotle.RSRemainderAlternating
