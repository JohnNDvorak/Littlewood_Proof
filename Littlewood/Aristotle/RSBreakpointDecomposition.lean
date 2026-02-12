/-
Riemann-Siegel breakpoint decomposition for the remainder first moment.

This module isolates the deep interval-splitting/sign-structure input used to
obtain the alternating-sqrt decomposition for the Riemann-Siegel remainder.

Co-authored-by: Codex (OpenAI)
-/

import Mathlib
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.RSBlockDecomposition

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.RSBreakpointDecomposition

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

/-- **Atomic sorry**: Breakpoint decomposition for `ErrorTerm`.

MATHEMATICAL CONTENT:
1. Split `∫_1^T ErrorTerm` at breakpoints `2π(k+1)^2` where `hardyN` jumps.
2. On each block, RS asymptotics provide alternating sign `(-1)^k` and
   block size `O(sqrt(k+1))`.
3. Summing block contributions yields the alternating-`sqrt` decomposition:
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
  exact Aristotle.RSBlockDecomposition.errorTerm_alternatingSqrt_decomposition_from_blocks

end Aristotle.RSBreakpointDecomposition
