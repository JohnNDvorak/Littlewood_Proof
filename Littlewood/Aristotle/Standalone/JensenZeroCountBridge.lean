/-
# Bridge from Jensen R·log R Zero Count to Direct Large-T Segment Bound

This file bridges the Jensen-based zero count to the direct segment bound
infrastructure. The key export is `xi_zero_count_R_logR`.

Note: The classical N(T+1) - N(T) = O(log T) follows from the Riemann-von
Mangoldt formula, not directly from Jensen. The Jensen bound gives global
growth; local density requires additional argument principle machinery.
-/
import Littlewood.Aristotle.Standalone.JensenZeroCountingOrderOne

set_option maxHeartbeats 200000

open Complex Real MeromorphicOn Aristotle.Standalone.XiGrowthBound

noncomputable section

namespace Aristotle.Standalone.JensenZeroCountBridge

/-- The Jensen R·log R zero count for RiemannXiAlt.
    This is non-circular: uses only Jensen formula + xi_growth_bound. -/
theorem xi_zero_count_R_logR :
    ∃ C' : ℝ, 0 < C' ∧ ∀ R : ℝ, 1 ≤ R →
      (zeroCount RiemannXiAlt R : ℝ) ≤ C' * R * Real.log (R + 1) :=
  _root_.xi_zero_count_R_logR

/-- Alias for use in partial summation: disk count bound. -/
theorem disk_zero_count_logR_bound :
    ∃ C' : ℝ, 0 < C' ∧ ∀ R : ℝ, 1 ≤ R →
      (zeroCount RiemannXiAlt R : ℝ) ≤ C' * R * Real.log (R + 1) :=
  xi_zero_count_R_logR

end Aristotle.Standalone.JensenZeroCountBridge
