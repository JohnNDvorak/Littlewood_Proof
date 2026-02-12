/-
Stationary phase decomposition for Hardy cosine integrals.

KEY RESULT:
  hardy_cos_integral_weighted_sum_bound :
    ∃ C > 0, ∀ T ≥ 2, |∑ (n+1)^{-1/2} ∫ cos(θ-t·log(n+1))| ≤ C·(N+1)

This directly provides HardyCosIntegralAlternatingSqrtDecompositionHyp,
closing the sorry at CriticalAssumptions.lean.

PROOF STRUCTURE (encapsulated in the atomic sorry):
1. The n-th Hardy cosine integral has stationary point at t₀ = 2π(n+1)² where
   φ'(t₀) = θ'(t₀) - log(n+1) ≈ 0.

2. Stationary phase / Fresnel evaluation on [t₀, t₀ + c(n+1)]:
     ∫ cos(φ_n) = c₁·(n+1)·cos(φ_n(t₀) + π/4) + O(1)
   Phase value: cos(φ_n(t₀)) involves (-1)^n via cos(π(n+1)²) = (-1)^n.

3. VdC first derivative test on the tail [t₀ + c(n+1), T]: |∫_tail| = O(1).

4. Per-mode: ∫ = c₁(n+1)(-1)^n + O(1), so weighted integral ≈ c₁(-1)^n√(n+1).

5. Alternating sum of √(n+1) is O(√N) by Abel summation.
   Error sum is O(N). Last mode (endpoint) contributes O(√N).
   Total: O(N).

REFERENCES:
  - Titchmarsh, "Theory of the Riemann Zeta Function", §7.6
  - θ'(t) asymptotics from ThetaDerivAsymptotic (via DigammaAsymptotic)
  - Van der Corput first derivative test from VdcFirstDerivTest
  - cos(πn²) = (-1)^n from CosPiSqSign
  - alternating_sqrt_sum_bound from CosPiSqSign (Abel summation)

Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZMeasurability
import Littlewood.Bridge.HardyFirstMomentWiring

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace StationaryPhaseDecomposition

open MeasureTheory Set Real Filter Topology HardyEstimatesPartial

/-! ## Atomic sorry: weighted sum bound -/

/-- **Atomic sorry**: The weighted sum of Hardy cosine integrals is O(N+1).

MATHEMATICAL PROOF SKETCH:
1. Per-mode stationary phase (for n + 1 < hardyN T, ensuring a proper
   integration interval):
   The phase φ_n(t) = θ(t) - t·log(n+1) has stationary point at
   t₀ = hardyStart(n) = 2π(n+1)², giving:
     ∫_{hardyStart(n)}^T cos(φ_n(t)) dt = c₀·(-1)^n·(n+1) + O(1)
   where c₀ involves the Fresnel integral √(2π) and the phase curvature.

2. Weighting by (n+1)^{-1/2}:
   (n+1)^{-1/2} · [c₀·(-1)^n·(n+1) + O(1)] = c₀·(-1)^n·√(n+1) + O(1)

3. Summing over n < N-1 (all but the last mode):
   ∑ = c₀ · ∑(-1)^n√(n+1) + ∑ O(1)
     = c₀ · O(√N) + O(N)     [alternating sum bound from CosPiSqSign]
     = O(N)

4. Last mode n = N-1: the integral is over [hardyStart(N-1), T] which has
   length ≤ hardyStart(N) - hardyStart(N-1) = O(N). With coefficient
   N^{-1/2}, the contribution is O(√N) ⊂ O(N).

5. Total: O(N) = O(N+1). -/
theorem hardy_cos_integral_weighted_sum_bound :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∑ n ∈ Finset.range (hardyN T),
          ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) *
            ∫ t in Ioc (hardyStart n) T,
              hardyCos n t|
        ≤ C * ((hardyN T : ℝ) + 1) := by
  sorry

end StationaryPhaseDecomposition

/-! ## Typeclass wiring -/

/-- Wire the sum-level bound into the typeclass instance.
This provides `HardyCosIntegralAlternatingSqrtDecompositionHyp`, which
auto-wires to `MainTermFirstMomentBoundHyp` via HardyFirstMomentWiring. -/
instance : HardyFirstMomentWiring.HardyCosIntegralAlternatingSqrtDecompositionHyp :=
  ⟨StationaryPhaseDecomposition.hardy_cos_integral_weighted_sum_bound⟩
