/-
Direct derived instance for the Hardy first moment upper bound.

This file now has no direct `sorry`: it assembles
`HardyFirstMomentUpperHyp` from the two wiring hypotheses:
  - main-term oscillatory cancellation
  - error-term first-moment control

MATHEMATICAL CONTENT:
  ∫₁ᵀ Z(t) dt = O(T^{1/2+ε}) for every ε > 0.

PROOF SKETCH:
  Z(t) = MainTerm(t) + ErrorTerm(t), where:
  - MainTerm = 2·∑_{n<N(T)} (n+1)^{-1/2}·cos(θ(t)-t·log(n+1))
  - ErrorTerm = Z(t) - MainTerm(t)

  For the main term: stationary phase at t₀ = 2π(n+1)² gives
    ∫ cos(θ-t·log(n+1)) = (-1)^{n+1}·C·(n+1) + O(1)
  Weighting by (n+1)^{-1/2}: alternating sum of √(n+1), which is O(√N) = O(T^{1/4}).

  For the error term: Riemann-Siegel sign structure on breakpoint blocks gives
    ∫ ErrorTerm = ∑ (-1)^k · O(√k) + O(1), also O(T^{1/4}).

  Both are O(T^{1/4}) ≤ O(T^{1/2+ε}).

REFERENCES: Hardy-Littlewood (1918); Titchmarsh, §§4.16–4.17, §9.7.
-/

import Mathlib
import Littlewood.Bridge.HardyChainHyp
import Littlewood.Bridge.HardyFirstMomentWiring

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.HardyFirstMomentDirect

open MeasureTheory Set HardyEstimatesPartial

/-- Derived Hardy first-moment upper bound from the two wiring hypotheses:
main-term oscillatory cancellation and error-term first-moment control. -/
instance
    [HardyFirstMomentWiring.MainTermFirstMomentBoundHyp]
    [HardyFirstMomentWiring.ErrorTermFirstMomentBoundHyp] :
    HardyFirstMomentUpperHyp := by
  exact HardyFirstMomentWiring.hardyFirstMomentUpper_from_two_bounds

end Aristotle.HardyFirstMomentDirect
