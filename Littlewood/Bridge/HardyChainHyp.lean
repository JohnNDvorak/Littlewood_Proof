/-
Hypothesis classes for the remaining Hardy chain fields.

These encode two classical results needed for Hardy's theorem:
1. Zeta convexity bound: |ζ(1/2+it)| ≤ C|t|^{1/4+ε}  (Phragmén-Lindelöf)
2. First moment upper bound: |∫₁ᵀ Z(t) dt| ≤ C·T^{1/2+ε}  (oscillatory cancellation)

When filled with genuine proofs, these discharge the last two sorry fields
in HardySetupV2Instance, completing the Hardy chain.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Complex Real Set Filter MeasureTheory

/-! ## Zeta Convexity Bound

The Phragmén-Lindelöf convexity principle gives:
  |ζ(1/2 + it)| ≤ C|t|^{1/4 + ε}
for any ε > 0.  The optimal exponent 1/4 comes from interpolating between
σ = 0 (exponent 1/2 from the functional equation) and σ = 1 (exponent 0).

Reference: Titchmarsh, Theory of the Riemann Zeta-Function, §5.1
-/

/-- The Phragmén-Lindelöf convexity bound on the critical line.
    |ζ(1/2 + it)| = O(|t|^{1/4 + ε}) for any ε > 0. -/
class ZetaCriticalLineBoundHyp : Prop where
  bound : ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ ∀ t : ℝ, |t| ≥ 2 →
    ‖riemannZeta (1/2 + I * t)‖ ≤ C * |t| ^ (1/4 + ε)

/-! ## Hardy Z First Moment Upper Bound

The first moment of Hardy's Z function satisfies:
  |∫₁ᵀ Z(t) dt| = O(T^{1/2 + ε})
for any ε > 0.  This follows from the approximate functional equation
  Z(t) ≈ 2 Σ_{n ≤ √(t/2π)} n^{-1/2} cos(θ(t) - t log n)
combined with oscillatory integral bounds on each term (van der Corput).

Reference: Titchmarsh, §7.6
-/

/-- The first moment of Hardy's Z function is O(T^{1/2+ε}). -/
class HardyFirstMomentUpperHyp : Prop where
  bound : ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ ∃ T₀ : ℝ, T₀ ≥ 2 ∧ ∀ T : ℝ, T ≥ T₀ →
    |∫ t in Ioc 1 T, HardyEstimatesPartial.hardyZ t| ≤ C * T ^ (1/2 + ε)
