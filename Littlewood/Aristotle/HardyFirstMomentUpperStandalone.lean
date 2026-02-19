import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.Standalone.RSFirstMomentQuarterFromCenteredBlocks
import Littlewood.Bridge.HardyFirstMomentWiring

/-
Standalone Hardy first-moment upper bound in the exact shape needed by
`HardyInfiniteZerosV2.HardySetupV2.first_moment_upper`.

This file is intentionally not imported by `Littlewood.lean`.
-/

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.HardyFirstMomentUpperStandalone

open Complex Real Set Filter Topology MeasureTheory
open HardyEstimatesPartial
open _root_.Aristotle.Standalone.RSFirstMomentQuarterFromCenteredBlocks

/-- Exact `HardySetupV2.first_moment_upper` signature for
`HardyEstimatesPartial.hardyZ`. -/
theorem hardy_first_moment_upper_for_setup_v2 :
    [HardyFirstMomentUpperHyp] →
    ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ ∃ T₀ : ℝ, T₀ ≥ 2 ∧ ∀ T : ℝ, T ≥ T₀ →
      |∫ t in Ioc 1 T, HardyEstimatesPartial.hardyZ t| ≤ C * T ^ (1 / 2 + ε) := by
  intro _inst ε hε
  simpa using (HardyFirstMomentUpperHyp.bound ε hε)

/-- Construct the exact `HardySetupV2.first_moment_upper` statement from:
1) the main-term first-moment hypothesis, and
2) centered-block control for the RS error term. -/
theorem hardy_first_moment_upper_for_setup_v2_from_centered_blocks
    [HardyFirstMomentWiring.MainTermFirstMomentBoundHyp]
    {A R : ℝ} (hA : 0 < A)
    (hcenter :
      ∀ T : ℝ, T ≥ 2 * Real.pi →
        |∑ k ∈ Finset.range (HardyEstimatesPartial.hardyN T),
          ((∫ t in Ioc (min T (HardyEstimatesPartial.hardyStart k))
                (min T (HardyEstimatesPartial.hardyStart (k + 1))),
              HardyEstimatesPartial.ErrorTerm t)
            - ((-1 : ℝ) ^ k * A * Real.sqrt ((k : ℝ) + 1)))| ≤ R) :
    ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧ ∃ T₀ : ℝ, T₀ ≥ 2 ∧ ∀ T : ℝ, T ≥ T₀ →
      |∫ t in Ioc 1 T, HardyEstimatesPartial.hardyZ t| ≤ C * T ^ (1 / 2 + ε) := by
  let _inst : HardyFirstMomentUpperHyp :=
    hardyFirstMomentUpperHyp_from_mainTerm_and_centered_blocks hA hcenter
  simpa using hardy_first_moment_upper_for_setup_v2

end Aristotle.HardyFirstMomentUpperStandalone
