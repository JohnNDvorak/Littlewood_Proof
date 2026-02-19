import Mathlib
import Littlewood.Aristotle.ZetaMeanSquare
import Littlewood.Aristotle.HardyApproxFunctionalEq
import Littlewood.Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerBridge

open Complex Real Set Filter Topology MeasureTheory Asymptotics

private lemma hardyZ_eq_decomp (t : ℝ) :
    HardyApproxFunctional.hardyZ t =
      Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp.hardyZ t := by
  unfold HardyApproxFunctional.hardyZ
  unfold Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp.hardyZ
  congr 1
  ring

/-- Exact target-shape Hardy mean-square lower bound for
`HardyApproxFunctional.hardyZ`, derived from the standalone decomposition theorem.

This is import-ready for replacing the `zeta_critical_mean_value_lower` atom once
`ZetaMeanSquareHalfBound` is supplied. -/
theorem zeta_critical_mean_value_lower_target
    [ZetaMeanSquareHalfBound] :
    ∃ c > 0, ∃ T₁ ≥ (2 : ℝ), ∀ T : ℝ, T ≥ T₁ →
      ∫ t in Set.Ioc 1 T, (HardyApproxFunctional.hardyZ t)^2 ≥ c * T * Real.log T := by
  rcases Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp.zeta_critical_mean_value_lower with
    ⟨c, hc, T₁, hT₁, hmain⟩
  refine ⟨c, hc, T₁, hT₁, ?_⟩
  intro T hT
  have hmain' := hmain T hT
  calc
    ∫ t in Set.Ioc 1 T, (HardyApproxFunctional.hardyZ t)^2
        = ∫ t in Set.Ioc 1 T,
            (Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp.hardyZ t)^2 := by
              refine setIntegral_congr_fun measurableSet_Ioc ?_
              intro t ht
              simp [hardyZ_eq_decomp t]
    _ ≥ c * T * Real.log T := hmain'

end Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerBridge

namespace HardyApproxFunctional

open Complex Real Set Filter Topology MeasureTheory Asymptotics

/-- Exact target-shape lower bound from an explicit critical-line second-moment
asymptotic input. This is the non-typeclass version for direct wiring. -/
theorem zeta_critical_mean_value_lower_from_half_asymptotic
    (h_asymp :
      (fun T : ℝ => mean_square_zeta (1 / 2) T - T * Real.log T)
        =O[atTop] (fun T : ℝ => T)) :
    ∃ c > 0, ∃ T₁ ≥ (2 : ℝ), ∀ T : ℝ, T ≥ T₁ →
      ∫ t in Set.Ioc 1 T, (HardyApproxFunctional.hardyZ t)^2 ≥ c * T * Real.log T := by
  let htarget :
      ∃ c > 0, ∃ T₁ ≥ (2 : ℝ), ∀ T : ℝ, T ≥ T₁ →
        ∫ t in Set.Ioc 1 T, (HardyApproxFunctional.hardyZ t)^2 ≥ c * T * Real.log T :=
    by
      rcases
          Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp.zeta_critical_mean_value_lower_of_asymptotic
            h_asymp with ⟨c, hc, T₁, hT₁, hmain⟩
      refine ⟨c, hc, T₁, hT₁, ?_⟩
      intro T hT
      have hmain' := hmain T hT
      calc
        ∫ t in Set.Ioc 1 T, (HardyApproxFunctional.hardyZ t)^2
            = ∫ t in Set.Ioc 1 T,
                (Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerDecomp.hardyZ t)^2 := by
                  refine setIntegral_congr_fun measurableSet_Ioc ?_
                  intro t ht
                  simp [Aristotle.Standalone.HardyApproxFunctionalEqMeanValueLowerBridge.hardyZ_eq_decomp t]
        _ ≥ c * T * Real.log T := hmain'
  exact htarget

/-- Typeclass-instantiated alias of
`zeta_critical_mean_value_lower_from_half_asymptotic`. -/
theorem zeta_critical_mean_value_lower_from_half_bound
    [ZetaMeanSquareHalfBound] :
    ∃ c > 0, ∃ T₁ ≥ (2 : ℝ), ∀ T : ℝ, T ≥ T₁ →
      ∫ t in Set.Ioc 1 T, (HardyApproxFunctional.hardyZ t)^2 ≥ c * T * Real.log T := by
  exact zeta_critical_mean_value_lower_from_half_asymptotic mean_square_zeta_half_asymp

end HardyApproxFunctional
