/-
Bridge file: Type conversion between hardyZ : ℝ → ℝ and hardyZV2 : ℝ → ℂ.

The project has two Hardy theta definitions:
- HardyEstimatesPartial.hardyTheta: uses (Complex.log ...).im
- hardyThetaV2: uses Complex.arg

These are equal because Complex.log_im gives (Complex.log z).im = Complex.arg z
for z ≠ 0.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyZRealV2

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Complex Real Set Filter MeasureTheory
open scoped Topology

namespace HardyZTransfer

/-- The Gamma arguments in the two theta definitions are equal. -/
private lemma gamma_arg_eq (t : ℝ) :
    (1 : ℂ) / 4 + Complex.I * (↑t / 2) = 1 / 4 + Complex.I * ↑t / 2 := by ring

/-- The two theta definitions agree: (Complex.log z).im = Complex.arg z for z ≠ 0. -/
theorem hardyTheta_eq_thetaV2 (t : ℝ) :
    HardyEstimatesPartial.hardyTheta t = hardyThetaV2 t := by
  unfold HardyEstimatesPartial.hardyTheta hardyThetaV2
  rw [gamma_arg_eq]
  simp [Complex.log_im]

/-- The real-valued hardyZ equals the real part of hardyZV2. -/
theorem hardyZ_eq_hardyZV2_re (t : ℝ) :
    HardyEstimatesPartial.hardyZ t = (hardyZV2 t).re := by
  simp only [HardyEstimatesPartial.hardyZ, hardyZV2, hardyTheta_eq_thetaV2]

/-- Transfer of hardyZ_abs_le to hardyZV2 types. -/
theorem hardyZ_abs_le_zeta_V2 (t : ℝ) :
    |(hardyZV2 t).re| ≤ ‖riemannZeta (1/2 + I * t)‖ := by
  rw [← hardyZ_eq_hardyZV2_re]
  exact HardyEstimatesPartial.hardyZ_abs_le t

/-- Transfer of conditional first moment to hardyZV2 types. -/
theorem first_moment_conditional_V2 (ε : ℝ) (hε : ε > 0)
    (h_integrable_main : ∀ T ≥ 1, IntegrableOn HardyEstimatesPartial.MainTerm (Ioc 1 T))
    (h_integrable_error : ∀ T ≥ 1, IntegrableOn HardyEstimatesPartial.ErrorTerm (Ioc 1 T))
    (h_main_bound : ∃ C₁ > 0, ∀ T ≥ 2,
      |∫ t in Ioc 1 T, HardyEstimatesPartial.MainTerm t| ≤ C₁ * T^(1/2 + ε))
    (h_error_bound : ∃ C₂ > 0, ∀ T ≥ 2,
      |∫ t in Ioc 1 T, HardyEstimatesPartial.ErrorTerm t| ≤ C₂ * T^(1/2 + ε)) :
    ∃ C > 0, ∃ T₀ > 0, ∀ T ≥ T₀,
      |∫ t in Ioc 1 T, (hardyZV2 t).re| ≤ C * T^(1/2 + ε) := by
  have h := HardyEstimatesPartial.hardyZ_first_moment_bound_conditional ε hε
    h_integrable_main h_integrable_error h_main_bound h_error_bound
  obtain ⟨C, hC, T₀, hT₀, hbound⟩ := h
  refine ⟨C, hC, T₀, hT₀, fun T hT => ?_⟩
  have : ∫ t in Ioc 1 T, (hardyZV2 t).re = ∫ t in Ioc 1 T, HardyEstimatesPartial.hardyZ t := by
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      fun x _ => (hardyZ_eq_hardyZV2_re x).symm
  rw [this]
  exact hbound T hT

end HardyZTransfer
