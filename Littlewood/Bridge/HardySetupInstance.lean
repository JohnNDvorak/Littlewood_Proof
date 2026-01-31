/-
HardySetup instance: Connect existing sorry-free Hardy infrastructure
to the HardySetup class in HardyInfiniteZeros.lean.

STATUS: 6/9 fields proved from existing infrastructure, 3 need Aristotle.
-/

import Mathlib
import Littlewood.Aristotle.HardyInfiniteZeros
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZRealV2
import Littlewood.Bridge.HardyZTransfer
import Littlewood.Aristotle.HardyZCauchySchwarz

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace HardySetupInstance

open Complex Real Set Filter Topology MeasureTheory

/-! ## Transfer lemmas -/

/-- hardyZ is continuous (transfer from continuous_hardyZV2). -/
theorem hardyZ_continuous : Continuous HardyEstimatesPartial.hardyZ := by
  have h_eq : HardyEstimatesPartial.hardyZ = fun t => (hardyZV2 t).re :=
    funext HardyZTransfer.hardyZ_eq_hardyZV2_re
  rw [h_eq]
  exact Complex.continuous_re.comp continuous_hardyZV2

/-- hardyZ t = 0 ↔ ζ(1/2 + it) = 0. -/
theorem hardyZ_zero_iff (t : ℝ) :
    HardyEstimatesPartial.hardyZ t = 0 ↔ riemannZeta (1/2 + Complex.I * t) = 0 := by
  rw [HardyZTransfer.hardyZ_eq_hardyZV2_re]
  constructor
  · intro h_re
    have h_im := hardyZV2_real t
    exact (hardyZV2_zero_iff_zeta_zero t).mp (Complex.ext h_re h_im)
  · intro h
    rw [(hardyZV2_zero_iff_zeta_zero t).mpr h, Complex.zero_re]

/-- ‖hardyZ t‖ = ‖ζ(1/2 + it)‖. -/
theorem hardyZ_norm_eq (t : ℝ) :
    ‖HardyEstimatesPartial.hardyZ t‖ = ‖riemannZeta (1/2 + Complex.I * t)‖ := by
  rw [HardyZTransfer.hardyZ_eq_hardyZV2_re]
  -- Since hardyZV2 t is real (im = 0), ‖Re(z)‖ = ‖z‖
  have him := hardyZV2_real t
  have h_norm : ‖(hardyZV2 t).re‖ = ‖hardyZV2 t‖ := by
    conv_rhs => rw [show hardyZV2 t = ((hardyZV2 t).re : ℂ) from
      Complex.ext rfl (by simp [him])]
    exact (Complex.norm_real _).symm
  rw [h_norm]
  exact hardyZV2_abs_eq_zeta_abs t

/-! ## The instance -/

noncomputable instance : HardyInfiniteZeros.HardySetup where
  hardyZV2 := HardyEstimatesPartial.hardyZ
  continuous_hardyZV2 := hardyZ_continuous
  hardyZV2_zero_iff := hardyZ_zero_iff
  norm_hardyZV2_eq_norm_zeta := hardyZ_norm_eq
  Z_integral_cauchy_schwarz := fun a b hab => by
    rcases eq_or_lt_of_le hab with rfl | hab'
    · simp
    · -- Convert interval integrals to set integrals on Ioc
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
      exact HardyEstimatesPartial.integral_cauchy_schwarz _ a b hab'
        (hardyZ_continuous.continuousOn.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self)
        ((hardyZ_continuous.pow 2).continuousOn.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self)
  hardyZ_integrable := fun a b => hardyZ_continuous.intervalIntegrable a b
  mean_square_lower_bound := by sorry  -- NEEDS ARISTOTLE: approx functional equation
  first_moment_upper_bound := by sorry  -- NEEDS ARISTOTLE: convexity bound
  l1_lower_bound := by sorry  -- NEEDS ARISTOTLE: see L1LowerBound.lean for mock proof technique

end HardySetupInstance
