/-
Instance of HardySetupV2 from existing project infrastructure.

Fields:
1. Z := HardyEstimatesPartial.hardyZ           ✅ (from HardyEstimatesPartial)
2. Z_continuous                                  ✅ (from HardySetupInstance.hardyZ_continuous)
3. Z_zero_iff                                    ✅ (from HardySetupInstance.hardyZ_zero_iff)
4. mean_square_lower                             ✅ (from MeanSquareBridge.re_hardyZ_mean_square_lower)
5. first_moment_upper                            ✅ (from HardyFirstMomentUpperHyp)
6. Z_convexity_bound                             ✅ (from ZetaCriticalLineBoundHyp + hardyZ_abs_le)

All 6 fields proved (modulo hypothesis instances).
hardy_infinitely_many_zeros_v2 fires → HardyCriticalLineZerosHyp discharges.
-/

import Mathlib
import Littlewood.Aristotle.HardyInfiniteZerosV2
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZRealV2
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Bridge.HardyZTransfer
import Littlewood.Bridge.MeanSquareBridge
import Littlewood.Bridge.HardySetupInstance
import Littlewood.Bridge.HardyChainHyp

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace HardySetupV2Instance

open Complex Real Set Filter Topology MeasureTheory

-- Reuse transfer lemmas from HardySetupInstance
-- (hardyZ_continuous, hardyZ_zero_iff are proved there)

/-- The V2 instance with all 6 fields proved.
    Fields 1-4 are unconditionally proved.
    Fields 5-6 use hypothesis classes (ZetaCriticalLineBoundHyp, HardyFirstMomentUpperHyp)
    whose sorry instances are in Assumptions.lean. -/
noncomputable instance [ZetaCriticalLineBoundHyp] [HardyFirstMomentUpperHyp] :
    HardyInfiniteZerosV2.HardySetupV2 where
  Z := HardyEstimatesPartial.hardyZ
  Z_continuous := HardySetupInstance.hardyZ_continuous
  Z_zero_iff := HardySetupInstance.hardyZ_zero_iff
  mean_square_lower := by
    obtain ⟨c, hc, T₀, hT₀, h⟩ := MeanSquareBridge.re_hardyZ_mean_square_lower
    exact ⟨c, hc, T₀, hT₀, fun T hT => h T hT⟩
  first_moment_upper := by
    intro ε hε
    obtain ⟨C, hC, T₀, hT₀, hb⟩ := HardyFirstMomentUpperHyp.bound ε hε
    exact ⟨C, hC, T₀, hT₀, hb⟩
  Z_convexity_bound := by
    intro ε hε
    obtain ⟨C, hC, hb⟩ := ZetaCriticalLineBoundHyp.bound ε hε
    exact ⟨C, hC, fun t ht => le_trans (HardyEstimatesPartial.hardyZ_abs_le t) (hb t ht)⟩

end HardySetupV2Instance
