import Littlewood.Aristotle.Standalone.HardyAfeSignedGapRootInfra

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.HardyAfeSignedGapRootLifts

open Filter Asymptotics MeasureTheory Set
open Aristotle.Standalone.HardyAfeMeanSquareBridgeInfra
open Aristotle.Standalone.HardyAfeSignedGapRootInfra

/-- Lift a critical-line mean-square class witness into the bundled B1 root payload. -/
theorem rootPayload_of_halfBound
    [ZetaMeanSquareHalfBound] :
    HardyAfeSignedGapRootPayload := by
  exact ⟨signed_gap_isBigO_of_halfBound⟩

/-- Lift an explicit critical-line mean-square asymptotic theorem into the bundled
B1 root payload. -/
theorem rootPayload_of_explicit_halfBound
    (hhalf :
      (fun T : ℝ => mean_square_zeta (1 / 2) T - T * Real.log T)
        =O[atTop] (fun T => T)) :
    HardyAfeSignedGapRootPayload := by
  exact ⟨signed_gap_isBigO_of_explicit_halfBound hhalf⟩

/-- Recover the signed AFE gap endpoint from a critical-line mean-square class witness. -/
theorem signed_gap_from_halfBound
    [ZetaMeanSquareHalfBound] :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
      =O[atTop] (fun T : ℝ => T) := by
  letI : HardyAfeSignedGapRootPayload := rootPayload_of_halfBound
  exact signed_gap_isBigO_of_rootPayload

/-- Recover the signed AFE gap endpoint from an explicit critical-line mean-square
asymptotic theorem. -/
theorem signed_gap_from_explicit_halfBound
    (hhalf :
      (fun T : ℝ => mean_square_zeta (1 / 2) T - T * Real.log T)
        =O[atTop] (fun T => T)) :
    (fun T => ∫ t in (1 : ℝ)..T, afeGapIntegrand t)
      =O[atTop] (fun T : ℝ => T) := by
  letI : HardyAfeSignedGapRootPayload := rootPayload_of_explicit_halfBound hhalf
  exact signed_gap_isBigO_of_rootPayload

end Aristotle.Standalone.HardyAfeSignedGapRootLifts
