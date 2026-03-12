import Littlewood.Aristotle.ZetaMeanSquare
import Littlewood.Aristotle.Standalone.HardyAfeSignedGapProvider

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone.ZetaMeanSquareHalfRootPayloadBridge

open Filter Asymptotics
open Aristotle.Standalone.HardyAfeSignedGapProvider

/-- Root payload for the explicit critical-line second-moment asymptotic. -/
class ZetaMeanSquareHalfBoundRootPayload : Prop where
  witness :
    (fun T : ℝ => mean_square_zeta (1 / 2) T - T * Real.log T)
      =O[atTop] (fun T : ℝ => T)

/-- Build `ZetaMeanSquareHalfBound` from an explicit payload witness. -/
theorem zetaMeanSquareHalfBound_of_rootPayload
    [ZetaMeanSquareHalfBoundRootPayload] :
    ZetaMeanSquareHalfBound := by
  exact
    zetaMeanSquareHalfBound_of_explicit
      ZetaMeanSquareHalfBoundRootPayload.witness

/-- Global auto-instance bridge from root payload to `ZetaMeanSquareHalfBound`. -/
instance (priority := 100)
    [ZetaMeanSquareHalfBoundRootPayload] :
    ZetaMeanSquareHalfBound :=
  zetaMeanSquareHalfBound_of_rootPayload

/-- Package a concrete asymptotic theorem as root payload. -/
def zetaMeanSquareHalfBoundRootPayload_of_witness
    (h :
      (fun T : ℝ => mean_square_zeta (1 / 2) T - T * Real.log T)
        =O[atTop] (fun T : ℝ => T)) :
    ZetaMeanSquareHalfBoundRootPayload :=
  ⟨h⟩

end Aristotle.Standalone.ZetaMeanSquareHalfRootPayloadBridge
