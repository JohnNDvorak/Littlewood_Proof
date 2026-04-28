import Littlewood.Aristotle.Standalone.SmallTPerronSqrtBridge
import Littlewood.Aristotle.Standalone.ExplicitFormulaPsiB5aShiftedBoundAtomic

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Aristotle.Standalone

/-!
# Shared small-`T` Perron leaf instances

This module exposes the bounded-height Perron contour provider used by both the
`ψ` and `π` theorem-first lanes.

The focused leaf is `SmallTPerronSqrtBoundHyp` on `2 ≤ T ≤ 16`. The stronger
public `SmallTPerronBoundHyp` surface is recovered automatically through
`SmallTPerronSqrtBridge`.
-/

/-- Focused bounded-height Perron leaf shared by the theorem-first `ψ` and `π`
lanes. The stronger absorbed small-`T` class is recovered automatically
through `SmallTPerronSqrtBridge`. -/
instance (priority := 100) :
    Aristotle.Standalone.SmallTPerronSqrtBridge.SmallTPerronSqrtBoundHyp where
  bound := by
    obtain ⟨C₂, hC₂, hBound⟩ :=
      Aristotle.Standalone.ExplicitFormulaPsiSkeleton.shifted_remainder_bound_atomic
    refine ⟨32 * C₂, by positivity, ?_⟩
    intro x T hx hT_lo _hT_hi
    have hx1 : 1 ≤ x := by linarith
    have hT1 : 1 ≤ T := by linarith
    have hBound' := hBound x T hx hT_lo
    have hsqrtT_pos : 0 < Real.sqrt T := by
      exact Real.sqrt_pos_of_pos (by linarith)
    have hlogsqdiv : (Real.log T) ^ 2 / Real.sqrt T ≤ 16 := by
      rw [div_le_iff₀ hsqrtT_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        Littlewood.Development.HadamardProductZeta.log_sq_le_mul_sqrt T hT1
    have hterm1 :
        Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T ≤ 16 * Real.sqrt x := by
      have hsqrtx_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
      have hmul := mul_le_mul_of_nonneg_left hlogsqdiv hsqrtx_nonneg
      rw [mul_div_assoc]
      simpa [mul_comm] using hmul
    have hlogx : (Real.log x) ^ 2 ≤ 16 * Real.sqrt x := by
      simpa [mul_comm] using
        Littlewood.Development.HadamardProductZeta.log_sq_le_mul_sqrt x hx1
    have hInside :
        Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2 ≤
          32 * Real.sqrt x := by
      linarith
    calc
      |Littlewood.Development.ShiftedRemainderInterface.shiftedRemainderRe x T|
          ≤ C₂ * (Real.sqrt x * (Real.log T) ^ 2 / Real.sqrt T + (Real.log x) ^ 2) := by
            simpa using hBound'
      _ ≤ C₂ * (32 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hInside hC₂.le
      _ = (32 * C₂) * Real.sqrt x := by ring

end Aristotle.Standalone
