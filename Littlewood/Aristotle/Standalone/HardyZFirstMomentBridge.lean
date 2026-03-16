/-
Bridge for the Hardy Z first moment bound: |∫₁ᵀ Z(t) dt| ≤ C·T^{1/2}.

The O(T^{1/2}) bound decomposes into:
  |∫ Z| ≤ |∫ MainTerm| + |∫ ErrorTerm|

(A) |∫ ErrorTerm| ≤ C·√T: proved in RSExpansionProof.errorTerm_first_moment_sqrt
    (imported here, cycle-free since RSExpansionProof no longer imports this file).

(B) |∫ MainTerm| ≤ C·√T: requires per-mode VdC assembly on the Dirichlet polynomial.
    SORRY: The per-mode VdC infrastructure exists (OffResonanceSmoothVdC, IBP Parts 6-7)
    but the final assembly into the MainTerm first moment bound is not yet written.

This sorry is NOT independently irreducible: it follows from the Siegel/Gabcke sorrys
plus per-mode VdC assembly. The remaining work is assembling per-mode VdC bounds
into |∫ MainTerm| ≤ C·√T.

Reference: Titchmarsh 1951 §4.15; Ingham 1932 §5.2.
-/

import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.Standalone.RSExpansionProof

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set

namespace Aristotle.Standalone.HardyZFirstMomentBridge

open HardyEstimatesPartial

/-- **Hardy Z first moment O(√T) bridge**.

    |∫₁ᵀ Z(t) dt| ≤ C·T^{1/2} for all T ≥ 2.

    Proof strategy:
    - ErrorTerm: O(√T) by alternating block cancellation (PROVED: errorTerm_first_moment_sqrt)
    - MainTerm: O(√T) by per-mode VdC on Dirichlet polynomial (SORRY)
    - Combine: |∫ Z| = |∫ MainTerm + ∫ ErrorTerm| ≤ C₁√T + C₂√T -/
theorem hardyZ_first_moment_sqrt :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, hardyZ t| ≤ C * T ^ ((1 : ℝ) / 2) := by
  -- Step 1: ErrorTerm first moment O(√T) — PROVED
  obtain ⟨C_E, hCE_pos, h_error⟩ :=
    Aristotle.Standalone.RSExpansionProof.errorTerm_first_moment_sqrt
  -- Step 2: MainTerm first moment O(√T) — SORRY (per-mode VdC assembly)
  suffices h_main : ∃ C_M > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, MainTerm t| ≤ C_M * T ^ ((1 : ℝ) / 2) by
    obtain ⟨C_M, hCM_pos, h_M⟩ := h_main
    refine ⟨C_M + C_E, by linarith, fun T hT => ?_⟩
    -- Z = MainTerm + ErrorTerm
    have h_split : ∫ t in Ioc 1 T, hardyZ t =
        (∫ t in Ioc 1 T, MainTerm t) + (∫ t in Ioc 1 T, ErrorTerm t) := by
      rw [← MeasureTheory.integral_add (mainTerm_integrable T) (errorTerm_integrable T)]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        fun x _ => by unfold ErrorTerm; ring
    rw [h_split]
    calc |(∫ t in Ioc 1 T, MainTerm t) + (∫ t in Ioc 1 T, ErrorTerm t)|
        ≤ |∫ t in Ioc 1 T, MainTerm t| + |∫ t in Ioc 1 T, ErrorTerm t| :=
          abs_add_le _ _
      _ ≤ C_M * T ^ ((1 : ℝ) / 2) + C_E * T ^ ((1 : ℝ) / 2) := by
          linarith [h_M T hT, h_error T hT]
      _ = (C_M + C_E) * T ^ ((1 : ℝ) / 2) := by ring
  -- SORRY: MainTerm first moment bound from per-mode VdC assembly
  -- Infrastructure exists in OffResonanceSmoothVdC + HardyZFirstMomentIBP Parts 6-7
  -- but final assembly into |∫ MainTerm| ≤ C·√T is not yet written.
  sorry

end Aristotle.Standalone.HardyZFirstMomentBridge
