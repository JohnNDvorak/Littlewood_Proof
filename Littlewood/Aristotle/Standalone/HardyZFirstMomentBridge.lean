/-
Bridge for the Hardy Z first moment bound: |∫₁ᵀ Z(t) dt| ≤ C·T^{1/2}.

PROOF STRUCTURE:
  Z(t) = MainTerm(t) + ErrorTerm(t).

  (A) |∫ ErrorTerm| ≤ C_E·√T: from RSExpansionProof.errorTerm_first_moment_sqrt.
  (B) |∫ MainTerm| ≤ C_M·√T: sorry — requires a global technique.

MATHEMATICAL NOTE ON THE PER-MODE APPROACH:
  The per-mode VdC approach (bounding |∫ hardyCos_n| uniformly in n) is
  MATHEMATICALLY IMPOSSIBLE for getting O(√T):

  • The stationary point of mode n sits at hardyStart(n) = 2π(n+1)².
  • θ''(hardyStart(n)) ≈ 1/(4π(n+1)²), so the Fresnel integral gives
    |∫ cos(θ - t·log(n+1))| = Θ(n+1) per mode.
  • Weighted: (n+1)^{-1/2} · Θ(n+1) = Θ(√(n+1)).
  • Summing ∑_{n<N} √(n+1) ≈ N^{3/2} = O(T^{3/4}).
  • The convexity bound has exponent 1/4, and 3/4 + 1/4 = 1, so O(T^{3/4})
    is NOT sufficient for the Hardy infinite-zeros contradiction.

  The standard O(T^{1/2}) proof (Titchmarsh §4.15) uses integration by parts on
  the integral of Z(t) directly, exploiting the functional equation of ζ, NOT
  mode-by-mode Van der Corput. A future agent should pursue this global approach.

Reference: Titchmarsh 1951 §4.15; Ingham 1932 §5.2; Ivić 2003 §4.2.
-/

import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyZMeasurability
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.Standalone.RSExpansionProof

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set

namespace Aristotle.Standalone.HardyZFirstMomentBridge

open HardyEstimatesPartial

/-- **Main term first moment O(√T) bound**.
    |∫₁ᵀ MainTerm(t) dt| ≤ C_M·T^{1/2}.

    This requires a global technique (IBP on the integral of Z with
    the functional equation), not per-mode VdC.
    See module docstring for why per-mode analysis gives only O(T^{3/4}).

    Reference: Titchmarsh 1951, §4.15 (integration by parts on ∫ Z(t) dt). -/
private theorem mainTerm_first_moment_sqrt :
    ∃ C_M > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, MainTerm t| ≤ C_M * T ^ ((1 : ℝ) / 2) := by
  sorry

/-- **Hardy Z first moment O(√T) bridge**.
    |∫₁ᵀ Z(t) dt| ≤ C·T^{1/2} for all T ≥ 2.
    Downstream: HardyZFirstMomentIBP.hardyZ_first_moment_sublinear. -/
theorem hardyZ_first_moment_sqrt :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, hardyZ t| ≤ C * T ^ ((1 : ℝ) / 2) := by
  obtain ⟨C_E, hCE, h_error⟩ :=
    Aristotle.Standalone.RSExpansionProof.errorTerm_first_moment_sqrt
  obtain ⟨C_M, hCM, h_main⟩ := mainTerm_first_moment_sqrt
  refine ⟨C_M + C_E, by positivity, fun T hT => ?_⟩
  have h_Z_split : ∀ t, hardyZ t = MainTerm t + ErrorTerm t := fun t => by
    unfold ErrorTerm; ring
  have h_main_intble : IntegrableOn MainTerm (Ioc 1 T) := mainTerm_integrable T
  have h_error_intble : IntegrableOn ErrorTerm (Ioc 1 T) := errorTerm_integrable T
  have h_int_eq : ∫ t in Ioc 1 T, hardyZ t =
      (∫ t in Ioc 1 T, MainTerm t) + (∫ t in Ioc 1 T, ErrorTerm t) := by
    rw [show (fun t => hardyZ t) = (fun t => MainTerm t + ErrorTerm t) from
      funext h_Z_split]
    exact integral_add h_main_intble h_error_intble
  calc |∫ t in Ioc 1 T, hardyZ t|
      = |(∫ t in Ioc 1 T, MainTerm t) + (∫ t in Ioc 1 T, ErrorTerm t)| := by
        rw [h_int_eq]
    _ ≤ |∫ t in Ioc 1 T, MainTerm t| + |∫ t in Ioc 1 T, ErrorTerm t| :=
        abs_add_le _ _
    _ ≤ C_M * T ^ ((1 : ℝ) / 2) + C_E * T ^ ((1 : ℝ) / 2) := by
        linarith [h_main T hT, h_error T hT]
    _ = (C_M + C_E) * T ^ ((1 : ℝ) / 2) := by ring

end Aristotle.Standalone.HardyZFirstMomentBridge
