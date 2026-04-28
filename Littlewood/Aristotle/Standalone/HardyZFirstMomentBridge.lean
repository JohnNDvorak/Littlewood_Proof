/-
Bridge for the Hardy Z first moment bound: |∫₁ᵀ Z(t) dt| ≤ C·T^{1/2}.

PROOF STRUCTURE:
  Z(t) = MainTerm(t) + ErrorTerm(t).

  (A) |∫ ErrorTerm| ≤ C_E·√T: from RSExpansionProof.errorTerm_first_moment_sqrt.
  (B) |∫ MainTerm| ≤ C_M·√T: from
      AtkinsonFormula.mainTerm_first_moment_sqrt_of_inversePhaseCellPrefix.

The MainTerm bound uses the Atkinson formula (1949): per-mode integration by parts
on the Dirichlet polynomial, with the boundary sum controlled by the kernel sum
estimate and the signed Fresnel contributions bounded by Abel's alternating sum lemma.
The per-mode absolute value bound gives only O(T^{3/4}); the O(T^{1/2}) bound
requires the signed cancellation of the Fresnel integrals (Atkinson's key insight).

Reference: Atkinson 1949; Titchmarsh 1951 §4.15; Ingham 1932 §5.2; Ivić 2003 §4.2.
-/

import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial
import Littlewood.Aristotle.HardyZFirstMoment
import Littlewood.Aristotle.HardyZMeasurability
import Littlewood.Aristotle.HardyNProperties
import Littlewood.Aristotle.Standalone.RSExpansionProof
import Littlewood.Aristotle.Standalone.AtkinsonFormula
import Littlewood.Aristotle.Standalone.CorePrefixDirect

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set

namespace Aristotle.Standalone.HardyZFirstMomentBridge

open HardyEstimatesPartial
open Aristotle.Standalone.AtkinsonFormula
open Aristotle.Standalone.SiegelSaddleExpansionHyp
open Aristotle.Standalone.GabckePhaseCouplingHyp

variable [AtkinsonShiftedInversePhaseCellPrefixBoundHyp]
variable [SiegelSaddleExpansionHyp]

/-- **Main term first moment O(√T) bound**.
    |∫₁ᵀ MainTerm(t) dt| ≤ C_M·T^{1/2}.

    Proved by the Atkinson formula: per-mode IBP on the Dirichlet polynomial
    with signed Fresnel cancellation. The per-mode absolute value bound gives
    only O(T^{3/4}); the O(T^{1/2}) bound requires the Atkinson signed sum.

    Reference: Atkinson 1949; Titchmarsh 1951, §4.15. -/
private theorem mainTerm_first_moment_sqrt :
    ∃ C_M > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, MainTerm t| ≤ C_M * T ^ ((1 : ℝ) / 2) :=
  Aristotle.Standalone.AtkinsonFormula.mainTerm_first_moment_sqrt_of_inversePhaseCellPrefix

/-- **Hardy Z first moment O(√T) bridge**.
    |∫₁ᵀ Z(t) dt| ≤ C·T^{1/2} for all T ≥ 2.
    Downstream: HardyZFirstMomentIBP.hardyZ_first_moment_sublinear. -/
theorem hardyZ_first_moment_sqrt :
    ∃ C > 0, ∀ T : ℝ, T ≥ 2 →
      |∫ t in Ioc 1 T, hardyZ t| ≤ C * T ^ ((1 : ℝ) / 2) := by
  let _ : GabckePhaseCouplingHyp := gabckePhaseCouplingHyp_of_siegelSaddleExpansionHyp
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
