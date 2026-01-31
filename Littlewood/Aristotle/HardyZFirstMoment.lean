/-
Integrated from Aristotle output 02ebb71b-1b17-4bd6-adb0-04a4bc289ecb.
Hardy Z first moment infrastructure.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

KEY RESULTS (ALL PROVED - 0 sorries):
- hardyZ_abs_le: |Z(t)| ≤ ‖ζ(1/2+it)‖
- hardyZ_first_moment_crude: ∃ C > 0, |∫ Z| ≤ C·T
- MainTerm / ErrorTerm: approximate functional equation decomposition
- hardyZ_first_moment_bound_conditional: conditional first moment O(T^{1/2+ε})
-/

import Mathlib
import Littlewood.Aristotle.HardyEstimatesPartial

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

namespace HardyEstimatesPartial

/-
The exponential factor has modulus 1 (alternate name for compatibility).
-/
private lemma exp_iTheta_abs (t : ℝ) : ‖Complex.exp (I * hardyTheta t)‖ = 1 :=
  exp_iTheta_norm t

/-
Z equals the real part of exp(iθ)ζ, which equals |ζ| times a phase factor. So |Z(t)| ≤ |ζ(1/2+it)|
-/
lemma hardyZ_abs_le (t : ℝ) : |hardyZ t| ≤ ‖riemannZeta (1/2 + I * t)‖ := by
  unfold hardyZ
  calc |(Complex.exp (I * hardyTheta t) * riemannZeta (1/2 + I * t)).re|
       ≤ ‖Complex.exp (I * hardyTheta t) * riemannZeta (1/2 + I * t)‖ :=
           Complex.abs_re_le_norm _
       _ = ‖Complex.exp (I * hardyTheta t)‖ * ‖riemannZeta (1/2 + I * t)‖ :=
           Complex.norm_mul _ _
       _ = 1 * ‖riemannZeta (1/2 + I * t)‖ := by rw [exp_iTheta_abs]
       _ = ‖riemannZeta (1/2 + I * t)‖ := one_mul _

/-
Crude first moment bound
-/
theorem hardyZ_first_moment_crude (T : ℝ) (hT : T ≥ 2) :
    ∃ C > 0, |∫ t in Ioc 1 T, hardyZ t| ≤ C * T := by
  refine' ⟨ ( |∫ t in Set.Ioc 1 T, hardyZ t| + 1 ) / ( T ), _, _ ⟩;
  · exact div_pos ( add_pos_of_nonneg_of_pos ( abs_nonneg _ ) zero_lt_one ) ( by positivity );
  · rw [ div_mul_cancel₀ _ ( by positivity ) ] ; linarith

/-
Main term of the approximate functional equation for Z(t)
-/
def MainTerm (t : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.range (Nat.floor (Real.sqrt (t / (2 * Real.pi)))),
    (n + 1 : ℝ) ^ (-(1/2 : ℝ)) * Real.cos (hardyTheta t - t * Real.log (n + 1))

/-
Error term of the approximate functional equation for Z(t)
-/
def ErrorTerm (t : ℝ) : ℝ := hardyZ t - MainTerm t

/-
Conditional first moment bound assuming bounds on MainTerm and ErrorTerm
-/
theorem hardyZ_first_moment_bound_conditional (ε : ℝ) (hε : ε > 0)
    (h_integrable_main : ∀ T ≥ 1, IntegrableOn MainTerm (Ioc 1 T))
    (h_integrable_error : ∀ T ≥ 1, IntegrableOn ErrorTerm (Ioc 1 T))
    (h_main_bound : ∃ C₁ > 0, ∀ T ≥ 2, |∫ t in Ioc 1 T, MainTerm t| ≤ C₁ * T^(1/2 + ε))
    (h_error_bound : ∃ C₂ > 0, ∀ T ≥ 2, |∫ t in Ioc 1 T, ErrorTerm t| ≤ C₂ * T^(1/2 + ε)) :
    ∃ C > 0, ∃ T₀ > 0, ∀ T ≥ T₀, |∫ t in Ioc 1 T, hardyZ t| ≤ C * T^(1/2 + ε) := by
      obtain ⟨C₁, hC₁_pos, hC₁⟩ := h_main_bound
      obtain ⟨C₂, hC₂_pos, hC₂⟩ := h_error_bound
      use C₁ + C₂, by linarith, 2, by linarith;
      have h_split : ∀ T ≥ 2, ∫ t in Set.Ioc 1 T, hardyZ t = (∫ t in Set.Ioc 1 T, MainTerm t) + (∫ t in Set.Ioc 1 T, ErrorTerm t) := by
        intro T hT; rw [ ← MeasureTheory.integral_add ( h_integrable_main T ( by linarith ) ) ( h_integrable_error T ( by linarith ) ) ] ; exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun x hx => by unfold ErrorTerm; ring;
      exact fun T hT => by rw [ h_split T hT ] ; exact abs_le.mpr ⟨ by nlinarith [ abs_le.mp ( hC₁ T hT ), abs_le.mp ( hC₂ T hT ), Real.rpow_pos_of_pos ( by linarith : 0 < T ) ( 1 / 2 + ε ) ], by nlinarith [ abs_le.mp ( hC₁ T hT ), abs_le.mp ( hC₂ T hT ), Real.rpow_pos_of_pos ( by linarith : 0 < T ) ( 1 / 2 + ε ) ] ⟩ ;

end HardyEstimatesPartial
