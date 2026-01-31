/-
Integrated from Aristotle output d7cdd34c-76c2-4f83-bfdb-dd88618d143e.
Hardy Z Cauchy-Schwarz + alternative formula.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

KEY RESULTS (ALL PROVED - 0 sorries):
- integral_cauchy_schwarz: Cauchy-Schwarz for integrals on Ioc
- exp_im_log_eq_div_abs: exp(i·Im(log z)) = z/‖z‖
- hardyZ_eq_alt: alternative formula for Z
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

lemma integral_cauchy_schwarz (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : IntegrableOn f (Ioc a b)) (hf2 : IntegrableOn (fun t => f t ^ 2) (Ioc a b)) :
    (∫ t in Ioc a b, |f t|)^2 ≤ (b - a) * ∫ t in Ioc a b, (f t)^2 := by
  have h_cauchy_schwarz : (∫ t in Set.Ioc a b, (abs (f t) - (∫ u in Set.Ioc a b, abs (f u)) / (b - a)) ^ 2) ≥ 0 := by
    exact MeasureTheory.integral_nonneg fun t => sq_nonneg _;
  simp_all +decide [ sub_sq, MeasureTheory.integral_sub, MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul ];
  rw [ MeasureTheory.integral_add, MeasureTheory.integral_sub ] at h_cauchy_schwarz;
  · simp_all +decide [ MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const, le_of_lt hab ];
    nlinarith [ mul_div_cancel₀ ( ∫ t in Set.Ioc a b, |f t| ) ( sub_ne_zero_of_ne hab.ne' ) ];
  · exact hf2;
  · exact MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.const_mul ( hf.norm ) _ ) _;
  · exact MeasureTheory.Integrable.sub hf2 ( MeasureTheory.Integrable.mul_const ( MeasureTheory.Integrable.const_mul ( hf.norm ) _ ) _ );
  · norm_num

lemma exp_im_log_eq_div_abs {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (I * (Complex.log z).im) = z / ↑‖z‖ := by
      have h_euler : Complex.exp (Complex.I * Complex.arg z) = Complex.cos (Complex.arg z) + Complex.I * Complex.sin (Complex.arg z) := by
        convert Complex.exp_mul_I _ using 2 <;> ring;
      have h_div : z / ‖z‖ = Complex.cos (Complex.arg z) + Complex.I * Complex.sin (Complex.arg z) := by
        have h_div : z = ‖z‖ * Complex.exp (Complex.I * Complex.arg z) := by
          nth_rw 1 [ ← Complex.norm_mul_exp_arg_mul_I z ] ; ring;
        grind;
      convert h_euler using 2 ; norm_num [ Complex.log_im ]

lemma hardyZ_eq_alt (t : ℝ) :
    hardyZ t = ((Complex.Gamma (1/4 + I * (t/2))) / ↑‖Complex.Gamma (1/4 + I * (t/2))‖ *
    Complex.exp (-I * (t/2) * Real.log Real.pi) * riemannZeta (1/2 + I * t)).re := by
      have h_exp : Complex.exp (Complex.I * hardyTheta t) = (Complex.Gamma (1 / 4 + Complex.I * (t / 2))) / ‖Complex.Gamma (1 / 4 + Complex.I * (t / 2))‖ * Complex.exp (-Complex.I * (t / 2) * Real.log Real.pi) := by
        have h_exp : Complex.exp (Complex.I * hardyTheta t) = Complex.exp (Complex.I * (Complex.log (Complex.Gamma (1/4 + Complex.I * (t/2)))).im - Complex.I * (t/2) * Real.log Real.pi) := by
          simp [hardyTheta];
          ring;
        have h_exp : Complex.exp (Complex.I * (Complex.log (Complex.Gamma (1/4 + Complex.I * (t/2)))).im) = Complex.Gamma (1/4 + Complex.I * (t/2)) / ‖Complex.Gamma (1/4 + Complex.I * (t/2))‖ := by
          convert exp_im_log_eq_div_abs _ using 1;
          exact Complex.Gamma_ne_zero_of_re_pos ( by norm_num [ Complex.add_re, Complex.mul_re ] );
        simp_all +decide [ mul_assoc, ← Complex.exp_add ];
        rw [ ← h_exp, ← Complex.exp_add ] ; ring;
      exact h_exp ▸ rfl

end HardyEstimatesPartial
