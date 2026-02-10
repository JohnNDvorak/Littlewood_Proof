/-
Branch-cut-free representation of Hardy's cos function.

KEY RESULT:
  exp_I_mul_arg_eq_div_norm: exp(I · arg z) = z / ‖z‖ for z ≠ 0
  exp_I_mul_log_im_eq_div_norm: exp(I · Im(log z)) = z / ‖z‖ for z ≠ 0
  differentiableAt_hardyCosExp: Re(Γ(s)/‖Γ(s)‖ · exp(phase)) is differentiable for ALL t

This shows that cos(θ(t) - t·log(n+1)) equals the real part of a manifestly
smooth function, bypassing the branch-cut issue with hardyTheta = Im(log Γ)
which has 2π jumps when Γ crosses the negative real axis.

The key identity: for any z ≠ 0, exp(I · arg z) = z / ‖z‖.
Combined with Complex.log_im (Im(log z) = arg z), this gives:
  exp(I · Im(log z)) = z / ‖z‖
which is smooth even when Im(log z) is discontinuous.

COROLLARY: The function
  t ↦ Re(Γ(1/4+it/2)/‖Γ(...)‖ · exp(-I·(t/2)·log(π(n+1)²)))
is differentiable at every t (no slit plane condition needed).

This is a prerequisite for the stationary phase analysis of
∫ hardyCos near the critical point t₀ = 2π(n+1)².

DEPENDENCIES: GammaHalfPlane.lean (Γ properties at 1/4+it/2)
Co-authored-by: Claude (Anthropic)
-/

import Mathlib
import Littlewood.Aristotle.GammaHalfPlane
import Littlewood.Aristotle.HardyZMeasurability

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace HardyCosSmooth

open Complex

/-- For any nonzero z : ℂ, exp(I * arg z) = z / ‖z‖.
    This is the branch-cut-free polar form: z = ‖z‖ · exp(I · arg z). -/
lemma exp_I_mul_arg_eq_div_norm (z : ℂ) (hz : z ≠ 0) :
    exp (I * ↑(Complex.arg z)) = z / ↑‖z‖ := by
  have h_norm_ne : (↑‖z‖ : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (ne_of_gt (norm_pos_iff.mpr hz))
  rw [mul_comm, eq_div_iff h_norm_ne, mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I z

/-- For any nonzero z : ℂ, exp(I * Im(log z)) = z / ‖z‖.
    Uses log_im : (log z).im = arg z. -/
lemma exp_I_mul_log_im_eq_div_norm (z : ℂ) (hz : z ≠ 0) :
    exp (I * ↑((Complex.log z).im)) = z / ↑‖z‖ := by
  rw [Complex.log_im]
  exact exp_I_mul_arg_eq_div_norm z hz

/-- The smooth representation function:
    F(n, t) = Γ(s)/‖Γ(s)‖ · exp(-I·(t/2)·log(π(n+1)²))
    where s = 1/4 + it/2. -/
def hardyCosExp (n : ℕ) (t : ℝ) : ℂ :=
  let s := (1/4 + I * (↑t/2) : ℂ)
  Gamma s / ↑‖Gamma s‖ *
    exp (-I * ↑((t/2) * Real.log (Real.pi * (↑n + 1)^2)))

/-- Phase used by `hardyCosExp`, in real form. -/
private def hardyPhaseArg (n : ℕ) (t : ℝ) : ℝ :=
  (Complex.log (Gamma (1/4 + I * (t/2)))).im - (t/2) * Real.log (Real.pi * (↑n + 1)^2)

lemma hardyPhaseArg_eq_hardyTheta_sub_log (n : ℕ) (t : ℝ) :
    hardyPhaseArg n t =
      HardyEstimatesPartial.hardyTheta t - t * Real.log (n + 1) := by
  unfold hardyPhaseArg HardyEstimatesPartial.hardyTheta
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hn : (0 : ℝ) < (↑n + 1) := by positivity
  have hsq : ((↑n + 1) ^ 2 : ℝ) = (↑n + 1) * (↑n + 1) := by ring
  rw [hsq, Real.log_mul (ne_of_gt hpi) (ne_of_gt (mul_pos hn hn))]
  rw [Real.log_mul (ne_of_gt hn) (ne_of_gt hn)]
  ring

lemma hardyCosExp_eq_cexp_phaseArg (n : ℕ) (t : ℝ) :
    hardyCosExp n t = Complex.exp (Complex.I * (hardyPhaseArg n t : ℂ)) := by
  let s : ℂ := (1/4 + I * (↑t/2) : ℂ)
  have hs : Gamma s ≠ 0 := by
    change Gamma (1 / 4 + I * (↑t / 2) : ℂ) ≠ 0
    simpa [mul_comm, mul_left_comm, mul_assoc] using GammaHalfPlane.gamma_quarter_ne_zero t
  have hgamma :
      Complex.exp (Complex.I * ((Complex.log (Gamma s)).im : ℂ))
        = Gamma s / ↑‖Gamma s‖ := by
    simpa using exp_I_mul_log_im_eq_div_norm (Gamma s) hs
  calc
    hardyCosExp n t
        = (Gamma s / ↑‖Gamma s‖)
            * Complex.exp (-Complex.I * (((t / 2) * Real.log (Real.pi * (↑n + 1) ^ 2)) : ℂ)) := by
              simp [hardyCosExp, s]
    _ = Complex.exp (Complex.I * ((Complex.log (Gamma s)).im : ℂ))
          * Complex.exp (-Complex.I * (((t / 2) * Real.log (Real.pi * (↑n + 1) ^ 2)) : ℂ)) := by
            rw [hgamma]
    _ = Complex.exp
          (Complex.I * ((Complex.log (Gamma s)).im : ℂ)
            + (-Complex.I * (((t / 2) * Real.log (Real.pi * (↑n + 1) ^ 2)) : ℂ))) := by
          rw [Complex.exp_add]
    _ = Complex.exp
          (Complex.I *
            (((Complex.log (Gamma s)).im
              - (t / 2) * Real.log (Real.pi * (↑n + 1) ^ 2)) : ℂ)) := by
          congr 1
          ring
    _ = Complex.exp (Complex.I * (hardyPhaseArg n t : ℂ)) := by
          simp [hardyPhaseArg, s]

lemma re_hardyCosExp_eq_cos_phaseArg (n : ℕ) (t : ℝ) :
    (hardyCosExp n t).re = Real.cos (hardyPhaseArg n t) := by
  rw [hardyCosExp_eq_cexp_phaseArg]
  calc
    (Complex.exp (Complex.I * (hardyPhaseArg n t : ℂ))).re
        = Real.exp ((Complex.I * (hardyPhaseArg n t : ℂ)).re)
            * Real.cos ((Complex.I * (hardyPhaseArg n t : ℂ)).im) := by
              simpa using Complex.exp_re (Complex.I * (hardyPhaseArg n t : ℂ))
    _ = Real.exp 0 * Real.cos (hardyPhaseArg n t) := by
          simp
    _ = Real.cos (hardyPhaseArg n t) := by simp

/-- Branch-cut-free identity: the Hardy cosine mode is the real part of the
smooth normalized-Gamma phase factor `hardyCosExp`. -/
theorem hardyCos_eq_re_hardyCosExp (n : ℕ) (t : ℝ) :
    HardyEstimatesPartial.hardyCos n t = (hardyCosExp n t).re := by
  unfold HardyEstimatesPartial.hardyCos
  have hphase :
      HardyEstimatesPartial.hardyTheta t - t * Real.log (n + 1) = hardyPhaseArg n t := by
    simpa using (hardyPhaseArg_eq_hardyTheta_sub_log n t).symm
  rw [hphase]
  symm
  exact re_hardyCosExp_eq_cos_phaseArg n t

/-- DifferentiableAt for the Gamma quotient t ↦ Γ(s)/‖Γ(s)‖. -/
lemma differentiableAt_gamma_div_norm (t : ℝ) :
    DifferentiableAt ℝ
      (fun t : ℝ => Gamma (1/4 + I * (↑t/2)) / ↑‖Gamma (1/4 + I * (↑t/2))‖) t := by
  have hf : DifferentiableAt ℝ (fun t : ℝ => Gamma (1/4 + I * (↑t/2))) t :=
    (GammaHalfPlane.hasDerivAt_gamma_quarter t).differentiableAt
  have h0 : Gamma (1/4 + I * (↑t/2)) ≠ 0 := GammaHalfPlane.gamma_quarter_ne_zero t
  apply DifferentiableAt.div hf
  · exact Complex.ofRealCLM.differentiableAt.comp t (DifferentiableAt.norm (𝕜 := ℝ) hf h0)
  · exact ofReal_ne_zero.mpr (ne_of_gt (GammaHalfPlane.norm_gamma_quarter_pos t))

/-- DifferentiableAt for the exponential phase factor. -/
lemma differentiableAt_exp_phase (n : ℕ) (t : ℝ) :
    DifferentiableAt ℝ
      (fun t : ℝ => exp (-I * ↑((t/2) * Real.log (Real.pi * (↑n + 1)^2)))) t := by
  apply DifferentiableAt.cexp
  apply DifferentiableAt.const_mul
  exact Complex.ofRealCLM.differentiableAt.comp t
    (((differentiableAt_id (𝕜 := ℝ)).div_const (2 : ℝ)).mul_const _)

/-- The smooth representation function is differentiable at every t.
    This bypasses the branch-cut issue: hardyTheta = Im(log Γ) is discontinuous,
    but Re(Γ/‖Γ‖ · exp(...)) is smooth since Γ/‖Γ‖ avoids the branch cut. -/
theorem differentiableAt_hardyCosExp (n : ℕ) (t : ℝ) :
    DifferentiableAt ℝ (fun t => (hardyCosExp n t).re) t := by
  have hf : DifferentiableAt ℝ (fun t => hardyCosExp n t) t := by
    unfold hardyCosExp
    simp only
    exact (differentiableAt_gamma_div_norm t).mul (differentiableAt_exp_phase n t)
  exact Complex.reCLM.differentiableAt.comp t hf

/-- Complex-valued smoothness of the branch-cut-free Hardy phase factor. -/
theorem differentiableAt_hardyCosExp_complex (n : ℕ) (t : ℝ) :
    DifferentiableAt ℝ (fun t => hardyCosExp n t) t := by
  unfold hardyCosExp
  simp only
  exact (differentiableAt_gamma_div_norm t).mul (differentiableAt_exp_phase n t)

theorem differentiable_hardyCosExp_complex (n : ℕ) :
    Differentiable ℝ (hardyCosExp n) := by
  intro t
  exact differentiableAt_hardyCosExp_complex n t

theorem continuous_hardyCosExp_complex (n : ℕ) :
    Continuous (hardyCosExp n) :=
  (differentiable_hardyCosExp_complex n).continuous

/-- As a corollary, each Hardy cosine mode is differentiable at every real
point, with no branch-cut side conditions. -/
theorem differentiableAt_hardyCos (n : ℕ) (t : ℝ) :
    DifferentiableAt ℝ (HardyEstimatesPartial.hardyCos n) t := by
  have h :
      DifferentiableAt ℝ (fun x : ℝ => (hardyCosExp n x).re) t :=
    differentiableAt_hardyCosExp n t
  have hEq :
      (fun x : ℝ => HardyEstimatesPartial.hardyCos n x)
        = (fun x : ℝ => (hardyCosExp n x).re) := by
    funext x
    exact hardyCos_eq_re_hardyCosExp n x
  simpa [hEq] using h

theorem differentiable_hardyCos (n : ℕ) :
    Differentiable ℝ (HardyEstimatesPartial.hardyCos n) := by
  intro t
  exact differentiableAt_hardyCos n t

theorem continuous_hardyCos (n : ℕ) :
    Continuous (HardyEstimatesPartial.hardyCos n) :=
  (differentiable_hardyCos n).continuous

theorem intervalIntegrable_hardyCos (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (HardyEstimatesPartial.hardyCos n) MeasureTheory.volume a b :=
  (continuous_hardyCos n).intervalIntegrable a b

end HardyCosSmooth
