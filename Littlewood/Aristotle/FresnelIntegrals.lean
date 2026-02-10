/-
Fresnel integral evaluations and infrastructure.

KEY RESULTS:
  fresnel_cos_integrable_on_Icc : cos(t^2) is integrable on [a, b]
  fresnel_sin_integrable_on_Icc : sin(t^2) is integrable on [a, b]
  gaussian_Ioi_re : Re(∫_{Ioi} cexp(-(ε+I)t²)) = ∫_{Ioi} exp(-εt²)cos(t²) for ε > 0
  gaussian_Ioi_im : Im(∫_{Ioi} cexp(-(ε+I)t²)) = -∫_{Ioi} exp(-εt²)sin(t²) for ε > 0
  fresnel_cos_eq : lim_{ε→0+} ∫₀^∞ exp(-εt²)cos(t²) dt = √(π/2)/2
  fresnel_sin_eq : lim_{ε→0+} ∫₀^∞ exp(-εt²)sin(t²) dt = √(π/2)/2

The proofs use Gaussian regularization: for ε > 0, the complex Gaussian integral
  ∫₀^∞ exp(-(ε+i)t²) dt = (π/(ε+i))^{1/2}/2
is known from Mathlib. The real/imaginary parts give damped Fresnel integrals.
Taking ε → 0+ recovers the Fresnel values.

APPLICATIONS: Stationary phase analysis in Hardy first moment.

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace FresnelIntegrals

open MeasureTheory Set Complex Filter Asymptotics Real Topology

/-! ## Section 1: Basic integrability on compact sets -/

/-- cos(t²) is continuous. -/
lemma fresnel_cos_continuous : Continuous (fun t : ℝ => Real.cos (t ^ 2)) :=
  Real.continuous_cos.comp (continuous_pow 2)

/-- sin(t²) is continuous. -/
lemma fresnel_sin_continuous : Continuous (fun t : ℝ => Real.sin (t ^ 2)) :=
  Real.continuous_sin.comp (continuous_pow 2)

/-- cos(t²) is integrable on any compact interval [a, b]. -/
lemma fresnel_cos_integrable_on_Icc (a b : ℝ) :
    IntegrableOn (fun t : ℝ => Real.cos (t ^ 2)) (Icc a b) :=
  fresnel_cos_continuous.continuousOn.integrableOn_compact isCompact_Icc

/-- sin(t²) is integrable on any compact interval [a, b]. -/
lemma fresnel_sin_integrable_on_Icc (a b : ℝ) :
    IntegrableOn (fun t : ℝ => Real.sin (t ^ 2)) (Icc a b) :=
  fresnel_sin_continuous.continuousOn.integrableOn_compact isCompact_Icc

/-- cos(t²) is interval-integrable on any [a, b]. -/
lemma fresnel_cos_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.cos (t ^ 2)) MeasureTheory.volume a b :=
  fresnel_cos_continuous.intervalIntegrable a b

/-- sin(t²) is interval-integrable on any [a, b]. -/
lemma fresnel_sin_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.sin (t ^ 2)) MeasureTheory.volume a b :=
  fresnel_sin_continuous.intervalIntegrable a b

/-! ## Section 2: Damped Fresnel integrals (exp(-εt²)·cos/sin(t²)) -/

/-- For ε > 0, exp(-εt²)·cos(t²) is integrable on Ioi 0. -/
lemma damped_fresnel_cos_integrable {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2)) (Ioi 0) := by
  have hc : Continuous (fun t : ℝ => Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2)) := by
    fun_prop
  apply Integrable.mono (integrable_exp_neg_mul_sq hε).integrableOn
    hc.aestronglyMeasurable
  exact ae_of_all _ fun t => by
    simp only [Real.norm_eq_abs, abs_mul]
    calc |Real.exp (-ε * t ^ 2)| * |Real.cos (t ^ 2)|
        ≤ |Real.exp (-ε * t ^ 2)| * 1 := by gcongr; exact abs_cos_le_one _
      _ = ‖Real.exp (-ε * t ^ 2)‖ := by rw [mul_one, Real.norm_eq_abs]

/-- For ε > 0, exp(-εt²)·sin(t²) is integrable on Ioi 0. -/
lemma damped_fresnel_sin_integrable {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => Real.exp (-ε * t ^ 2) * Real.sin (t ^ 2)) (Ioi 0) := by
  have hc : Continuous (fun t : ℝ => Real.exp (-ε * t ^ 2) * Real.sin (t ^ 2)) := by
    fun_prop
  apply Integrable.mono (integrable_exp_neg_mul_sq hε).integrableOn
    hc.aestronglyMeasurable
  exact ae_of_all _ fun t => by
    simp only [Real.norm_eq_abs, abs_mul]
    calc |Real.exp (-ε * t ^ 2)| * |Real.sin (t ^ 2)|
        ≤ |Real.exp (-ε * t ^ 2)| * 1 := by gcongr; exact abs_sin_le_one _
      _ = ‖Real.exp (-ε * t ^ 2)‖ := by rw [mul_one, Real.norm_eq_abs]

/-! ## Section 3: Decomposing the complex Gaussian into Re/Im parts -/

/-- cexp(-(ε+I)·t²) decomposes via Euler's formula. -/
lemma cexp_neg_eps_I_mul_sq (ε : ℝ) (t : ℝ) :
    Complex.exp (-((↑ε : ℂ) + Complex.I) * (↑t : ℂ) ^ 2) =
    ↑(Real.exp (-ε * t ^ 2)) * (↑(Real.cos (t ^ 2)) - Complex.I * ↑(Real.sin (t ^ 2))) := by
  have h1 : -((↑ε : ℂ) + Complex.I) * (↑t : ℂ) ^ 2 =
      ↑(-ε * t ^ 2) + ↑(-(t ^ 2)) * Complex.I := by push_cast; ring
  rw [h1, Complex.exp_add_mul_I, ← Complex.ofReal_exp]
  congr 1
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-- Re(cexp(-(ε+I)t²)) = exp(-εt²)·cos(t²). -/
lemma re_cexp_neg_eps_I_sq (ε : ℝ) (t : ℝ) :
    (Complex.exp (-((↑ε : ℂ) + Complex.I) * (↑t : ℂ) ^ 2)).re =
    Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2) := by
  rw [cexp_neg_eps_I_mul_sq]
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- Im(cexp(-(ε+I)t²)) = -exp(-εt²)·sin(t²). -/
lemma im_cexp_neg_eps_I_sq (ε : ℝ) (t : ℝ) :
    (Complex.exp (-((↑ε : ℂ) + Complex.I) * (↑t : ℂ) ^ 2)).im =
    -(Real.exp (-ε * t ^ 2) * Real.sin (t ^ 2)) := by
  rw [cexp_neg_eps_I_mul_sq]
  simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-! ## Section 4: Relating ∫ cexp(-(ε+I)t²) to damped Fresnel integrals -/

private lemma re_eps_I_pos {ε : ℝ} (hε : 0 < ε) : 0 < ((↑ε : ℂ) + Complex.I).re := by
  simp [hε]

/-- For ε > 0, Re(∫_{Ioi} cexp(-(ε+I)t²)) = ∫_{Ioi} exp(-εt²)cos(t²). -/
theorem gaussian_Ioi_re {ε : ℝ} (hε : 0 < ε) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-((↑ε : ℂ) + Complex.I) * (↑t : ℂ) ^ 2)).re =
    ∫ t : ℝ in Ioi 0, Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2) := by
  have hint := (integrable_cexp_neg_mul_sq (re_eps_I_pos hε)).integrableOn (s := Ioi 0)
  rw [show (∫ t : ℝ in Ioi 0, Complex.exp (-((↑ε : ℂ) + Complex.I) * (↑t : ℂ) ^ 2)).re =
    ∫ t : ℝ in Ioi 0, (Complex.exp (-((↑ε : ℂ) + Complex.I) * (↑t : ℂ) ^ 2)).re from by
      rw [← RCLike.re_to_complex]; exact (integral_re hint).symm]
  congr 1; ext t; exact re_cexp_neg_eps_I_sq ε t

/-- For ε > 0, Im(∫_{Ioi} cexp(-(ε+I)t²)) = -∫_{Ioi} exp(-εt²)sin(t²). -/
theorem gaussian_Ioi_im {ε : ℝ} (hε : 0 < ε) :
    (∫ t : ℝ in Ioi 0, Complex.exp (-((↑ε : ℂ) + Complex.I) * (↑t : ℂ) ^ 2)).im =
    -(∫ t : ℝ in Ioi 0, Real.exp (-ε * t ^ 2) * Real.sin (t ^ 2)) := by
  have hint := (integrable_cexp_neg_mul_sq (re_eps_I_pos hε)).integrableOn (s := Ioi 0)
  rw [show (∫ t : ℝ in Ioi 0, Complex.exp (-((↑ε : ℂ) + Complex.I) * (↑t : ℂ) ^ 2)).im =
    ∫ t : ℝ in Ioi 0, (Complex.exp (-((↑ε : ℂ) + Complex.I) * (↑t : ℂ) ^ 2)).im from by
      rw [← RCLike.im_to_complex]; exact (integral_im hint).symm]
  simp_rw [im_cexp_neg_eps_I_sq, integral_neg]

/-! ## Section 5: The complex Gaussian value for b = ε + I -/

/-- For ε > 0, ∫_{Ioi} cexp(-(ε+I)t²) = (π/(ε+I))^{1/2}/2. -/
theorem gaussian_Ioi_eps_I {ε : ℝ} (hε : 0 < ε) :
    ∫ t : ℝ in Ioi 0, Complex.exp (-((↑ε : ℂ) + Complex.I) * (↑t : ℂ) ^ 2) =
    (↑Real.pi / ((↑ε : ℂ) + Complex.I)) ^ (1 / 2 : ℂ) / 2 :=
  integral_gaussian_complex_Ioi (re_eps_I_pos hε)

/-! ## Section 6: Continuity of the Ioi Gaussian integral -/

/-- b ↦ ∫_{Ioi} cexp(-bt²) is continuous on {Re b > 0}.
    Follows from continuity of the full-line integral and even symmetry. -/
theorem continuousAt_gaussian_Ioi (b : ℂ) (hb : 0 < b.re) :
    ContinuousAt (fun c : ℂ => ∫ t : ℝ in Ioi 0, Complex.exp (-c * (↑t : ℂ) ^ 2)) b := by
  have h_full := continuousAt_gaussian_integral b hb
  -- For Re(c) > 0, Ioi integral = full/2 (using closed forms from Mathlib)
  have h_eq : (fun c : ℂ => ∫ t : ℝ in Ioi 0, Complex.exp (-c * (↑t : ℂ) ^ 2)) =ᶠ[𝓝 b]
      (fun c => (∫ t : ℝ, Complex.exp (-c * (↑t : ℂ) ^ 2)) / 2) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hb] with c hc
    have h1 := integral_gaussian_complex hc
    have h2 := integral_gaussian_complex_Ioi hc
    rw [h2, h1]
  exact (h_full.div_const 2).congr h_eq.symm

/-! ## Section 7: Algebraic identity π/I and limit of (π/(ε+I))^{1/2} as ε → 0+ -/

/-- π/I = -π·I. -/
lemma pi_div_I : (↑Real.pi : ℂ) / Complex.I = -(↑Real.pi : ℂ) * Complex.I := by
  have : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  simp [Complex.I_sq]

/-- (π/(ε+I))^{1/2} → (π/I)^{1/2} as ε → 0+. -/
lemma tendsto_sqrt_pi_div_eps_I :
    Tendsto (fun ε : ℝ => ((↑Real.pi : ℂ) / ((↑ε : ℂ) + Complex.I)) ^ (1 / 2 : ℂ))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 (((↑Real.pi : ℂ) / Complex.I) ^ (1 / 2 : ℂ))) := by
  -- cpow_const is continuous at z whenever z is not on the negative real axis
  -- π/I = -πI has Re = 0, Im = -π, so it's on the negative imaginary axis (not negative real)
  have h_cont : ContinuousAt (fun z : ℂ => z ^ (1/2 : ℂ))
      ((↑Real.pi : ℂ) / Complex.I) := by
    apply continuousAt_cpow_const
    rw [Complex.mem_slitPlane_iff]
    right
    -- Im(π/I) = Im(-πI) = -π ≠ 0
    rw [pi_div_I]
    show (-(↑Real.pi : ℂ) * Complex.I).im ≠ 0
    simp [Complex.mul_im, Real.pi_ne_zero]
  have h_div : Tendsto (fun ε : ℝ => (↑Real.pi : ℂ) / ((↑ε : ℂ) + Complex.I))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 ((↑Real.pi : ℂ) / Complex.I)) := by
    apply Tendsto.div tendsto_const_nhds _ Complex.I_ne_zero
    -- Need: (fun ε => ↑ε + I) → I = 0 + I as ε → 0+
    convert Tendsto.add (f := fun ε : ℝ => (↑ε : ℂ)) (g := fun _ => Complex.I)
      ((Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds)
      tendsto_const_nhds using 1
    simp
  exact h_cont.tendsto.comp h_div

/-! ## Section 8: Computing Re and Im of (π/I)^{1/2}/2 -/

/-- Helper: exp(log(π)/2) = √π. -/
private lemma exp_half_log_pi : Real.exp (Real.log Real.pi / 2) = Real.sqrt Real.pi := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos Real.pi_pos]
  ring_nf

/-- Helper: √π * √2 / 4 = √(π/2) / 2. Used in Fresnel Re/Im computations. -/
private lemma sqrt_pi_sqrt2_div4 :
    Real.sqrt Real.pi * Real.sqrt 2 / 4 = Real.sqrt (Real.pi / 2) / 2 := by
  rw [Real.sqrt_div Real.pi_pos.le]
  have h2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp
  nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

/-- Helper: √π * √2 / 4 = √(π/2) / 2 (negative version). -/
private lemma neg_sqrt_pi_sqrt2_div4 :
    -(Real.sqrt Real.pi * Real.sqrt 2 / 4) = -(Real.sqrt (Real.pi / 2) / 2) := by
  rw [sqrt_pi_sqrt2_div4]

-- Common setup for Re/Im computations of (π/I)^{1/2}/2
private lemma cpow_pi_div_I_setup :
    ((↑Real.pi : ℂ) / Complex.I) ^ (1 / 2 : ℂ) =
    ↑(Real.exp (Real.log Real.pi / 2)) *
      (↑(Real.cos (-(Real.pi / 4))) + ↑(Real.sin (-(Real.pi / 4))) * Complex.I) := by
  rw [pi_div_I, show -(↑Real.pi : ℂ) * Complex.I = ↑Real.pi * (-Complex.I) by ring]
  rw [Complex.cpow_def_of_ne_zero (by
    apply mul_ne_zero; exact_mod_cast Real.pi_ne_zero; exact neg_ne_zero.mpr Complex.I_ne_zero)]
  rw [Complex.log_ofReal_mul Real.pi_pos (neg_ne_zero.mpr Complex.I_ne_zero),
      Complex.log_neg_I]
  have h_exp : ((↑(Real.log Real.pi) + -(↑Real.pi / 2) * Complex.I) * (1 / 2 : ℂ)) =
      ↑(Real.log Real.pi / 2) + ↑(-(Real.pi / 4)) * Complex.I := by
    push_cast; ring
  rw [h_exp, Complex.exp_add_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_exp]

/-- Re((π/I)^{1/2}/2) = √(π/2)/2. -/
lemma re_sqrt_pi_div_I_div_2 :
    (((↑Real.pi : ℂ) / Complex.I) ^ (1 / 2 : ℂ) / 2).re =
    Real.sqrt (Real.pi / 2) / 2 := by
  rw [cpow_pi_div_I_setup]
  -- After setup: (↑(rexp ...) * (↑(cos ...) + ↑(sin ...) * I) / 2).re
  rw [Real.cos_neg, Real.cos_pi_div_four, Real.sin_neg, Real.sin_pi_div_four,
      exp_half_log_pi]
  -- Now: (↑√π * (↑(√2/2) + ↑(-(√2/2)) * I) / 2).re
  -- Compute directly using ofReal properties
  simp only [Complex.mul_re, Complex.add_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_ofNat_re]
  linarith [sqrt_pi_sqrt2_div4]

/-- Im((π/I)^{1/2}/2) = -√(π/2)/2. -/
lemma im_sqrt_pi_div_I_div_2 :
    (((↑Real.pi : ℂ) / Complex.I) ^ (1 / 2 : ℂ) / 2).im =
    -(Real.sqrt (Real.pi / 2) / 2) := by
  rw [cpow_pi_div_I_setup]
  rw [Real.cos_neg, Real.cos_pi_div_four, Real.sin_neg, Real.sin_pi_div_four,
      exp_half_log_pi]
  simp only [Complex.mul_im, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.div_ofNat_im]
  linarith [neg_sqrt_pi_sqrt2_div4]

/-! ## Section 9: Fresnel integral evaluation via Gaussian regularization -/

/-- **Fresnel cosine integral (Abel regularized)**: As ε → 0+,
    ∫₀^∞ exp(-εt²)cos(t²) dt → √(π/2)/2. -/
theorem fresnel_cos_eq :
    Tendsto (fun ε : ℝ =>
      ∫ t : ℝ in Ioi 0, Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 (Real.sqrt (Real.pi / 2) / 2)) := by
  have h_eq : ∀ ε : ℝ, 0 < ε →
      ∫ t : ℝ in Ioi 0, Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2) =
      (((↑Real.pi : ℂ) / ((↑ε : ℂ) + Complex.I)) ^ (1 / 2 : ℂ) / 2).re := by
    intro ε hε; rw [← gaussian_Ioi_re hε, gaussian_Ioi_eps_I hε]
  have h_lim : Tendsto (fun ε : ℝ =>
      (((↑Real.pi : ℂ) / ((↑ε : ℂ) + Complex.I)) ^ (1 / 2 : ℂ) / 2).re)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 (Real.sqrt (Real.pi / 2) / 2)) := by
    rw [← re_sqrt_pi_div_I_div_2]
    exact Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_sqrt_pi_div_eps_I.div_const 2)
  exact h_lim.congr' (by filter_upwards [self_mem_nhdsWithin] with ε hε; exact (h_eq ε hε).symm)

/-- **Fresnel sine integral (Abel regularized)**: As ε → 0+,
    ∫₀^∞ exp(-εt²)sin(t²) dt → √(π/2)/2. -/
theorem fresnel_sin_eq :
    Tendsto (fun ε : ℝ =>
      ∫ t : ℝ in Ioi 0, Real.exp (-ε * t ^ 2) * Real.sin (t ^ 2))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 (Real.sqrt (Real.pi / 2) / 2)) := by
  have h_eq : ∀ ε : ℝ, 0 < ε →
      ∫ t : ℝ in Ioi 0, Real.exp (-ε * t ^ 2) * Real.sin (t ^ 2) =
      -(((↑Real.pi : ℂ) / ((↑ε : ℂ) + Complex.I)) ^ (1 / 2 : ℂ) / 2).im := by
    intro ε hε
    have h1 := gaussian_Ioi_im hε
    rw [gaussian_Ioi_eps_I hε] at h1; linarith [h1]
  have h_lim : Tendsto (fun ε : ℝ =>
      -(((↑Real.pi : ℂ) / ((↑ε : ℂ) + Complex.I)) ^ (1 / 2 : ℂ) / 2).im)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 (Real.sqrt (Real.pi / 2) / 2)) := by
    rw [show Real.sqrt (Real.pi / 2) / 2 = -(-(Real.sqrt (Real.pi / 2) / 2)) by ring,
        ← im_sqrt_pi_div_I_div_2]
    exact (Complex.continuous_im.continuousAt.tendsto.comp
      (tendsto_sqrt_pi_div_eps_I.div_const 2)).neg
  exact h_lim.congr' (by filter_upwards [self_mem_nhdsWithin] with ε hε; exact (h_eq ε hε).symm)

/-! ## Section 10: Combined result -/

/-- The damped Fresnel cosine and sine integrals have the same limit √(π/2)/2. -/
theorem fresnel_cos_sin_eq_same_limit :
    Tendsto (fun ε : ℝ =>
      ∫ t : ℝ in Ioi 0, Real.exp (-ε * t ^ 2) * Real.cos (t ^ 2))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 (Real.sqrt (Real.pi / 2) / 2)) ∧
    Tendsto (fun ε : ℝ =>
      ∫ t : ℝ in Ioi 0, Real.exp (-ε * t ^ 2) * Real.sin (t ^ 2))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 (Real.sqrt (Real.pi / 2) / 2)) :=
  ⟨fresnel_cos_eq, fresnel_sin_eq⟩

end FresnelIntegrals
