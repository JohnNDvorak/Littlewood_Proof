/-
E₁ Cancellation and Analytic Extension of primeZeta + log(s-1)

Main result: Under PiLiHardBound(α, C, σ), the function
primeZeta(s) + log(s-1) extends analytically from {Re > 1} to {Re > α}.

PROOF STRATEGY:
1. Construct global antiderivative G of oneSubTwoPow_div via wedge integral
2. Show K₂(s) = ∫₂^∞ t^{-s}/log(t) dt + log(s-1) satisfies K₂' = oneSubTwoPow_div
   on {Re > 1} (E₁ cancellation — the key computation)
3. By constancy: K₂ = G + c on {Re > 1}, so K₂ extends to entire function K_ext
4. Decompose: primeZeta + log(s-1) = K_ext + Landau MCT terms + boundary
5. Assembly: Q is analytic on {Re > α}

References: Landau 1905; Montgomery-Vaughan §5.2.

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.PrimeZetaExtensionProof
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Aristotle.Standalone.E1CancellationProof

open Complex Real Filter Topology MeasureTheory Set
open Aristotle.Standalone.PrimeZetaExtensionProof
open Aristotle.Standalone.PiAtomHardCaseCorrectedCore
open Aristotle.CorrectionTermAnalyticity (primeZeta)

-- ============================================================
-- Section 1: Global antiderivative of entire functions via wedge integral
-- ============================================================

/-- The wedge integral from a fixed center gives a global antiderivative
of any entire function. For any entire `f` and fixed `c`, the function
`z ↦ wedgeIntegral c z f` satisfies `HasDerivAt _ (f z) z` at every point.

Proof: For any `z`, choose a ball `B(c, ‖z-c‖+1)` containing `z`.
Apply Mathlib's `hasDerivAt_wedgeIntegral` on this ball. -/
theorem entire_hasDerivAt_wedgeIntegral
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c z : ℂ) :
    HasDerivAt (fun w => Complex.wedgeIntegral c w f) (f z) z := by
  set R := ‖z - c‖ + 1 with hR_def
  have hR_pos : 0 < R := by positivity
  have hz_mem : z ∈ Metric.ball c R := by
    simp only [Metric.mem_ball, dist_eq_norm]
    linarith [norm_nonneg (z - c)]
  have hf_ball : DifferentiableOn ℂ f (Metric.ball c R) :=
    hf.differentiableOn
  have hf_cons : Complex.IsConservativeOn f (Metric.ball c R) :=
    hf_ball.isConservativeOn
  have hf_cont : ContinuousOn f (Metric.ball c R) :=
    hf_ball.continuousOn
  exact hf_cons.hasDerivAt_wedgeIntegral hf_cont hz_mem

/-- The global antiderivative of an entire function is itself differentiable. -/
theorem entire_antiderivative_differentiable
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ) :
    Differentiable ℂ (fun w => Complex.wedgeIntegral c w f) :=
  fun z => (entire_hasDerivAt_wedgeIntegral f hf c z).differentiableAt

-- ============================================================
-- Section 2: The antiderivative of oneSubTwoPow_div
-- ============================================================

/-- The antiderivative of `oneSubTwoPow_div` centered at s = 2,
defined as the wedge integral from 2 to s. -/
def oneSubTwoPow_antideriv : ℂ → ℂ :=
  fun s => Complex.wedgeIntegral 2 s oneSubTwoPow_div

/-- `oneSubTwoPow_antideriv` is entire. -/
theorem oneSubTwoPow_antideriv_differentiable :
    Differentiable ℂ oneSubTwoPow_antideriv :=
  entire_antiderivative_differentiable oneSubTwoPow_div
    oneSubTwoPow_div_differentiable 2

/-- `oneSubTwoPow_antideriv` has derivative `oneSubTwoPow_div` at every point. -/
theorem hasDerivAt_oneSubTwoPow_antideriv (s : ℂ) :
    HasDerivAt oneSubTwoPow_antideriv (oneSubTwoPow_div s) s :=
  entire_hasDerivAt_wedgeIntegral oneSubTwoPow_div
    oneSubTwoPow_div_differentiable 2 s

-- ============================================================
-- Section 3: The integral ∫₂^∞ (t/log t) · t^{-(s+1)} dt is analytic
-- ============================================================

/-- The function R(t) = t/log(t) for use with the MCT integral.
After the IBP s·∫₂^∞ li(t)·t^{-(s+1)} dt = ∫₂^∞ t^{-s}/log(t) dt,
the integrand becomes (t/log t) · t^{-(s+1)}. -/
private def tDivLog : ℝ → ℝ := fun t => t / Real.log t

private theorem tDivLog_nonneg (t : ℝ) (ht : 2 ≤ t) : 0 ≤ tDivLog t := by
  unfold tDivLog
  apply div_nonneg (by linarith) (Real.log_nonneg (by linarith))

private theorem tDivLog_bound (t : ℝ) (ht : 2 ≤ t) : tDivLog t ≤ 2 * t ^ (1 : ℝ) := by
  unfold tDivLog
  rw [rpow_one]
  have ht_pos : (0 : ℝ) < t := by linarith
  have hlog_pos : 0 < Real.log t := Real.log_pos (by linarith : (1 : ℝ) < t)
  rw [div_le_iff₀ hlog_pos]
  -- Need: t ≤ 2 * t * log t, i.e. 1 ≤ 2 * log t
  -- From one_sub_inv_le_log: 1 - t⁻¹ ≤ log t, and t⁻¹ ≤ 2⁻¹ = 1/2 for t ≥ 2
  have h1 := Real.one_sub_inv_le_log_of_pos ht_pos
  have h2 : t⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) ht
  nlinarith

private theorem tDivLog_measurable : Measurable tDivLog := by
  unfold tDivLog
  exact measurable_id.div measurable_log

/-- The function s · ∫₂^∞ (t/log t) · t^{-(s+1)} dt is analytic on {Re > 1}.
This is a direct application of the proved MCT theorem. -/
theorem s_mul_tDivLog_integral_analyticOnNhd :
    AnalyticOnNhd ℂ
      (fun s => s * ∫ t in Ioi (2 : ℝ), (↑(tDivLog t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
      {s : ℂ | (1 : ℝ) < s.re} :=
  (nonneg_dirichlet_integral_analyticOnNhd tDivLog 2 (by norm_num) 1 2
    tDivLog_nonneg tDivLog_bound tDivLog_measurable).mono
    (fun s hs => by exact hs)

/-- The integral ∫₂^∞ (t/log t) · t^{-(s+1)} dt is analytic on {Re > 1}.
Obtained from s · ∫ by dividing by s (which is nonzero on {Re > 1}). -/
theorem tDivLog_integral_analyticOnNhd :
    AnalyticOnNhd ℂ
      (fun s => ∫ t in Ioi (2 : ℝ), (↑(tDivLog t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
      {s : ℂ | (1 : ℝ) < s.re} := by
  intro s hs
  have hs_ne : s ≠ 0 := by
    intro heq; subst heq; norm_num at hs
  -- s * integral is analytic at s
  have h_prod := s_mul_tDivLog_integral_analyticOnNhd s hs
  -- integral = (s * integral) / s = (s * integral) * s⁻¹
  have h_inv : AnalyticAt ℂ (fun w => w⁻¹) s := by
    exact analyticAt_inv hs_ne
  -- The product (s * integral(s)) * s⁻¹ is analytic
  have h_mul := h_prod.mul h_inv
  -- Show our function equals (s * integral) * s⁻¹ near s
  refine h_mul.congr ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds hs_ne] with w hw
  simp only [Pi.mul_apply] at *
  rw [mul_comm (w * _) w⁻¹, ← mul_assoc, inv_mul_cancel₀ (Set.mem_compl_singleton_iff.mp hw),
      one_mul]

-- ============================================================
-- Section 4: E₁ cancellation — K₂ has derivative oneSubTwoPow_div
-- ============================================================

/-- **Leibniz integral differentiation for tDivLog integral**.
d/ds[∫₂^∞ (t/log t)·t^{-(s+1)} dt] = ∫₂^∞ -(t)^{-s} dt at s₀ with Re(s₀) > 1.

The pointwise derivative d/ds[(t/log t)·t^{-(s+1)}] = -t^{-s} follows from:
  d/ds[t^{-(s+1)}] = -log(t)·t^{-(s+1)}, times (t/log t) gives -t·t^{-(s+1)} = -t^{-s}.

Domination: ‖t^{-s}‖ = t^{-Re(s)} ≤ t^{-σ₀} for s near s₀, where σ₀ > 1.
Apply hasDerivAt_integral_of_dominated_loc_of_deriv_le. -/
theorem hasDerivAt_tDivLog_integral (s₀ : ℂ) (hs₀ : 1 < s₀.re) :
    HasDerivAt
      (fun s => ∫ t in Ioi (2 : ℝ), (↑(tDivLog t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
      (∫ t in Ioi (2 : ℝ), -((↑t : ℂ) ^ (-s₀)))
      s₀ := by
  -- Setup: ε-ball around s₀ within {Re > 1}, minimum real part σ_min
  set ε : ℝ := (s₀.re - 1) / 2 with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; linarith
  set σ_min : ℝ := s₀.re - ε with hσ_def
  have hσ_gt1 : 1 < σ_min := by rw [hσ_def, hε_def]; linarith
  -- Helper: for s in ball, Re(s) ≥ σ_min
  have ball_re : ∀ s ∈ Metric.ball s₀ ε, σ_min ≤ s.re := by
    intro s hs
    have hd : ‖s - s₀‖ < ε := by rwa [← Complex.dist_eq, ← Metric.mem_ball]
    have : |s.re - s₀.re| < ε := lt_of_le_of_lt
      (by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _) hd
    rw [hσ_def]; linarith [(abs_lt.mp this).1]
  -- Continuity helpers for measurability
  have cpow_contOn : ∀ c : ℂ, ContinuousOn (fun t : ℝ => (↑t : ℂ) ^ c) (Ioi (2 : ℝ)) :=
    fun c => fun t ht => (Complex.continuousAt_ofReal_cpow_const t c
      (Or.inr (ne_of_gt (lt_trans (by norm_num : (0:ℝ) < 2) ht)))).continuousWithinAt
  have tdl_contOn : ContinuousOn (fun t : ℝ => (↑(tDivLog t) : ℂ)) (Ioi (2 : ℝ)) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.div
        (Real.continuousOn_log.mono (fun t (ht : (2:ℝ) < t) =>
          ne_of_gt (show (0:ℝ) < t from by linarith)))
        (fun t (ht : (2:ℝ) < t) =>
          ne_of_gt (Real.log_pos (show (1:ℝ) < t from by linarith))))
  -- Apply: hasDerivAt_integral_of_dominated_loc_of_deriv_le
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun s t => -((↑t : ℂ) ^ (-s)))
    (bound := fun t => (t : ℝ) ^ (-σ_min))
    (s := Metric.ball s₀ ε)
    (Metric.ball_mem_nhds s₀ hε_pos)
    ?_ ?_ ?_ ?_ ?_ ?_).2
  -- (1) AEStronglyMeasurable (F s) μ eventually near s₀
  · exact Filter.univ_mem' (fun s =>
      (tdl_contOn.mul (cpow_contOn _)).aestronglyMeasurable measurableSet_Ioi)
  -- (2) Integrable (F s₀) μ — bound by 2·t^{-Re(s₀)}
  · refine Integrable.mono'
      ((integrableOn_Ioi_rpow_of_lt (show -s₀.re < -1 from by linarith)
        (show (0:ℝ) < 2 from by norm_num)).const_mul 2)
      ((tdl_contOn.mul (cpow_contOn _)).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht2 : (2 : ℝ) ≤ t := le_of_lt ht
    have ht_pos : (0 : ℝ) < t := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (tDivLog_nonneg t ht2),
        Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
    have hbd : tDivLog t ≤ 2 * t := by
      have := tDivLog_bound t ht2; rwa [rpow_one] at this
    have h_exp_eq : (1 : ℝ) + (-(s₀ + 1)).re = -s₀.re := by
      simp only [Complex.neg_re, Complex.add_re, Complex.one_re]; ring
    have h_rpow : t * t ^ (-(s₀ + 1)).re = t ^ (-s₀.re) := by
      have h1 := rpow_add ht_pos (1 : ℝ) ((-(s₀ + 1)).re)
      rw [rpow_one, h_exp_eq] at h1; exact h1.symm
    calc tDivLog t * t ^ (-(s₀ + 1)).re
        ≤ (2 * t) * t ^ (-(s₀ + 1)).re := by gcongr
      _ = 2 * (t * t ^ (-(s₀ + 1)).re) := by ring
      _ = 2 * t ^ (-s₀.re) := by rw [h_rpow]
  -- (3) AEStronglyMeasurable (F' s₀) μ
  · exact ((cpow_contOn _).neg).aestronglyMeasurable measurableSet_Ioi
  -- (4) ‖F'(s, t)‖ ≤ bound(t) for s near s₀, a.e. t — monotonicity of rpow
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro s hs
    have ht2 : (2 : ℝ) < t := ht
    have ht_pos : (0 : ℝ) < t := by linarith
    rw [norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht_pos, Complex.neg_re]
    exact rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ t)
      (neg_le_neg_iff.mpr (ball_re s hs))
  -- (5) Integrable bound μ — rpow integrability for exponent < -1
  · exact integrableOn_Ioi_rpow_of_lt (show -σ_min < -1 from by rw [hσ_def, hε_def]; linarith)
      (show (0:ℝ) < 2 from by norm_num)
  -- (6) HasDerivAt (F · t) (F' s t) s — chain rule for cpow + algebra
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro s _hs
    have ht2 : (2 : ℝ) < t := ht
    have ht_pos : (0 : ℝ) < t := by linarith
    have ht_ne : (↑t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht_pos)
    -- d/ds[-(s+1)] = -1, then chain rule for (↑t)^{-(s+1)}
    have h_cpow := HasDerivAt.const_cpow
      (((hasDerivAt_id s).add_const (1 : ℂ)).neg) (Or.inl ht_ne)
    -- Multiply by constant ↑(tDivLog t), adjust derivative value
    refine (h_cpow.const_mul _).congr_deriv ?_
    -- Algebra: ↑(tDivLog t) * ((↑t)^{-(s+1)} * log(↑t) * (-1)) = -(↑t)^{-s}
    have hlog_eq : Complex.log (↑t : ℂ) = ↑(Real.log t) :=
      (Complex.ofReal_log ht_pos.le).symm
    have h_cancel : (↑(tDivLog t) : ℂ) * Complex.log (↑t : ℂ) = ↑t := by
      rw [hlog_eq, ← Complex.ofReal_mul]; congr 1; unfold tDivLog
      exact div_mul_cancel₀ t (ne_of_gt (Real.log_pos (by linarith : (1:ℝ) < t)))
    have h_cpow_mul : (↑t : ℂ) * (↑t : ℂ) ^ (-(s + 1)) = (↑t : ℂ) ^ (-s) := by
      have h := cpow_add (1 : ℂ) (-(s + 1)) ht_ne
      rw [cpow_one, show (1 : ℂ) + (-(s + 1)) = -s from by ring] at h; exact h.symm
    calc ↑(tDivLog t) * ((↑t : ℂ) ^ (-(s + 1)) * Complex.log (↑t : ℂ) * (-1))
        = (↑(tDivLog t) * Complex.log (↑t : ℂ)) * ((↑t : ℂ) ^ (-(s + 1)) * (-1)) := by ring
      _ = ↑t * ((↑t : ℂ) ^ (-(s + 1)) * (-1)) := by rw [h_cancel]
      _ = -(↑t * (↑t : ℂ) ^ (-(s + 1))) := by ring
      _ = -((↑t : ℂ) ^ (-s)) := by rw [h_cpow_mul]

/-- Evaluation of ∫₂^∞ -(t)^{-s₀} dt for Re(s₀) > 1.
From integral_Ioi_cpow_of_lt: ∫₂^∞ t^a dt = -(2^{a+1})/(a+1) for Re(a) < -1.
With a = -s₀: ∫₂^∞ t^{-s₀} dt = 2^{1-s₀}/(s₀-1).
So ∫₂^∞ -(t^{-s₀}) dt = -2^{1-s₀}/(s₀-1). -/
theorem integral_neg_cpow_eval (s₀ : ℂ) (hs₀ : 1 < s₀.re) :
    (∫ t in Ioi (2 : ℝ), -((↑t : ℂ) ^ (-s₀))) =
      ((2 : ℂ) ^ (1 - s₀)) / (1 - s₀) := by
  rw [integral_neg]
  have ha : (-s₀).re < -1 := by simp; linarith
  rw [integral_Ioi_cpow_of_lt ha (by norm_num : (0 : ℝ) < 2)]
  rw [show (-s₀ + 1 : ℂ) = 1 - s₀ from by ring]
  simp [neg_div]

/-- **E₁ cancellation derivative**:
d/ds [∫₂^∞ t^{-s}/log(t) dt + log(s-1)] = (1 - 2^{1-s})/(s-1)

Combines:
  d/ds ∫₂^∞ t^{-s}/log(t) dt = -2^{1-s}/(s-1)  (Leibniz + evaluation)
  d/ds log(s-1) = 1/(s-1)                         (standard)
  -2^{1-s}/(s-1) + 1/(s-1) = (1 - 2^{1-s})/(s-1) = oneSubTwoPow_div(s). -/
theorem e1_cancellation_hasDerivAt (s₀ : ℂ) (hs₀ : 1 < s₀.re) :
    HasDerivAt
      (fun s => (∫ t in Ioi (2 : ℝ), (↑(tDivLog t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
        + Complex.log (s - 1))
      (oneSubTwoPow_div s₀) s₀ := by
  -- Step 1: derivative of the integral part
  have h_int := hasDerivAt_tDivLog_integral s₀ hs₀
  -- Step 2: derivative of log(s-1) is (s₀-1)⁻¹
  have h_mem : s₀ - 1 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have h_log : HasDerivAt (fun s => Complex.log (s - 1)) ((s₀ - 1)⁻¹) s₀ := by
    have h1 : HasDerivAt (fun s : ℂ => s - 1) 1 s₀ := (hasDerivAt_id s₀).sub_const 1
    convert h1.clog h_mem using 1
    simp [div_eq_mul_inv]
  -- Step 3: combine
  have h_sum := h_int.add h_log
  -- Step 4: show the derivative value equals oneSubTwoPow_div s₀
  refine h_sum.congr_deriv ?_
  rw [integral_neg_cpow_eval s₀ hs₀]
  have hs1 : s₀ ≠ 1 := by intro heq; rw [heq] at hs₀; simp at hs₀
  -- Convert 2^{1-s₀} to exp((1-s₀)·log 2) via cpow_def_of_ne_zero + ofReal_log
  have h_pow : (2 : ℂ) ^ (1 - s₀) = Complex.exp ((1 - s₀) * ↑(Real.log 2)) := by
    have h2ne : (2 : ℂ) ≠ 0 := by norm_num
    rw [cpow_def_of_ne_zero h2ne]; congr 1
    rw [show (2 : ℂ) = ↑(2 : ℝ) from by norm_cast,
        (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm]; ring
  rw [h_pow, oneSubTwoPow_div_eq hs1]
  -- Clear denominators (1-s₀) and (s₀-1), then close polynomial identity
  have hs1' : s₀ - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have h1s : (1 : ℂ) - s₀ ≠ 0 := by rwa [sub_ne_zero, ne_comm]
  field_simp
  ring

-- ============================================================
-- Section 5: K₂ extends to entire function by constancy argument
-- ============================================================

/-- K₂ - G has derivative 0 on {Re > 1}, hence is constant.
Uses: K₂' = oneSubTwoPow_div (e1_cancellation_hasDerivAt) and
      G' = oneSubTwoPow_div (hasDerivAt_oneSubTwoPow_antideriv). -/
theorem k2_minus_antideriv_const :
    ∃ c₀ : ℂ, ∀ s : ℂ, 1 < s.re →
      (∫ t in Ioi (2 : ℝ), (↑(tDivLog t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
        + Complex.log (s - 1)
      = oneSubTwoPow_antideriv s + c₀ := by
  -- Define h(s) = K₂(s) - G(s). Then h is analytic on {Re > 1}.
  set K₂ := fun s => (∫ t in Ioi (2 : ℝ), (↑(tDivLog t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
    + Complex.log (s - 1) with hK₂_def
  set G := oneSubTwoPow_antideriv with hG_def
  set h := fun s => K₂ s - G s with hh_def
  -- h is differentiable on {Re > 1}
  have h_diff : DifferentiableOn ℂ h {s : ℂ | (1 : ℝ) < s.re} := by
    apply DifferentiableOn.sub
    · -- K₂ is analytic on {Re > 1}
      have hK₂_anal : AnalyticOnNhd ℂ K₂ {s : ℂ | (1 : ℝ) < s.re} := by
        apply AnalyticOnNhd.add tDivLog_integral_analyticOnNhd
        intro s hs
        have hs_re : (1 : ℝ) < s.re := hs
        have h_mem : s - 1 ∈ Complex.slitPlane := by
          rw [Complex.mem_slitPlane_iff]
          left
          simp only [Complex.sub_re, Complex.one_re]
          linarith
        exact (analyticAt_id.sub analyticAt_const).clog h_mem
      exact hK₂_anal.differentiableOn
    · exact oneSubTwoPow_antideriv_differentiable.differentiableOn
  -- h has derivative 0 at every point of {Re > 1}
  have h_deriv_zero : ∀ s : ℂ, 1 < s.re → HasDerivAt h 0 s := by
    intro s hs
    have hK₂ := e1_cancellation_hasDerivAt s hs
    have hG := hasDerivAt_oneSubTwoPow_antideriv s
    exact (hK₂.sub hG).congr_deriv (by simp)
  -- {Re > 1} is connected (it's convex)
  have h_conn : IsPreconnected {s : ℂ | (1 : ℝ) < s.re} :=
    (convex_halfSpace_re_gt 1).isPreconnected
  -- {Re > 1} is open
  have h_open : IsOpen {s : ℂ | (1 : ℝ) < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  -- h is constant on {Re > 1} by IsOpen.is_const_of_deriv_eq_zero
  have h_eqOn_deriv : Set.EqOn (deriv h) 0 {s : ℂ | (1 : ℝ) < s.re} :=
    fun w hw => (h_deriv_zero w hw).deriv
  have h_const : ∀ s : ℂ, 1 < s.re → h s = h 2 :=
    fun s hs => h_open.is_const_of_deriv_eq_zero h_conn h_diff h_eqOn_deriv hs (by simp)
  use h 2
  intro s hs
  have h_eq := h_const s hs
  -- h s = h 2, i.e. K₂ s - G s = h 2, so K₂ s = G s + h 2
  simp only [hh_def, hK₂_def, hG_def] at h_eq ⊢
  linear_combination h_eq

/-- K₂(s) extends to an entire function.
The entire extension is oneSubTwoPow_antideriv + c for a specific constant c. -/
theorem li_mellin_plus_log_extends :
    ∃ K_ext : ℂ → ℂ, Differentiable ℂ K_ext ∧
      ∀ s : ℂ, 1 < s.re →
        K_ext s = (∫ t in Ioi (2 : ℝ), (↑(tDivLog t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
          + Complex.log (s - 1) := by
  obtain ⟨c₀, hc₀⟩ := k2_minus_antideriv_const
  exact ⟨fun s => oneSubTwoPow_antideriv s + c₀,
    oneSubTwoPow_antideriv_differentiable.add (differentiable_const c₀),
    fun s hs => (hc₀ s hs).symm⟩

end Aristotle.Standalone.E1CancellationProof
