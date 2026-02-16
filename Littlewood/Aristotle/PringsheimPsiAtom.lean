/-
Landau's non-negative Dirichlet integral theorem for ψ (Pringsheim atom).

Given a one-sided bound σ*(ψ(x)-x) ≤ C*x^α with 1/2 < α, construct a function
G analytic on {Re(s) > α} matching the formula
  G(s) = s*C/(s-α) + σ*s/(s-1) + σ*ζ'/ζ(s)
on {Re(s) > 1}.

## Proof Strategy

1. **Generating function**: g(t) = C*t^α + σ*(t - ψ(t)) ≥ 0 eventually.
2. **Convergence for Re > 1**: ∫₁^∞ g(t)*t^{-(s+1)} converges (from g = O(t)).
3. **Formula on Re > 1**: The integral splits into known Mellin transforms.
4. **MCT push to Re > α**: The corrected formula (ZetaPoleCancellation) is
   continuous at every real σ₀ > α. Monotone convergence on the non-negative
   tail forces the integral to converge at σ₀.
5. **Analyticity**: Parametric differentiation gives DifferentiableOn on {Re > α},
   hence AnalyticOnNhd by Cauchy integral theory.

## References

* Landau, "Über einen Satz von Tschebyschef" (1905), Satz 15
* Hardy-Riesz, "The General Theory of Dirichlet's Series", Ch. 1

SORRY COUNT: 1 (convergence — in progress)

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.PringsheimAtoms
import Littlewood.Aristotle.MellinIntegralFormulas
import Littlewood.Aristotle.PsiIntegralRepresentation
import Littlewood.Aristotle.ZetaPoleCancellation
import Littlewood.Basic.ChebyshevFunctions

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.PringsheimPsiAtom

open Complex Real Filter Topology MeasureTheory Set

/-! ## The generating function g and basic properties -/

/-- The generating function g(t) = C*t^α + σ*(t - ψ(t)). -/
def genFun (C : ℝ) (α : ℝ) (σ : ℝ) (t : ℝ) : ℝ :=
  C * t ^ α + σ * (t - chebyshevPsi t)

/-- g(t) ≥ 0 for large t, from the one-sided bound. -/
theorem genFun_nonneg_eventually (α : ℝ) (C : ℝ) (hC : 0 < C)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hbound : ∀ᶠ x in atTop, σ * (chebyshevPsi x - x) ≤ C * x ^ α) :
    ∀ᶠ t in atTop, (0 : ℝ) ≤ genFun C α σ t := by
  exact PringsheimAtoms.g_nonneg_eventually α C hC σ hσ hbound

/-- g(t) ≤ D*t for some constant D and all t ≥ 1.
    From ψ(t) ≥ 0 and ψ(t) ≤ 6t and C*t^α ≤ C*t for t ≥ 1, α ≤ 1. -/
theorem genFun_le_linear (C : ℝ) (hC : 0 < C) (α : ℝ) (hα : α ≤ 1)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 1 ≤ t → |genFun C α σ t| ≤ D * t := by
  refine ⟨C + 7, by linarith, fun t ht => ?_⟩
  unfold genFun
  have hψ_nn : 0 ≤ chebyshevPsi t := by
    unfold chebyshevPsi; exact Chebyshev.psi_nonneg _
  have hψ_le : chebyshevPsi t ≤ 6 * t := ChebyshevExt.chebyshevPsi_le t ht
  have ht_pos : 0 < t := by linarith
  have htα : t ^ α ≤ t := by
    calc t ^ α ≤ t ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le ht hα
        _ = t := Real.rpow_one t
  rcases hσ with rfl | rfl
  · -- σ = 1: g = C*t^α + t - ψ ≤ C*t + t ≤ (C+7)*t
    have h1 : 0 ≤ C * t ^ α := mul_nonneg hC.le (rpow_nonneg (by linarith) _)
    rw [abs_le]; constructor
    · nlinarith  -- g ≥ 0 - 5t ≥ -(C+7)*t
    · calc C * t ^ α + 1 * (t - chebyshevPsi t) ≤ C * t + t := by nlinarith
        _ ≤ (C + 7) * t := by nlinarith
  · -- σ = -1: g = C*t^α - t + ψ ≤ C*t - t + 6t = (C+5)*t ≤ (C+7)*t
    -- and g ≥ -(C*t^α + t) ≥ -(C+1)*t ≥ -(C+7)*t
    rw [abs_le]; constructor
    · -- Lower bound: g ≥ -(C+7)*t. Since C*t^α ≥ 0, ψ ≥ 0, and t ≥ 0:
      have h1 : 0 ≤ C * t ^ α := mul_nonneg hC.le (rpow_nonneg (by linarith) _)
      nlinarith
    · calc C * t ^ α + (-1) * (t - chebyshevPsi t) = C * t ^ α - t + chebyshevPsi t := by ring
        _ ≤ C * t + 6 * t := by nlinarith
        _ ≤ (C + 7) * t := by nlinarith

/-! ## Integrability helpers for Re > 1

These are building blocks for the formula verification. Each shows that a
component of the generating function, multiplied by t^{-(s+1)}, is integrable
on (1, ∞) when Re(s) is large enough. -/

/-- t^α * t^{-(s+1)} is integrable on Ioi 1 when Re(s) > α. -/
private theorem integrableOn_rpow_cpow (α : ℝ) (s : ℂ) (hs : α < s.re) :
    IntegrableOn (fun t : ℝ => (↑t : ℂ) ^ (↑α : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
      (Ioi (1 : ℝ)) := by
  have hre : ((↑α : ℂ) - s - 1).re < -1 := by
    simp only [sub_re, ofReal_re, one_re]; linarith
  exact (integrableOn_Ioi_cpow_of_lt hre one_pos).congr_fun
    (fun t ht => by
      have ht_ne : (↑t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt (by linarith [show (1:ℝ) < t from ht]))
      rw [← cpow_add _ _ ht_ne]; congr 1; ring)
    measurableSet_Ioi

/-- t * t^{-(s+1)} is integrable on Ioi 1 when Re(s) > 1. -/
private theorem integrableOn_x_cpow (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (↑t : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
      (Ioi (1 : ℝ)) := by
  have hre : (-s).re < -1 := by simp; linarith
  exact (integrableOn_Ioi_cpow_of_lt hre one_pos).congr_fun
    (fun t ht => by
      have ht_ne : (↑t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt (by linarith [show (1:ℝ) < t from ht]))
      rw [show -s = (1 : ℂ) + (-(s + 1)) from by ring, cpow_add _ _ ht_ne, cpow_one])
    measurableSet_Ioi

/-- ψ(t) * t^{-(s+1)} is integrable on Ioi 1 when Re(s) > 1.
    From |ψ(t)| ≤ 6t and integrability of t * t^{-(s+1)}. -/
private theorem integrableOn_psi_cpow (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (↑(chebyshevPsi t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
      (Ioi (1 : ℝ)) := by
  -- Comparison: ‖ψ(t) * t^{-(s+1)}‖ ≤ ‖6 * (t * t^{-(s+1)})‖ and the latter is integrable
  refine Integrable.mono ((integrableOn_x_cpow s hs).const_mul (6 : ℂ)) ?_ ?_
  · -- AEStronglyMeasurable of ψ(t) * t^{-(s+1)} on Ioi 1
    apply AEStronglyMeasurable.mul
    · exact (measurable_ofReal.comp Chebyshev.psi_mono.measurable).aestronglyMeasurable
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro t ht
      exact (continuousAt_ofReal_cpow_const t (-(s + 1))
        (Or.inr (ne_of_gt (lt_trans zero_lt_one ht)))).continuousWithinAt
  · -- Norm bound: ‖ψ(t) * t^{-(s+1)}‖ ≤ ‖6 * (t * t^{-(s+1)})‖ for t > 1
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [mem_Ioi] at ht
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
    -- Goal: |ψ(t)| * ‖(↑t)^{-(s+1)}‖ ≤ 6 * (|t| * ‖(↑t)^{-(s+1)}‖)
    have h_psi_le : |chebyshevPsi t| ≤ 6 * |t| :=
      calc |chebyshevPsi t| = chebyshevPsi t :=
              abs_of_nonneg (Chebyshev.psi_nonneg t)
        _ ≤ 6 * t := ChebyshevExt.chebyshevPsi_le t (by linarith)
        _ = 6 * |t| := by congr 1; exact (abs_of_pos (by linarith : (0:ℝ) < t)).symm
    exact (mul_le_mul_of_nonneg_right h_psi_le (norm_nonneg _)).trans_eq (by ring)

/-! ## Cast lemma connecting ψ to von Mangoldt sums -/

open ArithmeticFunction Finset in
private theorem chebyshevPsi_eq_sum_vonMangoldt (t : ℝ) :
    chebyshevPsi t = ∑ k ∈ Icc 1 ⌊t⌋₊, vonMangoldt k := by
  unfold chebyshevPsi Chebyshev.psi
  congr 1

open ArithmeticFunction Finset in
private theorem chebyshevPsi_ofReal_eq_vonMangoldt_sum (t : ℝ) :
    (↑(chebyshevPsi t) : ℂ) =
      ∑ k ∈ Icc 1 ⌊t⌋₊, (↑(vonMangoldt k) : ℂ) := by
  rw [chebyshevPsi_eq_sum_vonMangoldt]
  push_cast; rfl

/-! ## The Dirichlet integral H(s) = ∫₁^∞ g(t) * t^{-(s+1)} dt

For Re(s) > 1: converges absolutely (from g = O(t)).
For Re(s) > α: converges absolutely (from MCT + corrected formula). -/

/-- The Dirichlet integral of the generating function (complex-valued). -/
def dirichletIntegral (C : ℝ) (α : ℝ) (σ_sign : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), (↑(genFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))

/-- The witness function G(s) = s * H(s). -/
def witnessG (C : ℝ) (α : ℝ) (σ_sign : ℝ) (s : ℂ) : ℂ :=
  s * dirichletIntegral C α σ_sign s

/-! ## Key Lemma 1: Integral convergence for Re > α

The core of Landau's argument. For real σ₀ > α, the integral converges,
proved by monotone convergence: as σ ↓ σ₀ (from σ > 1), the non-negative
tail integral increases but stays bounded by the corrected formula.

Then for complex s with Re(s) > α, absolute convergence follows by comparison
with the real integral at Re(s). -/

/-- The Dirichlet integral of g converges absolutely for Re(s) > α. -/
theorem dirichletIntegral_integrableOn (C : ℝ) (hC : 0 < C) (α : ℝ)
    (hα : 1 / 2 < α) (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (s : ℂ) (hs : α < s.re) :
    IntegrableOn (fun t => (↑(genFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
      (Ioi 1) := by
  by_cases h1 : 1 < s.re
  · -- Re(s) > 1: split genFun into three integrable components
    have h_rpow := integrableOn_rpow_cpow α s hs
    have h_x := integrableOn_x_cpow s h1
    have h_psi := integrableOn_psi_cpow s h1
    have h3 : IntegrableOn (fun t : ℝ =>
        (↑C : ℂ) * ((↑t : ℂ) ^ (↑α : ℂ) * (↑t : ℂ) ^ (-(s + 1))) +
        (↑σ_sign : ℂ) * ((↑t : ℂ) * (↑t : ℂ) ^ (-(s + 1))) -
        (↑σ_sign : ℂ) * ((↑(chebyshevPsi t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))))
        (Ioi (1 : ℝ)) :=
      ((h_rpow.const_mul _).add (h_x.const_mul _)).sub (h_psi.const_mul _)
    exact h3.congr (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [mem_Ioi] at ht
      simp only [genFun]
      push_cast [ofReal_cpow (le_of_lt (lt_trans zero_lt_one ht))]
      ring)
  · -- α < Re(s) ≤ 1: requires Landau's abscissa of convergence theorem.
    -- The non-negative generating function g ≥ 0 for large t, combined with
    -- the corrected formula (ZetaPoleCancellation) providing analytic continuation
    -- along the real axis, and Pringsheim's theorem (PringsheimTheorem.lean) on
    -- non-negative Taylor coefficients, forces convergence for all Re(s) > α.
    -- See Landau, "Über einen Satz von Tschebyschef" (1905), Satz 15.
    push_neg at h1
    sorry

/-! ## Key Lemma 2: Analyticity on {Re > α} -/

/-- The witness function G is analytic on {Re > α}.
Proved by parametric differentiation under the integral sign
(using `hasDerivAt_integral_of_dominated_loc_of_deriv_le`) combined with
`DifferentiableOn.analyticOnNhd` (Cauchy integral formula). -/
theorem witnessG_analyticOnNhd (C : ℝ) (hC : 0 < C) (α : ℝ)
    (hα : 1 / 2 < α) (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α) :
    AnalyticOnNhd ℂ (witnessG C α σ_sign) {s : ℂ | α < s.re} := by
  -- Strategy: DifferentiableOn ℂ on open set → AnalyticOnNhd (Cauchy integral)
  have hopen : IsOpen {s : ℂ | α < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ hopen
  -- Show DifferentiableWithinAt at each point
  intro s₀ hs₀
  simp only [mem_setOf_eq] at hs₀
  apply DifferentiableAt.differentiableWithinAt
  -- witnessG = id * dirichletIntegral
  show DifferentiableAt ℂ (fun s => s * dirichletIntegral C α σ_sign s) s₀
  apply DifferentiableAt.mul differentiableAt_id
  -- Need: DifferentiableAt ℂ (dirichletIntegral C α σ_sign) s₀
  -- Set up parametric differentiation
  set δ : ℝ := (s₀.re - α) / 3 with hδ_def
  have hδ : 0 < δ := div_pos (by linarith) (by norm_num : (0 : ℝ) < 3)
  have hσ₂ : α < s₀.re - 2 * δ := by rw [hδ_def]; linarith
  set μ := MeasureTheory.Measure.restrict MeasureTheory.volume (Ioi (1 : ℝ))
  -- Abbreviation for the generating function integral
  let integ := dirichletIntegral_integrableOn C hC α hα σ_sign hσ hbound
  -- dirichletIntegral equals ∫ F s t ∂μ
  suffices h : DifferentiableAt ℂ (fun s => ∫ t,
      (↑(genFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)) ∂μ) s₀ by
    convert h using 1
  -- h1: AEStronglyMeasurable of integrand for z near s₀
  have h1 : ∀ᶠ z in 𝓝 s₀, AEStronglyMeasurable
      (fun t => (↑(genFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(z + 1))) μ := by
    filter_upwards [hopen.mem_nhds hs₀] with z hz
    exact (integ z hz).aestronglyMeasurable
  -- h2: Integrable at s₀
  have h2 : Integrable
      (fun t => (↑(genFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s₀ + 1))) μ :=
    integ s₀ hs₀
  -- h3: AEStronglyMeasurable of s-derivative at s₀
  -- F'(s,t) = g(t) * t^{-(s+1)} * (-log t) = F(s,t) * (-log t)
  have h3 : AEStronglyMeasurable (fun t =>
      (↑(genFun C α σ_sign t) : ℂ) * ((↑t : ℂ) ^ (-(s₀ + 1)) *
        (-(↑(Real.log t) : ℂ)))) μ := by
    -- First prove -ofReal(log t) is measurable on μ
    have h_log_meas : AEStronglyMeasurable (fun t : ℝ => -(↑(Real.log t) : ℂ)) μ :=
      ContinuousOn.aestronglyMeasurable (fun t ht => by
        have ht' : 0 < t := lt_trans zero_lt_one (mem_Ioi.mp ht)
        exact (continuous_neg.continuousAt.comp
          (Complex.continuous_ofReal.continuousAt.comp
            (Real.continuousAt_log (ne_of_gt ht')))).continuousWithinAt)
        measurableSet_Ioi
    -- F(s₀, t) * (-log t) is measurable, then regroup by ring
    exact (h2.aestronglyMeasurable.mul h_log_meas).congr
      (by filter_upwards with t; simp only [Pi.mul_apply]; ring)
  -- h4: uniform derivative bound: ‖F'(z,t)‖ ≤ bnd(t) for z ∈ ball s₀ δ
  have h4 : ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball s₀ δ,
      ‖(↑(genFun C α σ_sign t) : ℂ) * ((↑t : ℂ) ^ (-(z + 1)) *
        (-(↑(Real.log t) : ℂ)))‖ ≤
      (1 / δ) * ‖(↑(genFun C α σ_sign t) : ℂ) *
        (↑t : ℂ) ^ (-((↑(s₀.re - 2 * δ) : ℂ) + 1))‖ := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht z hz => ?_
    simp only [mem_Ioi] at ht
    have ht_pos : 0 < t := by linarith
    have ht1 : 1 ≤ t := by linarith
    -- Simplify all norms uniformly
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      norm_cpow_eq_rpow_re_of_pos ht_pos, neg_re, add_re, one_re, ofReal_re]
    -- After simp, goal is:
    -- |g| * (t^{-(z.re+1)} * |log t|) ≤ 1/δ * (|g| * t^{-(s₀.re-2δ+1)})
    -- Step 1: |log t| = log t (since t > 1)
    rw [abs_of_pos (Real.log_pos ht)]
    -- Step 2: log t ≤ t^δ/δ
    have h_log_le : Real.log t ≤ t ^ δ / δ := Real.log_le_rpow_div ht_pos.le hδ
    -- Step 3: exponent bound from ball membership
    have h_re : -(z.re + 1) + δ ≤ -(s₀.re - 2 * δ + 1) := by
      rw [Metric.mem_ball] at hz
      have h_abs : |z.re - s₀.re| ≤ δ := by
        calc |z.re - s₀.re| = |(z - s₀).re| := by rw [sub_re]
          _ ≤ ‖z - s₀‖ := Complex.abs_re_le_norm _
          _ ≤ δ := hz.le
      linarith [(abs_le.mp h_abs).1]
    calc |genFun C α σ_sign t| * (t ^ (-(z.re + 1)) * Real.log t)
        ≤ |genFun C α σ_sign t| * (t ^ (-(z.re + 1)) * (t ^ δ / δ)) := by
          gcongr
      _ = |genFun C α σ_sign t| * (t ^ (-(z.re + 1) + δ) / δ) := by
          congr 1; rw [← mul_div_assoc, ← Real.rpow_add ht_pos]
      _ ≤ |genFun C α σ_sign t| * (t ^ (-(s₀.re - 2 * δ + 1)) / δ) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact div_le_div_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le ht1 h_re) hδ.le
      _ = 1 / δ * (|genFun C α σ_sign t| * t ^ (-(s₀.re - 2 * δ + 1))) := by ring
  -- h5: bound is integrable
  have h5 : Integrable (fun t =>
      (1 / δ) * ‖(↑(genFun C α σ_sign t) : ℂ) *
        (↑t : ℂ) ^ (-((↑(s₀.re - 2 * δ) : ℂ) + 1))‖) μ := by
    have hint : IntegrableOn (fun t => (↑(genFun C α σ_sign t) : ℂ) *
        (↑t : ℂ) ^ (-((↑(s₀.re - 2 * δ) : ℂ) + 1))) (Ioi (1 : ℝ)) :=
      integ (↑(s₀.re - 2 * δ) : ℂ) (by simp [Complex.ofReal_re]; exact hσ₂)
    exact hint.norm.const_mul (1 / δ)
  -- h6: HasDerivAt of integrand in s for z ∈ ball s₀ δ
  have h6 : ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball s₀ δ,
      HasDerivAt (fun s => (↑(genFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)))
        ((↑(genFun C α σ_sign t) : ℂ) * ((↑t : ℂ) ^ (-(z + 1)) *
          (-(↑(Real.log t) : ℂ)))) z := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht z _ => ?_
    simp only [mem_Ioi] at ht
    have ht' : (↑t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one ht))
    -- Derivative of t^{-(s+1)} in s is t^{-(s+1)} * log(t) * (-1)
    have hderiv : HasDerivAt (fun s => (↑t : ℂ) ^ (-(s + 1)))
        ((↑t : ℂ) ^ (-(z + 1)) * (↑(Real.log t) : ℂ) * (-1)) z := by
      have h_neg_add : HasDerivAt (fun s => -(s + 1)) (-1) z :=
        ((hasDerivAt_id z).add_const 1).neg
      convert h_neg_add.const_cpow (Or.inl ht') using 1
      rw [Complex.ofReal_log (le_of_lt (lt_trans zero_lt_one ht))]
    -- Multiply by constant g(t)
    convert (hasDerivAt_const z (↑(genFun C α σ_sign t) : ℂ)).mul hderiv using 1
    ring
  -- Apply the parametric differentiation theorem
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s₀ hδ) h1 h2 h3 h4 h5 h6).2.differentiableAt

/-! ## Key Lemma 3: Formula verification on {Re > 1}

For Re(s) > 1, the integral splits as:
  s * ∫ g(t) * t^{-(s+1)} = s*C/(s-α) + σ*s/(s-1) + σ*ζ'/ζ(s)

The proof splits the Dirichlet integral into three Mellin transforms,
applies mellin_rpow_alpha, mellin_x, and neg_zeta_logDeriv_eq_integral. -/

/-- The Dirichlet integral splits into three known integrals for Re > 1. -/
private theorem dirichletIntegral_eq_split (C : ℝ) (α : ℝ) (σ_sign : ℝ)
    (s : ℂ) (hs : 1 < s.re) (_hα : 1 / 2 < α) (hαs : α < s.re) :
    dirichletIntegral C α σ_sign s =
      (↑C : ℂ) * (∫ t in Ioi (1 : ℝ), (↑t : ℂ) ^ (↑α : ℂ) * (↑t : ℂ) ^ (-(s + 1))) +
      (↑σ_sign : ℂ) * (∫ t in Ioi (1 : ℝ), (↑t : ℂ) * (↑t : ℂ) ^ (-(s + 1))) -
      (↑σ_sign : ℂ) * (∫ t in Ioi (1 : ℝ), (↑(chebyshevPsi t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))) := by
  unfold dirichletIntegral
  -- Integrability of each piece
  have h1 := integrableOn_rpow_cpow α s hαs
  have h2 := integrableOn_x_cpow s hs
  have h3 := integrableOn_psi_cpow s hs
  -- Rewrite integrand to the sum of three parts
  have h_eq : ∀ t ∈ Ioi (1 : ℝ),
      (↑(genFun C α σ_sign t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)) =
      (↑C : ℂ) * ((↑t : ℂ) ^ (↑α : ℂ) * (↑t : ℂ) ^ (-(s + 1))) +
      (↑σ_sign : ℂ) * ((↑t : ℂ) * (↑t : ℂ) ^ (-(s + 1))) -
      (↑σ_sign : ℂ) * ((↑(chebyshevPsi t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))) := by
    intro t ht
    unfold genFun
    push_cast [ofReal_cpow (lt_trans zero_lt_one ht).le]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h_eq]
  -- Provide integrability with explicit function types to avoid Pi.add
  have h_ab : IntegrableOn (fun (x : ℝ) =>
      (↑C : ℂ) * ((↑x : ℂ) ^ (↑α : ℂ) * (↑x : ℂ) ^ (-(s + 1))) +
      (↑σ_sign : ℂ) * ((↑x : ℂ) * (↑x : ℂ) ^ (-(s + 1)))) (Ioi (1 : ℝ)) :=
    (h1.const_mul _).add (h2.const_mul _)
  have h_c : IntegrableOn (fun (x : ℝ) =>
      (↑σ_sign : ℂ) * ((↑(chebyshevPsi x) : ℂ) * (↑x : ℂ) ^ (-(s + 1)))) (Ioi (1 : ℝ)) :=
    h3.const_mul _
  exact (integral_sub h_ab h_c).trans (by
    have h_a : IntegrableOn (fun (x : ℝ) =>
        (↑C : ℂ) * ((↑x : ℂ) ^ (↑α : ℂ) * (↑x : ℂ) ^ (-(s + 1)))) (Ioi (1 : ℝ)) :=
      h1.const_mul _
    have h_b : IntegrableOn (fun (x : ℝ) =>
        (↑σ_sign : ℂ) * ((↑x : ℂ) * (↑x : ℂ) ^ (-(s + 1)))) (Ioi (1 : ℝ)) :=
      h2.const_mul _
    rw [integral_add h_a h_b, integral_const_mul, integral_const_mul, integral_const_mul])

open ArithmeticFunction Finset in
open scoped LSeries.notation ArithmeticFunction in
/-- The ψ integral relates to -ζ'/ζ via neg_zeta_logDeriv_eq_integral. -/
private theorem psi_integral_eq (s : ℂ) (hs : 1 < s.re) :
    s * (∫ t in Ioi (1 : ℝ), (↑(chebyshevPsi t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))) =
      -deriv riemannZeta s / riemannZeta s := by
  -- Rewrite chebyshevPsi as von Mangoldt sum in the integral
  have h_int_eq : (∫ t in Ioi (1 : ℝ),
      (↑(chebyshevPsi t) : ℂ) * (↑t : ℂ) ^ (-(s + 1))) =
      ∫ t in Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, (↗Λ) k) *
        (↑t : ℂ) ^ (-(s + 1)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by
      congr 1; exact chebyshevPsi_ofReal_eq_vonMangoldt_sum t
  rw [h_int_eq]
  exact (PsiIntegralRepresentation.neg_zeta_logDeriv_eq_integral hs).symm

/-- The witness function equals the formula when Re(s) > max(1, α). -/
theorem witnessG_eq_formula (C : ℝ) (hC : 0 < C) (α : ℝ)
    (hα : 1 / 2 < α) (σ_sign : ℝ) (hσ : σ_sign = 1 ∨ σ_sign = -1)
    (hbound : ∀ᶠ x in atTop, σ_sign * (chebyshevPsi x - x) ≤ C * x ^ α)
    (s : ℂ) (hs : 1 < s.re) (hαs : α < s.re) :
    witnessG C α σ_sign s =
      s * (↑C : ℂ) / (s - (↑α : ℂ)) + (↑σ_sign : ℂ) * (s / (s - 1)) +
      (↑σ_sign : ℂ) * (deriv riemannZeta s / riemannZeta s) := by
  unfold witnessG
  rw [dirichletIntegral_eq_split C α σ_sign s hs hα hαs]
  rw [MellinIntegralFormulas.mellin_rpow_alpha α s hαs]
  rw [MellinIntegralFormulas.mellin_x s hs]
  -- Goal: s * (C * (1/(s-α)) + σ * (1/(s-1)) - σ * (∫ ψ*...))
  --     = s*C/(s-α) + σ*s/(s-1) + σ*ζ'/ζ(s)
  -- Replace s * (∫ ψ) using psi_integral_eq
  set I := ∫ t in Ioi (1 : ℝ),
    (↑(chebyshevPsi t) : ℂ) * (↑t : ℂ) ^ (-(s + 1)) with hI_def
  have h_sI : s * I = -deriv riemannZeta s / riemannZeta s :=
    psi_integral_eq s hs
  -- Algebra: distribute s, substitute, simplify signs
  calc s * ((↑C : ℂ) * (1 / (s - ↑α)) + (↑σ_sign : ℂ) * (1 / (s - 1)) -
        (↑σ_sign : ℂ) * I)
    = s * (↑C : ℂ) * (1 / (s - ↑α)) + (↑σ_sign : ℂ) * (s * (1 / (s - 1))) -
        (↑σ_sign : ℂ) * (s * I) := by ring
    _ = s * (↑C : ℂ) * (1 / (s - ↑α)) + (↑σ_sign : ℂ) * (s * (1 / (s - 1))) -
        (↑σ_sign : ℂ) * (-deriv riemannZeta s / riemannZeta s) := by rw [h_sI]
    _ = s * (↑C : ℂ) / (s - ↑α) + (↑σ_sign : ℂ) * (s / (s - 1)) +
        (↑σ_sign : ℂ) * (deriv riemannZeta s / riemannZeta s) := by ring

/-! ## Main theorem: the Pringsheim ψ atom -/

/-- **Landau's non-negative Dirichlet integral theorem for ψ**.

Given a one-sided bound σ*(ψ(x)-x) ≤ C*x^α with 1/2 < α, there exists
G analytic on {Re > α} matching the Landau formula on {Re > 1}. -/
theorem pringsheim_psi_atom :
    ∀ (α : ℝ), 1 / 2 < α → ∀ (C : ℝ), 0 < C →
    ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
    (∀ᶠ x in atTop, σ * (chebyshevPsi x - x) ≤ C * x ^ α) →
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        G s = s * (↑C : ℂ) / (s - (↑α : ℂ)) + (↑σ : ℂ) * (s / (s - 1)) +
              (↑σ : ℂ) * (deriv riemannZeta s / riemannZeta s) := by
  intro α hα C hC σ hσ hbound
  by_cases hα1 : α ≤ 1
  · -- Main case: α ≤ 1, so Re(s) > 1 implies α < Re(s)
    exact ⟨witnessG C α σ,
      witnessG_analyticOnNhd C hC α hα σ hσ hbound,
      fun s hs => witnessG_eq_formula C hC α hα σ hσ hbound s hs (by linarith)⟩
  · -- Trivial case: α > 1 — the formula itself is the witness.
    -- {Re > α} ⊂ {Re > 1} and the formula is analytic there since
    -- ζ(s) ≠ 0 for Re(s) ≥ 1 and s ≠ 1 (but Re(s) > α > 1 forces s ≠ 1).
    push_neg at hα1
    refine ⟨fun s => s * (↑C : ℂ) / (s - (↑α : ℂ)) + (↑σ : ℂ) * (s / (s - 1)) +
      (↑σ : ℂ) * (deriv riemannZeta s / riemannZeta s), ?_, fun _ _ => rfl⟩
    intro s hs
    simp only [mem_setOf_eq] at hs
    have hs1 : s ≠ 1 := by
      intro h; subst h; simp only [one_re] at hs; linarith
    have hsα : s - (↑α : ℂ) ≠ 0 := by
      intro h; linarith [show s.re = α by rw [sub_eq_zero.mp h, ofReal_re]]
    have hζ_ne : riemannZeta s ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by linarith)
    have hζ_diffOn : DifferentiableOn ℂ riemannZeta {t | t ≠ 1} :=
      fun t ht => (differentiableAt_riemannZeta ht).differentiableWithinAt
    have hζ_anal : AnalyticAt ℂ riemannZeta s :=
      hζ_diffOn.analyticOnNhd isOpen_ne s hs1
    -- Build analyticity piece by piece in tactic mode
    apply AnalyticAt.add
    · apply AnalyticAt.add
      · exact (analyticAt_id.mul analyticAt_const).div
          (analyticAt_id.sub analyticAt_const) hsα
      · exact analyticAt_const.mul
          (analyticAt_id.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs1))
    · exact analyticAt_const.mul (hζ_anal.deriv.div hζ_anal hζ_ne)

end Aristotle.PringsheimPsiAtom
