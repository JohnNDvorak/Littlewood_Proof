/-
Sub-lemma 3 for rvm_N_formula_bound:
Contour integral splits over the logDeriv decomposition.

**THIS FILE IS SORRY-FREE.**

Shows that on the rectangle (-1,2)×(1,T):
  contourIntegralRect(logDeriv RiemannXiAlt)
    = contourIntegralRect(logDeriv completedRiemannZeta)

Proof outline:
1. logDeriv(ξ) = s⁻¹ + (s-1)⁻¹ + logDeriv(Λ) pointwise on the boundary
   (bridge lemma, proved in this file)
2. By contourIntegralRect_congr_boundary, replace integrand
3. s⁻¹ + (s-1)⁻¹ is holomorphic on closedRect (poles outside)
4. Cauchy-Goursat gives ∮(s⁻¹ + (s-1)⁻¹) = 0
5. Linearity: ∮(s⁻¹ + (s-1)⁻¹ + logDeriv Λ) = 0 + ∮(logDeriv Λ)

References:
- Titchmarsh, "Theory of the Riemann Zeta-Function", §9.3

Co-authored-by: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
-/

import Littlewood.ZetaZeros.RvMContourEvaluation
import Littlewood.ZetaZeros.RectArgumentPrinciple
import Littlewood.Aristotle.RiemannXiEntire
import Littlewood.Aristotle.ZetaLogDerivInfra

set_option maxHeartbeats 6400000
set_option autoImplicit false

noncomputable section

open Complex Real Set MeasureTheory Topology Filter RectArgumentPrinciple
open scoped Real

namespace ZetaZeros.RvMContourLinearity

/-! ## Pointwise decomposition on the boundary -/

/-- logDeriv(RiemannXiAlt)(s) = s⁻¹ + (s-1)⁻¹ + logDeriv(completedRiemannZeta)(s)
    for s with Im > 0 and completedRiemannZeta s ≠ 0.

    On the boundary of (-1,2)×(1,T), Im ≥ 1 > 0 so s ≠ 0 and s ≠ 1,
    and completedRiemannZeta s ≠ 0 when ξ ≠ 0 on boundary. -/
theorem logDeriv_xi_eq_inv_plus_logDeriv_completed (s : ℂ)
    (h_im : 0 < s.im) (hcomp : completedRiemannZeta s ≠ 0) :
    logDeriv RiemannXiAlt s =
      s⁻¹ + (s - 1)⁻¹ + logDeriv completedRiemannZeta s := by
  have h0 : s ≠ 0 := by intro h; rw [h] at h_im; simp at h_im
  have h1 : s ≠ 1 := by intro h; rw [h] at h_im; simp at h_im
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  -- RiemannXiAlt = (1/2)(g + 1) where g = s(s-1)Λ₀
  set g := fun z : ℂ => z * (z - 1) * completedRiemannZeta₀ z + 1 with hg_def
  -- logDeriv(const · f) = logDeriv(f)
  have hld_const : logDeriv RiemannXiAlt s = logDeriv g s := by
    show logDeriv (fun z => (1/2 : ℂ) * g z) s = logDeriv g s
    exact logDeriv_const_mul s (1/2 : ℂ) (by norm_num)
  -- g agrees with s(s-1)Λ near s (s ≠ 0,1)
  have hgf_eq : ∀ z : ℂ, z ≠ 0 → z ≠ 1 →
      g z = z * (z - 1) * completedRiemannZeta z := by
    intro z hz0 hz1; simp only [hg_def]
    have h := completedRiemannZeta_eq z; rw [h]
    have hz1' : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
    field_simp [hz0, hz1']; ring
  have hg_at_s : g s = s * (s - 1) * completedRiemannZeta s := hgf_eq s h0 h1
  have hgf_nhds : g =ᶠ[nhds s] (fun z => z * (z - 1) * completedRiemannZeta z) :=
    Filter.Eventually.mono
      (IsOpen.mem_nhds (isOpen_ne.inter isOpen_ne) ⟨h0, h1⟩)
      (fun z ⟨hz0, hz1⟩ => hgf_eq z hz0 hz1)
  have hlogderiv_eq : logDeriv g s =
      logDeriv (fun z => z * (z - 1) * completedRiemannZeta z) s := by
    simp only [logDeriv_apply, hg_at_s, Filter.EventuallyEq.deriv_eq hgf_nhds]
  -- Product rule for logDeriv(s(s-1)Λ)
  have hdLam : DifferentiableAt ℂ completedRiemannZeta s :=
    differentiableAt_completedZeta h0 h1
  have hd_poly : HasDerivAt (fun z : ℂ => z * (z - 1)) (2 * s - 1) s := by
    convert (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const (1 : ℂ)) using 1
    simp only [id]; ring
  have hd_prod : HasDerivAt (fun z => z * (z - 1) * completedRiemannZeta z)
      ((2 * s - 1) * completedRiemannZeta s +
        s * (s - 1) * deriv completedRiemannZeta s) s := by
    have h1' := hd_poly.mul hdLam.hasDerivAt
    have : ((fun z => z * (z - 1)) * completedRiemannZeta) =
        (fun z => z * (z - 1) * completedRiemannZeta z) := by
      ext z; simp [Pi.mul_apply]
    rwa [this] at h1'
  rw [hld_const, hlogderiv_eq]
  simp only [logDeriv_apply, hd_prod.deriv]
  field_simp [h0, hs1, hcomp]
  ring

private theorem ofReal_add_mul_I_ne_zero {x y : ℝ} (hy : y ≠ 0) :
    ((↑x : ℂ) + ↑y * I) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hy0 : y = 0 := by
    simpa [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im] using him
  exact hy hy0

private theorem ofReal_add_mul_I_ne_one {x y : ℝ} (hy : y ≠ 0) :
    ((↑x : ℂ) + ↑y * I) ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  have hy0 : y = 0 := by
    simpa [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im] using him
  exact hy hy0

private theorem edge_mem_closedRect {a b c d : ℝ} (_hab : a ≤ b) (_hcd : c ≤ d)
    (x : ℝ) (hx1 : a ≤ x) (hx2 : x ≤ b) (y : ℝ) (hy1 : c ≤ y) (hy2 : y ≤ d) :
    (↑x + ↑y * I : ℂ) ∈ closedRect a b c d := by
  simp only [closedRect, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im,
    Complex.add_im, Complex.mul_im] <;> linarith

private theorem xi_ne_zero_of_completed_ne_zero {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) (hcomp : completedRiemannZeta s ≠ 0) :
    RiemannXiAlt s ≠ 0 := by
  rw [RiemannXiAlt_eq_formula h0 h1]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h0) (sub_ne_zero.mpr h1)) hcomp

private theorem xi_deriv_continuous : Continuous (deriv RiemannXiAlt) := by
  simpa using
    ((RiemannXiAlt_entire.contDiff : ContDiff ℂ ⊤ RiemannXiAlt).continuous_deriv (by simp))

private theorem completedLogDeriv_continuousOn_of_xi_decomp
    {φ : ℝ → ℂ} {s : Set ℝ}
    (hφ : Continuous φ)
    (hφ0 : ∀ t ∈ s, φ t ≠ 0)
    (hφ1 : ∀ t ∈ s, φ t ≠ 1)
    (hcomp : ∀ t ∈ s, completedRiemannZeta (φ t) ≠ 0)
    (hdecomp : ∀ t ∈ s,
      logDeriv RiemannXiAlt (φ t) =
        (φ t)⁻¹ + (φ t - 1)⁻¹ + logDeriv completedRiemannZeta (φ t)) :
    ContinuousOn (fun t : ℝ => logDeriv completedRiemannZeta (φ t)) s := by
  have hh_cont : ContinuousOn (fun t : ℝ => (φ t)⁻¹ + (φ t - 1)⁻¹) s := by
    apply ContinuousOn.add
    · apply ContinuousOn.inv₀
      · exact hφ.continuousOn
      · intro t ht h0
        exact hφ0 t ht h0
    · apply ContinuousOn.inv₀
      · exact hφ.continuousOn.sub continuousOn_const
      · intro t ht h1
        exact hφ1 t ht (sub_eq_zero.mp h1)
  have hxi_cont : ContinuousOn (fun t : ℝ => logDeriv RiemannXiAlt (φ t)) s := by
    have hnum : ContinuousOn (fun t : ℝ => deriv RiemannXiAlt (φ t)) s :=
      (xi_deriv_continuous.comp hφ).continuousOn
    have hden : ContinuousOn (fun t : ℝ => RiemannXiAlt (φ t)) s :=
      (RiemannXiAlt_entire.continuous.comp hφ).continuousOn
    have hne : ∀ t ∈ s, RiemannXiAlt (φ t) ≠ 0 := by
      intro t ht
      exact xi_ne_zero_of_completed_ne_zero (hφ0 t ht) (hφ1 t ht) (hcomp t ht)
    simpa [logDeriv_apply] using hnum.div hden hne
  refine (hxi_cont.sub hh_cont).congr ?_
  intro t ht
  symm
  exact (sub_eq_iff_eq_add).2 (by
    simpa [add_assoc, add_left_comm, add_comm] using hdecomp t ht)

/-- **Sub-lemma 3: Contour integral of logDeriv(ξ) equals contour integral of logDeriv(Λ).**

    contourIntegralRect(logDeriv RiemannXiAlt) (-1) 2 1 T
      = contourIntegralRect(logDeriv completedRiemannZeta) (-1) 2 1 T

    Proof: By the pointwise decomposition, logDeriv ξ = s⁻¹ + (s-1)⁻¹ + logDeriv Λ
    on the boundary. By congr_boundary, the contour integral of logDeriv ξ equals
    that of (s⁻¹ + (s-1)⁻¹ + logDeriv Λ). The sum s⁻¹ + (s-1)⁻¹ is holomorphic
    on the closed rectangle (poles at 0 and 1 are outside since Im ≥ 1). Adding a
    holomorphic function to the integrand changes the contour integral by a
    Cauchy-Goursat-zero term. -/
theorem contour_logDeriv_xi_eq_completedZeta (T : ℝ) (hT : 1 ≤ T)
    (hcomp_ne_zero : ∀ s, s.re ∈ Icc (-1 : ℝ) 2 → s.im ∈ Icc (1 : ℝ) T →
      (s.im = 1 ∨ s.im = T ∨ s.re = -1 ∨ s.re = 2) →
      completedRiemannZeta s ≠ 0) :
    contourIntegralRect (logDeriv RiemannXiAlt) (-1) 2 1 T =
    contourIntegralRect (logDeriv completedRiemannZeta) (-1) 2 1 T := by
  -- Step 1: Replace logDeriv ξ by (s⁻¹ + (s-1)⁻¹ + logDeriv Λ) on the boundary.
  have h_decomp_bot : ∀ x ∈ Icc (-1 : ℝ) 2,
      logDeriv RiemannXiAlt (↑x + (1 : ℂ) * I) =
        (↑x + (1 : ℂ) * I)⁻¹ + ((↑x + (1 : ℂ) * I) - 1)⁻¹ +
        logDeriv completedRiemannZeta (↑x + (1 : ℂ) * I) := by
    intro x hx
    apply logDeriv_xi_eq_inv_plus_logDeriv_completed
    · simp
    · exact hcomp_ne_zero _
        (by simpa using hx)
        (by simpa using (show (1 : ℝ) ∈ Icc (1 : ℝ) T from ⟨le_rfl, hT⟩))
        (Or.inl (by simp))
  have h_decomp_top : ∀ x ∈ Icc (-1 : ℝ) 2,
      logDeriv RiemannXiAlt (↑x + (↑T : ℂ) * I) =
        (↑x + (↑T : ℂ) * I)⁻¹ + ((↑x + (↑T : ℂ) * I) - 1)⁻¹ +
        logDeriv completedRiemannZeta (↑x + (↑T : ℂ) * I) := by
    intro x hx
    apply logDeriv_xi_eq_inv_plus_logDeriv_completed
    · simp; linarith
    · exact hcomp_ne_zero _
        (by simpa using hx)
        (by simpa using (show T ∈ Icc (1 : ℝ) T from ⟨hT, le_rfl⟩))
        (Or.inr (Or.inl (by simp)))
  have h_decomp_right : ∀ y ∈ Icc (1 : ℝ) T,
      logDeriv RiemannXiAlt ((2 : ℂ) + ↑y * I) =
        ((2 : ℂ) + ↑y * I)⁻¹ + (((2 : ℂ) + ↑y * I) - 1)⁻¹ +
        logDeriv completedRiemannZeta ((2 : ℂ) + ↑y * I) := by
    intro y hy
    apply logDeriv_xi_eq_inv_plus_logDeriv_completed
    · simp; linarith [hy.1]
    · exact hcomp_ne_zero _
        (by simpa using (show (2 : ℝ) ∈ Icc (-1 : ℝ) 2 from ⟨by norm_num, le_rfl⟩))
        (by simpa using hy)
        (Or.inr (Or.inr (Or.inr (by simp))))
  have h_decomp_left : ∀ y ∈ Icc (1 : ℝ) T,
      logDeriv RiemannXiAlt (((↑(-1 : ℝ) : ℂ) + ↑y * I)) =
        (((↑(-1 : ℝ) : ℂ) + ↑y * I))⁻¹ + ((((↑(-1 : ℝ) : ℂ) + ↑y * I) - 1))⁻¹ +
        logDeriv completedRiemannZeta (((↑(-1 : ℝ) : ℂ) + ↑y * I)) := by
    intro y hy
    apply logDeriv_xi_eq_inv_plus_logDeriv_completed
    · simp; linarith [hy.1]
    · exact hcomp_ne_zero _
        (by simpa using (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 2 from ⟨le_rfl, by norm_num⟩))
        (by simpa using hy)
        (Or.inr (Or.inr (Or.inl (by simp))))
  -- Step 2: contourIntegralRect(logDeriv ξ) = contourIntegralRect(s⁻¹ + (s-1)⁻¹ + logDeriv Λ)
  have h_congr := contourIntegralRect_congr_boundary
    (fun s => logDeriv RiemannXiAlt s)
    (fun s => s⁻¹ + (s - 1)⁻¹ + logDeriv completedRiemannZeta s)
    (-1) 2 1 T
    (by norm_num : (-1 : ℝ) ≤ 2) hT
    h_decomp_bot h_decomp_top h_decomp_right h_decomp_left
  rw [h_congr]
  -- Step 3: The function s ↦ s⁻¹ + (s-1)⁻¹ is holomorphic on closedRect.
  -- Its contour integral vanishes by Cauchy-Goursat.
  have h_pole_holo : DifferentiableOn ℂ (fun s => s⁻¹ + (s - 1)⁻¹)
      (closedRect (-1) 2 1 T) := by
    apply DifferentiableOn.add
    · apply DifferentiableOn.inv differentiableOn_id
      intro s hs heq
      have hs0 : s = 0 := by simpa using heq
      obtain ⟨_, _, him, _⟩ := hs
      rw [hs0] at him
      simp at him
      linarith
    · apply DifferentiableOn.inv (differentiableOn_id.sub (differentiableOn_const 1))
      intro s hs heq
      have : s = 1 := sub_eq_zero.mp heq
      obtain ⟨_, _, him, _⟩ := hs
      rw [this] at him; simp at him; linarith
  have h_pole_zero : contourIntegralRect (fun s => s⁻¹ + (s - 1)⁻¹) (-1) 2 1 T = 0 :=
    cauchy_goursat_rect _ _ _ _ _ (by norm_num) (by linarith) h_pole_holo
  -- Step 4: Linearity.
  -- ∮(f + g) = ∮f + ∮g. Since ∮f = 0, ∮(f + g) = ∮g.
  -- Here f = s⁻¹ + (s-1)⁻¹ and g = logDeriv Λ.
  -- We need: on each edge, ∫(f+g) = ∫f + ∫g.
  -- This needs integrability of f on each edge (from holomorphicity + compactness)
  -- and g = logDeriv Λ on each edge.
  -- f is continuous on closedRect, hence integrable on each compact edge.
  -- For g: we assume it's integrable (it appears as the RHS target).
  -- Key simplification: ∮(f+g) = ∮f + ∮g by definitional unfolding + integral_add.
  -- Rather than prove integrability of g, use the algebraic identity:
  -- ∮(f+g) - ∮g = ∮f by subtraction. And ∮f = 0.
  -- But subtraction also needs linearity...
  -- Let me prove it by computing each edge integral.
  -- Actually, from the unfold, each integral is ∫(f+g). We want to show the
  -- combination equals ∫g (combination). The difference is ∮f = 0.
  -- Use: A - B + C - D = (A' - B' + C' - D') means A-A' = B-B' + (A-B) - (A'-B') etc.
  -- This is too tangled. Let me use linarith with the vanishing result.
  -- h_pole_zero says: I_bot_f - I_top_f + I·I_right_f - I·I_left_f = 0
  -- Goal says: I_bot_{f+g} - I_top_{f+g} + I·I_right_{f+g} - I·I_left_{f+g}
  --          = I_bot_g - I_top_g + I·I_right_g - I·I_left_g
  -- This is equivalent to I_bot_f - I_top_f + I·I_right_f - I·I_left_f = 0 (= h_pole_zero)
  -- PROVIDED ∫(f+g) = ∫f + ∫g on each edge.
  -- We need: on each edge, the integral of f+g = integral of f + integral of g.
  -- This is where we need integrability.
  -- f = s⁻¹ + (s-1)⁻¹ is continuous on closedRect, hence integrable on each edge.
  -- g = logDeriv completedRiemannZeta: need to know it's integrable on each edge.
  -- Since the goal involves ∫g (as the RHS), if ∫g doesn't exist, both sides are 0
  -- (Lean's integral of non-integrable functions is 0 by convention).
  -- So we can split: either g is integrable on each edge (in which case we use
  -- integral_add), or it's not (in which case both sides are 0).
  -- This is getting too complex. Let me just use the linearity and integrability
  -- more concretely.
  -- Integrability of f on each edge:
  have hf_bot : IntervalIntegrable
      (fun x : ℝ => (↑x + (1:ℂ) * I)⁻¹ + ((↑x + (1:ℂ) * I) - 1)⁻¹) volume (-1) 2 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact (h_pole_holo.continuousOn.comp
      (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
      (fun x hx => edge_mem_closedRect (by norm_num) hT x hx.1 hx.2 1 le_rfl hT))
  have hf_top : IntervalIntegrable
      (fun x : ℝ => (↑x + (↑T:ℂ) * I)⁻¹ + ((↑x + (↑T:ℂ) * I) - 1)⁻¹) volume (-1) 2 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact (h_pole_holo.continuousOn.comp
      (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
      (fun x hx => edge_mem_closedRect (by norm_num) hT x hx.1 hx.2 T hT le_rfl))
  have hf_right : IntervalIntegrable
      (fun y : ℝ => ((2:ℂ) + ↑y * I)⁻¹ + (((2:ℂ) + ↑y * I) - 1)⁻¹) volume 1 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    exact (h_pole_holo.continuousOn.comp
      (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      (fun y hy => edge_mem_closedRect (by norm_num) hT 2 (by norm_num) le_rfl y hy.1 hy.2))
  have hf_left : IntervalIntegrable
      (fun y : ℝ => (((↑(-1 : ℝ) : ℂ) + ↑y * I))⁻¹ +
        ((((↑(-1 : ℝ) : ℂ) + ↑y * I) - 1))⁻¹) volume 1 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    exact (h_pole_holo.continuousOn.comp
      (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      (fun y hy =>
        edge_mem_closedRect (by norm_num) hT (-1 : ℝ) le_rfl (by norm_num) y hy.1 hy.2))
  -- Now use integral_add on each edge (valid even if g is not integrable,
  -- since integral_add with one integrable and one potentially non-integrable
  -- ... actually, integral_add requires BOTH to be integrable).
  -- So we need integrability of g = logDeriv completedRiemannZeta on each edge.
  -- If it IS integrable: use integral_add, then h_pole_zero gives the result.
  -- If it's NOT integrable: the interval integral of the sum f+g may not split,
  -- but in this case the RHS integral of g would also be 0 (Lean convention).
  -- This case analysis is painful. Let me just assume integrability and close it.
  -- For the case where g IS integrable on each edge, we get:
  -- ∫(f+g) = ∫f + ∫g. Then the contour integral combination gives:
  -- ∮(f+g) = ∮f + ∮g = 0 + ∮g = ∮g. QED.
  -- For the case where g is NOT integrable on some edge: the LHS integral over
  -- that edge is 0 (Lean convention for non-integrable integral), and so is the
  -- RHS integral. The f integral over that edge IS well-defined (integrable).
  -- Hmm, this means ∫(f+g) ≠ ∫f + ∫g in general when g is not integrable.
  -- Actually, if f is integrable and g is not, and f+g is not integrable either,
  -- then ∫(f+g) = 0 and ∫f + ∫g = ∫f + 0 ≠ 0 in general. So we can't split.
  -- So I DO need integrability of g on each edge.
  -- Claim: logDeriv completedRiemannZeta is continuous on the closedRect
  -- (away from poles at 0 and 1, which are outside since Im ≥ 1).
  -- completedRiemannZeta is differentiable on ℂ \ {0, 1} and ≠ 0 on boundary
  -- (by hypothesis). logDeriv of a differentiable nonvanishing function is
  -- continuous. On the boundary, completedRiemannZeta is differentiable and ≠ 0.
  -- So logDeriv Λ is continuous on the boundary, hence integrable.
  -- But wait: we only know Λ ≠ 0 on the BOUNDARY, not on all of closedRect.
  -- That's fine: we only need integrability on each boundary edge.
  -- Let's prove integrability of g = logDeriv Λ on each edge.
  -- g is continuous on each edge because:
  -- 1. completedRiemannZeta is differentiable at each boundary point (s ≠ 0, 1)
  -- 2. completedRiemannZeta is nonzero at each boundary point (hypothesis)
  -- 3. logDeriv of differentiable + nonzero = continuous
  -- Edge integrability for g:
  have hg_bot : IntervalIntegrable
      (fun x : ℝ => logDeriv completedRiemannZeta (↑x + (1:ℂ) * I)) volume (-1) 2 := by
    have hcont : ContinuousOn
        (fun x : ℝ => logDeriv completedRiemannZeta (↑x + (1 : ℂ) * I))
        (Icc (-1 : ℝ) 2) := by
      exact completedLogDeriv_continuousOn_of_xi_decomp
        (continuous_ofReal.add (continuous_const.mul continuous_const))
        (fun x _ => ofReal_add_mul_I_ne_zero (x := x) (by norm_num))
        (fun x _ => ofReal_add_mul_I_ne_one (x := x) (by norm_num))
        (fun x hx =>
          hcomp_ne_zero _ (by simpa using hx)
            (by simpa using (show (1 : ℝ) ∈ Icc (1 : ℝ) T from ⟨le_rfl, hT⟩))
            (Or.inl (by simp)))
        (fun x hx => h_decomp_bot x hx)
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  have hg_top : IntervalIntegrable
      (fun x : ℝ => logDeriv completedRiemannZeta (↑x + (↑T:ℂ) * I)) volume (-1) 2 := by
    have hT0 : T ≠ 0 := by linarith
    have hcont : ContinuousOn
        (fun x : ℝ => logDeriv completedRiemannZeta (↑x + (↑T : ℂ) * I))
        (Icc (-1 : ℝ) 2) := by
      exact completedLogDeriv_continuousOn_of_xi_decomp
        (continuous_ofReal.add (continuous_const.mul continuous_const))
        (fun x _ => ofReal_add_mul_I_ne_zero (x := x) hT0)
        (fun x _ => ofReal_add_mul_I_ne_one (x := x) hT0)
        (fun x hx =>
          hcomp_ne_zero _ (by simpa using hx)
            (by simpa using (show T ∈ Icc (1 : ℝ) T from ⟨hT, le_rfl⟩))
            (Or.inr (Or.inl (by simp))))
        (fun x hx => h_decomp_top x hx)
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  have hg_right : IntervalIntegrable
      (fun y : ℝ => logDeriv completedRiemannZeta ((2:ℂ) + ↑y * I)) volume 1 T := by
    have hcont : ContinuousOn
        (fun y : ℝ => logDeriv completedRiemannZeta ((2 : ℂ) + ↑y * I))
        (Icc (1 : ℝ) T) := by
      exact completedLogDeriv_continuousOn_of_xi_decomp
        (continuous_const.add (continuous_ofReal.mul continuous_const))
        (fun y hy => ofReal_add_mul_I_ne_zero (x := 2) (by linarith [hy.1]))
        (fun y hy => ofReal_add_mul_I_ne_one (x := 2) (by linarith [hy.1]))
        (fun y hy =>
          hcomp_ne_zero _
            (by simpa using (show (2 : ℝ) ∈ Icc (-1 : ℝ) 2 from ⟨by norm_num, le_rfl⟩))
            (by simpa using hy)
            (Or.inr (Or.inr (Or.inr (by simp)))))
        (fun y hy => h_decomp_right y hy)
    exact hcont.intervalIntegrable_of_Icc hT
  have hg_left : IntervalIntegrable
      (fun y : ℝ => logDeriv completedRiemannZeta (((↑(-1 : ℝ) : ℂ) + ↑y * I))) volume 1 T := by
    have hcont : ContinuousOn
        (fun y : ℝ => logDeriv completedRiemannZeta (((↑(-1 : ℝ) : ℂ) + ↑y * I)))
        (Icc (1 : ℝ) T) := by
      exact completedLogDeriv_continuousOn_of_xi_decomp
        (continuous_const.add (continuous_ofReal.mul continuous_const))
        (fun y hy => ofReal_add_mul_I_ne_zero (x := -1) (by linarith [hy.1]))
        (fun y hy => ofReal_add_mul_I_ne_one (x := -1) (by linarith [hy.1]))
        (fun y hy =>
          hcomp_ne_zero _
            (by simpa using (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 2 from ⟨le_rfl, by norm_num⟩))
            (by simpa using hy)
            (Or.inr (Or.inr (Or.inl (by simp)))))
        (fun y hy => h_decomp_left y hy)
    simpa using hcont.intervalIntegrable_of_Icc hT
  have h_add :
      contourIntegralRect
          (fun s => s⁻¹ + (s - 1)⁻¹ + logDeriv completedRiemannZeta s) (-1) 2 1 T =
        contourIntegralRect (fun s => s⁻¹ + (s - 1)⁻¹) (-1) 2 1 T +
          contourIntegralRect (logDeriv completedRiemannZeta) (-1) 2 1 T := by
    simpa [Pi.add_apply] using
      (contourIntegralRect_add
        (fun s => s⁻¹ + (s - 1)⁻¹) (logDeriv completedRiemannZeta)
        (-1) 2 1 T hf_bot hg_bot hf_top hg_top hf_right hg_right hf_left hg_left)
  rw [h_add, h_pole_zero, zero_add]

end ZetaZeros.RvMContourLinearity
