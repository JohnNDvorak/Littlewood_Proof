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
    · exact hcomp_ne_zero _ (by simp; exact hx) (by simp; exact ⟨le_refl _, hT⟩) (Or.inl (by simp))
  have h_decomp_top : ∀ x ∈ Icc (-1 : ℝ) 2,
      logDeriv RiemannXiAlt (↑x + (↑T : ℂ) * I) =
        (↑x + (↑T : ℂ) * I)⁻¹ + ((↑x + (↑T : ℂ) * I) - 1)⁻¹ +
        logDeriv completedRiemannZeta (↑x + (↑T : ℂ) * I) := by
    intro x hx
    apply logDeriv_xi_eq_inv_plus_logDeriv_completed
    · simp; linarith
    · exact hcomp_ne_zero _ (by simp; exact hx) (by simp) (Or.inr (Or.inl (by simp)))
  have h_decomp_right : ∀ y ∈ Icc (1 : ℝ) T,
      logDeriv RiemannXiAlt ((2 : ℂ) + ↑y * I) =
        ((2 : ℂ) + ↑y * I)⁻¹ + (((2 : ℂ) + ↑y * I) - 1)⁻¹ +
        logDeriv completedRiemannZeta ((2 : ℂ) + ↑y * I) := by
    intro y hy
    apply logDeriv_xi_eq_inv_plus_logDeriv_completed
    · simp; linarith [hy.1]
    · exact hcomp_ne_zero _ (by simp) (by simp; exact hy) (Or.inr (Or.inr (Or.inr (by simp))))
  have h_decomp_left : ∀ y ∈ Icc (1 : ℝ) T,
      logDeriv RiemannXiAlt ((-1 : ℂ) + ↑y * I) =
        ((-1 : ℂ) + ↑y * I)⁻¹ + (((-1 : ℂ) + ↑y * I) - 1)⁻¹ +
        logDeriv completedRiemannZeta ((-1 : ℂ) + ↑y * I) := by
    intro y hy
    apply logDeriv_xi_eq_inv_plus_logDeriv_completed
    · simp; linarith [hy.1]
    · exact hcomp_ne_zero _ (by simp) (by simp; exact hy) (Or.inr (Or.inr (Or.inl (by simp))))
  -- Step 2: contourIntegralRect(logDeriv ξ) = contourIntegralRect(s⁻¹ + (s-1)⁻¹ + logDeriv Λ)
  have h_congr := contourIntegralRect_congr_boundary _ _ _ _ _ _
    (by norm_num : (-1:ℝ) ≤ 2) (by linarith)
    h_decomp_bot h_decomp_top h_decomp_right h_decomp_left
  rw [h_congr]
  -- Step 3: The function s ↦ s⁻¹ + (s-1)⁻¹ is holomorphic on closedRect.
  -- Its contour integral vanishes by Cauchy-Goursat.
  have h_pole_holo : DifferentiableOn ℂ (fun s => s⁻¹ + (s - 1)⁻¹)
      (closedRect (-1) 2 1 T) := by
    apply DifferentiableOn.add
    · apply DifferentiableOn.inv differentiableOn_id
      intro s hs heq
      obtain ⟨_, _, him, _⟩ := hs
      rw [heq] at him; simp at him; linarith
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
  -- Unfold contourIntegralRect and use integral_add on each edge.
  unfold contourIntegralRect
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
  -- From h_pole_zero (unfold contourIntegralRect):
  unfold contourIntegralRect at h_pole_zero
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
      (fun x hx => by
        rw [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 2), mem_Icc] at hx
        exact ⟨by simp; linarith [hx.1], by simp; linarith [hx.2],
               by simp, by simp; linarith⟩))
  have hf_top : IntervalIntegrable
      (fun x : ℝ => (↑x + (↑T:ℂ) * I)⁻¹ + ((↑x + (↑T:ℂ) * I) - 1)⁻¹) volume (-1) 2 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact (h_pole_holo.continuousOn.comp
      (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
      (fun x hx => by
        rw [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 2), mem_Icc] at hx
        exact ⟨by simp; linarith [hx.1], by simp; linarith [hx.2],
               by simp; linarith, by simp⟩))
  have hf_right : IntervalIntegrable
      (fun y : ℝ => ((2:ℂ) + ↑y * I)⁻¹ + (((2:ℂ) + ↑y * I) - 1)⁻¹) volume 1 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    exact (h_pole_holo.continuousOn.comp
      (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      (fun y hy => by
        rw [uIcc_of_le hT, mem_Icc] at hy
        exact ⟨by simp, by simp, by simp; linarith [hy.1], by simp; linarith [hy.2]⟩))
  have hf_left : IntervalIntegrable
      (fun y : ℝ => ((-1:ℂ) + ↑y * I)⁻¹ + (((-1:ℂ) + ↑y * I) - 1)⁻¹) volume 1 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    exact (h_pole_holo.continuousOn.comp
      (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      (fun y hy => by
        rw [uIcc_of_le hT, mem_Icc] at hy
        exact ⟨by simp, by simp, by simp; linarith [hy.1], by simp; linarith [hy.2]⟩))
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
  have hg_cont_bot : ContinuousOn
      (fun x : ℝ => logDeriv completedRiemannZeta (↑x + (1:ℂ) * I))
      (Icc (-1 : ℝ) 2) := by
    apply ContinuousOn.logDeriv
    · intro x hx
      have h0 : (↑x + (1:ℂ) * I) ≠ 0 := by
        intro h; have := congr_arg Complex.im h; simp at this
      have h1 : (↑x + (1:ℂ) * I) ≠ 1 := by
        intro h; have := congr_arg Complex.im h; simp at this
      exact (differentiableAt_completedZeta h0 h1).comp_of_eq
        ((continuous_ofReal.add (continuous_const.mul continuous_const))
          .continuousAt.differentiableAt) rfl
    · intro x hx
      exact (hcomp_ne_zero _ (by simp; exact hx) (by simp; exact ⟨le_refl _, hT⟩)
        (Or.inl (by simp))).symm ▸ absurd · (by push_neg; exact
          hcomp_ne_zero _ (by simp; exact hx) (by simp; exact ⟨le_refl _, hT⟩)
            (Or.inl (by simp)))
  -- This is getting very long. Let me just assert the integrability and close with linarith.
  -- Actually, I realize there's a much cleaner approach.
  -- Since BOTH f and f+g are "present" in our unfold, and we've computed ∮f = 0,
  -- we can just show the algebraic identity on integrals.
  -- Key: ∫(f+g) = ∫f + ∫g when f is integrable.
  -- This is MeasureTheory.integral_add (or intervalIntegral.integral_add).
  -- If g is not integrable, then f+g may also not be integrable, and both sides = 0.
  -- Actually IntervalIntegrable.add says: if f and g are both integrable, f+g is.
  -- And integral_add says: if f and g integrable, ∫(f+g) = ∫f + ∫g.
  -- But if g is not integrable, ∫g = 0 by convention, and ∫(f+g) may not = ∫f.
  -- So we really do need integrability.
  -- I'll take a shortcut: just compute each edge integral by breaking into f and g.
  -- This requires integral_add on each edge, which requires integrability.
  -- For a clean proof, let me just use the integral_add approach with integrability.
  -- Due to the complexity, let me just convert the goal to use h_pole_zero directly.
  -- Since each edge integral of f+g = integral of f + integral of g,
  -- the contour integral of f+g = contour integral of f + contour integral of g.
  -- = 0 + contour integral of g.
  -- This is clean if we can invoke integral_add.
  -- Let me write it out, assuming all edge-integrabilities (they follow from continuity).
  -- Due to the verbosity of the integrability proofs, let me use a different strategy:
  -- Prove that the difference (LHS - RHS) = ∮(s⁻¹ + (s-1)⁻¹) = 0.
  -- LHS - RHS = ∮(logDeriv ξ) - ∮(logDeriv Λ)
  -- But this is not the same as ∮(logDeriv ξ - logDeriv Λ) without linearity!
  -- OK I'm going to use a much more direct approach. Since both the LHS (after congr)
  -- and the result involve the SAME g-integrals, and differ only by the f-integrals,
  -- and the f-integrals sum to 0, I can use the algebraic structure directly.
  -- Actually the cleanest way: show each edge integral splits, then h_pole_zero.
  -- For edge integrability of g, I'll use a lemma: logDeriv of a nonvanishing
  -- differentiable function composed with a continuous path is integrable.
  -- But that's still a lot of work.
  -- PRAGMATIC DECISION: Skip the integrability bookkeeping and use
  -- a simp/ring approach with the intermediate step.
  -- Let me use a completely different proof strategy:
  -- Define h = fun s => s⁻¹ + (s-1)⁻¹.
  -- We have: logDeriv ξ = h + logDeriv Λ on boundary (proved above via congr).
  -- We have: ∮ h = 0 (proved above via Cauchy-Goursat).
  -- We want: ∮(h + logDeriv Λ) = ∮(logDeriv Λ).
  -- Rewrite: ∮(h + logDeriv Λ) = ∮ h + ∮(logDeriv Λ) = 0 + ∮(logDeriv Λ).
  -- The first equality is linearity. For contourIntegralRect, this follows from
  -- contourIntegralRect_add, which needs integrability of h and logDeriv Λ on each edge.
  -- h is integrable (proved above: hf_bot, hf_top, hf_right, hf_left).
  -- logDeriv Λ is integrable on each edge: it's continuous there because
  -- completedRiemannZeta is differentiable and nonzero on the boundary.
  -- For brevity, let me just use the integral_add + simp approach.
  -- Declare the edge integrability of g:
  have hg_bot : IntervalIntegrable
      (fun x : ℝ => logDeriv completedRiemannZeta (↑x + (1:ℂ) * I)) volume (-1) 2 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    apply ContinuousOn.logDeriv
    · intro x hx
      rw [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 2), mem_Icc] at hx
      have h0 : (↑x + (1:ℂ) * I) ≠ 0 := by
        intro h; have := congr_arg Complex.im h; simp at this
      have h1 : (↑x + (1:ℂ) * I) ≠ 1 := by
        intro h; have := congr_arg Complex.im h; simp at this
      exact (differentiableAt_completedZeta h0 h1).comp_of_eq
        ((continuous_ofReal.add (continuous_const.mul continuous_const))
          .continuousAt.differentiableAt) rfl
    · intro x hx
      rw [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 2), mem_Icc] at hx
      exact hcomp_ne_zero _ (by simp; exact hx) (by simp; exact ⟨le_refl _, hT⟩)
        (Or.inl (by simp))
  have hg_top : IntervalIntegrable
      (fun x : ℝ => logDeriv completedRiemannZeta (↑x + (↑T:ℂ) * I)) volume (-1) 2 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    apply ContinuousOn.logDeriv
    · intro x hx
      rw [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 2), mem_Icc] at hx
      have h0 : (↑x + (↑T:ℂ) * I) ≠ 0 := by
        intro h; have := congr_arg Complex.im h; simp at this; linarith
      have h1 : (↑x + (↑T:ℂ) * I) ≠ 1 := by
        intro h; have := congr_arg Complex.im h; simp at this; linarith
      exact (differentiableAt_completedZeta h0 h1).comp_of_eq
        ((continuous_ofReal.add (continuous_const.mul continuous_const))
          .continuousAt.differentiableAt) rfl
    · intro x hx
      rw [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 2), mem_Icc] at hx
      exact hcomp_ne_zero _ (by simp; exact hx) (by simp) (Or.inr (Or.inl (by simp)))
  have hg_right : IntervalIntegrable
      (fun y : ℝ => logDeriv completedRiemannZeta ((2:ℂ) + ↑y * I)) volume 1 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    apply ContinuousOn.logDeriv
    · intro y hy
      rw [uIcc_of_le hT, mem_Icc] at hy
      have h0 : ((2:ℂ) + ↑y * I) ≠ 0 := by
        intro h; have := congr_arg Complex.im h; simp at this; linarith [hy.1]
      have h1 : ((2:ℂ) + ↑y * I) ≠ 1 := by
        intro h; have := congr_arg Complex.im h; simp at this; linarith [hy.1]
      exact (differentiableAt_completedZeta h0 h1).comp_of_eq
        ((continuous_const.add (continuous_ofReal.mul continuous_const))
          .continuousAt.differentiableAt) rfl
    · intro y hy
      rw [uIcc_of_le hT, mem_Icc] at hy
      exact hcomp_ne_zero _ (by simp) (by simp; exact hy)
        (Or.inr (Or.inr (Or.inr (by simp))))
  have hg_left : IntervalIntegrable
      (fun y : ℝ => logDeriv completedRiemannZeta ((-1:ℂ) + ↑y * I)) volume 1 T := by
    apply ContinuousOn.intervalIntegrable_of_Icc hT
    apply ContinuousOn.logDeriv
    · intro y hy
      rw [uIcc_of_le hT, mem_Icc] at hy
      have h0 : ((-1:ℂ) + ↑y * I) ≠ 0 := by
        intro h; have := congr_arg Complex.im h; simp at this; linarith [hy.1]
      have h1 : ((-1:ℂ) + ↑y * I) ≠ 1 := by
        intro h; have := congr_arg Complex.im h; simp at this; linarith [hy.1]
      exact (differentiableAt_completedZeta h0 h1).comp_of_eq
        ((continuous_const.add (continuous_ofReal.mul continuous_const))
          .continuousAt.differentiableAt) rfl
    · intro y hy
      rw [uIcc_of_le hT, mem_Icc] at hy
      exact hcomp_ne_zero _ (by simp) (by simp; exact hy)
        (Or.inr (Or.inr (Or.inl (by simp))))
  -- Use integral_add on each edge:
  simp only [Pi.add_apply] at *
  rw [intervalIntegral.integral_add hf_bot hg_bot,
      intervalIntegral.integral_add hf_top hg_top,
      intervalIntegral.integral_add hf_right hg_right,
      intervalIntegral.integral_add hf_left hg_left]
  linarith

end ZetaZeros.RvMContourLinearity
