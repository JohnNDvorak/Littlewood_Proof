/-
Rectangular Argument Principle for Meromorphic Functions

Defines the argument principle for meromorphic functions integrated over rectangular
contours. The main result states that for a meromorphic function f on a closed
rectangle with no zeros or poles on the boundary:

  (1/2πi) integral_boundary_rect (f'/f) = #{zeros inside R} - #{poles inside R}

counted with multiplicity.

This file provides:
1. Definition of the logarithmic integral of f'/f over a rectangle boundary
2. Sub-lemma decomposition for the argument principle
3. The argument principle for rectangles (composed from sub-lemmas)
4. Application infrastructure for the Riemann-von Mangoldt formula

## Sub-sorry Decomposition

The argument principle for rectangles decomposes into three atomic claims:

(A) **Winding number for rectangles** (`rect_winding_number_eq_one`):
    For w inside the open rectangle, (1/2πi) ∫_∂R 1/(s-w) ds = 1.
    This is the rectangle analogue of the Cauchy integral formula.
    Proof route: deform the rectangle contour to a small circle around w
    (using Cauchy-Goursat on the annular region), then apply
    `Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`.

(B) **Log-derivative decomposition** (`logDeriv_decompose_entire`):
    For f entire with finitely many simple zeros z₁,...,zₙ inside R and
    no zeros on ∂R, the log-derivative f'/f decomposes as
    f'(s)/f(s) = ∑ₖ 1/(s - zₖ) + h(s) where h is holomorphic on R.

(C) **Cauchy-Goursat for rectangles** (PROVED — `cauchy_goursat_rect`):
    Follows from Mathlib's `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`.
    ∫_∂R h ds = 0 for h holomorphic on the closed rectangle.

Composing: ∫_∂R f'/f = ∑ₖ ∫_∂R 1/(s-zₖ) + ∫_∂R h = ∑ₖ 2πi + 0 = 2πi · n.

## References
- Titchmarsh, "Theory of Functions", Chapter 3
- Ahlfors, "Complex Analysis", Chapter 5
- Conway, "Functions of One Complex Variable II", Chapter VII

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Littlewood.Aristotle.ZetaLogDerivInfra

set_option maxHeartbeats 1600000
set_option autoImplicit false

noncomputable section

namespace RectArgumentPrinciple

open Complex Set MeasureTheory Topology Filter
open scoped Real

/-! ## Rectangle Definitions -/

/-- Open rectangle in ℂ: {z | a < Re(z) < b, c < Im(z) < d}. -/
def openRect (a b c d : ℝ) : Set ℂ :=
  {z : ℂ | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d}

/-- Closed rectangle in ℂ: {z | a ≤ Re(z) ≤ b, c ≤ Im(z) ≤ d}. -/
def closedRect (a b c d : ℝ) : Set ℂ :=
  {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d}

/-- Boundary of a rectangle (closed minus open). -/
def rectBoundary (a b c d : ℝ) : Set ℂ :=
  closedRect a b c d \ openRect a b c d

theorem openRect_subset_closedRect {a b c d : ℝ} :
    openRect a b c d ⊆ closedRect a b c d :=
  fun _ ⟨h1, h2, h3, h4⟩ => ⟨le_of_lt h1, le_of_lt h2, le_of_lt h3, le_of_lt h4⟩

theorem isOpen_openRect (a b c d : ℝ) : IsOpen (openRect a b c d) := by
  unfold openRect
  apply IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re)
  apply IsOpen.inter (isOpen_lt Complex.continuous_re continuous_const)
  apply IsOpen.inter (isOpen_lt continuous_const Complex.continuous_im)
  exact isOpen_lt Complex.continuous_im continuous_const

/-! ## Logarithmic Contour Integral

The key integral: `(1/2πi) ∫_∂R (f'/f)(s) ds`, decomposed into four line
segments matching Mathlib's `integral_boundary_rect` convention:
  ∫_bottom - ∫_top + I·∫_right - I·∫_left -/

/-- The logarithmic contour integral `(1/2πi) ∫_∂R (f'/f) ds` over a rectangle
    boundary, decomposed into four line segments. This matches Mathlib's
    `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`
    decomposition. -/
def logIntegralRect (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (1 / (2 * ↑Real.pi * I)) * (
    -- Bottom: left→right at height c
    (∫ x in (a : ℝ)..b, logDeriv f (↑x + ↑c * I)) -
    -- Top: left→right at height d
    (∫ x in (a : ℝ)..b, logDeriv f (↑x + ↑d * I)) +
    -- Right: bottom→top at position b
    I * (∫ y in (c : ℝ)..d, logDeriv f (↑b + ↑y * I)) -
    -- Left: bottom→top at position a
    I * (∫ y in (c : ℝ)..d, logDeriv f (↑a + ↑y * I)))

/-- The raw (un-normalized) contour integral ∫_∂R g ds for a function g,
    matching Mathlib's boundary rectangle convention. -/
def contourIntegralRect (g : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x in (a : ℝ)..b, g (↑x + ↑c * I)) -
  (∫ x in (a : ℝ)..b, g (↑x + ↑d * I)) +
  I * (∫ y in (c : ℝ)..d, g (↑b + ↑y * I)) -
  I * (∫ y in (c : ℝ)..d, g (↑a + ↑y * I))

theorem logIntegralRect_eq_normalized_contour (f : ℂ → ℂ) (a b c d : ℝ) :
    logIntegralRect f a b c d =
    (1 / (2 * ↑Real.pi * I)) * contourIntegralRect (logDeriv f) a b c d := by
  unfold logIntegralRect contourIntegralRect
  ring

/-! ## Compactness and Finiteness -/

theorem isCompact_closedRect (a b c d : ℝ) : IsCompact (closedRect a b c d) := by
  rw [show closedRect a b c d = (Set.Icc a b) ×ℂ (Set.Icc c d) from by
    ext z; simp [closedRect, Complex.mem_reProdIm, Set.mem_Icc]; tauto]
  exact isCompact_Icc.reProdIm isCompact_Icc

/-- An entire function that is not identically zero has finitely many zeros in any
    compact set. This follows from isolated zeros (Mathlib) + compactness. -/
theorem finite_zeros_in_compact (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hz : ∃ z, f z ≠ 0)
    (K : Set ℂ) (hK : IsCompact K) :
    {z ∈ K | f z = 0}.Finite := by
  have hanalytic : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  obtain ⟨w, hw⟩ := hz
  rcases hanalytic.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h | h
  · exact absurd (h (Set.mem_univ w)) hw
  · have hmem : {x | f x ≠ 0} ∈ Filter.codiscreteWithin (Set.univ : Set ℂ) := h
    rw [codiscreteWithin_iff_locallyFiniteComplementWithin] at hmem
    have key : ∀ z : ℂ, ∃ t ∈ nhds z, Set.Finite (t ∩ {x | f x = 0}) := by
      intro z
      obtain ⟨t, ht, hfin⟩ := hmem z (Set.mem_univ z)
      exact ⟨t, ht, hfin.subset (fun x hx =>
        ⟨hx.1, Set.mem_univ x, not_not.mpr hx.2⟩)⟩
    choose U hU_nhds hU_fin using key
    have hopen : ∀ z, ∃ V ⊆ U z, IsOpen V ∧ z ∈ V :=
      fun z => mem_nhds_iff.mp (hU_nhds z)
    choose V hV_sub hV_open hV_mem using hopen
    obtain ⟨s, hs_cover⟩ := hK.elim_finite_subcover V (fun z => hV_open z)
      (fun z _ => Set.mem_iUnion.2 ⟨z, hV_mem z⟩)
    refine (s.finite_toSet.biUnion (fun z _ => hU_fin z)).subset ?_
    intro x ⟨hxK, hfx⟩
    obtain ⟨z, hz_mem, hxV⟩ := Set.mem_iUnion₂.mp (hs_cover hxK)
    exact Set.mem_biUnion hz_mem ⟨hV_sub z hxV, hfx⟩

/-! ## Zero Counting for Rectangles -/

/-- The number of zeros of f (counted with multiplicity) inside the open rectangle.
    For entire functions, all zeros have positive multiplicity. -/
def zeroCountRect (f : ℂ → ℂ) (a b c d : ℝ) : ℕ :=
  Set.ncard {z ∈ openRect a b c d | f z = 0}

/-- The multiplicity-counted number of zeros of `f` inside the open rectangle.
    This sums `analyticOrderAt f z` over the interior zero set. If the zero set is
    infinite, this returns `0`; the entire-function route below supplies finiteness. -/
noncomputable def zeroCountRectMult (f : ℂ → ℂ) (a b c d : ℝ) : ℕ :=
  by
    classical
    exact
      if hfin : {z ∈ openRect a b c d | f z = 0}.Finite then
        ∑ z ∈ hfin.toFinset, (analyticOrderAt f z).toNat
      else
        0

theorem zeroCountRectMult_eq_sum (f : ℂ → ℂ) (a b c d : ℝ)
    (hfin : {z ∈ openRect a b c d | f z = 0}.Finite) :
    zeroCountRectMult f a b c d =
      ∑ z ∈ hfin.toFinset, (analyticOrderAt f z).toNat := by
  classical
  unfold zeroCountRectMult
  simp [hfin]

/-- For a non-zero entire function, the zero set in the open rectangle is finite.
    This ensures `zeroCountRect` gives a meaningful natural number. -/
theorem finite_zeros_in_openRect (f : ℂ → ℂ)
    (a b c d : ℝ) (_hab : a < b) (_hcd : c < d)
    (hf : Differentiable ℂ f) (hz : ∃ z, f z ≠ 0) :
    {z ∈ openRect a b c d | f z = 0}.Finite :=
  (finite_zeros_in_compact f hf hz (closedRect a b c d) (isCompact_closedRect a b c d)).subset
    (fun _ ⟨h1, h2⟩ => ⟨openRect_subset_closedRect h1, h2⟩)

private theorem differentiable_dslope (f : ℂ → ℂ) (a : ℂ)
    (hf : Differentiable ℂ f) :
    Differentiable ℂ (dslope f a) := by
  show Differentiable ℂ (dslope f a)
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (isOpen_univ.mem_nhds (Set.mem_univ a))).mpr
    hf.differentiableOn

private theorem mul_dslope_eq (f : ℂ → ℂ) {a z : ℂ} (ha : f a = 0) :
    (z - a) * dslope f a z = f z := by
  simpa [ha, smul_eq_mul] using sub_smul_dslope f a z

private theorem analyticOrderAt_ne_top_of_differentiable (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) {w z : ℂ} (hw : f w ≠ 0) :
    analyticOrderAt f z ≠ ⊤ := by
  have hanalytic : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hbase : analyticOrderAt f w ≠ ⊤ := by
    have hzero : analyticOrderAt f w = 0 :=
      (hf.analyticAt w).analyticOrderAt_eq_zero.mpr hw
    simpa [hzero]
  exact hanalytic.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ w) (Set.mem_univ z) hbase

private theorem analyticOrderAt_toNat_pos_of_mem_zeroSet (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hw : ∃ w, f w ≠ 0)
    {a b c d : ℝ} {z : ℂ}
    (hz : z ∈ {z ∈ openRect a b c d | f z = 0}) :
    0 < (analyticOrderAt f z).toNat := by
  rcases hw with ⟨w, hw⟩
  have hanalytic : AnalyticAt ℂ f z := hf.analyticAt z
  have hne_top : analyticOrderAt f z ≠ ⊤ :=
    analyticOrderAt_ne_top_of_differentiable f hf hw
  have hne_zero : analyticOrderAt f z ≠ 0 :=
    (hanalytic.analyticOrderAt_ne_zero).2 hz.2
  have hnat_ne_zero : (analyticOrderAt f z).toNat ≠ 0 := by
    intro hzero
    have hcast : (((analyticOrderAt f z).toNat : ℕ) : ℕ∞) = analyticOrderAt f z :=
      ENat.coe_toNat hne_top
    apply hne_zero
    rw [← hcast, hzero]
    simp
  exact Nat.pos_of_ne_zero hnat_ne_zero

private theorem logDeriv_eq_one_div_add_logDeriv_dslope (f : ℂ → ℂ)
    (z₀ s : ℂ) (hf : Differentiable ℂ f) (hfz₀ : f z₀ = 0)
    (hs : s ≠ z₀) (hgs : dslope f z₀ s ≠ 0) :
    logDeriv f s = (1 : ℂ) / (s - z₀) + logDeriv (dslope f z₀) s := by
  let g := dslope f z₀
  have hg : Differentiable ℂ g := differentiable_dslope f z₀ hf
  have hfg : f = fun z => (z - z₀) * g z := by
    funext z
    simpa [g, hfz₀, smul_eq_mul] using (mul_dslope_eq f (a := z₀) (z := z) hfz₀).symm
  have hderiv : deriv f s = g s + (s - z₀) * deriv g s := by
    rw [hfg]
    have h1 : HasDerivAt (fun z : ℂ => z - z₀) 1 s := (hasDerivAt_id s).sub_const z₀
    have h2 : HasDerivAt g (deriv g s) s := (hg s).hasDerivAt
    simpa [one_mul, g] using (h1.mul h2).deriv
  have hfs : f s = (s - z₀) * g s := by
    simpa [g, hfz₀, smul_eq_mul] using (mul_dslope_eq f (a := z₀) (z := s) hfz₀).symm
  have hsub : s - z₀ ≠ 0 := sub_ne_zero.mpr hs
  rw [logDeriv_apply, logDeriv_apply, hderiv, hfs]
  field_simp [hgs, hsub]
  simp [g, mul_assoc, mul_left_comm, mul_comm, hgs, hsub]

private theorem intervalIntegrable_logDeriv_horiz (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) {y : ℝ} {p q : ℝ}
    (hzero : ∀ x ∈ Set.uIcc p q, f (↑x + ↑y * I) ≠ 0) :
    IntervalIntegrable (fun x => logDeriv f (↑x + ↑y * I)) MeasureTheory.volume p q := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hlog : AnalyticAt ℂ (logDeriv f) (↑x + ↑y * I) := by
    simpa [logDeriv_apply] using Aristotle.ZetaLogDerivInfra.analyticAt_log_deriv
      (hf.analyticAt _) (hzero x hx)
  have hmap : Continuous (fun x : ℝ => (↑x + ↑y * I : ℂ)) :=
    continuous_ofReal.add (continuous_const.mul continuous_const)
  have hcont : ContinuousAt (fun x : ℝ => logDeriv f (↑x + ↑y * I)) x := by
    exact ContinuousAt.comp
      (show ContinuousAt (fun z : ℂ => logDeriv f z) ((fun x : ℝ => (↑x + ↑y * I : ℂ)) x) from
        hlog.continuousAt)
      (show ContinuousAt (fun x : ℝ => (↑x + ↑y * I : ℂ)) x from hmap.continuousAt)
  exact hcont.continuousWithinAt

private theorem intervalIntegrable_logDeriv_vert (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) {x : ℝ} {p q : ℝ}
    (hzero : ∀ y ∈ Set.uIcc p q, f (↑x + ↑y * I) ≠ 0) :
    IntervalIntegrable (fun y => logDeriv f (↑x + ↑y * I)) MeasureTheory.volume p q := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  have hlog : AnalyticAt ℂ (logDeriv f) (↑x + ↑y * I) := by
    simpa [logDeriv_apply] using Aristotle.ZetaLogDerivInfra.analyticAt_log_deriv
      (hf.analyticAt _) (hzero y hy)
  have hmap : Continuous (fun y : ℝ => (↑x + ↑y * I : ℂ)) :=
    continuous_const.add (continuous_ofReal.mul continuous_const)
  have hcont : ContinuousAt (fun y : ℝ => logDeriv f (↑x + ↑y * I)) y := by
    exact ContinuousAt.comp
      (show ContinuousAt (fun z : ℂ => logDeriv f z) ((fun y : ℝ => (↑x + ↑y * I : ℂ)) y) from
        hlog.continuousAt)
      (show ContinuousAt (fun y : ℝ => (↑x + ↑y * I : ℂ)) y from hmap.continuousAt)
  exact hcont.continuousWithinAt

private theorem analyticOrderNatAt_dslope_eq (f : ℂ → ℂ) (z₀ z : ℂ)
    (hf : Differentiable ℂ f) (hfz₀ : f z₀ = 0)
    (hwf : ∃ w, f w ≠ 0) (hwg : ∃ w, dslope f z₀ w ≠ 0) :
    analyticOrderNatAt f z = analyticOrderNatAt (dslope f z₀) z + if z = z₀ then 1 else 0 := by
  let g := dslope f z₀
  have hg : Differentiable ℂ g := differentiable_dslope f z₀ hf
  have hfg : f = fun s => (s - z₀) * g s := by
    funext s
    simpa [g, hfz₀, smul_eq_mul] using (mul_dslope_eq f (a := z₀) (z := s) hfz₀).symm
  have hne_top_f : analyticOrderAt f z ≠ ⊤ := by
    rcases hwf with ⟨w, hw⟩
    exact analyticOrderAt_ne_top_of_differentiable f hf hw
  have hne_top_g : analyticOrderAt g z ≠ ⊤ := by
    rcases hwg with ⟨w, hw⟩
    exact analyticOrderAt_ne_top_of_differentiable g hg hw
  by_cases hzz : z = z₀
  · have hlin_one : analyticOrderAt (fun s : ℂ => s - z₀) z₀ = 1 := by
      simpa using (analyticOrderAt_centeredMonomial (z₀ := z₀) (n := 1))
    have hlin_top : analyticOrderAt (fun s : ℂ => s - z₀) z₀ ≠ ⊤ := by
      rw [hlin_one]
      simp
    have hne_top_g0 : analyticOrderAt g z₀ ≠ ⊤ := by
      rcases hwg with ⟨w, hw⟩
      exact analyticOrderAt_ne_top_of_differentiable g hg hw
    have hmul :=
      analyticOrderNatAt_mul (f := fun s : ℂ => s - z₀) (g := g)
        (by fun_prop) (hg.analyticAt _) hlin_top hne_top_g0
    have hmul' : analyticOrderNatAt f z₀ = analyticOrderNatAt (fun s : ℂ => s - z₀) z₀ +
        analyticOrderNatAt g z₀ := by
      simpa [Pi.mul_apply, hfg] using hmul
    simpa [g, analyticOrderNatAt, hzz, hlin_one, add_comm, add_left_comm, add_assoc] using hmul'
  · have hlin_zero : analyticOrderAt (fun s : ℂ => s - z₀) z = 0 := by
      exact ((by fun_prop : AnalyticAt ℂ (fun s : ℂ => s - z₀) z).analyticOrderAt_eq_zero).mpr
        (sub_ne_zero.mpr hzz)
    have hlin_top : analyticOrderAt (fun s : ℂ => s - z₀) z ≠ ⊤ := by
      rw [hlin_zero]
      simp
    have hmul :=
      analyticOrderNatAt_mul (f := fun s : ℂ => s - z₀) (g := g)
        (by fun_prop) (hg.analyticAt _) hlin_top hne_top_g
    have hmul' : analyticOrderNatAt f z = analyticOrderNatAt (fun s : ℂ => s - z₀) z +
        analyticOrderNatAt g z := by
      simpa [Pi.mul_apply, hfg] using hmul
    simpa [g, analyticOrderNatAt, hlin_zero, hzz] using hmul'

/-! ## Sub-lemma A: Winding Number for Rectangles

For w inside the open rectangle R = (a,b) × (c,d):
  (1/2πi) ∫_∂R 1/(s - w) ds = 1

This is the rectangle analogue of the Cauchy integral formula for the function 1.
The proof strategy: choose ε small enough that B(w, ε) ⊂ R. Then 1/(s-w) is
holomorphic on R \ {w}, so by Cauchy-Goursat on R minus the ε-disk, the rectangle
integral equals the circle integral. The circle integral gives 2πi by
`Complex.circleIntegral_sub_center_inv_smul`.

Proved via the fundamental theorem of calculus. On each edge, `Complex.log(z - w)` is an
antiderivative (valid when `z - w ∈ slitPlane`). The left edge crosses the branch cut at
`Im(w)`, producing a `2πi` jump that yields the winding number.

Specifically, the four edge integrals are:
- Bottom: `log(b+ic-w) - log(a+ic-w)`  (Im ≠ 0)
- Top (negated): `-(log(b+id-w) - log(a+id-w))`  (Im ≠ 0)
- Right: `log(b+id-w) - log(b+ic-w)`  (Re > 0)
- Left (split at Im(w)): `-(log(a+id-w) - log(a+ic-w) - 2πi)`
These telescope to `2πi`. -/

/-! ### FTC Infrastructure for Winding Number -/

section WindingFTC

set_option maxHeartbeats 3200000

private theorem im_sub_pt {x y : ℝ} {w : ℂ} : (↑x + ↑y * I - w).im = y - w.im := by
  simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re,
    Complex.sub_im]

private theorem re_sub_pt {x y : ℝ} {w : ℂ} : (↑x + ↑y * I - w).re = x - w.re := by
  simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.sub_re]

/-- d/dx [log(x + c'I - w)] = (x + c'I - w)⁻¹ when Im ≠ Im(w). -/
private theorem hasDerivAt_log_horiz_sub {w : ℂ} {x c' : ℝ} (hc : c' ≠ w.im) :
    HasDerivAt (fun t : ℝ => Complex.log (↑t + ↑c' * I - w)) ((↑x + ↑c' * I - w)⁻¹) x := by
  have hsp := Complex.mem_slitPlane_iff.mpr (Or.inr (show (↑x + ↑c' * I - w).im ≠ 0 from
    by rw [im_sub_pt]; exact sub_ne_zero.mpr hc))
  have h1 : HasDerivAt (fun t : ℝ => (↑t + ↑c' * I - w : ℂ)) 1 x := by
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) + (↑c' * I - w)) 1 x := by
      simpa using Complex.ofRealCLM.hasDerivAt.add_const (↑c' * I - w : ℂ)
    have heq : (fun t : ℝ => (↑t : ℂ) + (↑c' * I - w)) = (fun t : ℝ => ↑t + ↑c' * I - w) :=
      funext fun t => by ring
    rwa [heq] at h2
  exact ((Complex.hasDerivAt_log hsp).comp x h1).congr_deriv (mul_one _)

/-- d/dy [I⁻¹ · log(x₀ + yI - w)] = (x₀ + yI - w)⁻¹ when x₀+yI-w ∈ slitPlane. -/
private theorem hasDerivAt_log_vert_sub {w : ℂ} {x₀ y : ℝ}
    (hsp : (↑x₀ + ↑y * I - w) ∈ Complex.slitPlane) :
    HasDerivAt (fun t : ℝ => I⁻¹ * Complex.log (↑x₀ + ↑t * I - w))
      ((↑x₀ + ↑y * I - w)⁻¹) y := by
  have h1 : HasDerivAt (fun t : ℝ => (↑x₀ + ↑t * I - w : ℂ)) I y := by
    have hd := Complex.ofRealCLM.hasDerivAt (x := y)
    have : ⇑Complex.ofRealCLM = fun (t : ℝ) => (t : ℂ) := rfl; rw [this] at hd; simp at hd
    have hd2 : HasDerivAt (fun t : ℝ => ((t : ℂ) * I)) I y :=
      (hd.mul_const I).congr_deriv (one_mul I)
    have h3 := hd2.const_add (↑x₀ - w : ℂ)
    have heq : (fun t : ℝ => ↑x₀ - w + (↑t : ℂ) * I) = (fun t : ℝ => ↑x₀ + ↑t * I - w) :=
      funext fun t => by ring
    rwa [heq] at h3
  exact ((Complex.hasDerivAt_log hsp).comp y h1 |>.const_mul I⁻¹).congr_deriv (by
    rw [← mul_assoc, mul_comm I⁻¹, mul_assoc, inv_mul_cancel₀ I_ne_zero, mul_one])

/-- (·-w)⁻¹ is integrable on horizontal edges where Im ≠ Im(w). -/
private theorem intble_horiz_sub {w : ℂ} {c' : ℝ} (hc : c' ≠ w.im) (p q : ℝ) :
    IntervalIntegrable (fun x => (↑x + ↑c' * I - w)⁻¹) MeasureTheory.volume p q := by
  apply ContinuousOn.intervalIntegrable; apply ContinuousOn.inv₀
  · exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn.sub
      continuousOn_const
  · intro x _; exact Complex.slitPlane_ne_zero (Complex.mem_slitPlane_iff.mpr (Or.inr
      (by rw [im_sub_pt]; exact sub_ne_zero.mpr hc)))

/-- (·-w)⁻¹ is integrable on vertical edges where Re ≠ Re(w). -/
private theorem intble_vert_sub {w : ℂ} {x₀ : ℝ} (hx : x₀ ≠ w.re) (p q : ℝ) :
    IntervalIntegrable (fun y => (↑x₀ + ↑y * I - w)⁻¹) MeasureTheory.volume p q := by
  apply ContinuousOn.intervalIntegrable; apply ContinuousOn.inv₀
  · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn.sub
      continuousOn_const
  · intro y _ h; have := congr_arg Complex.re h
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, Complex.sub_re, Complex.zero_re] at this; exact hx (by linarith)

/-- Tendsto of the antiderivative at the branch cut from below. -/
private theorem tendsto_antideriv_lower {w : ℂ} {a₀ : ℝ} (ha : a₀ < w.re) :
    Filter.Tendsto (fun y : ℝ => I⁻¹ * Complex.log (↑a₀ + ↑y * I - w))
      (nhdsWithin w.im (Set.Iio w.im))
      (nhds (I⁻¹ * (↑(Real.log ‖(↑a₀ + ↑w.im * I - w : ℂ)‖) - ↑Real.pi * I))) := by
  set φ : ℝ → ℂ := fun y => ↑a₀ + ↑y * I - w
  set z₀ := φ w.im
  have hz₀_re : z₀.re < 0 := by
    simp [z₀, φ, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.sub_re]; linarith
  have hz₀_im : z₀.im = 0 := by
    simp [z₀, φ, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.I_re, Complex.sub_im]
  have hcont : Continuous φ :=
    continuous_const.add (continuous_ofReal.mul continuous_const) |>.sub continuous_const
  have htend : Filter.Tendsto φ (nhdsWithin w.im (Set.Iio w.im))
      (nhdsWithin z₀ {z : ℂ | z.im < 0}) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      Filter.eventually_of_mem self_mem_nhdsWithin (fun y (hy : y < w.im) => by
        show (φ y).im < 0
        simp [φ, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
          Complex.I_re, Complex.sub_im]; linarith)⟩
  exact ((Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hz₀_re hz₀_im).comp
    htend).const_mul I⁻¹

/-- Tendsto of the antiderivative at the branch cut from above. -/
private theorem tendsto_antideriv_upper {w : ℂ} {a₀ : ℝ} (ha : a₀ < w.re) :
    Filter.Tendsto (fun y : ℝ => I⁻¹ * Complex.log (↑a₀ + ↑y * I - w))
      (nhdsWithin w.im (Set.Ioi w.im))
      (nhds (I⁻¹ * (↑(Real.log ‖(↑a₀ + ↑w.im * I - w : ℂ)‖) + ↑Real.pi * I))) := by
  set φ : ℝ → ℂ := fun y => ↑a₀ + ↑y * I - w
  set z₀ := φ w.im
  have hz₀_re : z₀.re < 0 := by
    simp [z₀, φ, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.sub_re]; linarith
  have hz₀_im : z₀.im = 0 := by
    simp [z₀, φ, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.I_re, Complex.sub_im]
  have hcont : Continuous φ :=
    continuous_const.add (continuous_ofReal.mul continuous_const) |>.sub continuous_const
  have htend : Filter.Tendsto φ (nhdsWithin w.im (Set.Ioi w.im))
      (nhdsWithin z₀ {z : ℂ | 0 ≤ z.im}) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      Filter.eventually_of_mem self_mem_nhdsWithin (fun y (hy : w.im < y) => by
        show 0 ≤ (φ y).im
        simp [φ, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
          Complex.I_re, Complex.sub_im]; linarith)⟩
  exact ((Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hz₀_re hz₀_im).comp
    htend).const_mul I⁻¹

end WindingFTC

theorem rect_winding_number_eq_one (w : ℂ) (a b c d : ℝ)
    (hab : a < b) (hcd : c < d)
    (hw : w ∈ openRect a b c d) :
    (1 / (2 * ↑Real.pi * I)) * contourIntegralRect (fun s => 1 / (s - w)) a b c d = 1 := by
  obtain ⟨ha_w, hw_b, hc_w, hw_d⟩ := hw
  -- Rewrite 1/(s-w) to (s-w)⁻¹
  simp_rw [one_div]
  -- Suffices: contourIntegralRect (·-w)⁻¹ = 2πi
  suffices h : contourIntegralRect (fun s => (s - w)⁻¹) a b c d = 2 * ↑Real.pi * I by
    rw [h]; field_simp [Real.pi_ne_zero, I_ne_zero]
  unfold contourIntegralRect
  -- Apply FTC on horizontal edges
  have hbot := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_log_horiz_sub (ne_of_lt hc_w)) (intble_horiz_sub (ne_of_lt hc_w) a b)
  have htop := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_log_horiz_sub (ne_of_gt hw_d)) (intble_horiz_sub (ne_of_gt hw_d) a b)
  -- Apply FTC on right vertical edge
  have hright := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hasDerivAt_log_vert_sub (Complex.mem_slitPlane_iff.mpr
      (Or.inl (by rw [re_sub_pt]; linarith)))) (intble_vert_sub (ne_of_gt hw_b) c d)
  -- Split left edge at w.im
  have hleft_split := (intervalIntegral.integral_add_adjacent_intervals
    (intble_vert_sub (ne_of_lt ha_w) c w.im)
    (intble_vert_sub (ne_of_lt ha_w) w.im d)).symm
  -- FTC on left lower half [c, w.im]
  have hcont_c : Filter.Tendsto (fun y : ℝ => I⁻¹ * Complex.log (↑a + ↑y * I - w))
      (nhdsWithin c (Set.Ioi c)) (nhds (I⁻¹ * Complex.log (↑a + ↑c * I - w))) :=
    (hasDerivAt_log_vert_sub (Complex.mem_slitPlane_iff.mpr (Or.inr (by
      rw [im_sub_pt]; linarith)))).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hleft_lo := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hc_w
    (fun y hy => hasDerivAt_log_vert_sub (Complex.mem_slitPlane_iff.mpr
      (Or.inr (by rw [im_sub_pt]; linarith [hy.2]))))
    (intble_vert_sub (ne_of_lt ha_w) c w.im) hcont_c (tendsto_antideriv_lower ha_w)
  -- FTC on left upper half [w.im, d]
  have hcont_d : Filter.Tendsto (fun y : ℝ => I⁻¹ * Complex.log (↑a + ↑y * I - w))
      (nhdsWithin d (Set.Iio d)) (nhds (I⁻¹ * Complex.log (↑a + ↑d * I - w))) :=
    (hasDerivAt_log_vert_sub (Complex.mem_slitPlane_iff.mpr (Or.inr (by
      rw [im_sub_pt]; linarith)))).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hleft_up := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hw_d
    (fun y hy => hasDerivAt_log_vert_sub (Complex.mem_slitPlane_iff.mpr
      (Or.inr (by rw [im_sub_pt]; linarith [hy.1]))))
    (intble_vert_sub (ne_of_lt ha_w) w.im d) (tendsto_antideriv_upper ha_w) hcont_d
  -- Substitute all FTC results
  rw [hbot, htop, hright, hleft_split, hleft_lo, hleft_up]
  -- Now the goal is a pure algebraic identity involving log values and I, I⁻¹
  -- (L_bc - L_ac) - (L_bd - L_ad) + I*(I⁻¹*L_bd - I⁻¹*L_bc) -
  --   I*((I⁻¹*(ln-πi) - I⁻¹*L_ac) + (I⁻¹*L_ad - I⁻¹*(ln+πi))) = 2πi
  -- Using I*I⁻¹ = 1, this telescopes to 2πi
  have hII : I * I⁻¹ = 1 := mul_inv_cancel₀ I_ne_zero
  -- Goal after substitution should be purely algebraic in log values
  -- Let's try to simplify step by step
  -- First, distribute I * (sum)
  simp only [mul_add, mul_sub]
  -- Simplify I * (I⁻¹ * _) = _
  simp only [← mul_assoc, hII, one_mul]
  -- Now everything should telescope
  ring

/-! ## Sub-lemma B: Log-Derivative Decomposition

For f entire with zeros z₁,...,zₙ (all simple) inside R, and no zeros on ∂R:
  f'/f = ∑ₖ 1/(s - zₖ) + h(s)
where h is holomorphic on the closed rectangle.

For higher-order zeros of order mₖ, the partial fraction is mₖ/(s - zₖ).

This follows from the Weierstrass factorization theorem for entire functions,
or more directly: if f(s) = (s - zₖ)^mₖ · gₖ(s) near zₖ with gₖ(zₖ) ≠ 0,
then f'(s)/f(s) = mₖ/(s - zₖ) + gₖ'(s)/gₖ(s) near zₖ. Subtracting all
such principal parts leaves a holomorphic function.

SORRY STATUS: Requires partial-fraction decomposition of f'/f. Mathlib has
`logDeriv_mul` and `logDeriv_fun_zpow` which give the local structure, but
assembling the global decomposition on R requires more work.
For the RvM application, this is applied to ξ(s) which has only simple zeros
(conjectured but consistent with the formalization's N(T) using ncard). -/
private theorem logDeriv_decompose_aux (n : ℕ) :
    ∀ (f : ℂ → ℂ) (K : Set ℂ) (S : Finset ℂ),
    S.card = n → Differentiable ℂ f →
    (∀ z ∈ S, f z = 0) → (∀ z ∈ S, deriv f z ≠ 0) →
    (∀ z ∈ K, z ∉ S → f z ≠ 0) → (∀ z ∈ S, K ∈ nhds z) →
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h K ∧
      ∀ s ∈ K, s ∉ S → logDeriv f s = (∑ z ∈ S, (1 : ℂ) / (s - z)) + h s := by
  induction n with
  | zero =>
    intro f K S hcard hf _ _ hK_nonzero _
    have hS_empty : S = ∅ := Finset.card_eq_zero.mp hcard; subst hS_empty
    refine ⟨logDeriv f, ?_, by simp⟩
    intro z hz; unfold logDeriv
    exact ((hf.analyticAt z).deriv.differentiableAt.div (hf z)
      (hK_nonzero z hz (fun h => nomatch h))).differentiableWithinAt
  | succ n ih =>
    intro f K S hcard hf hS_zeros hS_simple hK_nonzero hK_nhds
    obtain ⟨z₀, hz₀⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    set S' := S.erase z₀
    have hS'_card : S'.card = n := by rw [Finset.card_erase_of_mem hz₀]; omega
    have hz₀_not_S' : z₀ ∉ S' := by intro h; exact (Finset.mem_erase.mp h).1 rfl
    have hinsert : insert z₀ S' = S := Finset.insert_erase hz₀
    have hfz₀ : f z₀ = 0 := hS_zeros z₀ hz₀
    have hdf : deriv f z₀ ≠ 0 := hS_simple z₀ hz₀
    set g := dslope f z₀
    have hg_entire : Differentiable ℂ g := by
      show Differentiable ℂ (dslope f z₀); rw [← differentiableOn_univ]
      exact (Complex.differentiableOn_dslope (isOpen_univ.mem_nhds (Set.mem_univ z₀))).mpr
        hf.differentiableOn
    have hg_zeros : ∀ z ∈ S', g z = 0 := by
      intro z hz; show dslope f z₀ z = 0
      have hne : z ≠ z₀ := (Finset.mem_erase.mp hz).1
      rw [dslope_of_ne _ hne, slope_def_field, hfz₀, sub_zero, div_eq_zero_iff]
      left; exact hS_zeros z (Finset.mem_of_mem_erase hz)
    have hg_simple : ∀ z ∈ S', deriv g z ≠ 0 := by
      intro z hz; show deriv (dslope f z₀) z ≠ 0
      have hne : z ≠ z₀ := (Finset.mem_erase.mp hz).1
      have hfz : f z = 0 := hS_zeros z (Finset.mem_of_mem_erase hz)
      have hfe : (dslope f z₀) =ᶠ[𝓝 z] fun w => f w / (w - z₀) := by
        filter_upwards [isOpen_ne.mem_nhds hne] with w hw
        rw [dslope_of_ne _ hw, slope_def_field, hfz₀, sub_zero]
      -- deriv (dslope f z₀) z = deriv f z / (z - z₀) ≠ 0
      rw [hfe.deriv_eq]
      have hd := (hf z).hasDerivAt.div ((hasDerivAt_id z).sub_const z₀) (sub_ne_zero.mpr hne)
      -- hd gives deriv at z for the quotient; extract the value
      have hval : deriv (fun w => f w / (w - z₀)) z =
          (deriv f z * (z - z₀) - f z * 1) / (z - z₀) ^ 2 := hd.deriv
      rw [hval, hfz]
      simp only [zero_mul, sub_zero, mul_one]
      exact div_ne_zero (mul_ne_zero (hS_simple z (Finset.mem_of_mem_erase hz))
        (sub_ne_zero.mpr hne)) (pow_ne_zero 2 (sub_ne_zero.mpr hne))
    have hg_nonzero : ∀ z ∈ K, z ∉ S' → g z ≠ 0 := by
      intro z hz hzS'; show dslope f z₀ z ≠ 0
      by_cases hzz₀ : z = z₀
      · subst hzz₀; rw [dslope_same]; exact hdf
      · rw [dslope_of_ne _ hzz₀, slope_def_field, hfz₀, sub_zero]
        refine div_ne_zero (hK_nonzero z hz (fun hmem => ?_)) (sub_ne_zero.mpr hzz₀)
        rw [← hinsert, Finset.mem_insert] at hmem
        exact hmem.elim (absurd · hzz₀) (absurd · hzS')
    obtain ⟨h', hh'_diff, hh'_eq⟩ := ih g K S' hS'_card hg_entire hg_zeros hg_simple hg_nonzero
      (fun z hz => hK_nhds z (Finset.mem_of_mem_erase hz))
    exact ⟨h', hh'_diff, fun s hs hsS => by
      have hs_ne : s ≠ z₀ := by
        intro heq; exact hsS (hinsert ▸ heq ▸ Finset.mem_insert_self z₀ S')
      have hs_not : s ∉ S' := by
        intro hmem; exact hsS (hinsert ▸ Finset.mem_insert_of_mem hmem)
      have hsub : s - z₀ ≠ 0 := sub_ne_zero.mpr hs_ne
      have hfs : f s = (s - z₀) * dslope f z₀ s := by
        rw [dslope_of_ne _ hs_ne, slope_def_field, hfz₀, sub_zero, mul_div_cancel₀ _ hsub]
      have hfe : f =ᶠ[𝓝 s] fun z => (z - z₀) * dslope f z₀ z := by
        filter_upwards [isOpen_ne.mem_nhds hs_ne] with w hw
        rw [dslope_of_ne _ hw, slope_def_field, hfz₀, sub_zero,
          mul_div_cancel₀ _ (sub_ne_zero.mpr hw)]
      have hderiv : deriv f s = dslope f z₀ s + (s - z₀) * deriv (dslope f z₀) s := by
        rw [hfe.deriv_eq]
        have h1 : HasDerivAt (fun z => z - z₀) 1 s := (hasDerivAt_id s).sub_const z₀
        have h2 : HasDerivAt (dslope f z₀) (deriv (dslope f z₀) s) s := (hg_entire s).hasDerivAt
        have h3 : HasDerivAt (fun z => (z - z₀) * dslope f z₀ z)
          (1 * dslope f z₀ s + (s - z₀) * deriv (dslope f z₀) s) s := h1.mul h2
        rw [h3.deriv]; ring
      have hgs_ne : dslope f z₀ s ≠ 0 := hg_nonzero s hs hs_not
      have hsplit : deriv f s / f s =
          1 / (s - z₀) + deriv (dslope f z₀) s / dslope f z₀ s := by
        rw [hderiv, hfs]; field_simp
      have hg_eq : deriv (dslope f z₀) s / dslope f z₀ s =
          ∑ z ∈ S', 1 / (s - z) + h' s := by
        have := hh'_eq s hs hs_not; rwa [logDeriv_apply] at this
      show logDeriv f s = (∑ z ∈ S, (1 : ℂ) / (s - z)) + h' s
      rw [logDeriv_apply, hsplit, hg_eq, ← hinsert, Finset.sum_insert hz₀_not_S']; ring⟩

theorem logDeriv_decompose_rect (f : ℂ → ℂ)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hf : Differentiable ℂ f)
    (hbdy : ∀ z ∈ rectBoundary a b c d, f z ≠ 0)
    (hfin : {z ∈ openRect a b c d | f z = 0}.Finite)
    (hsimple : ∀ z ∈ openRect a b c d, f z = 0 → deriv f z ≠ 0) :
    ∃ h : ℂ → ℂ,
      DifferentiableOn ℂ h (closedRect a b c d) ∧
      ∀ s ∈ closedRect a b c d, (∀ z ∈ openRect a b c d, f z = 0 → s ≠ z) →
        logDeriv f s = (∑ z ∈ hfin.toFinset, (1 : ℂ) / (s - z)) + h s := by
  have hS_zeros : ∀ z ∈ hfin.toFinset, f z = 0 :=
    fun z hz => (Set.Finite.mem_toFinset hfin |>.mp hz).2
  have hS_simple : ∀ z ∈ hfin.toFinset, deriv f z ≠ 0 :=
    fun z hz => let ⟨ho, hfz⟩ := Set.Finite.mem_toFinset hfin |>.mp hz; hsimple z ho hfz
  have hK_nonzero : ∀ z ∈ closedRect a b c d, z ∉ hfin.toFinset → f z ≠ 0 := by
    intro z hz hzS
    by_cases hopen : z ∈ openRect a b c d
    · intro hfz; exact hzS (Set.Finite.mem_toFinset hfin |>.mpr ⟨hopen, hfz⟩)
    · exact hbdy z ⟨hz, hopen⟩
  have hK_nhds : ∀ z ∈ hfin.toFinset, closedRect a b c d ∈ nhds z := by
    intro z hz
    have hmem := (Set.Finite.mem_toFinset hfin |>.mp hz).1
    exact Filter.mem_of_superset ((isOpen_openRect a b c d).mem_nhds hmem)
      openRect_subset_closedRect
  obtain ⟨h, hh_diff, hh_eq⟩ := logDeriv_decompose_aux hfin.toFinset.card f
    (closedRect a b c d) hfin.toFinset rfl hf hS_zeros hS_simple hK_nonzero hK_nhds
  exact ⟨h, hh_diff, fun s hs hne => hh_eq s hs (fun hmem =>
    let ⟨hz_open, hfz⟩ := Set.Finite.mem_toFinset hfin |>.mp hmem
    absurd rfl (hne _ hz_open hfz))⟩

/-- Multiplicity-counted version of `logDeriv_decompose_rect`: subtract the full principal part
    with coefficients given by analytic orders. This is the sharp local ingredient needed for the
    multiplicity-counted argument principle. -/
private theorem exists_local_logDeriv_remainder_at_zero (f : ℂ → ℂ) (z₀ : ℂ)
    (hf : Differentiable ℂ f) (hfz₀ : f z₀ = 0) (hwf : ∃ w, f w ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableAt ℂ g z₀ ∧
      ∀ᶠ s in 𝓝[≠] z₀,
        logDeriv f s = (((analyticOrderAt f z₀).toNat : ℂ) / (s - z₀)) + g s := by
  have hne_top : analyticOrderAt f z₀ ≠ ⊤ := by
    rcases hwf with ⟨w, hw⟩
    exact analyticOrderAt_ne_top_of_differentiable f hf hw
  obtain ⟨G, hG_analytic, hG_nonzero, hfac⟩ :=
    (hf.analyticAt z₀).analyticOrderAt_ne_top.mp hne_top
  let m : ℕ := analyticOrderNatAt f z₀
  let F : ℂ → ℂ := fun s => (s - z₀) ^ m * G s
  have hfac' : ∀ᶠ s in 𝓝 z₀, f s = F s := by
    simpa [F, m, smul_eq_mul] using hfac
  have hpow :
      ∀ᶠ s in 𝓝[≠] z₀,
        logDeriv F s = ((m : ℂ) / (s - z₀)) + logDeriv G s := by
    simpa [F, logDeriv_apply] using
      Aristotle.ZetaLogDerivInfra.log_deriv_pow_mul_analytic z₀ m G hG_analytic hG_nonzero
  obtain ⟨U, hUf, hUo, hzU⟩ := eventually_nhds_iff.mp hfac'
  have hU : U ∈ 𝓝[≠] z₀ := mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hzU)
  have hlogG : DifferentiableAt ℂ (logDeriv G) z₀ := by
    simpa [logDeriv_apply] using
      (Aristotle.ZetaLogDerivInfra.analyticAt_log_deriv hG_analytic hG_nonzero).differentiableAt
  refine ⟨logDeriv G, hlogG, ?_⟩
  filter_upwards [hpow, hU] with s hs_pow hsU
  have hfs : f s = F s := hUf s hsU
  have hderiv : deriv f s = deriv F s := by
    exact Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (hUo.mem_nhds hsU) hUf)
  simpa [F, m, analyticOrderNatAt, logDeriv_apply, hderiv, hfs] using hs_pow

theorem logDeriv_decompose_rect_mult (f : ℂ → ℂ)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hf : Differentiable ℂ f)
    (hbdy : ∀ z ∈ rectBoundary a b c d, f z ≠ 0)
    (hfin : {z ∈ openRect a b c d | f z = 0}.Finite) :
    ∃ h : ℂ → ℂ,
      DifferentiableOn ℂ h (closedRect a b c d) ∧
      ∀ s ∈ closedRect a b c d, (∀ z ∈ openRect a b c d, f z = 0 → s ≠ z) →
        logDeriv f s =
          (∑ z ∈ hfin.toFinset, (((analyticOrderAt f z).toNat : ℂ) / (s - z))) + h s := by
  classical
  let S : Finset ℂ := hfin.toFinset
  have hS_zeros : ∀ z ∈ S, f z = 0 := by
    intro z hz
    exact (Set.Finite.mem_toFinset hfin |>.mp hz).2
  have hK_nonzero : ∀ z ∈ closedRect a b c d, z ∉ S → f z ≠ 0 := by
    intro z hz hzS
    by_cases hopen : z ∈ openRect a b c d
    · intro hfz
      exact hzS (Set.Finite.mem_toFinset hfin |>.mpr ⟨hopen, hfz⟩)
    · exact hbdy z ⟨hz, hopen⟩
  have hcorner : ((a : ℂ) + (c : ℂ) * I) ∈ rectBoundary a b c d := by
    constructor
    · simp [closedRect, hab.le, hcd.le]
    · simp [openRect, not_lt.mpr hab.le]
  have hwf : ∃ w, f w ≠ 0 := ⟨(a : ℂ) + (c : ℂ) * I, hbdy _ hcorner⟩
  have hS_local : ∀ z ∈ S, ∃ g : ℂ → ℂ, DifferentiableAt ℂ g z ∧
      ∀ᶠ s in 𝓝[≠] z,
        logDeriv f s = (((analyticOrderAt f z).toNat : ℂ) / (s - z)) + g s := by
    intro z hz
    exact exists_local_logDeriv_remainder_at_zero f z hf (hS_zeros z hz) hwf
  choose H hHdiff hHeq using hS_local
  let h : ℂ → ℂ := fun s =>
    if hs : s ∈ S then
      H s hs s - ∑ z ∈ S.erase s, (((analyticOrderAt f z).toNat : ℂ) / (s - z))
    else
      logDeriv f s - ∑ z ∈ S, (((analyticOrderAt f z).toNat : ℂ) / (s - z))
  refine ⟨h, ?_, ?_⟩
  · intro s hs_closed
    by_cases hsS : s ∈ S
    · let g : ℂ → ℂ := fun w =>
        H s hsS w - ∑ z ∈ S.erase s, (((analyticOrderAt f z).toNat : ℂ) / (w - z))
      have hg_sum : DifferentiableAt ℂ
          (fun w => ∑ z ∈ S.erase s, (((analyticOrderAt f z).toNat : ℂ) / (w - z))) s := by
        refine DifferentiableAt.fun_sum ?_
        intro z hz
        have hne : z ≠ s := (Finset.mem_erase.mp hz).1
        exact (differentiableAt_const (((analyticOrderAt f z).toNat : ℂ))).div
          (differentiableAt_id.sub_const z)
          (sub_ne_zero.mpr hne.symm)
      have hg_diff : DifferentiableWithinAt ℂ g (closedRect a b c d) s :=
        ((hHdiff s hsS).sub hg_sum).differentiableWithinAt
      let C : Set ℂ := {w | w ≠ s ∧ w ∉ S.erase s ∧
        logDeriv f w = (((analyticOrderAt f s).toNat : ℂ) / (w - s)) + H s hsS w}
      have hC : C ∈ 𝓝[≠] s := by
        have hne : {w | w ≠ s} ∈ 𝓝[≠] s := self_mem_nhdsWithin
        have havoid : {w | w ∉ S.erase s} ∈ 𝓝[≠] s := by
          have hmem : s ∈ ((↑(S.erase s) : Set ℂ)ᶜ) := by
            simp
          exact mem_nhdsWithin_of_mem_nhds
            (((S.erase s).finite_toSet.isClosed.isOpen_compl).mem_nhds hmem)
        exact Filter.inter_mem hne <|
          Filter.inter_mem havoid (by simpa [C] using hHeq s hsS)
      have hEq : h =ᶠ[𝓝[closedRect a b c d] s] g := by
        have hC' : insert s C ∈ 𝓝 s := (insert_mem_nhds_iff).2 hC
        have hC'' : insert s C ∈ 𝓝[closedRect a b c d] s :=
          mem_nhdsWithin_of_mem_nhds hC'
        filter_upwards [hC''] with w hw
        rcases hw with rfl | hwC
        · simp [h, g, hsS]
        · have hw_notS : w ∉ S := by
            intro hwS
            exact hwC.2.1 (by simpa [Finset.mem_erase, hwC.1, hwS])
          have hw_sum :
              (∑ z ∈ S, (((analyticOrderAt f z).toNat : ℂ) / (w - z))) =
                (((analyticOrderAt f s).toNat : ℂ) / (w - s)) +
                  ∑ z ∈ S.erase s, (((analyticOrderAt f z).toNat : ℂ) / (w - z)) := by
            rw [← Finset.insert_erase hsS, Finset.sum_insert]
            · simp
            · simp
          simp [h, g, hw_notS, hw_sum, hwC.2.2]
      exact hg_diff.congr_of_eventuallyEq_of_mem hEq hs_closed
    · let g : ℂ → ℂ := fun w =>
        logDeriv f w - ∑ z ∈ S, (((analyticOrderAt f z).toNat : ℂ) / (w - z))
      have hs_nonzero : f s ≠ 0 := hK_nonzero s hs_closed hsS
      have hg_log_an : AnalyticAt ℂ (logDeriv f) s := by
        simpa [logDeriv_apply] using
          Aristotle.ZetaLogDerivInfra.analyticAt_log_deriv (hf.analyticAt s) hs_nonzero
      have hg_log : DifferentiableAt ℂ (logDeriv f) s := hg_log_an.differentiableAt
      have hg_sum : DifferentiableAt ℂ
          (fun w => ∑ z ∈ S, (((analyticOrderAt f z).toNat : ℂ) / (w - z))) s := by
        refine DifferentiableAt.fun_sum ?_
        intro z hz
        have hne : s ≠ z := by
          intro hsz
          apply hsS
          simpa [hsz] using hz
        exact (differentiableAt_const (((analyticOrderAt f z).toNat : ℂ))).div
          (differentiableAt_id.sub_const z)
          (sub_ne_zero.mpr hne)
      have hg_diff : DifferentiableWithinAt ℂ g (closedRect a b c d) s :=
        (hg_log.sub hg_sum).differentiableWithinAt
      have havoid : {w | w ∉ S} ∈ 𝓝[closedRect a b c d] s := by
        have hmem : s ∈ ((↑S : Set ℂ)ᶜ) := by simpa using hsS
        exact mem_nhdsWithin_of_mem_nhds
          ((S.finite_toSet.isClosed.isOpen_compl).mem_nhds hmem)
      have hEq : h =ᶠ[𝓝[closedRect a b c d] s] g := by
        filter_upwards [havoid] with w hw
        simp [h, g, hw]
      exact hg_diff.congr_of_eventuallyEq_of_mem hEq hs_closed
  · intro s hs_closed hne
    have hsS : s ∉ S := by
      intro hs_mem
      rcases Set.Finite.mem_toFinset hfin |>.mp hs_mem with ⟨hs_open, hs_zero⟩
      exact (hne s hs_open hs_zero) rfl
    simp [h, hsS]
    ring

/-! ## Sub-lemma C: Cauchy-Goursat for Rectangles (MATHLIB)

This is `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`.
It states that for a function holomorphic on an open set containing the closed
rectangle (minus a countable set), the boundary integral is zero.

We record a convenient form using our `contourIntegralRect` definition. -/

private lemma closedRect_eq_uIcc_prod {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    closedRect a b c d = Set.uIcc a b ×ℂ Set.uIcc c d := by
  ext z
  simp only [closedRect, Set.mem_setOf_eq, Complex.mem_reProdIm,
    Set.uIcc_of_le hab, Set.uIcc_of_le hcd, Set.mem_Icc]
  tauto

/-- Cauchy-Goursat for rectangles: the contour integral of a holomorphic function
    around a rectangle boundary is zero. This follows directly from Mathlib's
    `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`. -/
theorem cauchy_goursat_rect (g : ℂ → ℂ) (a b c d : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (hg : DifferentiableOn ℂ g (closedRect a b c d)) :
    contourIntegralRect g a b c d = 0 := by
  rw [closedRect_eq_uIcc_prod hab hcd] at hg
  unfold contourIntegralRect
  have hre1 : (↑a + ↑c * I : ℂ).re = a := by simp
  have him1 : (↑a + ↑c * I : ℂ).im = c := by simp
  have hre2 : (↑b + ↑d * I : ℂ).re = b := by simp
  have him2 : (↑b + ↑d * I : ℂ).im = d := by simp
  have key := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g
    (↑a + ↑c * I) (↑b + ↑d * I)
  rw [hre1, him1, hre2, him2, smul_eq_mul, smul_eq_mul] at key
  exact key hg

/-! ## Contour Integral Linearity

Infrastructure for composing the argument principle from sub-lemmas. -/

/-- `contourIntegralRect` distributes over addition, given integrability. -/
theorem contourIntegralRect_add (g₁ g₂ : ℂ → ℂ) (a b c d : ℝ)
    (h₁b : IntervalIntegrable (fun x => g₁ (↑x + ↑c * I)) MeasureTheory.volume a b)
    (h₂b : IntervalIntegrable (fun x => g₂ (↑x + ↑c * I)) MeasureTheory.volume a b)
    (h₁t : IntervalIntegrable (fun x => g₁ (↑x + ↑d * I)) MeasureTheory.volume a b)
    (h₂t : IntervalIntegrable (fun x => g₂ (↑x + ↑d * I)) MeasureTheory.volume a b)
    (h₁r : IntervalIntegrable (fun y => g₁ (↑b + ↑y * I)) MeasureTheory.volume c d)
    (h₂r : IntervalIntegrable (fun y => g₂ (↑b + ↑y * I)) MeasureTheory.volume c d)
    (h₁l : IntervalIntegrable (fun y => g₁ (↑a + ↑y * I)) MeasureTheory.volume c d)
    (h₂l : IntervalIntegrable (fun y => g₂ (↑a + ↑y * I)) MeasureTheory.volume c d) :
    contourIntegralRect (g₁ + g₂) a b c d =
    contourIntegralRect g₁ a b c d + contourIntegralRect g₂ a b c d := by
  simp only [contourIntegralRect, Pi.add_apply]
  rw [intervalIntegral.integral_add h₁b h₂b, intervalIntegral.integral_add h₁t h₂t,
      intervalIntegral.integral_add h₁r h₂r, intervalIntegral.integral_add h₁l h₂l]
  ring

/-- `contourIntegralRect` commutes with multiplication by a complex constant. -/
theorem contourIntegralRect_const_mul (c : ℂ) (g : ℂ → ℂ) (a b c' d : ℝ)
    (hb : IntervalIntegrable (fun x => g (↑x + ↑c' * I)) MeasureTheory.volume a b)
    (ht : IntervalIntegrable (fun x => g (↑x + ↑d * I)) MeasureTheory.volume a b)
    (hr : IntervalIntegrable (fun y => g (↑b + ↑y * I)) MeasureTheory.volume c' d)
    (hl : IntervalIntegrable (fun y => g (↑a + ↑y * I)) MeasureTheory.volume c' d) :
    contourIntegralRect (fun z => c * g z) a b c' d = c * contourIntegralRect g a b c' d := by
  unfold contourIntegralRect
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

/-- Points on rectangle edges lie in the closed rectangle. -/
private theorem edge_mem_closedRect {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (x : ℝ) (hx1 : a ≤ x) (hx2 : x ≤ b) (y : ℝ) (hy1 : c ≤ y) (hy2 : y ≤ d) :
    (↑x + ↑y * I : ℂ) ∈ closedRect a b c d := by
  simp only [closedRect, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im,
    Complex.add_im, Complex.mul_im] <;> linarith

/-- Points on rectangle edges are NOT in the open rectangle (at least one coord is extremal). -/
private theorem bottom_edge_not_openRect {a b c d : ℝ} (x : ℝ) :
    (↑x + ↑c * I : ℂ) ∉ openRect a b c d := by
  intro ⟨_, _, h3, _⟩
  simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re] at h3

private theorem top_edge_not_openRect {a b c d : ℝ} (x : ℝ) :
    (↑x + ↑d * I : ℂ) ∉ openRect a b c d := by
  intro ⟨_, _, _, h4⟩
  simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re] at h4

private theorem right_edge_not_openRect {a b c d : ℝ} (y : ℝ) :
    (↑b + ↑y * I : ℂ) ∉ openRect a b c d := by
  intro ⟨_, h2, _, _⟩
  simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im] at h2

private theorem left_edge_not_openRect {a b c d : ℝ} (y : ℝ) :
    (↑a + ↑y * I : ℂ) ∉ openRect a b c d := by
  intro ⟨h1, _, _, _⟩
  simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im] at h1

/-- On rectangle edges, a point not in openRect cannot equal any point in openRect. -/
private theorem edge_ne_interior_zero {a b c d : ℝ} {s z : ℂ} (hs : s ∉ openRect a b c d)
    (hz : z ∈ openRect a b c d) : s ≠ z :=
  fun h => hs (h ▸ hz)

/-- `contourIntegralRect` respects pointwise equality on the rectangle boundary.
    If g₁ = g₂ at all points traversed by the contour, then the integrals agree. -/
theorem contourIntegralRect_congr_boundary (g₁ g₂ : ℂ → ℂ) (a b c d : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (hbot : ∀ x ∈ Set.Icc a b, g₁ (↑x + ↑c * I) = g₂ (↑x + ↑c * I))
    (htop : ∀ x ∈ Set.Icc a b, g₁ (↑x + ↑d * I) = g₂ (↑x + ↑d * I))
    (hright : ∀ y ∈ Set.Icc c d, g₁ (↑b + ↑y * I) = g₂ (↑b + ↑y * I))
    (hleft : ∀ y ∈ Set.Icc c d, g₁ (↑a + ↑y * I) = g₂ (↑a + ↑y * I)) :
    contourIntegralRect g₁ a b c d = contourIntegralRect g₂ a b c d := by
  unfold contourIntegralRect
  congr 1; congr 1; congr 1
  · apply intervalIntegral.integral_congr
    intro x hx; rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx; exact hbot x hx
  · apply intervalIntegral.integral_congr
    intro x hx; rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx; exact htop x hx
  · congr 1; apply intervalIntegral.integral_congr
    intro y hy; rw [Set.uIcc_of_le hcd, Set.mem_Icc] at hy; exact hright y hy
  · congr 1; apply intervalIntegral.integral_congr
    intro y hy; rw [Set.uIcc_of_le hcd, Set.mem_Icc] at hy; exact hleft y hy

/-! ## The Argument Principle for Rectangles

Composed from sub-lemmas A, B, C:
1. By (B), f'/f = ∑ 1/(s-zₖ) + h where h is holomorphic on R
2. By linearity, ∫_∂R f'/f = ∑ₖ ∫_∂R 1/(s-zₖ) + ∫_∂R h
3. By (C), ∫_∂R h = 0 since h is holomorphic
4. By (A), (1/2πi) ∫_∂R 1/(s-zₖ) = 1 for each zₖ inside R
5. Summing: (1/2πi) ∫_∂R f'/f = ∑ₖ 1 = n = #{zeros}

SORRY STATUS: The three sub-lemmas above are sorry'd. The composition itself
(this theorem) will be provable once those are closed. The deepest sorry is
`rect_winding_number_eq_one` which requires contour deformation. -/
/-- The boundary of a rectangle lies inside the closed rectangle. -/
theorem rectBoundary_subset_closedRect {a b c d : ℝ} :
    rectBoundary a b c d ⊆ closedRect a b c d :=
  fun _ h => h.1

/-- Points on the boundary are not in the open rectangle. -/
theorem rectBoundary_disjoint_openRect {a b c d : ℝ} :
    Disjoint (rectBoundary a b c d) (openRect a b c d) := by
  rw [Set.disjoint_iff]
  intro z ⟨hbdy, hopen⟩
  exact hbdy.2 hopen

/-- Sum of interval-integrable functions is interval-integrable. -/
private theorem intervalIntegrable_finset_sum {ι : Type*} (t : Finset ι)
    (f : ι → ℝ → ℂ) (p q : ℝ)
    (hf : ∀ i ∈ t, IntervalIntegrable (f i) volume p q) :
    IntervalIntegrable (fun x => ∑ i ∈ t, f i x) volume p q := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact intervalIntegrable_const
  | @insert a t' hna ih =>
    simp only [Finset.sum_insert hna]
    exact (hf a (Finset.mem_insert_self a t')).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Contour integral distributes over a finite sum plus a remainder term.
    Each g_i must be interval-integrable on each edge. -/
theorem contourIntegralRect_finset_sum_add {ι : Type*} (s : Finset ι)
    (g : ι → ℂ → ℂ) (h : ℂ → ℂ) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    -- Integrability of each gᵢ on the 4 edges
    (hg_bot : ∀ i ∈ s, IntervalIntegrable (fun x => g i (↑x + ↑c * I)) MeasureTheory.volume a b)
    (hg_top : ∀ i ∈ s, IntervalIntegrable (fun x => g i (↑x + ↑d * I)) MeasureTheory.volume a b)
    (hg_right : ∀ i ∈ s, IntervalIntegrable (fun y => g i (↑b + ↑y * I)) MeasureTheory.volume c d)
    (hg_left : ∀ i ∈ s, IntervalIntegrable (fun y => g i (↑a + ↑y * I)) MeasureTheory.volume c d)
    -- Integrability of h on the 4 edges
    (hh_bot : IntervalIntegrable (fun x => h (↑x + ↑c * I)) MeasureTheory.volume a b)
    (hh_top : IntervalIntegrable (fun x => h (↑x + ↑d * I)) MeasureTheory.volume a b)
    (hh_right : IntervalIntegrable (fun y => h (↑b + ↑y * I)) MeasureTheory.volume c d)
    (hh_left : IntervalIntegrable (fun y => h (↑a + ↑y * I)) MeasureTheory.volume c d) :
    contourIntegralRect (fun z => (∑ i ∈ s, g i z) + h z) a b c d =
    (∑ i ∈ s, contourIntegralRect (g i) a b c d) + contourIntegralRect h a b c d := by
  -- Sum is integrable on each edge
  have sum_bot := intervalIntegrable_finset_sum s _ a b (fun i hi => hg_bot i hi)
  have sum_top := intervalIntegrable_finset_sum s _ a b (fun i hi => hg_top i hi)
  have sum_right := intervalIntegrable_finset_sum s _ c d (fun i hi => hg_right i hi)
  have sum_left := intervalIntegrable_finset_sum s _ c d (fun i hi => hg_left i hi)
  -- Unfold and use linearity on each edge
  unfold contourIntegralRect
  rw [intervalIntegral.integral_add sum_bot hh_bot,
      intervalIntegral.integral_add sum_top hh_top,
      intervalIntegral.integral_add sum_right hh_right,
      intervalIntegral.integral_add sum_left hh_left,
      intervalIntegral.integral_finset_sum (fun i hi => hg_bot i hi),
      intervalIntegral.integral_finset_sum (fun i hi => hg_top i hi),
      intervalIntegral.integral_finset_sum (fun i hi => hg_right i hi),
      intervalIntegral.integral_finset_sum (fun i hi => hg_left i hi)]
  simp only [mul_add, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- The lower-left corner of a rectangle lies on its boundary. -/
theorem corner_mem_rectBoundary {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    (↑a + ↑c * I : ℂ) ∈ rectBoundary a b c d := by
  constructor
  · -- In closedRect
    simp only [closedRect, Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · -- Not in openRect
    simp only [openRect, Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im]
    push_neg; intro _; linarith

/-- **Argument principle for rectangles (entire functions).**
    Composed from sub-lemmas A (winding number), B (log-derivative decomposition),
    and C (Cauchy-Goursat). The structure:
    1. f'/f = ∑ₖ 1/(s-zₖ) + h(s) where h is holomorphic on R
    2. ∫_∂R f'/f = ∑ₖ ∫_∂R 1/(s-zₖ) + ∫_∂R h = ∑ₖ 2πi + 0 = 2πi·n -/
theorem argument_principle_rect_entire (f : ℂ → ℂ)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hf : Differentiable ℂ f)
    (hbdy : ∀ z ∈ rectBoundary a b c d, f z ≠ 0)
    (hsimple : ∀ z ∈ openRect a b c d, f z = 0 → deriv f z ≠ 0) :
    logIntegralRect f a b c d = ↑(zeroCountRect f a b c d) := by
  -- Obtain the zero set and its finiteness
  have hz : ∃ z, f z ≠ 0 := ⟨_, hbdy _ (corner_mem_rectBoundary hab hcd)⟩
  have hfin := finite_zeros_in_openRect f a b c d hab hcd hf hz
  -- Get the decomposition from sub-lemma B
  obtain ⟨h, hh_diff, hh_eq⟩ :=
    logDeriv_decompose_rect f a b c d hab hcd hf hbdy hfin hsimple
  -- Apply Cauchy-Goursat to the holomorphic part h
  have hh_zero := cauchy_goursat_rect h a b c d (le_of_lt hab) (le_of_lt hcd) hh_diff
  -- Apply the winding number formula to each zero
  have hwinding : ∀ z ∈ hfin.toFinset,
    (1 / (2 * ↑Real.pi * I)) * contourIntegralRect (fun s => 1 / (s - z)) a b c d = 1 := by
    intro z hz
    have hz_open : z ∈ openRect a b c d := by
      rw [Set.Finite.mem_toFinset] at hz; exact hz.1
    exact rect_winding_number_eq_one z a b c d hab hcd hz_open
  -- The logIntegralRect = (1/2πi) * contourIntegralRect (logDeriv f)
  rw [logIntegralRect_eq_normalized_contour]
  -- Unfold zeroCountRect and relate to Finset.card via finiteness
  unfold zeroCountRect
  rw [Set.ncard_eq_toFinset_card _ hfin]
  -- Step 1: On the boundary, logDeriv f = ∑ 1/(·-zₖ) + h, so the contour integrals agree
  -- Edge points are in closedRect but not in openRect, so the decomposition applies
  have hdecomp_eq : ∀ s ∈ closedRect a b c d, s ∉ openRect a b c d →
      logDeriv f s = (∑ z ∈ hfin.toFinset, (1 : ℂ) / (s - z)) + h s := by
    intro s hs hsnot
    exact hh_eq s hs (fun z hz hfz => edge_ne_interior_zero hsnot hz)
  -- Step 2: Replace logDeriv f by the decomposition on the contour
  have hcontour_eq : contourIntegralRect (logDeriv f) a b c d =
      contourIntegralRect (fun s => (∑ z ∈ hfin.toFinset, (1 : ℂ) / (s - z)) + h s)
        a b c d := by
    apply contourIntegralRect_congr_boundary _ _ _ _ _ _ (le_of_lt hab) (le_of_lt hcd)
    · -- Bottom edge
      intro x hx
      exact hdecomp_eq _ (edge_mem_closedRect (le_of_lt hab) (le_of_lt hcd) x hx.1 hx.2 c
        (le_refl _) (le_of_lt hcd)) (bottom_edge_not_openRect x)
    · -- Top edge
      intro x hx
      exact hdecomp_eq _ (edge_mem_closedRect (le_of_lt hab) (le_of_lt hcd) x hx.1 hx.2 d
        (le_of_lt hcd) (le_refl _)) (top_edge_not_openRect x)
    · -- Right edge
      intro y hy
      exact hdecomp_eq _ (edge_mem_closedRect (le_of_lt hab) (le_of_lt hcd) b
        (le_of_lt hab) (le_refl _) y hy.1 hy.2) (right_edge_not_openRect y)
    · -- Left edge
      intro y hy
      exact hdecomp_eq _ (edge_mem_closedRect (le_of_lt hab) (le_of_lt hcd) a
        (le_refl _) (le_of_lt hab) y hy.1 hy.2) (left_edge_not_openRect y)
  rw [hcontour_eq]
  -- Step 3: Suffices to show the contour integral decomposes linearly
  suffices h_linear : contourIntegralRect
      (fun s => (∑ z ∈ hfin.toFinset, (1 : ℂ) / (s - z)) + h s) a b c d =
      (∑ z ∈ hfin.toFinset, contourIntegralRect (fun s => 1 / (s - z)) a b c d) +
      contourIntegralRect h a b c d by
    rw [h_linear, hh_zero, add_zero, Finset.mul_sum]
    -- Now goal: ∑ₖ (1/2πi * contourIntegralRect (1/(·-zₖ))) = ↑card
    have : ∀ z ∈ hfin.toFinset, (1 / (2 * ↑Real.pi * I)) *
        contourIntegralRect (fun s => 1 / (s - z)) a b c d = (1 : ℂ) := hwinding
    rw [Finset.sum_congr rfl this]
    simp [Finset.sum_const, mul_one]
  exact contourIntegralRect_finset_sum_add hfin.toFinset
    (fun z s => 1 / (s - z)) h a b c d (le_of_lt hab) (le_of_lt hcd)
    (by intro z hz; rw [Set.Finite.mem_toFinset] at hz
        apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div continuousOn_const
        · exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn.sub
            continuousOn_const
        · intro x hx; rw [Set.uIcc_of_le (le_of_lt hab), Set.mem_Icc] at hx
          simp only [sub_ne_zero]
          exact edge_ne_interior_zero (bottom_edge_not_openRect x) hz.1)
    (by intro z hz; rw [Set.Finite.mem_toFinset] at hz
        apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div continuousOn_const
        · exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn.sub
            continuousOn_const
        · intro x hx; rw [Set.uIcc_of_le (le_of_lt hab), Set.mem_Icc] at hx
          simp only [sub_ne_zero]
          exact edge_ne_interior_zero (top_edge_not_openRect x) hz.1)
    (by intro z hz; rw [Set.Finite.mem_toFinset] at hz
        apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div continuousOn_const
        · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn.sub
            continuousOn_const
        · intro y hy; rw [Set.uIcc_of_le (le_of_lt hcd), Set.mem_Icc] at hy
          simp only [sub_ne_zero]
          exact edge_ne_interior_zero (right_edge_not_openRect y) hz.1)
    (by intro z hz; rw [Set.Finite.mem_toFinset] at hz
        apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div continuousOn_const
        · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn.sub
            continuousOn_const
        · intro y hy; rw [Set.uIcc_of_le (le_of_lt hcd), Set.mem_Icc] at hy
          simp only [sub_ne_zero]
          exact edge_ne_interior_zero (left_edge_not_openRect y) hz.1)
    (hh_diff.continuousOn.comp
      (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
      (fun x hx => by
        rw [Set.uIcc_of_le (le_of_lt hab), Set.mem_Icc] at hx
        exact edge_mem_closedRect (le_of_lt hab) (le_of_lt hcd) x hx.1 hx.2 c
          (le_refl _) (le_of_lt hcd))).intervalIntegrable
    (hh_diff.continuousOn.comp
      (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
      (fun x hx => by
        rw [Set.uIcc_of_le (le_of_lt hab), Set.mem_Icc] at hx
        exact edge_mem_closedRect (le_of_lt hab) (le_of_lt hcd) x hx.1 hx.2 d
          (le_of_lt hcd) (le_refl _))).intervalIntegrable
    (hh_diff.continuousOn.comp
      (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      (fun y hy => by
        rw [Set.uIcc_of_le (le_of_lt hcd), Set.mem_Icc] at hy
        exact edge_mem_closedRect (le_of_lt hab) (le_of_lt hcd) b
          (le_of_lt hab) (le_refl _) y hy.1 hy.2)).intervalIntegrable
    (hh_diff.continuousOn.comp
      (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      (fun y hy => by
        rw [Set.uIcc_of_le (le_of_lt hcd), Set.mem_Icc] at hy
        exact edge_mem_closedRect (le_of_lt hab) (le_of_lt hcd) a
          (le_refl _) (le_of_lt hab) y hy.1 hy.2)).intervalIntegrable

/-- Multiplicity-counted rectangle argument principle, with the zero count expressed as
    an explicit sum of analytic orders over the interior zero set. This is the additive
    parallel surface to `argument_principle_rect_entire`, leaving the simple-zero API intact
    for current callers. -/
theorem argument_principle_rect_entire_mult_sum (f : ℂ → ℂ)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hf : Differentiable ℂ f)
    (hbdy : ∀ z ∈ rectBoundary a b c d, f z ≠ 0)
    (hfin : {z ∈ openRect a b c d | f z = 0}.Finite) :
    logIntegralRect f a b c d =
      ↑(∑ z ∈ hfin.toFinset, (analyticOrderAt f z).toNat) := by
  obtain ⟨h, hh_diff, hh_eq⟩ :=
    logDeriv_decompose_rect_mult f a b c d hab hcd hf hbdy hfin
  have hh_zero := cauchy_goursat_rect h a b c d (le_of_lt hab) (le_of_lt hcd) hh_diff
  have hwinding : ∀ z ∈ hfin.toFinset,
    (1 / (2 * ↑Real.pi * I)) *
        contourIntegralRect
          (fun s => (((analyticOrderAt f z).toNat : ℂ) / (s - z))) a b c d =
      ↑((analyticOrderAt f z).toNat) := by
    intro z hz
    have hz_open : z ∈ openRect a b c d := by
      rw [Set.Finite.mem_toFinset] at hz
      exact hz.1
    have hconst :=
      contourIntegralRect_const_mul (((analyticOrderAt f z).toNat : ℂ))
        (fun s => 1 / (s - z)) a b c d
        (by
          apply ContinuousOn.intervalIntegrable
          apply ContinuousOn.div continuousOn_const
          · exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn.sub
              continuousOn_const
          · intro x hx
            rw [Set.uIcc_of_le (le_of_lt hab), Set.mem_Icc] at hx
            simp only [sub_ne_zero]
            exact edge_ne_interior_zero (bottom_edge_not_openRect x) hz_open)
        (by
          apply ContinuousOn.intervalIntegrable
          apply ContinuousOn.div continuousOn_const
          · exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn.sub
              continuousOn_const
          · intro x hx
            rw [Set.uIcc_of_le (le_of_lt hab), Set.mem_Icc] at hx
            simp only [sub_ne_zero]
            exact edge_ne_interior_zero (top_edge_not_openRect x) hz_open)
        (by
          apply ContinuousOn.intervalIntegrable
          apply ContinuousOn.div continuousOn_const
          · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn.sub
              continuousOn_const
          · intro y hy
            rw [Set.uIcc_of_le (le_of_lt hcd), Set.mem_Icc] at hy
            simp only [sub_ne_zero]
            exact edge_ne_interior_zero (right_edge_not_openRect y) hz_open)
        (by
          apply ContinuousOn.intervalIntegrable
          apply ContinuousOn.div continuousOn_const
          · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn.sub
              continuousOn_const
          · intro y hy
            rw [Set.uIcc_of_le (le_of_lt hcd), Set.mem_Icc] at hy
            simp only [sub_ne_zero]
            exact edge_ne_interior_zero (left_edge_not_openRect y) hz_open)
    have hwind := rect_winding_number_eq_one z a b c d hab hcd hz_open
    calc
      (1 / (2 * ↑Real.pi * I)) *
          contourIntegralRect
            (fun s => (((analyticOrderAt f z).toNat : ℂ) / (s - z))) a b c d
          = (1 / (2 * ↑Real.pi * I)) *
              contourIntegralRect
                (fun s => (((analyticOrderAt f z).toNat : ℂ) * (1 / (s - z)))) a b c d := by
                  congr 2
                  ext s
                  rw [div_eq_mul_inv, one_div]
      _ = (1 / (2 * ↑Real.pi * I)) *
            ((((analyticOrderAt f z).toNat : ℂ) *
              contourIntegralRect (fun s => 1 / (s - z)) a b c d)) := by
                rw [hconst]
      _ = (((analyticOrderAt f z).toNat : ℂ) *
            ((1 / (2 * ↑Real.pi * I)) *
              contourIntegralRect (fun s => 1 / (s - z)) a b c d)) := by ring
      _ = ↑((analyticOrderAt f z).toNat) := by rw [hwind]; ring
  rw [logIntegralRect_eq_normalized_contour]
  have hdecomp_eq : ∀ s ∈ closedRect a b c d, s ∉ openRect a b c d →
      logDeriv f s =
        (∑ z ∈ hfin.toFinset, (((analyticOrderAt f z).toNat : ℂ) / (s - z))) + h s := by
    intro s hs hsnot
    exact hh_eq s hs (fun z hz hfz => edge_ne_interior_zero hsnot hz)
  have hcontour_eq : contourIntegralRect (logDeriv f) a b c d =
      contourIntegralRect
        (fun s => (∑ z ∈ hfin.toFinset, (((analyticOrderAt f z).toNat : ℂ) / (s - z))) + h s)
        a b c d := by
    apply contourIntegralRect_congr_boundary _ _ _ _ _ _ (le_of_lt hab) (le_of_lt hcd)
    · intro x hx
      exact hdecomp_eq _ (edge_mem_closedRect (le_of_lt hab) (le_of_lt hcd) x hx.1 hx.2 c
        (le_refl _) (le_of_lt hcd)) (bottom_edge_not_openRect x)
    · intro x hx
      exact hdecomp_eq _ (edge_mem_closedRect (le_of_lt hab) (le_of_lt hcd) x hx.1 hx.2 d
        (le_of_lt hcd) (le_refl _)) (top_edge_not_openRect x)
    · intro y hy
      exact hdecomp_eq _ (edge_mem_closedRect (le_of_lt hab) (le_of_lt hcd) b
        (le_of_lt hab) (le_refl _) y hy.1 hy.2) (right_edge_not_openRect y)
    · intro y hy
      exact hdecomp_eq _ (edge_mem_closedRect (le_of_lt hab) (le_of_lt hcd) a
        (le_refl _) (le_of_lt hab) y hy.1 hy.2) (left_edge_not_openRect y)
  rw [hcontour_eq]
  suffices h_linear : contourIntegralRect
      (fun s => (∑ z ∈ hfin.toFinset, (((analyticOrderAt f z).toNat : ℂ) / (s - z))) + h s)
        a b c d =
      (∑ z ∈ hfin.toFinset,
        contourIntegralRect
          (fun s => (((analyticOrderAt f z).toNat : ℂ) / (s - z))) a b c d) +
      contourIntegralRect h a b c d by
    rw [h_linear, hh_zero, add_zero, Finset.mul_sum]
    rw [Finset.sum_congr rfl hwinding]
    rw [Nat.cast_sum]
  exact contourIntegralRect_finset_sum_add hfin.toFinset
    (fun z s => (((analyticOrderAt f z).toNat : ℂ) / (s - z))) h a b c d
    (le_of_lt hab) (le_of_lt hcd)
    (by
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const
      · exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn.sub
          continuousOn_const
      · intro x hx
        rw [Set.uIcc_of_le (le_of_lt hab), Set.mem_Icc] at hx
        simp only [sub_ne_zero]
        exact edge_ne_interior_zero (bottom_edge_not_openRect x) hz.1)
    (by
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const
      · exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn.sub
          continuousOn_const
      · intro x hx
        rw [Set.uIcc_of_le (le_of_lt hab), Set.mem_Icc] at hx
        simp only [sub_ne_zero]
        exact edge_ne_interior_zero (top_edge_not_openRect x) hz.1)
    (by
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const
      · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn.sub
          continuousOn_const
      · intro y hy
        rw [Set.uIcc_of_le (le_of_lt hcd), Set.mem_Icc] at hy
        simp only [sub_ne_zero]
        exact edge_ne_interior_zero (right_edge_not_openRect y) hz.1)
    (by
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const
      · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn.sub
          continuousOn_const
      · intro y hy
        rw [Set.uIcc_of_le (le_of_lt hcd), Set.mem_Icc] at hy
        simp only [sub_ne_zero]
        exact edge_ne_interior_zero (left_edge_not_openRect y) hz.1)
    (hh_diff.continuousOn.comp
      (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
      (fun x hx => by
        rw [Set.uIcc_of_le (le_of_lt hab), Set.mem_Icc] at hx
        exact edge_mem_closedRect (le_of_lt hab) (le_of_lt hcd) x hx.1 hx.2 c
          (le_refl _) (le_of_lt hcd))).intervalIntegrable
    (hh_diff.continuousOn.comp
      (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
      (fun x hx => by
        rw [Set.uIcc_of_le (le_of_lt hab), Set.mem_Icc] at hx
        exact edge_mem_closedRect (le_of_lt hab) (le_of_lt hcd) x hx.1 hx.2 d
          (le_of_lt hcd) (le_refl _))).intervalIntegrable
    (hh_diff.continuousOn.comp
      (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      (fun y hy => by
        rw [Set.uIcc_of_le (le_of_lt hcd), Set.mem_Icc] at hy
        exact edge_mem_closedRect (le_of_lt hab) (le_of_lt hcd) b
          (le_of_lt hab) (le_refl _) y hy.1 hy.2)).intervalIntegrable
    (hh_diff.continuousOn.comp
      (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      (fun y hy => by
        rw [Set.uIcc_of_le (le_of_lt hcd), Set.mem_Icc] at hy
        exact edge_mem_closedRect (le_of_lt hab) (le_of_lt hcd) a
          (le_refl _) (le_of_lt hab) y hy.1 hy.2)).intervalIntegrable

/-- Multiplicity-counted rectangle argument principle. This wraps
    `argument_principle_rect_entire_mult_sum` in the same outer hypotheses as the existing
    distinct-count theorem, but drops the simple-zero requirement. -/
theorem argument_principle_rect_entire_mult (f : ℂ → ℂ)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hf : Differentiable ℂ f)
    (hbdy : ∀ z ∈ rectBoundary a b c d, f z ≠ 0) :
    logIntegralRect f a b c d = ↑(zeroCountRectMult f a b c d) := by
  have hz : ∃ z, f z ≠ 0 := ⟨_, hbdy _ (corner_mem_rectBoundary hab hcd)⟩
  have hfin := finite_zeros_in_openRect f a b c d hab hcd hf hz
  rw [zeroCountRectMult_eq_sum (f := f) (a := a) (b := b) (c := c) (d := d) hfin]
  simpa using argument_principle_rect_entire_mult_sum f a b c d hab hcd hf hbdy hfin

end RectArgumentPrinciple
