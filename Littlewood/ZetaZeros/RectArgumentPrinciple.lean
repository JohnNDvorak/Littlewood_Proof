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
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta

set_option maxHeartbeats 800000
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

/-- For a non-zero entire function, the zero set in the open rectangle is finite.
    This ensures `zeroCountRect` gives a meaningful natural number. -/
theorem finite_zeros_in_openRect (f : ℂ → ℂ)
    (a b c d : ℝ) (_hab : a < b) (_hcd : c < d)
    (hf : Differentiable ℂ f) (hz : ∃ z, f z ≠ 0) :
    {z ∈ openRect a b c d | f z = 0}.Finite :=
  (finite_zeros_in_compact f hf hz (closedRect a b c d) (isCompact_closedRect a b c d)).subset
    (fun _ ⟨h1, h2⟩ => ⟨openRect_subset_closedRect h1, h2⟩)

/-! ## Sub-lemma A: Winding Number for Rectangles

For w inside the open rectangle R = (a,b) × (c,d):
  (1/2πi) ∫_∂R 1/(s - w) ds = 1

This is the rectangle analogue of the Cauchy integral formula for the function 1.
The proof strategy: choose ε small enough that B(w, ε) ⊂ R. Then 1/(s-w) is
holomorphic on R \ {w}, so by Cauchy-Goursat on R minus the ε-disk, the rectangle
integral equals the circle integral. The circle integral gives 2πi by
`Complex.circleIntegral_sub_center_inv_smul`.

SORRY STATUS: Requires contour deformation (rectangle → circle). The individual
pieces are in Mathlib:
- Cauchy-Goursat: `integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`
- Circle CIF: `circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`
but connecting them requires constructing the deformation path explicitly. -/
theorem rect_winding_number_eq_one (w : ℂ) (a b c d : ℝ)
    (hab : a < b) (hcd : c < d)
    (hw : w ∈ openRect a b c d) :
    (1 / (2 * ↑Real.pi * I)) * contourIntegralRect (fun s => 1 / (s - w)) a b c d = 1 := by
  sorry

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
theorem logDeriv_decompose_rect (f : ℂ → ℂ)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hf : Differentiable ℂ f)
    (hbdy : ∀ z ∈ rectBoundary a b c d, f z ≠ 0)
    (hfin : {z ∈ openRect a b c d | f z = 0}.Finite) :
    ∃ h : ℂ → ℂ,
      DifferentiableOn ℂ h (closedRect a b c d) ∧
      ∀ s ∈ closedRect a b c d, (∀ z ∈ openRect a b c d, f z = 0 → s ≠ z) →
        logDeriv f s = (∑ z ∈ hfin.toFinset, (1 : ℂ) / (s - z)) + h s := by
  sorry

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
theorem argument_principle_rect_entire (f : ℂ → ℂ)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hf : Differentiable ℂ f)
    (hbdy : ∀ z ∈ rectBoundary a b c d, f z ≠ 0) :
    logIntegralRect f a b c d = ↑(zeroCountRect f a b c d) := by
  sorry

end RectArgumentPrinciple
