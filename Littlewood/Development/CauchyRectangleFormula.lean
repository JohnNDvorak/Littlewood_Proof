/-
Cauchy Integral Formula for Rectangles

Proves: if f is holomorphic on a closed rectangle R and w is in the open interior,
then the rectangle contour integral of f(z)/(z-w) equals 2*pi*i*f(w).

## Architecture

1. `closedRect_eq_reProdIm`: Converts our rectangle to Mathlib's reProdIm format.
2. `rectangle_contains_ball`: Interior point has ball inside the closed rectangle.
3. `cauchy_goursat_rect`: Cauchy-Goursat for our rectangle (via Mathlib's version).
4. `rect_winding_number`: Rectangle integral of (z-w)^{-1} = 2*pi*i (via FTC + complex log).
5. `cauchy_integral_formula_rectangle`: CIF via dslope + Cauchy-Goursat + winding number.
6. `rectangle_circle_agreement`: Corollary relating rectangle and circle integrals.
7. Norm estimates for rectangle integrals (all sorry-free).

## References
- Mathlib: `Complex.circleIntegral_div_sub_of_differentiable_on_off_countable`
- Mathlib: `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace Littlewood.Development.CauchyRectangleFormula

open Complex Set MeasureTheory Topology Filter Real

/-! ## Section 1: Rectangle Definitions -/

/-- Open rectangle in C with corners (a,c) and (b,d). -/
def openRect (a b c d : ℝ) : Set ℂ :=
  {z : ℂ | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d}

/-- Closed rectangle in C with corners (a,c) and (b,d). -/
def closedRect (a b c d : ℝ) : Set ℂ :=
  {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ c ≤ z.im ∧ z.im ≤ d}

theorem openRect_subset_closedRect (a b c d : ℝ) :
    openRect a b c d ⊆ closedRect a b c d :=
  fun _ ⟨h1, h2, h3, h4⟩ => ⟨h1.le, h2.le, h3.le, h4.le⟩

theorem isOpen_openRect (a b c d : ℝ) : IsOpen (openRect a b c d) := by
  unfold openRect
  apply IsOpen.inter (isOpen_lt continuous_const continuous_re)
  apply IsOpen.inter (isOpen_lt continuous_re continuous_const)
  apply IsOpen.inter (isOpen_lt continuous_const continuous_im)
  exact isOpen_lt continuous_im continuous_const

theorem closedRect_eq_reProdIm (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    closedRect a b c d = Set.uIcc a b ×ℂ Set.uIcc c d := by
  ext z
  simp only [closedRect, Complex.mem_reProdIm, Set.mem_uIcc, Set.mem_setOf_eq]
  constructor
  · intro ⟨h1, h2, h3, h4⟩
    exact ⟨Or.inl ⟨h1, h2⟩, Or.inl ⟨h3, h4⟩⟩
  · intro ⟨h1, h2⟩
    rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
    rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ <;>
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ## Section 2: Ball Inside Rectangle -/

/-- An interior point of a rectangle has a ball around it inside the closed rectangle. -/
theorem rectangle_contains_ball {a b c d : ℝ} {w : ℂ}
    (hw : w ∈ openRect a b c d) :
    ∃ R > 0, Metric.closedBall w R ⊆ closedRect a b c d := by
  obtain ⟨ha, hb, hc, hd⟩ := hw
  set R := min (min (w.re - a) (b - w.re)) (min (w.im - c) (d - w.im))
  have hR : 0 < R := lt_min (lt_min (by linarith) (by linarith))
    (lt_min (by linarith) (by linarith))
  refine ⟨R, hR, fun z hz => ?_⟩
  simp only [Metric.mem_closedBall, Complex.dist_eq] at hz
  have hre : |z.re - w.re| ≤ R := (Complex.abs_re_le_norm (z - w)).trans hz
  have him : |z.im - w.im| ≤ R := (Complex.abs_im_le_norm (z - w)).trans hz
  have hR1 : R ≤ w.re - a := le_trans (min_le_left _ _) (min_le_left _ _)
  have hR2 : R ≤ b - w.re := le_trans (min_le_left _ _) (min_le_right _ _)
  have hR3 : R ≤ w.im - c := le_trans (min_le_right _ _) (min_le_left _ _)
  have hR4 : R ≤ d - w.im := le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨hre1, hre2⟩ := abs_le.mp hre
  obtain ⟨him1, him2⟩ := abs_le.mp him
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Interior point is in ball contained in rectangle. -/
theorem rectangle_interior_mem_ball {a b c d : ℝ} {w : ℂ}
    (hw : w ∈ openRect a b c d)
    {R : ℝ} (hR : 0 < R) (hRw : Metric.closedBall w R ⊆ closedRect a b c d) :
    w ∈ Metric.ball w R :=
  Metric.mem_ball_self hR

/-! ## Section 3: The Rectangle Integral and Cauchy-Goursat -/

/-- The rectangle boundary integral of f over the rectangle with corners
    (a,c) and (b,d), in the same form as Mathlib's boundary integral. -/
def rectangleIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x in a..b, f (↑x + ↑c * I)) - (∫ x in a..b, f (↑x + ↑d * I)) +
  I * (∫ y in c..d, f (↑b + ↑y * I)) - I * (∫ y in c..d, f (↑a + ↑y * I))

/-- Cauchy-Goursat for rectangles: if f is differentiable on the closed rectangle,
    then the boundary integral is zero. -/
theorem cauchy_goursat_rect (f : ℂ → ℂ) (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (hf : DifferentiableOn ℂ f (closedRect a b c d)) :
    rectangleIntegral f a b c d = 0 := by
  unfold rectangleIntegral
  have hconv : closedRect a b c d = Set.uIcc a b ×ℂ Set.uIcc c d :=
    closedRect_eq_reProdIm a b c d hab hcd
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ⟨a, c⟩ ⟨b, d⟩ (hconv ▸ hf)
  convert h using 2 <;> simp [smul_eq_mul]

/-! ## Section 3b: Rectangle Splitting and Integrability

Infrastructure for decomposing rectangle integrals into sub-rectangles.
This is the key tool for the contour deformation argument. -/

/-- Integrability of f along horizontal segments of the rectangle. -/
private theorem intble_horiz (f : ℂ → ℂ) (a b c d y : ℝ)
    (hf : ContinuousOn f (closedRect a b c d))
    (hab : a ≤ b) (hcy : c ≤ y) (hyd : y ≤ d) :
    IntervalIntegrable (fun x => f (↑x + ↑y * I)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.comp hf (Continuous.continuousOn (by continuity))
  intro x hx; simp only [Set.mem_uIcc] at hx
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith)

/-- Integrability of f along vertical segments of the rectangle. -/
private theorem intble_vert (f : ℂ → ℂ) (a b c d x : ℝ)
    (hf : ContinuousOn f (closedRect a b c d))
    (hcd : c ≤ d) (hax : a ≤ x) (hxb : x ≤ b) :
    IntervalIntegrable (fun y => f (↑x + ↑y * I)) volume c d := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.comp hf (Continuous.continuousOn (by continuity))
  intro y hy; simp only [Set.mem_uIcc] at hy
  rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith)

/-- Sub-interval integrability from full interval. -/
private theorem sub_intble {f : ℝ → ℂ} {a p b : ℝ} (hap : a ≤ p) (hpb : p ≤ b)
    (h : IntervalIntegrable f volume a b) :
    IntervalIntegrable f volume a p ∧ IntervalIntegrable f volume p b :=
  ⟨h.mono_set (Set.uIcc_subset_uIcc_left (Set.mem_uIcc.mpr (Or.inl ⟨hap, hpb⟩))),
   h.mono_set (Set.uIcc_subset_uIcc_right (Set.mem_uIcc.mpr (Or.inl ⟨hap, hpb⟩)))⟩

/-- **Rectangle splitting**: splitting a rectangle at an interior point (p,q)
    decomposes its boundary integral into the sum of 4 sub-rectangle integrals.
    Internal edges cancel. This is the key combinatorial tool for the
    contour deformation argument. -/
theorem rectIntegral_split (f : ℂ → ℂ) (a p b c q d : ℝ)
    (hap : a ≤ p) (hpb : p ≤ b) (hcq : c ≤ q) (hqd : q ≤ d)
    (hf : ContinuousOn f (closedRect a b c d)) :
    rectangleIntegral f a b c d =
      rectangleIntegral f a p c q + rectangleIntegral f p b c q +
      rectangleIntegral f a p q d + rectangleIntegral f p b q d := by
  have hab := le_trans hap hpb
  have hcd := le_trans hcq hqd
  have hbc := intble_horiz f a b c d c hf hab le_rfl hcd
  have hbd := intble_horiz f a b c d d hf hab hcd le_rfl
  have _hbq := intble_horiz f a b c d q hf hab hcq hqd
  have hvb := intble_vert f a b c d b hf hcd hab le_rfl
  have hva := intble_vert f a b c d a hf hcd le_rfl hab
  have _hvp := intble_vert f a b c d p hf hcd hap hpb
  obtain ⟨hbc1, hbc2⟩ := sub_intble hap hpb hbc
  obtain ⟨hbd1, hbd2⟩ := sub_intble hap hpb hbd
  obtain ⟨hvb1, hvb2⟩ := sub_intble hcq hqd hvb
  obtain ⟨hva1, hva2⟩ := sub_intble hcq hqd hva
  have Hbc : ∫ x in a..b, f (↑x + ↑c * I) =
      (∫ x in a..p, f (↑x + ↑c * I)) + ∫ x in p..b, f (↑x + ↑c * I) :=
    (intervalIntegral.integral_add_adjacent_intervals hbc1 hbc2).symm
  have Hbd : ∫ x in a..b, f (↑x + ↑d * I) =
      (∫ x in a..p, f (↑x + ↑d * I)) + ∫ x in p..b, f (↑x + ↑d * I) :=
    (intervalIntegral.integral_add_adjacent_intervals hbd1 hbd2).symm
  have Hvb : ∫ y in c..d, f (↑b + ↑y * I) =
      (∫ y in c..q, f (↑b + ↑y * I)) + ∫ y in q..d, f (↑b + ↑y * I) :=
    (intervalIntegral.integral_add_adjacent_intervals hvb1 hvb2).symm
  have Hva : ∫ y in c..d, f (↑a + ↑y * I) =
      (∫ y in c..q, f (↑a + ↑y * I)) + ∫ y in q..d, f (↑a + ↑y * I) :=
    (intervalIntegral.integral_add_adjacent_intervals hva1 hva2).symm
  unfold rectangleIntegral
  rw [Hbc, Hbd, Hvb, Hva]
  ring

/-! ## Section 4: Winding Number for Rectangles via FTC

The rectangle integral of `(z-w)⁻¹` around an interior point `w` equals `2πi`.

Proof via the fundamental theorem of calculus. On each edge, `Complex.log(z - w)` is an
antiderivative (valid when `z - w ∈ slitPlane`). The left edge crosses the branch cut at
`Im(w)`, producing a `2πi` jump that yields the winding number.

Adapted from `RectArgumentPrinciple.rect_winding_number_eq_one`. -/

section WindingNumber

set_option maxHeartbeats 3200000

private theorem im_sub_pt {x y : ℝ} {w : ℂ} : (↑x + ↑y * I - w).im = y - w.im := by
  simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re,
    Complex.sub_im]

private theorem re_sub_pt {x y : ℝ} {w : ℂ} : (↑x + ↑y * I - w).re = x - w.re := by
  simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.sub_re]

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

private theorem intble_horiz_sub {w : ℂ} {c' : ℝ} (hc : c' ≠ w.im) (p q : ℝ) :
    IntervalIntegrable (fun x => (↑x + ↑c' * I - w)⁻¹) MeasureTheory.volume p q := by
  apply ContinuousOn.intervalIntegrable; apply ContinuousOn.inv₀
  · exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn.sub
      continuousOn_const
  · intro x _; exact Complex.slitPlane_ne_zero (Complex.mem_slitPlane_iff.mpr (Or.inr
      (by rw [im_sub_pt]; exact sub_ne_zero.mpr hc)))

private theorem intble_vert_sub {w : ℂ} {x₀ : ℝ} (hx : x₀ ≠ w.re) (p q : ℝ) :
    IntervalIntegrable (fun y => (↑x₀ + ↑y * I - w)⁻¹) MeasureTheory.volume p q := by
  apply ContinuousOn.intervalIntegrable; apply ContinuousOn.inv₀
  · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn.sub
      continuousOn_const
  · intro y _ h; have := congr_arg Complex.re h
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, Complex.sub_re, Complex.zero_re] at this; exact hx (by linarith)

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

/-- **Winding number for rectangles**: the rectangle integral of `(z-w)⁻¹` around
    a rectangle containing `w` in its open interior equals `2πi`.

    Proved via FTC on each edge with `Complex.log` as antiderivative.
    The left edge crosses the branch cut at `Im(w)`, producing a `2πi` jump. -/
theorem rect_winding_number (w : ℂ) (a b c d : ℝ)
    (hw : w ∈ openRect a b c d) :
    rectangleIntegral (fun z => (z - w)⁻¹) a b c d = 2 * ↑Real.pi * I := by
  obtain ⟨ha_w, hw_b, hc_w, hw_d⟩ := hw
  unfold rectangleIntegral
  have hbot := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_log_horiz_sub (ne_of_lt hc_w)) (intble_horiz_sub (ne_of_lt hc_w) a b)
  have htop := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_log_horiz_sub (ne_of_gt hw_d)) (intble_horiz_sub (ne_of_gt hw_d) a b)
  have hright := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hasDerivAt_log_vert_sub (Complex.mem_slitPlane_iff.mpr
      (Or.inl (by rw [re_sub_pt]; linarith)))) (intble_vert_sub (ne_of_gt hw_b) c d)
  have hleft_split := (intervalIntegral.integral_add_adjacent_intervals
    (intble_vert_sub (ne_of_lt ha_w) c w.im)
    (intble_vert_sub (ne_of_lt ha_w) w.im d)).symm
  have hcont_c : Filter.Tendsto (fun y : ℝ => I⁻¹ * Complex.log (↑a + ↑y * I - w))
      (nhdsWithin c (Set.Ioi c)) (nhds (I⁻¹ * Complex.log (↑a + ↑c * I - w))) :=
    (hasDerivAt_log_vert_sub (Complex.mem_slitPlane_iff.mpr (Or.inr (by
      rw [im_sub_pt]; linarith)))).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hleft_lo := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hc_w
    (fun y hy => hasDerivAt_log_vert_sub (Complex.mem_slitPlane_iff.mpr
      (Or.inr (by rw [im_sub_pt]; linarith [hy.2]))))
    (intble_vert_sub (ne_of_lt ha_w) c w.im) hcont_c (tendsto_antideriv_lower ha_w)
  have hcont_d : Filter.Tendsto (fun y : ℝ => I⁻¹ * Complex.log (↑a + ↑y * I - w))
      (nhdsWithin d (Set.Iio d)) (nhds (I⁻¹ * Complex.log (↑a + ↑d * I - w))) :=
    (hasDerivAt_log_vert_sub (Complex.mem_slitPlane_iff.mpr (Or.inr (by
      rw [im_sub_pt]; linarith)))).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hleft_up := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hw_d
    (fun y hy => hasDerivAt_log_vert_sub (Complex.mem_slitPlane_iff.mpr
      (Or.inr (by rw [im_sub_pt]; linarith [hy.1]))))
    (intble_vert_sub (ne_of_lt ha_w) w.im d) (tendsto_antideriv_upper ha_w) hcont_d
  rw [hbot, htop, hright, hleft_split, hleft_lo, hleft_up]
  have hII : I * I⁻¹ = 1 := mul_inv_cancel₀ I_ne_zero
  simp only [mul_add, mul_sub]
  simp only [← mul_assoc, hII, one_mul]
  ring

end WindingNumber

/-! ## Section 5: Cauchy Integral Formula for Rectangles

Proved directly via the dslope trick + winding number, without
going through the circle integral. -/

/-- The closed rectangle is a neighborhood of any interior point. -/
theorem closedRect_mem_nhds {a b c d : ℝ} {w : ℂ}
    (hw : w ∈ openRect a b c d) :
    closedRect a b c d ∈ nhds w :=
  Filter.mem_of_superset ((isOpen_openRect a b c d).mem_nhds hw)
    (openRect_subset_closedRect a b c d)

/-- Cauchy-Goursat for `dslope f w` on a rectangle containing w in its interior. -/
theorem cauchy_goursat_dslope (f : ℂ → ℂ) (a b c d : ℝ) (w : ℂ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (hf : DifferentiableOn ℂ f (closedRect a b c d))
    (hw : w ∈ openRect a b c d) :
    rectangleIntegral (dslope f w) a b c d = 0 := by
  apply cauchy_goursat_rect _ a b c d hab hcd
  rwa [Complex.differentiableOn_dslope (closedRect_mem_nhds hw)]

/-- On the rectangle boundary (where z ≠ w), `dslope f w z = (z-w)⁻¹ * (f z - f w)`. -/
private theorem dslope_eq_on_boundary {f : ℂ → ℂ} {w z : ℂ} (hz : z ≠ w) :
    dslope f w z = (z - w)⁻¹ * (f z - f w) := by
  rw [dslope_of_ne _ hz, slope, vsub_eq_sub, smul_eq_mul]

/-- **Cauchy Integral Formula for Rectangles**: if f is differentiable on the closed
    rectangle [a,b] x [c,d] and w is in its open interior, then
      integral_{boundary R} f(z)/(z-w) dz = 2*pi*i*f(w).

    Proof: dslope + Cauchy-Goursat + winding number via FTC. -/
theorem cauchy_integral_formula_rectangle (f : ℂ → ℂ) (a b c d : ℝ)
    (hab : a < b) (hcd : c < d)
    (hf : DifferentiableOn ℂ f (closedRect a b c d))
    (w : ℂ) (hw : w ∈ openRect a b c d) :
    rectangleIntegral (fun z => f z / (z - w)) a b c d =
    2 * ↑Real.pi * I * f w := by
  have hw' := hw
  obtain ⟨ha_w, hw_b, hc_w, hw_d⟩ := hw
  -- Edge z ≠ w facts:
  have hbot_ne : ∀ x : ℝ, (↑x + ↑c * I : ℂ) ≠ w := fun x h =>
    absurd (congr_arg Complex.im h) (by simp [Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_im, Complex.I_re]; linarith)
  have htop_ne : ∀ x : ℝ, (↑x + ↑d * I : ℂ) ≠ w := fun x h =>
    absurd (congr_arg Complex.im h) (by simp [Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_im, Complex.I_re]; linarith)
  have hright_ne : ∀ y : ℝ, (↑b + ↑y * I : ℂ) ≠ w := fun y h =>
    absurd (congr_arg Complex.re h) (by simp [Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]; linarith)
  have hleft_ne : ∀ y : ℝ, (↑a + ↑y * I : ℂ) ≠ w := fun y h =>
    absurd (congr_arg Complex.re h) (by simp [Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]; linarith)
  -- Pointwise identity: f(z)/(z-w) = dslope f w z + f(w) * (z-w)⁻¹ for z ≠ w
  have hid : ∀ (z : ℂ), z ≠ w →
      f z / (z - w) = dslope f w z + f w * (z - w)⁻¹ := by
    intro z hz
    rw [dslope_eq_on_boundary hz, div_eq_mul_inv]
    ring
  -- Integrability: dslope is continuous hence integrable on all edges
  have hdslope_cont := ((Complex.differentiableOn_dslope
    (closedRect_mem_nhds hw')).mpr hf).continuousOn
  -- Integrability of (z-w)⁻¹ on each edge
  have hint_bot := intble_horiz_sub (ne_of_lt hc_w) a b
  have hint_top := intble_horiz_sub (ne_of_gt hw_d) a b
  have hint_right := intble_vert_sub (ne_of_gt hw_b) c d
  have hint_left := intble_vert_sub (ne_of_lt ha_w) c d
  -- Integrability of dslope on each edge
  have hds_bot := intble_horiz (dslope f w) a b c d c hdslope_cont hab.le le_rfl hcd.le
  have hds_top := intble_horiz (dslope f w) a b c d d hdslope_cont hab.le hcd.le le_rfl
  have hds_right := intble_vert (dslope f w) a b c d b hdslope_cont hcd.le hab.le le_rfl
  have hds_left := intble_vert (dslope f w) a b c d a hdslope_cont hcd.le le_rfl hab.le
  -- Integrability of f(w) * (z-w)⁻¹ on each edge
  have hfw_bot := hint_bot.const_mul (f w)
  have hfw_top := hint_top.const_mul (f w)
  have hfw_right := hint_right.const_mul (f w)
  have hfw_left := hint_left.const_mul (f w)
  -- Each edge integral of f/(z-w) = edge integral of dslope + edge integral of f(w)*(z-w)⁻¹
  have edge_bot : ∫ x in a..b, f (↑x + ↑c * I) / (↑x + ↑c * I - w) =
      (∫ x in a..b, dslope f w (↑x + ↑c * I)) +
      ∫ x in a..b, f w * (↑x + ↑c * I - w)⁻¹ := by
    rw [← intervalIntegral.integral_add hds_bot hfw_bot]
    exact intervalIntegral.integral_congr (fun x _ => hid _ (hbot_ne x))
  have edge_top : ∫ x in a..b, f (↑x + ↑d * I) / (↑x + ↑d * I - w) =
      (∫ x in a..b, dslope f w (↑x + ↑d * I)) +
      ∫ x in a..b, f w * (↑x + ↑d * I - w)⁻¹ := by
    rw [← intervalIntegral.integral_add hds_top hfw_top]
    exact intervalIntegral.integral_congr (fun x _ => hid _ (htop_ne x))
  have edge_right : ∫ y in c..d, f (↑b + ↑y * I) / (↑b + ↑y * I - w) =
      (∫ y in c..d, dslope f w (↑b + ↑y * I)) +
      ∫ y in c..d, f w * (↑b + ↑y * I - w)⁻¹ := by
    rw [← intervalIntegral.integral_add hds_right hfw_right]
    exact intervalIntegral.integral_congr (fun y _ => hid _ (hright_ne y))
  have edge_left : ∫ y in c..d, f (↑a + ↑y * I) / (↑a + ↑y * I - w) =
      (∫ y in c..d, dslope f w (↑a + ↑y * I)) +
      ∫ y in c..d, f w * (↑a + ↑y * I - w)⁻¹ := by
    rw [← intervalIntegral.integral_add hds_left hfw_left]
    exact intervalIntegral.integral_congr (fun y _ => hid _ (hleft_ne y))
  -- Factor out f(w) from the (z-w)⁻¹ integrals
  have cfactor_bot := intervalIntegral.integral_const_mul (f w)
    (fun x => (↑x + ↑c * I - w)⁻¹ : ℝ → ℂ) (a := a) (b := b) (μ := volume)
  have cfactor_top := intervalIntegral.integral_const_mul (f w)
    (fun x => (↑x + ↑d * I - w)⁻¹ : ℝ → ℂ) (a := a) (b := b) (μ := volume)
  have cfactor_right := intervalIntegral.integral_const_mul (f w)
    (fun y => (↑b + ↑y * I - w)⁻¹ : ℝ → ℂ) (a := c) (b := d) (μ := volume)
  have cfactor_left := intervalIntegral.integral_const_mul (f w)
    (fun y => (↑a + ↑y * I - w)⁻¹ : ℝ → ℂ) (a := c) (b := d) (μ := volume)
  -- Now expand rectangleIntegral and substitute
  unfold rectangleIntegral
  rw [edge_bot, edge_top, edge_right, edge_left,
      cfactor_bot, cfactor_top, cfactor_right, cfactor_left]
  -- The dslope parts sum to 0 (Cauchy-Goursat), the (z-w)⁻¹ parts sum to f(w) * 2πi
  have hds_zero := cauchy_goursat_dslope f a b c d w hab.le hcd.le hf hw'
  unfold rectangleIntegral at hds_zero
  have hwinding := rect_winding_number w a b c d hw'
  unfold rectangleIntegral at hwinding
  linear_combination hds_zero + (f w) * hwinding

/-- **Contour deformation**: the rectangle integral of f(z)/(z-w) equals
    the circle integral. Derived as a corollary of the rectangle CIF + Mathlib circle CIF. -/
theorem rectangle_circle_agreement (f : ℂ → ℂ) (a b c d : ℝ)
    (hab : a < b) (hcd : c < d)
    (hf : DifferentiableOn ℂ f (closedRect a b c d))
    (w : ℂ) (hw : w ∈ openRect a b c d)
    (R : ℝ) (hR : 0 < R)
    (hRw : Metric.closedBall w R ⊆ closedRect a b c d) :
    rectangleIntegral (fun z => f z / (z - w)) a b c d =
    ∮ z in C(w, R), f z / (z - w) := by
  rw [cauchy_integral_formula_rectangle f a b c d hab hcd hf w hw]
  have hf_ball : DifferentiableOn ℂ f (Metric.closedBall w R) := hf.mono hRw
  have := hf_ball.circleIntegral_sub_inv_smul (Metric.mem_ball_self hR)
  simp only [smul_eq_mul, div_eq_inv_mul] at this ⊢
  exact this.symm

/-- (1/2*pi*i) * integral = f(w). -/
theorem cauchy_integral_formula_rectangle_inv (f : ℂ → ℂ) (a b c d : ℝ)
    (hab : a < b) (hcd : c < d)
    (hf : DifferentiableOn ℂ f (closedRect a b c d))
    (w : ℂ) (hw : w ∈ openRect a b c d) :
    (2 * ↑Real.pi * I)⁻¹ *
    rectangleIntegral (fun z => f z / (z - w)) a b c d = f w := by
  rw [cauchy_integral_formula_rectangle f a b c d hab hcd hf w hw]
  rw [← mul_assoc, inv_mul_cancel₀, one_mul]
  apply mul_ne_zero (mul_ne_zero ?_ ?_) I_ne_zero
  · exact_mod_cast (two_ne_zero : (2:ℝ) ≠ 0)
  · exact_mod_cast Real.pi_ne_zero

/-! ## Section 6: Norm Estimates for Rectangle Integrals -/

/-- The rectangle integral norm is bounded by the sum of the side integral norms. -/
theorem rectangleIntegral_norm_le (f : ℂ → ℂ) (a b c d : ℝ) :
    ‖rectangleIntegral f a b c d‖ ≤
      ‖∫ x in a..b, f (↑x + ↑c * I)‖ + ‖∫ x in a..b, f (↑x + ↑d * I)‖ +
      ‖∫ y in c..d, f (↑b + ↑y * I)‖ + ‖∫ y in c..d, f (↑a + ↑y * I)‖ := by
  unfold rectangleIntegral
  calc ‖(∫ x in a..b, f (↑x + ↑c * I)) - (∫ x in a..b, f (↑x + ↑d * I)) +
        I * (∫ y in c..d, f (↑b + ↑y * I)) - I * (∫ y in c..d, f (↑a + ↑y * I))‖
    _ ≤ ‖(∫ x in a..b, f (↑x + ↑c * I)) - (∫ x in a..b, f (↑x + ↑d * I)) +
        I * (∫ y in c..d, f (↑b + ↑y * I))‖ +
        ‖I * (∫ y in c..d, f (↑a + ↑y * I))‖ := norm_sub_le _ _
    _ ≤ (‖(∫ x in a..b, f (↑x + ↑c * I)) - (∫ x in a..b, f (↑x + ↑d * I))‖ +
        ‖I * (∫ y in c..d, f (↑b + ↑y * I))‖) +
        ‖I * (∫ y in c..d, f (↑a + ↑y * I))‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ ((‖∫ x in a..b, f (↑x + ↑c * I)‖ + ‖∫ x in a..b, f (↑x + ↑d * I)‖) +
        ‖∫ y in c..d, f (↑b + ↑y * I)‖) +
        ‖∫ y in c..d, f (↑a + ↑y * I)‖ := by
        gcongr
        · exact norm_sub_le _ _
        · rw [norm_mul, Complex.norm_I, one_mul]
        · rw [norm_mul, Complex.norm_I, one_mul]
    _ = _ := by ring

/-- Bound on a vertical line integral. -/
theorem vertical_integral_bound {f : ℂ → ℂ} {σ T₁ T₂ M : ℝ}
    (hT : T₁ ≤ T₂) (hM : 0 ≤ M)
    (hf : ∀ t ∈ Set.Icc T₁ T₂, ‖f (↑σ + ↑t * I)‖ ≤ M)
    (hf_int : IntervalIntegrable (fun t => f (↑σ + ↑t * I)) volume T₁ T₂) :
    ‖∫ t in T₁..T₂, f (↑σ + ↑t * I)‖ ≤ M * (T₂ - T₁) := by
  calc ‖∫ t in T₁..T₂, f (↑σ + ↑t * I)‖
      ≤ ∫ t in T₁..T₂, ‖f (↑σ + ↑t * I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hT
    _ ≤ ∫ _ in T₁..T₂, M := by
        apply intervalIntegral.integral_mono_on hT hf_int.norm (intervalIntegrable_const)
        intro t ht; exact hf t ⟨ht.1, ht.2⟩
    _ = M * (T₂ - T₁) := by
        simp [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- Bound on a horizontal line integral. -/
theorem horizontal_integral_bound {f : ℂ → ℂ} {a b T M : ℝ}
    (hab : a ≤ b) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Set.Icc a b, ‖f (↑x + ↑T * I)‖ ≤ M)
    (hf_int : IntervalIntegrable (fun x => f (↑x + ↑T * I)) volume a b) :
    ‖∫ x in a..b, f (↑x + ↑T * I)‖ ≤ M * (b - a) := by
  calc ‖∫ x in a..b, f (↑x + ↑T * I)‖
      ≤ ∫ x in a..b, ‖f (↑x + ↑T * I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ _ in a..b, M := by
        apply intervalIntegral.integral_mono_on hab hf_int.norm (intervalIntegrable_const)
        intro x hx; exact hf x ⟨hx.1, hx.2⟩
    _ = M * (b - a) := by
        simp [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- If f is bounded by M on the rectangle boundary with dimensions (b-a) x (d-c),
    then the rectangle integral is bounded by 2M(b-a+d-c). -/
theorem rectangleIntegral_norm_le_of_bound {f : ℂ → ℂ} {a b c d M : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hM : 0 ≤ M)
    (hf_bottom : ∀ x ∈ Set.Icc a b, ‖f (↑x + ↑c * I)‖ ≤ M)
    (hf_top : ∀ x ∈ Set.Icc a b, ‖f (↑x + ↑d * I)‖ ≤ M)
    (hf_right : ∀ y ∈ Set.Icc c d, ‖f (↑b + ↑y * I)‖ ≤ M)
    (hf_left : ∀ y ∈ Set.Icc c d, ‖f (↑a + ↑y * I)‖ ≤ M)
    (hf_bot_int : IntervalIntegrable (fun x => f (↑x + ↑c * I)) volume a b)
    (hf_top_int : IntervalIntegrable (fun x => f (↑x + ↑d * I)) volume a b)
    (hf_right_int : IntervalIntegrable (fun y => f (↑b + ↑y * I)) volume c d)
    (hf_left_int : IntervalIntegrable (fun y => f (↑a + ↑y * I)) volume c d) :
    ‖rectangleIntegral f a b c d‖ ≤ 2 * M * (b - a + (d - c)) := by
  have h_bot := horizontal_integral_bound hab hM hf_bottom hf_bot_int
  have h_top := horizontal_integral_bound hab hM hf_top hf_top_int
  have h_right := vertical_integral_bound hcd hM hf_right hf_right_int
  have h_left := vertical_integral_bound hcd hM hf_left hf_left_int
  calc ‖rectangleIntegral f a b c d‖
      ≤ ‖∫ x in a..b, f (↑x + ↑c * I)‖ + ‖∫ x in a..b, f (↑x + ↑d * I)‖ +
        ‖∫ y in c..d, f (↑b + ↑y * I)‖ + ‖∫ y in c..d, f (↑a + ↑y * I)‖ :=
        rectangleIntegral_norm_le f a b c d
    _ ≤ M * (b - a) + M * (b - a) + M * (d - c) + M * (d - c) := by linarith
    _ = 2 * M * (b - a + (d - c)) := by ring

/-! ## Section 7: Application to Perron Formula

Key bounds for the Perron integral. For x^s/s on a rectangle contour
with sigma in [1/2, c] and t in [-T, T], the integrand is bounded
by |x^s|/|s| which admits explicit bounds. -/

/-- For sigma >= 1/2 and |t| >= 1, |1/(sigma + it)| <= 1/|t|. -/
theorem inv_sigma_it_bound {σ t : ℝ} (_hσ : 1/2 ≤ σ) (ht : 1 ≤ |t|) :
    1 / Real.sqrt (σ ^ 2 + t ^ 2) ≤ 1 / |t| := by
  apply div_le_div_of_nonneg_left (by linarith) (by positivity)
  calc |t| = Real.sqrt (t ^ 2) := (Real.sqrt_sq_eq_abs t).symm
    _ ≤ Real.sqrt (σ ^ 2 + t ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg σ])

/-- x^sigma is monotone in sigma for x >= 1. -/
theorem rpow_le_rpow_of_sigma {x : ℝ} (hx : 1 ≤ x) {σ₁ σ₂ : ℝ} (hσ : σ₁ ≤ σ₂) :
    x ^ σ₁ ≤ x ^ σ₂ :=
  Real.rpow_le_rpow_of_exponent_le hx hσ

end Littlewood.Development.CauchyRectangleFormula
