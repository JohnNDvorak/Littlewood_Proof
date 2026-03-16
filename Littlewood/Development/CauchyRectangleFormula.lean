/-
Cauchy Integral Formula for Rectangles

Proves: if f is holomorphic on a closed rectangle R and w is in the open interior,
then the rectangle contour integral of f(z)/(z-w) equals 2*pi*i*f(w).

## Architecture

1. `closedRect_eq_reProdIm`: Converts our rectangle to Mathlib's reProdIm format.
2. `rectangle_contains_ball`: Interior point has ball inside the closed rectangle.
3. `cauchy_goursat_rect`: Cauchy-Goursat for our rectangle (via Mathlib's version).
4. `rectangle_circle_agreement`: Rectangle integral = circle integral (deformation).
   THIS IS THE ONE KEY SORRY -- requires connecting the two contour integrals.
5. `cauchy_integral_formula_rectangle`: The CIF, proved from (4) + Mathlib circle CIF.
6. Norm estimates for rectangle integrals (all sorry-free).

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

/-! ## Section 4: Contour Deformation (Key Sorry)

The theorem that the rectangle integral of f(z)/(z-w) equals the circle
integral of the same function. This is the critical gap: it requires
showing that two contours enclosing the same point give the same integral
for a holomorphic function.

Mathematical proof sketch:
- f(z)/(z-w) is holomorphic on closedRect \ {w}
- Choose a small disk D(w,r) inside the rectangle
- The region closedRect \ D(w,r) is an annular domain
- Decompose it into sub-rectangles where f(z)/(z-w) is holomorphic
- Apply Cauchy-Goursat to each; the internal edges cancel
- What remains: rectangle boundary integral - circle integral = 0

The formal proof requires:
1. Splitting the rectangle into sub-rectangles around the disk
2. Showing each sub-rectangle integral vanishes (Cauchy-Goursat)
3. Showing the internal boundary integrals cancel
This is a combinatorial/topological argument, not deep analysis. -/

/-- **Contour deformation**: the rectangle integral of f(z)/(z-w) equals
    the circle integral. THIS IS THE KEY SORRY. -/
theorem rectangle_circle_agreement (f : ℂ → ℂ) (a b c d : ℝ)
    (hab : a < b) (hcd : c < d)
    (hf : DifferentiableOn ℂ f (closedRect a b c d))
    (w : ℂ) (hw : w ∈ openRect a b c d)
    (R : ℝ) (hR : 0 < R)
    (hRw : Metric.closedBall w R ⊆ closedRect a b c d) :
    rectangleIntegral (fun z => f z / (z - w)) a b c d =
    ∮ z in C(w, R), f z / (z - w) := by
  sorry

/-! ## Section 5: Cauchy Integral Formula for Rectangles -/

/-- **Cauchy Integral Formula for Rectangles**: if f is differentiable on the closed
    rectangle [a,b] x [c,d] and w is in its open interior, then
      integral_{boundary R} f(z)/(z-w) dz = 2*pi*i*f(w).

    This is the rectangle analogue of Mathlib's
    `Complex.circleIntegral_div_sub_of_differentiable_on_off_countable`. -/
theorem cauchy_integral_formula_rectangle (f : ℂ → ℂ) (a b c d : ℝ)
    (hab : a < b) (hcd : c < d)
    (hf : DifferentiableOn ℂ f (closedRect a b c d))
    (w : ℂ) (hw : w ∈ openRect a b c d) :
    rectangleIntegral (fun z => f z / (z - w)) a b c d =
    2 * ↑Real.pi * I * f w := by
  -- Step 1: Find R > 0 with closedBall w R inside closedRect
  obtain ⟨R, hR, hRw⟩ := rectangle_contains_ball hw
  -- Step 2: Rectangle integral = circle integral (contour deformation)
  rw [rectangle_circle_agreement f a b c d hab hcd hf w hw R hR hRw]
  -- Step 3: Apply Mathlib's circle CIF
  have hf_ball : DifferentiableOn ℂ f (Metric.closedBall w R) := hf.mono hRw
  have := hf_ball.circleIntegral_sub_inv_smul (Metric.mem_ball_self hR)
  simp only [smul_eq_mul, div_eq_inv_mul] at this ⊢
  exact this

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
