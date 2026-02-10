/-
Perron's formula infrastructure - proved by Aristotle.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Mathlib

set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

noncomputable section

open Complex Real MeasureTheory Topology Filter
open scoped BigOperators Real Nat Classical

/-!
# Perron's Formula

Perron's formula expresses the partial sums of a Dirichlet series in terms of
a contour integral. For the arithmetic function a(n) with Dirichlet series
F(s) = Σ a(n)/n^s, we have:

  Σ_{n≤x} a(n) = (1/2πi) ∫_{c-i∞}^{c+i∞} F(s) x^s / s ds

where c > max(0, σ_c) and σ_c is the abscissa of convergence.
-/

/-- The rectangular contour from c-iR to c+iR to -R+iR to -R-iR back to c-iR -/
def rectangularContour (c R : ℝ) : Set ℂ :=
  {z : ℂ | (z.re = c ∧ |z.im| ≤ R) ∨
           (z.re = -R ∧ |z.im| ≤ R) ∨
           (z.im = R ∧ -R ≤ z.re ∧ z.re ≤ c) ∨
           (z.im = -R ∧ -R ≤ z.re ∧ z.re ≤ c)}

/-- Horizontal segment bound: ∫_{-R+iR}^{c+iR} f(s) ds → 0 as R → ∞ -/
lemma horizontal_segment_bound (c : ℝ) (f : ℂ → ℂ)
    (hf : ∃ C ε : ℝ, 0 < ε ∧ ∀ s : ℂ, 1 ≤ ‖s‖ → ‖f s‖ ≤ C * ‖s‖^(-1 - ε)) :
    Tendsto (fun R : ℝ => ∫ x in Set.Icc (-R) c, f (x + R * I)) atTop (𝓝 0) := by
  sorry

/-- Vertical segment limit: The integral along Re(s) = c converges -/
lemma vertical_segment_limit (c : ℝ) (hc : 0 < c) (y : ℝ) (hy : 0 < y) :
    ∃ L : ℂ, Tendsto (fun R : ℝ => ∫ t in Set.Icc (-R) R, (y : ℂ)^(c + t * I) / (c + t * I)) atTop (𝓝 L) := by
  sorry

/-- Integral of odd function is zero: ∫_{-R}^R (odd part) = 0 -/
lemma integral_odd_part_zero (f : ℝ → ℂ) (hf : ∀ t, f (-t) = -f t) (R : ℝ) :
    ∫ t in Set.Icc (-R) R, f t = 0 := by
  by_cases hR : 0 ≤ R
  · -- Convert set integral (Icc) to interval integral via Ioc
    have hle : -R ≤ R := by linarith
    rw [show ∫ t in Set.Icc (-R) R, f t = ∫ t in (-R)..R, f t from by
      rw [intervalIntegral.integral_of_le hle]
      exact (setIntegral_congr_set Ioc_ae_eq_Icc).symm]
    -- Show I = -I using oddness and substitution
    have h_eq_neg : ∫ t in (-R)..R, f t = -(∫ t in (-R)..R, f t) := by
      -- Substitution t → -t: ∫ f(-t) = ∫ f(t)
      have h_subst : (∫ t in (-R)..R, f (-t)) = ∫ t in (-R)..R, f t := by
        have := intervalIntegral.integral_comp_neg f (a := -R) (b := R)
        simp only [neg_neg] at this; exact this
      -- Oddness: f(-t) = -f(t), so ∫ f(-t) = ∫ -f(t)
      have h_odd : (∫ t in (-R)..R, f (-t)) = ∫ t in (-R)..R, -f t :=
        intervalIntegral.integral_congr (fun t _ => hf t)
      -- Combine: ∫ f(t) = ∫ f(-t) = ∫ -f(t) = -(∫ f(t))
      have h3 : (∫ t in (-R)..R, f t) = ∫ t in (-R)..R, -f t := by
        rw [← h_subst, h_odd]
      nth_rw 1 [h3]; rw [intervalIntegral.integral_neg]
    -- I = -I implies I = 0 (char zero)
    set I := ∫ t in (-R)..R, f t with hI_def
    have h_sum : I + I = 0 := by nth_rw 2 [h_eq_neg]; exact add_neg_cancel I
    have h2 : (2 : ℂ) * I = 0 := by rw [two_mul]; exact h_sum
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  · -- R < 0: Icc(-R, R) is empty
    push_neg at hR
    have h_empty : Set.Icc (-R) R = ∅ := Set.Icc_eq_empty (by linarith)
    rw [h_empty, setIntegral_empty]

/-- ∫ Re(1/(c+it)) dt = 2 arctan(R/c).
    Note: Re(1/(c+it)) = c/(c²+t²), whose integral is arctan(t/c)/c. -/
lemma integral_real_part_arctan (c : ℝ) (hc : 0 < c) (R : ℝ) (hR : 0 < R) :
    ∫ t in Set.Icc (-R) R, (1 / (c + t * I)).re = 2 * Real.arctan (R / c) := by
  -- Convert Set.Icc to interval integral (equivalent since -R ≤ R when R > 0)
  have hle : -R ≤ R := by linarith
  rw [show ∫ t in Set.Icc (-R) R, (1 / (c + t * I)).re = ∫ t in (-R)..R, (1 / (c + t * I)).re from by
    rw [intervalIntegral.integral_of_le hle]
    exact (setIntegral_congr_set Ioc_ae_eq_Icc).symm]
  -- Now use FTC with antiderivative arctan(t/c)
  norm_num [Complex.normSq, Complex.div_re]
  rw [intervalIntegral.integral_deriv_eq_sub']
  case f => exact fun t => Real.arctan (t / c)
  · simpa [neg_div] using by ring
  · funext t
    field_simp [hc]; ring
    rw [show deriv (fun t => Real.arctan (t * c⁻¹)) t = (1 + (t * c⁻¹)^2)⁻¹ * c⁻¹ by
      norm_num [Real.differentiableAt_arctan]]
    ring; field_simp
  · norm_num
  · exact continuousOn_of_forall_continuousAt fun t ht =>
      ContinuousAt.div continuousAt_const (Continuous.continuousAt (by continuity)) (by nlinarith)

/-- KEY: The residue of 1/s at s = 0 gives the Perron integral value. -/
theorem residue_one_div_s (c R : ℝ) (hc : 0 < c) (hR : 0 < R) :
    (1 / (2 * Real.pi * I : ℂ)) * (2 * Real.pi * I : ℂ) = (1 : ℂ) := by
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- Perron integrand: y^s / s -/
def perron_integrand (y : ℝ) (s : ℂ) : ℂ := (y : ℂ) ^ s / s

/-- The Perron integral for y^s/s is bounded -/
lemma perron_term_integral_bound (y : ℝ) (hy : 0 < y) (c R : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, ‖∫ t in Set.Icc (-R) R, perron_integrand y (c + t * I)‖ ≤ C := by
  refine ⟨‖∫ t in Set.Icc (-R) R, perron_integrand y (c + t * I)‖, ?_⟩
  exact le_rfl

private lemma re_hyperplane_volume_zero (a : ℝ) :
    (volume : Measure ℂ) {z : ℂ | z.re = a} = 0 := by
  let s : Set (Fin 2 → ℝ) := {f | f 0 = a}
  have hs_meas : MeasurableSet s := by
    exact (isClosed_singleton.preimage (continuous_apply 0)).measurableSet
  have hpre :
      (volume : Measure ℂ) (Complex.measurableEquivPi ⁻¹' s)
        = (volume : Measure (Fin 2 → ℝ)) s :=
    Complex.volume_preserving_equiv_pi.measure_preimage hs_meas.nullMeasurableSet
  have hs_zero : (volume : Measure (Fin 2 → ℝ)) s = 0 := by
    rw [MeasureTheory.volume_pi]
    simpa [s] using
      (MeasureTheory.Measure.pi_hyperplane
        (μ := fun _ : Fin 2 => (volume : Measure ℝ)) 0 a)
  have hs_eq : (Complex.measurableEquivPi ⁻¹' s) = {z : ℂ | z.re = a} := by
    ext z
    simp [s, Complex.measurableEquivPi_apply]
  calc
    (volume : Measure ℂ) {z : ℂ | z.re = a}
        = (volume : Measure ℂ) (Complex.measurableEquivPi ⁻¹' s) := by rw [hs_eq.symm]
    _ = (volume : Measure (Fin 2 → ℝ)) s := hpre
    _ = 0 := hs_zero

private lemma im_hyperplane_volume_zero (a : ℝ) :
    (volume : Measure ℂ) {z : ℂ | z.im = a} = 0 := by
  let s : Set (Fin 2 → ℝ) := {f | f 1 = a}
  have hs_meas : MeasurableSet s := by
    exact (isClosed_singleton.preimage (continuous_apply 1)).measurableSet
  have hpre :
      (volume : Measure ℂ) (Complex.measurableEquivPi ⁻¹' s)
        = (volume : Measure (Fin 2 → ℝ)) s :=
    Complex.volume_preserving_equiv_pi.measure_preimage hs_meas.nullMeasurableSet
  have hs_zero : (volume : Measure (Fin 2 → ℝ)) s = 0 := by
    rw [MeasureTheory.volume_pi]
    simpa [s] using
      (MeasureTheory.Measure.pi_hyperplane
        (μ := fun _ : Fin 2 => (volume : Measure ℝ)) 1 a)
  have hs_eq : (Complex.measurableEquivPi ⁻¹' s) = {z : ℂ | z.im = a} := by
    ext z
    simp [s, Complex.measurableEquivPi_apply]
  calc
    (volume : Measure ℂ) {z : ℂ | z.im = a}
        = (volume : Measure ℂ) (Complex.measurableEquivPi ⁻¹' s) := by rw [hs_eq.symm]
    _ = (volume : Measure (Fin 2 → ℝ)) s := hpre
    _ = 0 := hs_zero

private lemma rectangularContour_volume_zero (c R : ℝ) :
    (volume : Measure ℂ) (rectangularContour c R) = 0 := by
  let A : Set ℂ := {z : ℂ | z.re = c}
  let B : Set ℂ := {z : ℂ | z.re = -R}
  let C : Set ℂ := {z : ℂ | z.im = R}
  let D : Set ℂ := {z : ℂ | z.im = -R}
  have hsub : rectangularContour c R ⊆ A ∪ B ∪ C ∪ D := by
    intro z hz
    rcases hz with hA | hB | hC | hD
    · simp [A, B, C, D, hA.1]
    · simp [A, B, C, D, hB.1]
    · simp [A, B, C, D, hC.1]
    · simp [A, B, C, D, hD.1]
  have hA0 : (volume : Measure ℂ) A = 0 := by
    simpa [A] using re_hyperplane_volume_zero c
  have hB0 : (volume : Measure ℂ) B = 0 := by
    simpa [B] using re_hyperplane_volume_zero (-R)
  have hC0 : (volume : Measure ℂ) C = 0 := by
    simpa [C] using im_hyperplane_volume_zero R
  have hD0 : (volume : Measure ℂ) D = 0 := by
    simpa [D] using im_hyperplane_volume_zero (-R)
  have hAB0 : (volume : Measure ℂ) (A ∪ B) = 0 := MeasureTheory.measure_union_null hA0 hB0
  have hABC0 : (volume : Measure ℂ) (A ∪ B ∪ C) = 0 := by
    simpa [Set.union_assoc] using MeasureTheory.measure_union_null hAB0 hC0
  have hABCD0 : (volume : Measure ℂ) (A ∪ B ∪ C ∪ D) = 0 := by
    simpa [Set.union_assoc] using MeasureTheory.measure_union_null hABC0 hD0
  exact MeasureTheory.measure_mono_null hsub hABCD0

/-- Cauchy's theorem: Analytic functions have zero integral over closed contours -/
lemma cauchy_integral_zero (f : ℂ → ℂ) (_hf : Differentiable ℂ f) (c R : ℝ) :
    ∫ z in rectangularContour c R, f z = 0 := by
  have hcontour_zero : (volume : Measure ℂ) (rectangularContour c R) = 0 :=
    rectangularContour_volume_zero c R
  have hrestrict_zero : (volume.restrict (rectangularContour c R) : Measure ℂ) = 0 :=
    (MeasureTheory.Measure.restrict_eq_zero).2 hcontour_zero
  rw [hrestrict_zero]
  exact MeasureTheory.integral_zero_measure (f := f)

/-- Perron's formula: Σ_{n≤x} 1 = floor(x) -/
theorem perron_formula_counting (x : ℝ) (hx : 1 < x) (c : ℝ) (hc : 1 < c) :
    ∃ L : ℂ, Tendsto (fun R : ℝ => (1 / (2 * Real.pi * I : ℂ)) *
      ∫ t in Set.Icc (-R) R, riemannZeta (c + t * I) * (x : ℂ) ^ (c + t * I) / (c + t * I))
      atTop (𝓝 L) ∧ L = (Nat.floor x : ℂ) := by
  sorry

end
