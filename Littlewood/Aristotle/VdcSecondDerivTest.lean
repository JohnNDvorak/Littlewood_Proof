/-
Van der Corput second derivative test for oscillatory integrals.

KEY RESULT:
  vdc_second_deriv_bound: If φ is C² with φ'' ≥ lam > 0 on [a,b], then
    |∫_a^b cos(φ(t)) dt| ≤ 8/√lam

PROOF STRATEGY:
  1. φ' is strictly increasing (from φ'' ≥ lam).
  2. If φ' ≥ 0 on [a,b]: split at a+δ, bound each piece (trivial + first-deriv VdC).
  3. If φ' ≤ 0 on [a,b]: split at b-δ, bound each piece (first-deriv VdC for negative + trivial).
  4. If φ' changes sign at t₀: IVT finds zero, split [a,t₀] and [t₀,b], apply cases 2/3.
  5. Optimize δ = 1/√lam gives constant 4/√lam per piece, total 8/√lam.

APPLICATIONS:
  - MainTermFirstMomentBoundHyp (B2): per-mode oscillatory integral bound
  - Stationary phase analysis in Riemann-Siegel expansion

DEPENDS ON:
  - VdcFirstDerivTest.lean (first-derivative VdC bound + IBP identity, PROVED)

SORRY COUNT: 0

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.VdcFirstDerivTest

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 1600000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace VdcSecondDerivTest

open MeasureTheory intervalIntegral Set Filter Real
open VdcFirstDerivTest

/-! ## Derivative growth from second derivative lower bound -/

/-- If φ'' ≥ λ on [a,b], then φ'(t) ≥ φ'(s) + λ(t-s) for s ≤ t in [a,b]. -/
lemma deriv_growth (phi : ℝ → ℝ) (a b lam : ℝ)
    (hphi' : Differentiable ℝ (deriv phi))
    (hphi''cont : Continuous (deriv (deriv phi)))
    (hphi''_lower : ∀ t ∈ Icc a b, lam ≤ deriv (deriv phi) t)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    deriv phi s + lam * (t - s) ≤ deriv phi t := by
  suffices lam * (t - s) ≤ deriv phi t - deriv phi s by linarith
  rw [← integral_eq_sub_of_hasDerivAt (fun u _ => (hphi' u).hasDerivAt)
    hphi''cont.continuousOn.intervalIntegrable,
    show lam * (t - s) = ∫ _ in s..t, lam from by
      rw [intervalIntegral.integral_const]; simp [smul_eq_mul, mul_comm]]
  exact integral_mono_on hst continuousOn_const.intervalIntegrable
    hphi''cont.continuousOn.intervalIntegrable
    fun u hu => hphi''_lower u ⟨le_trans hs.1 hu.1, le_trans hu.2 ht.2⟩

/-! ## Trivial bound on any interval -/

/-- On any interval [a,b], |∫ cos(φ)| ≤ b - a. -/
private lemma trivial_cos_bound (phi : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : Continuous (fun t => Real.cos (phi t))) :
    |∫ t in a..b, Real.cos (phi t)| ≤ b - a := by
  calc |∫ t in a..b, Real.cos (phi t)|
      ≤ ∫ t in a..b, ‖Real.cos (phi t)‖ := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..b, (1 : ℝ) := by
        apply integral_mono_on hab hcont.continuousOn.intervalIntegrable.norm
          continuousOn_const.intervalIntegrable
        intro t _; rw [Real.norm_eq_abs]; exact abs_cos_le_one _
    _ = b - a := by rw [intervalIntegral.integral_const]; simp

/-! ## First-derivative VdC for negative derivative -/

/-- VdC first derivative test for negative derivative:
If φ' ≤ -m on [a,b] and φ'' ≥ 0, then |∫ cos φ| ≤ 3/m.
Proved using the same IBP identity as vdc_cos_bound, with modified bounds. -/
theorem vdc_cos_bound_neg (phi : ℝ → ℝ) (a b m : ℝ) (hab : a ≤ b) (hm : 0 < m)
    (hphi : Differentiable ℝ phi) (hphi' : Differentiable ℝ (deriv phi))
    (hphi'' : Continuous (deriv (deriv phi)))
    (hphi'_upper : ∀ t ∈ Icc a b, deriv phi t ≤ -m)
    (hphi''_nonneg : ∀ t ∈ Icc a b, 0 ≤ deriv (deriv phi) t) :
    |∫ t in a..b, Real.cos (phi t)| ≤ 3 / m := by
  have hne : ∀ t ∈ Icc a b, deriv phi t ≠ 0 := fun t ht => by linarith [hphi'_upper t ht]
  rw [ibp_cos_identity phi a b hab hphi hphi' hphi'' hne]
  have ha_neg : deriv phi a < 0 := by linarith [hphi'_upper a (left_mem_Icc.mpr hab)]
  have hb_neg : deriv phi b < 0 := by linarith [hphi'_upper b (right_mem_Icc.mpr hab)]
  -- Boundary bounds: |sin(φ(x))/φ'(x)| ≤ 1/m
  have hb_bound : |Real.sin (phi b) / deriv phi b| ≤ 1 / m := by
    rw [abs_div, abs_of_neg hb_neg]
    exact (div_le_div_of_nonneg_right (abs_sin_le_one _) (neg_pos.mpr hb_neg).le).trans
      (one_div_le_one_div_of_le hm (by linarith [hphi'_upper b (right_mem_Icc.mpr hab)]))
  have ha_bound : |Real.sin (phi a) / deriv phi a| ≤ 1 / m := by
    rw [abs_div, abs_of_neg ha_neg]
    exact (div_le_div_of_nonneg_right (abs_sin_le_one _) (neg_pos.mpr ha_neg).le).trans
      (one_div_le_one_div_of_le hm (by linarith [hphi'_upper a (left_mem_Icc.mpr hab)]))
  -- Integrability
  have h_int_sin_corr : IntervalIntegrable
      (fun t => Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2) volume a b :=
    (ContinuousOn.div ((continuous_sin.comp hphi.continuous).continuousOn.mul hphi''.continuousOn)
      ((continuous_pow 2).comp_continuousOn hphi'.continuous.continuousOn)
      (fun t ht => pow_ne_zero 2 (hne t ht))).intervalIntegrable_of_Icc hab
  have h_int_corr : IntervalIntegrable
      (fun t => deriv (deriv phi) t / (deriv phi t) ^ 2) volume a b :=
    (ContinuousOn.div hphi''.continuousOn
      ((continuous_pow 2).comp_continuousOn hphi'.continuous.continuousOn)
      (fun t ht => pow_ne_zero 2 (hne t ht))).intervalIntegrable_of_Icc hab
  -- Correction integrand is nonneg (φ'' ≥ 0, (φ')² > 0)
  have h_corr_nonneg : ∀ t ∈ Icc a b, 0 ≤ deriv (deriv phi) t / (deriv phi t) ^ 2 :=
    fun t ht => div_nonneg (hphi''_nonneg t ht) (sq_nonneg _)
  -- |∫ sin·g| ≤ ∫ g (since |sin| ≤ 1 and g ≥ 0)
  have h_upper : ∫ t in a..b, Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2
      ≤ ∫ t in a..b, deriv (deriv phi) t / (deriv phi t) ^ 2 := by
    apply integral_mono_on hab h_int_sin_corr h_int_corr
    intro t ht
    have : Real.sin (phi t) * deriv (deriv phi) t ≤ 1 * deriv (deriv phi) t :=
      mul_le_mul_of_nonneg_right (sin_le_one _) (hphi''_nonneg t ht)
    calc Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2
        ≤ 1 * deriv (deriv phi) t / (deriv phi t) ^ 2 :=
          div_le_div_of_nonneg_right this (sq_nonneg _)
      _ = deriv (deriv phi) t / (deriv phi t) ^ 2 := by ring
  have h_lower : -(∫ t in a..b, deriv (deriv phi) t / (deriv phi t) ^ 2)
      ≤ ∫ t in a..b, Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2 := by
    rw [← intervalIntegral.integral_neg]
    apply integral_mono_on hab h_int_corr.neg h_int_sin_corr
    intro t ht
    calc -(deriv (deriv phi) t / (deriv phi t) ^ 2)
        = (-1) * (deriv (deriv phi) t / (deriv phi t) ^ 2) := by ring
      _ ≤ Real.sin (phi t) * (deriv (deriv phi) t / (deriv phi t) ^ 2) :=
          mul_le_mul_of_nonneg_right (neg_one_le_sin _) (h_corr_nonneg t ht)
      _ = Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2 := by ring
  -- FTC: ∫ φ''/(φ')² = 1/φ'(a) - 1/φ'(b) ≤ 1/m
  have hFTC : ∫ t in a..b, deriv (deriv phi) t / (deriv phi t) ^ 2 =
      1 / deriv phi a - 1 / deriv phi b := by
    rw [integral_eq_sub_of_hasDerivAt
      (fun t ht => by rw [uIcc_of_le hab] at ht
                      convert ((hphi' t).hasDerivAt.inv (hne t ht)).neg using 1; ring)
      h_int_corr]
    simp [one_div]; ring
  have hFTC_bound : 1 / deriv phi a - 1 / deriv phi b ≤ 1 / m := by
    rw [div_sub_div _ _ ha_neg.ne hb_neg.ne, div_le_div_iff₀
      (mul_pos_of_neg_of_neg ha_neg hb_neg) hm]
    nlinarith [mul_le_mul_of_nonneg_left (show m ≤ -deriv phi b by
        linarith [hphi'_upper b (right_mem_Icc.mpr hab)])
      (show 0 ≤ -deriv phi a by linarith)]
  have h_corr_bound : |∫ t in a..b,
      Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2| ≤ 1 / m := by
    rw [abs_le]; exact ⟨by linarith [hFTC_bound, hFTC], by linarith [hFTC_bound, hFTC]⟩
  -- Triangle inequality: ≤ 1/m + 1/m + 1/m = 3/m
  calc |Real.sin (phi b) / deriv phi b - Real.sin (phi a) / deriv phi a +
         ∫ t in a..b, Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2|
      ≤ |Real.sin (phi b) / deriv phi b - Real.sin (phi a) / deriv phi a| +
        |∫ t in a..b, Real.sin (phi t) * deriv (deriv phi) t / (deriv phi t) ^ 2| :=
        abs_add_le _ _
    _ ≤ (|Real.sin (phi b) / deriv phi b| + |Real.sin (phi a) / deriv phi a|) + 1 / m := by
        gcongr
        calc |Real.sin (phi b) / deriv phi b - Real.sin (phi a) / deriv phi a|
            = |Real.sin (phi b) / deriv phi b + (-(Real.sin (phi a) / deriv phi a))| := by
              rw [sub_eq_add_neg]
          _ ≤ |Real.sin (phi b) / deriv phi b| + |-(Real.sin (phi a) / deriv phi a)| :=
              abs_add_le _ _
          _ = |Real.sin (phi b) / deriv phi b| + |Real.sin (phi a) / deriv phi a| := by
              rw [abs_neg]
    _ ≤ (1 / m + 1 / m) + 1 / m := by linarith
    _ = 3 / m := by ring

/-! ## Half-interval bounds -/

/-- On [a,b] with φ' ≥ 0 and φ'' ≥ λ > 0, the integral |∫ cos φ| ≤ 4/√λ.
Split at a + 1/√λ: trivial bound on short piece, first-deriv VdC on tail. -/
lemma half_bound (phi : ℝ → ℝ) (a b lam : ℝ) (hab : a ≤ b) (hlam : 0 < lam)
    (hphi : Differentiable ℝ phi) (hphi' : Differentiable ℝ (deriv phi))
    (hphi'' : Continuous (deriv (deriv phi)))
    (hphi''_lower : ∀ t ∈ Icc a b, lam ≤ deriv (deriv phi) t)
    (hphi'_nonneg : ∀ t ∈ Icc a b, 0 ≤ deriv phi t) :
    |∫ t in a..b, Real.cos (phi t)| ≤ 4 / Real.sqrt lam := by
  set δ := 1 / Real.sqrt lam with hδ_def
  have hsq : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hδ_pos : 0 < δ := div_pos one_pos hsq
  have hcont : Continuous (fun t => Real.cos (phi t)) := continuous_cos.comp hphi.continuous
  by_cases hshort : b ≤ a + δ
  · -- Short interval: trivial bound ≤ δ ≤ 4δ = 4/√λ
    calc |∫ t in a..b, Real.cos (phi t)|
        ≤ b - a := trivial_cos_bound phi a b hab hcont
      _ ≤ δ := by linarith
      _ ≤ 4 * δ := by linarith
      _ = 4 / Real.sqrt lam := by rw [hδ_def]; ring
  · -- Long interval: split at c = a + δ
    push_neg at hshort
    set c := a + δ
    have hac : a ≤ c := by linarith
    have hcb : c ≤ b := le_of_lt hshort
    have hsplit := integral_add_adjacent_intervals
      (hcont.continuousOn.intervalIntegrable (a := a) (b := c) (μ := volume))
      (hcont.continuousOn.intervalIntegrable (a := c) (b := b) (μ := volume))
    calc |∫ t in a..b, Real.cos (phi t)|
        = |(∫ t in a..c, Real.cos (phi t)) + (∫ t in c..b, Real.cos (phi t))| := by
          rw [← hsplit]
      _ ≤ |∫ t in a..c, Real.cos (phi t)| + |∫ t in c..b, Real.cos (phi t)| :=
          abs_add_le _ _
      _ ≤ δ + 3 / (lam * δ) := by
          gcongr
          · -- First piece [a, c]: trivial bound ≤ δ
            calc |∫ t in a..c, Real.cos (phi t)|
                ≤ c - a := trivial_cos_bound phi a c hac hcont
              _ = δ := by simp [c]
          · -- Second piece [c, b]: first-derivative VdC with m = λδ
            have hm : 0 < lam * δ := mul_pos hlam hδ_pos
            apply vdc_cos_bound phi c b (lam * δ) hcb hm hphi hphi' hphi''
            · -- φ'(t) ≥ λδ for t ∈ [c, b]
              intro t ht
              have htab : t ∈ Icc a b := ⟨le_trans hac ht.1, ht.2⟩
              have hcab : c ∈ Icc a b := ⟨hac, hcb⟩
              calc lam * δ = lam * (c - a) := by simp [c]
                _ ≤ deriv phi a + lam * (c - a) := by
                    linarith [hphi'_nonneg a (left_mem_Icc.mpr hab)]
                _ ≤ deriv phi c :=
                    deriv_growth phi a b lam hphi' hphi'' hphi''_lower
                      (left_mem_Icc.mpr hab) hcab hac
                _ ≤ deriv phi c + lam * (t - c) := by
                    linarith [mul_nonneg hlam.le (sub_nonneg.mpr ht.1)]
                _ ≤ deriv phi t :=
                    deriv_growth phi a b lam hphi' hphi'' hphi''_lower hcab htab ht.1
            · -- φ'' ≥ 0 (it's actually ≥ λ > 0)
              intro t ht
              linarith [hphi''_lower t ⟨le_trans hac ht.1, ht.2⟩]
      _ = 4 / Real.sqrt lam := by
          rw [hδ_def]
          have : lam * (1 / Real.sqrt lam) = Real.sqrt lam := by
            rw [mul_one_div, div_eq_iff hsq.ne']; exact (Real.mul_self_sqrt hlam.le).symm
          rw [this]; ring

/-- On [a,b] with φ' ≤ 0 and φ'' ≥ λ > 0, the integral |∫ cos φ| ≤ 4/√λ.
Split at b - 1/√λ: VdC for negative derivative on left, trivial on right. -/
lemma half_bound_neg (phi : ℝ → ℝ) (a b lam : ℝ) (hab : a ≤ b) (hlam : 0 < lam)
    (hphi : Differentiable ℝ phi) (hphi' : Differentiable ℝ (deriv phi))
    (hphi'' : Continuous (deriv (deriv phi)))
    (hphi''_lower : ∀ t ∈ Icc a b, lam ≤ deriv (deriv phi) t)
    (hphi'_nonpos : ∀ t ∈ Icc a b, deriv phi t ≤ 0) :
    |∫ t in a..b, Real.cos (phi t)| ≤ 4 / Real.sqrt lam := by
  set δ := 1 / Real.sqrt lam with hδ_def
  have hsq : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hδ_pos : 0 < δ := div_pos one_pos hsq
  have hcont : Continuous (fun t => Real.cos (phi t)) := continuous_cos.comp hphi.continuous
  by_cases hshort : b ≤ a + δ
  · calc |∫ t in a..b, Real.cos (phi t)|
        ≤ b - a := trivial_cos_bound phi a b hab hcont
      _ ≤ δ := by linarith
      _ ≤ 4 * δ := by linarith
      _ = 4 / Real.sqrt lam := by rw [hδ_def]; ring
  · push_neg at hshort
    set c := b - δ
    have hcb : c ≤ b := by linarith
    have hac : a ≤ c := by linarith
    have hsplit := integral_add_adjacent_intervals
      (hcont.continuousOn.intervalIntegrable (a := a) (b := c) (μ := volume))
      (hcont.continuousOn.intervalIntegrable (a := c) (b := b) (μ := volume))
    calc |∫ t in a..b, Real.cos (phi t)|
        = |(∫ t in a..c, Real.cos (phi t)) + (∫ t in c..b, Real.cos (phi t))| := by
          rw [← hsplit]
      _ ≤ |∫ t in a..c, Real.cos (phi t)| + |∫ t in c..b, Real.cos (phi t)| :=
          abs_add_le _ _
      _ ≤ 3 / (lam * δ) + δ := by
          gcongr
          · -- First piece [a, c]: VdC for negative derivative with m = λδ
            have hm : 0 < lam * δ := mul_pos hlam hδ_pos
            apply vdc_cos_bound_neg phi a c (lam * δ) hac hm hphi hphi' hphi''
            · -- φ'(t) ≤ -λδ for t ∈ [a, c]
              intro t ht
              have htab : t ∈ Icc a b := ⟨ht.1, le_trans ht.2 hcb⟩
              have hcab : c ∈ Icc a b := ⟨hac, hcb⟩
              -- φ'(c) ≤ φ'(b) - λδ ≤ 0 - λδ = -λδ
              have hpc : deriv phi c ≤ -lam * δ := by
                have := deriv_growth phi a b lam hphi' hphi'' hphi''_lower hcab
                  (right_mem_Icc.mpr hab) hcb
                have := hphi'_nonpos b (right_mem_Icc.mpr hab)
                simp [c] at *; linarith
              -- φ'(t) ≤ φ'(c) since φ' is increasing and t ≤ c
              have : deriv phi t ≤ deriv phi c := by
                have := deriv_growth phi a b lam hphi' hphi'' hphi''_lower htab hcab ht.2
                linarith [mul_nonneg hlam.le (sub_nonneg.mpr ht.2)]
              linarith
            · -- φ'' ≥ 0
              intro t ht
              linarith [hphi''_lower t ⟨ht.1, le_trans ht.2 hcb⟩]
          · -- Second piece [c, b]: trivial bound ≤ δ
            calc |∫ t in c..b, Real.cos (phi t)|
                ≤ b - c := trivial_cos_bound phi c b hcb hcont
              _ = δ := by simp [c]
      _ = 4 / Real.sqrt lam := by
          rw [hδ_def]
          have : lam * (1 / Real.sqrt lam) = Real.sqrt lam := by
            rw [mul_one_div, div_eq_iff hsq.ne']; exact (Real.mul_self_sqrt hlam.le).symm
          rw [this]; ring

/-! ## Main theorem -/

/-- **Van der Corput second derivative test**: If φ'' ≥ lam > 0 on [a,b], then
    |∫_a^b cos(φ(t)) dt| ≤ 8/√lam.

The constant 8 comes from handling both sides of the stationary point
(4/√lam each, via the optimization delta = 1/√lam). The bound can be improved
to C/√lam with C ~ 2√2 using Fresnel integrals directly.

Reference: Montgomery-Vaughan, "Multiplicative Number Theory I", Lemma 8.2. -/
theorem vdc_second_deriv_bound (phi : ℝ → ℝ) (a b lam : ℝ) (hab : a ≤ b) (hlam : 0 < lam)
    (hphi : Differentiable ℝ phi) (hphi' : Differentiable ℝ (deriv phi))
    (hphi'' : Continuous (deriv (deriv phi)))
    (hphi''_lower : ∀ t ∈ Icc a b, lam ≤ deriv (deriv phi) t) :
    |∫ t in a..b, Real.cos (phi t)| ≤ 8 / Real.sqrt lam := by
  have hsq : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hcont : Continuous (fun t => Real.cos (phi t)) := continuous_cos.comp hphi.continuous
  -- Case analysis on signs of φ'(a) and φ'(b)
  by_cases ha_sign : 0 ≤ deriv phi a
  · -- φ'(a) ≥ 0. Since φ' is increasing (φ'' ≥ λ > 0), φ' ≥ 0 on all of [a,b].
    have hpos : ∀ t ∈ Icc a b, 0 ≤ deriv phi t := by
      intro t ht
      have := deriv_growth phi a b lam hphi' hphi'' hphi''_lower
        (left_mem_Icc.mpr hab) ht ht.1
      linarith [mul_nonneg hlam.le (sub_nonneg.mpr ht.1)]
    calc |∫ t in a..b, Real.cos (phi t)|
        ≤ 4 / Real.sqrt lam := half_bound phi a b lam hab hlam hphi hphi' hphi'' hphi''_lower hpos
      _ ≤ 8 / Real.sqrt lam := div_le_div_of_nonneg_right (by norm_num) hsq.le
  · push_neg at ha_sign
    by_cases hb_sign : deriv phi b ≤ 0
    · -- φ'(b) ≤ 0. Since φ' is increasing and φ'(b) ≤ 0, φ' ≤ 0 on all of [a,b].
      have hneg : ∀ t ∈ Icc a b, deriv phi t ≤ 0 := by
        intro t ht
        have := deriv_growth phi a b lam hphi' hphi'' hphi''_lower
          ht (right_mem_Icc.mpr hab) ht.2
        linarith [mul_nonneg hlam.le (sub_nonneg.mpr ht.2)]
      calc |∫ t in a..b, Real.cos (phi t)|
          ≤ 4 / Real.sqrt lam :=
            half_bound_neg phi a b lam hab hlam hphi hphi' hphi'' hphi''_lower hneg
        _ ≤ 8 / Real.sqrt lam := div_le_div_of_nonneg_right (by norm_num) hsq.le
    · -- φ'(a) < 0 and φ'(b) > 0. IVT gives t₀ with φ'(t₀) = 0.
      push_neg at hb_sign
      obtain ⟨t₀, ht₀, ht₀_zero⟩ : ∃ t₀ ∈ Icc a b, deriv phi t₀ = 0 := by
        have := intermediate_value_Icc hab hphi'.continuous.continuousOn
          (show (0 : ℝ) ∈ Icc (deriv phi a) (deriv phi b) from ⟨by linarith, by linarith⟩)
        obtain ⟨t₀, ht₀, hft₀⟩ := this; exact ⟨t₀, ht₀, hft₀⟩
      -- Split integral at t₀
      have hsplit := integral_add_adjacent_intervals
        (hcont.continuousOn.intervalIntegrable (a := a) (b := t₀) (μ := volume))
        (hcont.continuousOn.intervalIntegrable (a := t₀) (b := b) (μ := volume))
      calc |∫ t in a..b, Real.cos (phi t)|
          = |(∫ t in a..t₀, Real.cos (phi t)) + (∫ t in t₀..b, Real.cos (phi t))| := by
            rw [← hsplit]
        _ ≤ |∫ t in a..t₀, Real.cos (phi t)| + |∫ t in t₀..b, Real.cos (phi t)| :=
            abs_add_le _ _
        _ ≤ 4 / Real.sqrt lam + 4 / Real.sqrt lam := by
            gcongr
            · -- Left half [a, t₀]: φ' ≤ 0 (φ' increases from negative to 0)
              apply half_bound_neg phi a t₀ lam ht₀.1 hlam hphi hphi' hphi''
              · intro t ht; exact hphi''_lower t ⟨ht.1, le_trans ht.2 ht₀.2⟩
              · intro t ht
                have := deriv_growth phi a b lam hphi' hphi'' hphi''_lower
                  ⟨ht.1, le_trans ht.2 ht₀.2⟩ ht₀ ht.2
                linarith [mul_nonneg hlam.le (sub_nonneg.mpr ht.2)]
            · -- Right half [t₀, b]: φ' ≥ 0 (φ' increases from 0 to positive)
              apply half_bound phi t₀ b lam ht₀.2 hlam hphi hphi' hphi''
              · intro t ht; exact hphi''_lower t ⟨le_trans ht₀.1 ht.1, ht.2⟩
              · intro t ht
                have := deriv_growth phi a b lam hphi' hphi'' hphi''_lower
                  ht₀ ⟨le_trans ht₀.1 ht.1, ht.2⟩ ht.1
                linarith [mul_nonneg hlam.le (sub_nonneg.mpr ht.1)]
        _ = 8 / Real.sqrt lam := by ring

end VdcSecondDerivTest
