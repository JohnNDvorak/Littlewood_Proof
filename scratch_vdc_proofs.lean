/-
  scratch_vdc_proofs.lean
  =======================
  AXLE-verified Mathlib-only Van der Corput first-derivative bounds.

  Agent 2 (iteration 3), 2026-03-15.

  Self-contained reproduction of `vdc_first_deriv_cos` and `vdc_first_deriv_sin`
  from VanDerCorputGeneric.lean, using only Mathlib imports. These cannot be
  imported into RSExpansionProof.lean due to circular dependencies, so Agent 1
  can inline them directly.

  Statement (VdC first derivative test):
    If f : ℝ → ℝ is C² on [a,b], f' ≥ λ > 0, and f' is monotone increasing,
    then ‖∫_a^b sin(f(t)) dt‖ ≤ 2/λ  (and similarly for cos).

  Proof: IBP with u = 1/f', v = -cos(f), then bound endpoints + correction.

  Reference: Titchmarsh, "The Theory of the Riemann Zeta-Function", Lemma 4.2.
-/

import Mathlib

set_option maxHeartbeats 3200000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace VdCScratch

open MeasureTheory Set Real Filter intervalIntegral

-- ════════════════════════════════════════════════════════════
-- Sub-lemmas for integration by parts
-- ════════════════════════════════════════════════════════════

/-- HasDerivAt for v(t) = -cos(f(t)): derivative is sin(f(t))·f'(t). -/
private lemma hasDerivAt_neg_cos_comp {f : ℝ → ℝ} {t : ℝ}
    (hf : HasDerivAt f (deriv f t) t) :
    HasDerivAt (fun s => -Real.cos (f s)) (Real.sin (f t) * deriv f t) t :=
  ((Real.hasDerivAt_cos (f t)).neg.comp t hf).congr_deriv (by ring)

/-- HasDerivAt for u(t) = (f'(t))⁻¹: derivative is -f''(t)/(f'(t))². -/
private lemma hasDerivAt_inv_deriv {f : ℝ → ℝ} {t : ℝ}
    (hf' : HasDerivAt (deriv f) (deriv (deriv f) t) t)
    (hf'_ne : deriv f t ≠ 0) :
    HasDerivAt (fun s => (deriv f s)⁻¹)
      (-(deriv (deriv f) t) / (deriv f t) ^ 2) t :=
  hf'.inv hf'_ne

-- ════════════════════════════════════════════════════════════
-- IBP identity
-- ════════════════════════════════════════════════════════════

/-- **Integration by parts identity** for oscillatory integrals.

∫_a^b sin(f(t)) dt = [-cos(f(t))/f'(t)]_a^b - ∫_a^b f''(t)·cos(f(t))/(f'(t))² dt

Proved via Mathlib's `integral_mul_deriv_eq_deriv_mul` with u = 1/f', v = -cos∘f. -/
theorem sin_integral_ibp
    {a b : ℝ}
    {f : ℝ → ℝ}
    (hf_deriv : ∀ t ∈ Set.uIcc a b, HasDerivAt f (deriv f t) t)
    (hf'_deriv : ∀ t ∈ Set.uIcc a b, HasDerivAt (deriv f) (deriv (deriv f) t) t)
    (hf'_ne : ∀ t ∈ Set.uIcc a b, deriv f t ≠ 0)
    (hu'_cont : ContinuousOn
      (fun t => -(deriv (deriv f) t) / (deriv f t) ^ 2) (Set.uIcc a b))
    (hv'_cont : ContinuousOn
      (fun t => Real.sin (f t) * deriv f t) (Set.uIcc a b)) :
    ∫ t in a..b, Real.sin (f t) =
      -Real.cos (f b) / deriv f b + Real.cos (f a) / deriv f a -
      ∫ t in a..b, deriv (deriv f) t * Real.cos (f t) / (deriv f t) ^ 2 := by
  have h_ibp := integral_mul_deriv_eq_deriv_mul
    (fun t ht => hasDerivAt_inv_deriv (hf'_deriv t ht) (hf'_ne t ht))
    (fun t ht => hasDerivAt_neg_cos_comp (hf_deriv t ht))
    hu'_cont.intervalIntegrable hv'_cont.intervalIntegrable
  have h_lhs : ∫ t in a..b, (deriv f t)⁻¹ * (Real.sin (f t) * deriv f t) =
      ∫ t in a..b, Real.sin (f t) :=
    intervalIntegral.integral_congr (fun t ht => by field_simp [hf'_ne t ht])
  rw [h_lhs] at h_ibp
  have h_corr : ∫ t in a..b,
      (-(deriv (deriv f) t) / (deriv f t) ^ 2) * (-Real.cos (f t)) =
      ∫ t in a..b, deriv (deriv f) t * Real.cos (f t) / (deriv f t) ^ 2 :=
    intervalIntegral.integral_congr (fun t _ => by ring)
  rw [h_corr] at h_ibp
  have h_bd : (deriv f b)⁻¹ * -Real.cos (f b) - (deriv f a)⁻¹ * -Real.cos (f a) =
      -Real.cos (f b) / deriv f b + Real.cos (f a) / deriv f a := by
    rw [inv_eq_one_div, inv_eq_one_div]; ring
  linarith

-- ════════════════════════════════════════════════════════════
-- VdC first derivative test (sin)
-- ════════════════════════════════════════════════════════════

/-- **Van der Corput first-derivative test (C², positive monotone derivative).**

If `f` is C² on `[a,b]` with `f' ≥ lam > 0` and `f'` monotone increasing,
then `‖∫_a^b sin(f(t)) dt‖ ≤ 2/lam`.

Proof: Apply `sin_integral_ibp`, then bound:
- Endpoints: `|cos(f(a))/f'(a)| + |cos(f(b))/f'(b)| ≤ 1/f'(a) + 1/f'(b)`
- Correction: `|∫ f''·cos(f)/f'²| ≤ ∫ f''/f'² = 1/f'(a) - 1/f'(b)` (since f'' ≥ 0)
- Total: `2/f'(a) ≤ 2/lam`. -/
theorem vdc_first_deriv_sin
    {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ}
    (hf_deriv : ∀ t ∈ Set.uIcc a b, HasDerivAt f (deriv f t) t)
    (hf'_deriv : ∀ t ∈ Set.uIcc a b, HasDerivAt (deriv f) (deriv (deriv f) t) t)
    (hf'_cont : ContinuousOn (deriv f) (Set.uIcc a b))
    (hf''_cont : ContinuousOn (deriv (deriv f)) (Set.uIcc a b))
    {lam : ℝ} (hlam : 0 < lam)
    (hf'_pos : ∀ t ∈ Icc a b, lam ≤ deriv f t)
    (hf'_mono : MonotoneOn (deriv f) (Icc a b)) :
    ‖∫ t in a..b, Real.sin (f t)‖ ≤ 2 / lam := by
  rcases eq_or_lt_of_le hab with rfl | hab_lt
  · simp [intervalIntegral.integral_same]; positivity
  have huIcc_eq : Set.uIcc a b = Icc a b := Set.uIcc_of_le hab
  have hf'_pos' : ∀ t ∈ Icc a b, 0 < deriv f t :=
    fun t ht => lt_of_lt_of_le hlam (hf'_pos t ht)
  have hf'_ne : ∀ t ∈ Set.uIcc a b, deriv f t ≠ 0 := by
    intro t ht; rw [huIcc_eq] at ht; exact ne_of_gt (hf'_pos' t ht)
  have hu'_cont : ContinuousOn
      (fun t => -(deriv (deriv f) t) / (deriv f t) ^ 2) (Set.uIcc a b) := by
    rw [huIcc_eq]
    exact (huIcc_eq ▸ hf''_cont).neg.div ((huIcc_eq ▸ hf'_cont).pow 2)
      (fun t ht => pow_ne_zero 2 (ne_of_gt (hf'_pos' t ht)))
  have hf_contOn : ContinuousOn f (Set.uIcc a b) :=
    fun t ht => (hf_deriv t ht).continuousAt.continuousWithinAt
  have hv'_cont : ContinuousOn
      (fun t => Real.sin (f t) * deriv f t) (Set.uIcc a b) :=
    (continuous_sin.comp_continuousOn hf_contOn).mul hf'_cont
  have h_ibp := sin_integral_ibp hf_deriv hf'_deriv hf'_ne hu'_cont hv'_cont
  rw [h_ibp, Real.norm_eq_abs]
  have hfa_pos : 0 < deriv f a := hf'_pos' a (left_mem_Icc.mpr hab)
  have hfb_pos : 0 < deriv f b := hf'_pos' b (right_mem_Icc.mpr hab)
  -- Endpoint bound
  have h_endpt_b : |Real.cos (f b) / deriv f b| ≤ (deriv f b)⁻¹ := by
    rw [abs_div, abs_of_pos hfb_pos, ← one_div]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hfb_pos.le
  have h_endpt_a : |Real.cos (f a) / deriv f a| ≤ (deriv f a)⁻¹ := by
    rw [abs_div, abs_of_pos hfa_pos, ← one_div]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hfa_pos.le
  have h_endpt : |-Real.cos (f b) / deriv f b + Real.cos (f a) / deriv f a| ≤
      (deriv f a)⁻¹ + (deriv f b)⁻¹ := by
    have h1 := abs_add_le (-Real.cos (f b) / deriv f b) (Real.cos (f a) / deriv f a)
    have h2 : |-Real.cos (f b) / deriv f b| = |Real.cos (f b) / deriv f b| := by
      rw [neg_div, abs_neg]
    linarith
  -- Correction bound: ‖∫ f''·cos(f)/f'²‖ ≤ 1/f'(a) - 1/f'(b)
  have hf''_nonneg : ∀ t ∈ Icc a b, 0 ≤ deriv (deriv f) t := by
    intro t ht
    have hUDF := uniqueDiffOn_convex (convex_Icc a b)
      (by rw [interior_Icc]; exact nonempty_Ioo.mpr hab_lt)
    have h1 : 0 ≤ derivWithin (deriv f) (Icc a b) t := hf'_mono.derivWithin_nonneg
    rwa [(hf'_deriv t (huIcc_eq ▸ ht)).hasDerivWithinAt.derivWithin (hUDF t ht)] at h1
  have h_dom_int : IntervalIntegrable
      (fun t => deriv (deriv f) t / (deriv f t) ^ 2) volume a b :=
    ((huIcc_eq ▸ ((huIcc_eq ▸ hf''_cont).div ((huIcc_eq ▸ hf'_cont).pow 2)
      (fun t ht => pow_ne_zero 2 (ne_of_gt (hf'_pos' t ht)))))).intervalIntegrable
  have h_corr : |∫ t in a..b, deriv (deriv f) t * Real.cos (f t) / (deriv f t) ^ 2| ≤
      (deriv f a)⁻¹ - (deriv f b)⁻¹ := by
    rw [← Real.norm_eq_abs]
    calc ‖∫ t in a..b, deriv (deriv f) t * Real.cos (f t) / (deriv f t) ^ 2‖
        ≤ ∫ t in a..b, deriv (deriv f) t / (deriv f t) ^ 2 :=
          intervalIntegral.norm_integral_le_of_norm_le hab
            (by filter_upwards with t ht
                have htm := Ioc_subset_Icc_self ht
                rw [Real.norm_eq_abs, abs_div,
                    abs_of_pos (sq_pos_of_pos (hf'_pos' t htm)),
                    abs_mul, abs_of_nonneg (hf''_nonneg t htm)]
                exact div_le_div_of_nonneg_right
                  ((mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
                    (hf''_nonneg t htm)).trans_eq (mul_one _)) (sq_nonneg _))
            h_dom_int
      _ = (deriv f a)⁻¹ - (deriv f b)⁻¹ := by
          have hF : ∀ t ∈ Set.uIcc a b,
              HasDerivAt (fun s => -(deriv f s)⁻¹)
                (deriv (deriv f) t / (deriv f t) ^ 2) t := by
            intro t ht
            convert ((hf'_deriv t ht).inv (hf'_ne t ht)).neg using 1; ring
          rw [integral_eq_sub_of_hasDerivAt hF h_dom_int]; ring
  -- Assembly: |E - C| ≤ |E| + |C| ≤ 2/f'(a) ≤ 2/lam
  set E := -Real.cos (f b) / deriv f b + Real.cos (f a) / deriv f a
  set C := ∫ t in a..b, deriv (deriv f) t * Real.cos (f t) / (deriv f t) ^ 2
  have h_tri : |E - C| ≤ |E| + |C| := by
    calc |E - C| = |E + (-C)| := by rw [sub_eq_add_neg]
      _ ≤ |E| + |-C| := abs_add_le E (-C)
      _ = |E| + |C| := by rw [abs_neg]
  have h_inv : (deriv f a)⁻¹ ≤ lam⁻¹ :=
    inv_anti₀ hlam (hf'_pos a (left_mem_Icc.mpr hab))
  linarith [div_eq_mul_inv (2 : ℝ) lam]

-- ════════════════════════════════════════════════════════════
-- VdC first derivative test (cos) — via phase shift
-- ════════════════════════════════════════════════════════════

/-- **Van der Corput first-derivative test for cosine (C², positive monotone derivative).**

Proved by phase shift: `cos(f(t)) = sin(f(t) + π/2)`, then apply `vdc_first_deriv_sin`. -/
theorem vdc_first_deriv_cos
    {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ}
    (hf_deriv : ∀ t ∈ Set.uIcc a b, HasDerivAt f (deriv f t) t)
    (hf'_deriv : ∀ t ∈ Set.uIcc a b, HasDerivAt (deriv f) (deriv (deriv f) t) t)
    (hf'_cont : ContinuousOn (deriv f) (Set.uIcc a b))
    (hf''_cont : ContinuousOn (deriv (deriv f)) (Set.uIcc a b))
    {lam : ℝ} (hlam : 0 < lam)
    (hf'_pos : ∀ t ∈ Icc a b, lam ≤ deriv f t)
    (hf'_mono : MonotoneOn (deriv f) (Icc a b)) :
    ‖∫ t in a..b, Real.cos (f t)‖ ≤ 2 / lam := by
  set g := fun t => f t + Real.pi / 2
  have hg_deriv_eq : deriv g = deriv f := by
    ext t; exact deriv_add_const (Real.pi / 2)
  have h_eq : (∫ t in a..b, Real.cos (f t)) = ∫ t in a..b, Real.sin (g t) := by
    congr 1; ext t; exact (Real.sin_add_pi_div_two (f t)).symm
  rw [h_eq]
  exact vdc_first_deriv_sin hab
    (fun t ht => by rw [show deriv g t = deriv f t from congr_fun hg_deriv_eq t]
                    exact (hf_deriv t ht).add (hasDerivAt_const t _) |>.congr_deriv (by ring))
    (fun t ht => by rw [hg_deriv_eq]; exact hf'_deriv t ht)
    (hg_deriv_eq ▸ hf'_cont) (hg_deriv_eq ▸ hf''_cont)
    hlam (fun t ht => hg_deriv_eq ▸ hf'_pos t ht)
    (fun x hx y hy hxy => by
      show deriv g x ≤ deriv g y
      simp only [show ∀ t, deriv g t = deriv f t from congr_fun hg_deriv_eq]
      exact hf'_mono hx hy hxy)

end VdCScratch
