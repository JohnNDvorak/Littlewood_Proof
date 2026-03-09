/-
Gauss series identity for Γ'/Γ - log via locally uniform convergence of GammaSeq.

Main result: `gauss_series_identity` — the identity
  Γ'(s)/Γ(s) - log(s) = Σ_{n≥0} [log(1 + 1/(s+n)) - 1/(s+n)]
for s with Re(s) > 0 and Γ(s) ≠ 0.

Co-authored-by: Claude (Anthropic)
-/

import Mathlib

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Complex Filter MeasureTheory Topology Finset

namespace GammaSeqLocalUniform

-- ============================================================
-- Helpers (needed by multiple sections)
-- ============================================================

lemma prod_range_add_ne_zero (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    ∏ j ∈ Finset.range (n + 1), (s + (j : ℂ)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro j _
  apply ne_of_apply_ne re
  simp only [add_re, natCast_re, zero_re]
  linarith [Nat.cast_nonneg (α := ℝ) j]

private lemma add_natCast_ne_zero (s : ℂ) (hs : 0 < s.re) (j : ℕ) :
    s + (j : ℂ) ≠ 0 := by
  apply ne_of_apply_ne re
  simp only [add_re, natCast_re, zero_re]
  linarith [Nat.cast_nonneg (α := ℝ) j]

-- ============================================================
-- GammaSeq differentiability on {Re > 0}
-- ============================================================

theorem GammaSeq_differentiableOn_re_pos {n : ℕ} (hn : n ≠ 0) :
    DifferentiableOn ℂ (fun s => Complex.GammaSeq s n) {s : ℂ | 0 < s.re} := by
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  unfold Complex.GammaSeq
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.div
  · exact (DifferentiableAt.const_cpow differentiableAt_id
      (Or.inl (Nat.cast_ne_zero.mpr hn))).mul (differentiableAt_const _)
  · exact DifferentiableAt.fun_finset_prod fun j _ =>
      differentiableAt_id.add (differentiableAt_const _)
  · exact prod_range_add_ne_zero s hs n

-- ============================================================
-- Section 1: Locally uniform convergence of GammaSeq
-- ============================================================

-- Uniform norm bound: ‖GammaSeq s n‖ ≤ Real.Gamma(Re(s)) for Re(s) > 0 and n ≥ 1.
private lemma norm_GammaSeq_le {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    ‖Complex.GammaSeq s n‖ ≤ Real.Gamma s.re := by
  rw [Complex.GammaSeq_eq_approx_Gamma_integral hs hn]
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [intervalIntegral.integral_of_le hnn]
  set f : ℝ → ℂ := fun x => ↑((1 - x / ↑n) ^ n) * (↑x : ℂ) ^ (s - 1)
  set g : ℝ → ℝ := fun x => Real.exp (-x) * x ^ (s.re - 1)
  have hf_int : IntegrableOn f (Set.Ioc (0 : ℝ) ↑n) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hnn]
    have h1 : IntervalIntegrable (fun x : ℝ => (↑x : ℂ) ^ (s - 1)) volume 0 (↑n) :=
      intervalIntegral.intervalIntegrable_cpow'
        (show -1 < (s - 1).re by simp only [sub_re, one_re]; linarith)
    have h2 : ContinuousOn (fun x : ℝ => (↑((1 - x / ↑n) ^ n) : ℂ)) (Set.uIcc 0 ↑n) :=
      (Continuous.continuousOn (by continuity))
    exact h1.continuousOn_mul h2
  have hg_int_Ioi : IntegrableOn g (Set.Ioi 0) := Real.GammaIntegral_convergent hs
  calc ‖∫ x in Set.Ioc (0 : ℝ) ↑n, f x‖
      ≤ ∫ x in Set.Ioc (0 : ℝ) ↑n, ‖f x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in Set.Ioc (0 : ℝ) ↑n, g x := by
        apply MeasureTheory.setIntegral_mono_on hf_int.norm
          (hg_int_Ioi.mono_set Set.Ioc_subset_Ioi_self) measurableSet_Ioc
        intro x hx
        show ‖f x‖ ≤ g x
        simp only [f, g, norm_mul, Complex.norm_of_nonneg
          (pow_nonneg (sub_nonneg.mpr (div_le_one_of_le₀ hx.2 (by positivity))) _),
          norm_cpow_eq_rpow_re_of_pos hx.1, sub_re, one_re]
        exact mul_le_mul_of_nonneg_right (Real.one_sub_div_pow_le_exp_neg hx.2)
          (Real.rpow_nonneg (le_of_lt hx.1) _)
    _ ≤ ∫ x in Set.Ioi 0, g x := by
        apply MeasureTheory.setIntegral_mono_set hg_int_Ioi
        · exact (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x (hx : 0 < x) =>
            mul_nonneg (le_of_lt (Real.exp_pos _)) (Real.rpow_nonneg (le_of_lt hx) _))
        · exact Set.Ioc_subset_Ioi_self.eventuallyLE
    _ = Real.Gamma s.re := (Real.Gamma_eq_integral hs).symm

-- Helper: Re(w) > 0 when w is in a closedBall with center.re > radius
private lemma re_pos_of_closedBall {c : ℂ} {R : ℝ}
    (hcR : 0 < c.re - R) {w : ℂ} (hw : w ∈ Metric.closedBall c R) :
    0 < w.re := by
  have hdist := Metric.mem_closedBall.mp hw
  have habs : |w.re - c.re| ≤ R := by
    calc |w.re - c.re| = |(w - c).re| := by rw [sub_re]
      _ ≤ ‖w - c‖ := abs_re_le_norm _
      _ = dist w c := (dist_eq_norm _ _).symm
      _ ≤ R := hdist
  linarith [(abs_le.mp habs).1]

-- Lipschitz bound for GammaSeq(·, n) on closedBall within {Re > 0}.
private lemma GammaSeq_equiLipschitz_on_ball (x₀ : ℂ) (hx₀ : 0 < x₀.re) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ {s : ℂ | 0 < s.re}) :
    ∃ L : ℝ, ∀ (n : ℕ), n ≠ 0 → ∀ s ∈ Metric.closedBall x₀ r,
      ‖Complex.GammaSeq s n - Complex.GammaSeq x₀ n‖ ≤ L * ‖s - x₀‖ := by
  -- δ = x₀.re - r > 0 (since closedBall ⊂ {Re > 0})
  have hδ : 0 < x₀.re - r := by
    have hmem : x₀ - (r : ℂ) ∈ Metric.closedBall x₀ r := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      rw [show x₀ - (r : ℂ) - x₀ = -(r : ℂ) from by ring]
      rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg hr.le]
    have h := hball hmem
    simp only [Set.mem_setOf_eq, sub_re, ofReal_re] at h
    linarith
  set δ := x₀.re - r with hδ_def
  set ρ := δ / 2 with hρ_def
  have hρ_pos : 0 < ρ := by linarith
  -- Uniform GammaSeq bound on the thickened ball closedBall x₀ (r + ρ)
  have hball' : Metric.closedBall x₀ (r + ρ) ⊆ {s : ℂ | 0 < s.re} := by
    intro w hw
    exact re_pos_of_closedBall (by linarith : 0 < x₀.re - (r + ρ)) hw
  -- Real.Gamma continuous on [δ/2, x₀.re + r + ρ], hence bounded
  have hΓcont : ContinuousOn Real.Gamma (Set.Icc (δ / 2) (x₀.re + r + ρ)) := by
    intro x hx
    apply (Real.differentiableAt_Gamma (fun m => ?_)).continuousAt.continuousWithinAt
    linarith [hx.1, Nat.cast_nonneg (α := ℝ) m]
  have hΓbdd := isCompact_Icc.bddAbove_image hΓcont
  obtain ⟨C₀, hC₀⟩ := hΓbdd
  have hC_bound : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), n ≠ 0 →
      ∀ w ∈ Metric.closedBall x₀ (r + ρ), ‖Complex.GammaSeq w n‖ ≤ C := by
    refine ⟨max C₀ 1, by positivity, fun n hn w hw => ?_⟩
    have hw_re_pos : 0 < w.re := hball' hw
    have hdist := Metric.mem_closedBall.mp hw
    have habs : |w.re - x₀.re| ≤ r + ρ := by
      calc |w.re - x₀.re| = |(w - x₀).re| := by rw [sub_re]
        _ ≤ ‖w - x₀‖ := abs_re_le_norm _
        _ = dist w x₀ := (dist_eq_norm _ _).symm
        _ ≤ r + ρ := hdist
    have hw_bounds : w.re ∈ Set.Icc (δ / 2) (x₀.re + r + ρ) :=
      ⟨by linarith [(abs_le.mp habs).1], by linarith [(abs_le.mp habs).2]⟩
    calc ‖Complex.GammaSeq w n‖
        ≤ Real.Gamma w.re := norm_GammaSeq_le hw_re_pos hn
      _ ≤ C₀ := hC₀ (Set.mem_image_of_mem _ hw_bounds)
      _ ≤ max C₀ 1 := le_max_left _ _
  obtain ⟨C, hC_pos, hC⟩ := hC_bound
  -- For s ∈ closedBall x₀ r, s.re ≥ δ
  have hre_ge_δ : ∀ s ∈ Metric.closedBall x₀ r, δ ≤ s.re := by
    intro s hs
    have hdist := Metric.mem_closedBall.mp hs
    have : |s.re - x₀.re| ≤ r := by
      calc |s.re - x₀.re| = |(s - x₀).re| := by rw [sub_re]
        _ ≤ ‖s - x₀‖ := abs_re_le_norm _
        _ = dist s x₀ := (dist_eq_norm _ _).symm
        _ ≤ r := hdist
    linarith [(abs_le.mp this).1]
  -- Cauchy estimate: ‖deriv(GammaSeq · n)(s)‖ ≤ C/ρ for s ∈ closedBall x₀ r
  have hderiv_bound : ∀ (n : ℕ), n ≠ 0 → ∀ s ∈ Metric.closedBall x₀ r,
      ‖deriv (fun z => Complex.GammaSeq z n) s‖ ≤ C / ρ := by
    intro n hn s hs
    apply norm_deriv_le_of_forall_mem_sphere_norm_le hρ_pos
    · -- DiffContOnCl ℂ (GammaSeq · n) (ball s ρ)
      apply DiffContOnCl.mk_ball
      · -- DifferentiableOn on open ball
        exact (GammaSeq_differentiableOn_re_pos hn).mono (fun w hw => by
          rw [Metric.mem_ball] at hw
          exact re_pos_of_closedBall (by linarith [hre_ge_δ s hs] : 0 < s.re - ρ)
            (Metric.mem_closedBall.mpr hw.le))
      · -- ContinuousOn on closed ball
        exact (GammaSeq_differentiableOn_re_pos hn).continuousOn.mono (fun w hw =>
          re_pos_of_closedBall (by linarith [hre_ge_δ s hs] : 0 < s.re - ρ) hw)
    · -- Norm bound on sphere
      intro w hw
      apply hC n hn
      rw [Metric.mem_closedBall] at hs ⊢
      rw [Metric.mem_sphere] at hw
      calc dist w x₀ ≤ dist w s + dist s x₀ := dist_triangle _ _ _
        _ = ρ + dist s x₀ := by rw [hw]
        _ ≤ ρ + r := by linarith
        _ = r + ρ := by ring
  -- Mean value inequality on convex closedBall
  refine ⟨C / ρ, fun n hn s hs => ?_⟩
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (GammaSeq_differentiableOn_re_pos hn w (hball hw)).differentiableAt
      (IsOpen.mem_nhds (isOpen_lt continuous_const continuous_re) (hball hw)))
    (fun w hw => hderiv_bound n hn w hw)
    (convex_closedBall x₀ r) (Metric.mem_closedBall_self hr.le) hs

theorem GammaSeq_tendstoLocallyUniformlyOn_re_pos :
    TendstoLocallyUniformlyOn
      (fun n : ℕ => fun s : ℂ => Complex.GammaSeq s n)
      Gamma atTop {s : ℂ | 0 < s.re} := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x₀ hx₀
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hopen x₀ hx₀
  set r := R / 3 with hr_def
  have hr : 0 < r := by linarith
  have hcball : Metric.closedBall x₀ r ⊆ {s : ℂ | 0 < s.re} :=
    fun s hs => hball (Metric.closedBall_subset_ball (by linarith) hs)
  obtain ⟨L, hL⟩ := GammaSeq_equiLipschitz_on_ball x₀ hx₀ r hr hcball
  have hptwise : Tendsto (fun n => Complex.GammaSeq x₀ n) atTop (𝓝 (Gamma x₀)) :=
    Complex.GammaSeq_tendsto_Gamma x₀
  have hptwise_dist : ∀ᶠ n in atTop, dist (Gamma x₀) (Complex.GammaSeq x₀ n) < ε / 3 := by
    have h : Tendsto (fun n => dist (Gamma x₀) (Complex.GammaSeq x₀ n)) atTop (𝓝 0) := by
      rw [← dist_self (Gamma x₀)]
      exact tendsto_const_nhds.dist hptwise
    exact h.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 3))
  have hx₀_re : 0 < x₀.re := hx₀
  have hΓcont : ContinuousAt Gamma x₀ := by
    apply (differentiableAt_Gamma x₀ (fun m => ?_)).continuousAt
    intro h; have := congrArg re h
    simp only [neg_re, natCast_re] at this
    linarith [Nat.cast_nonneg (α := ℝ) m]
  obtain ⟨δ₁, hδ₁, hΓδ₁⟩ := Metric.continuousAt_iff.mp hΓcont (ε / 3) (by linarith)
  set ρ := min r (min δ₁ (ε / (3 * (|L| + 1)))) with hρ_def
  have hρ : 0 < ρ := by positivity
  refine ⟨Metric.ball x₀ ρ ∩ {s : ℂ | 0 < s.re}, ?_, ?_⟩
  · exact Filter.inter_mem
      (nhdsWithin_le_nhds (Metric.ball_mem_nhds x₀ hρ))
      (nhdsWithin_le_nhds (hopen.mem_nhds hx₀))
  filter_upwards [hptwise_dist, Filter.eventually_ge_atTop 1] with n hdist_x₀ hn
  intro s ⟨hs_ball, hs_re⟩
  calc dist (Gamma s) (Complex.GammaSeq s n)
      ≤ dist (Gamma s) (Gamma x₀) + dist (Complex.GammaSeq s n) (Complex.GammaSeq x₀ n) +
        dist (Gamma x₀) (Complex.GammaSeq x₀ n) :=
        dist_triangle4_right (Gamma s) (Complex.GammaSeq s n) (Gamma x₀) (Complex.GammaSeq x₀ n)
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have hρ_le_r : ρ ≤ r := min_le_left _ _
        have hρ_le_δ₁ : ρ ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
        have hρ_le_ε3L : ρ ≤ ε / (3 * (|L| + 1)) := (min_le_right _ _).trans (min_le_right _ _)
        have h1 : dist (Gamma s) (Gamma x₀) < ε / 3 := by
          apply hΓδ₁
          exact lt_of_lt_of_le (Metric.mem_ball.mp hs_ball) hρ_le_δ₁
        have h3 : dist (Complex.GammaSeq s n) (Complex.GammaSeq x₀ n) ≤ ε / 3 := by
          rw [dist_eq_norm]
          have hs_cball : s ∈ Metric.closedBall x₀ r :=
            Metric.closedBall_subset_closedBall hρ_le_r
              (le_of_lt (Metric.mem_ball.mp hs_ball))
          have hs_dist : ‖s - x₀‖ < ε / (3 * (|L| + 1)) := by
            rw [← dist_eq_norm]
            exact lt_of_lt_of_le (Metric.mem_ball.mp hs_ball) hρ_le_ε3L
          calc ‖Complex.GammaSeq s n - Complex.GammaSeq x₀ n‖
              ≤ L * ‖s - x₀‖ := hL n (by omega) s hs_cball
            _ ≤ |L| * ‖s - x₀‖ := by gcongr; exact le_abs_self L
            _ ≤ |L| * (ε / (3 * (|L| + 1))) :=
                mul_le_mul_of_nonneg_left hs_dist.le (abs_nonneg L)
            _ ≤ (|L| + 1) * (ε / (3 * (|L| + 1))) := by
                gcongr; linarith [abs_nonneg L]
            _ = ε / 3 := by field_simp
        linarith [hdist_x₀]
    _ = ε := by ring

-- ============================================================
-- Section 3: logDeriv of GammaSeq = log(n) - Σ 1/(s+j)
-- ============================================================

theorem logDeriv_GammaSeq (s : ℂ) (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    logDeriv (fun z => Complex.GammaSeq z n) s =
      Complex.log (n : ℂ) - ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹ := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnf : (↑(Nat.factorial n) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h_eq : (fun z => Complex.GammaSeq z n) =
      fun z => ↑(Nat.factorial n) * ((n : ℂ) ^ z / ∏ j ∈ range (n + 1), (z + (j : ℂ))) := by
    ext z; simp only [Complex.GammaSeq]; ring
  rw [h_eq, logDeriv_const_mul s _ hnf]
  have hns : (n : ℂ) ^ s ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hn')
  have hprod : ∏ j ∈ range (n + 1), (s + (j : ℂ)) ≠ 0 := prod_range_add_ne_zero s hs n
  simp only [logDeriv]
  have hd_cpow : HasDerivAt (fun z => (n : ℂ) ^ z) ((n : ℂ) ^ s * Complex.log n) s := by
    have h := HasDerivAt.const_cpow (hasDerivAt_id s) (Or.inl hn')
    simp only [mul_one] at h; exact h
  have hd_prod : HasDerivAt (fun z => ∏ j ∈ range (n + 1), (z + (j : ℂ)))
      (∑ j ∈ range (n + 1), ∏ k ∈ (range (n + 1)).erase j, (s + (k : ℂ))) s := by
    have h := HasDerivAt.fun_finset_prod
      (fun j (_ : j ∈ range (n + 1)) => (hasDerivAt_id s).add (hasDerivAt_const s (j : ℂ)))
    convert h using 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [smul_eq_mul, add_zero, mul_one, Pi.add_apply, id_eq]
  have hd_quot := hd_cpow.div hd_prod hprod
  have hderiv : deriv (fun z => (n : ℂ) ^ z / ∏ j ∈ range (n + 1), (z + (j : ℂ))) s =
      ((n : ℂ) ^ s * Complex.log n * (∏ j ∈ range (n + 1), (s + (j : ℂ))) -
        (n : ℂ) ^ s * ∑ j ∈ range (n + 1), ∏ k ∈ (range (n + 1)).erase j, (s + (k : ℂ))) /
        (∏ j ∈ range (n + 1), (s + (j : ℂ))) ^ 2 := by
    convert hd_quot.deriv using 1
  simp only [Pi.div_apply]
  rw [hderiv, div_div]
  have hden : (∏ j ∈ range (n + 1), (s + (j : ℂ))) ^ 2 *
      ((n : ℂ) ^ s / ∏ j ∈ range (n + 1), (s + (j : ℂ))) =
      (∏ j ∈ range (n + 1), (s + (j : ℂ))) * (n : ℂ) ^ s := by
    rw [sq, mul_assoc, mul_div_cancel₀ _ hprod]
  rw [hden, mul_assoc, ← mul_sub,
      mul_comm (∏ j ∈ range (n + 1), (s + (j : ℂ))) ((n : ℂ) ^ s),
      mul_div_mul_left _ _ hns, sub_div, mul_div_cancel_right₀ _ hprod]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hj_ne : s + (j : ℂ) ≠ 0 := add_natCast_ne_zero s hs j
  have h_mul := Finset.prod_erase_mul (range (n + 1)) (fun k => s + (↑k : ℂ)) hj
  rw [div_eq_iff hprod, ← div_eq_inv_mul, eq_div_iff hj_ne]
  exact h_mul

-- ============================================================
-- Section 4: The Gauss series term and limit helpers
-- ============================================================

/-- The Gauss series term. -/
abbrev gaussTerm (w : ℂ) : ℂ := Complex.log (1 + 1 / w) - 1 / w

-- n/(s+n) → 1 as n → ∞
private lemma tendsto_natCast_div_add_swap (s : ℂ) :
    Tendsto (fun n : ℕ => (n : ℂ) / (s + (n : ℂ))) atTop (𝓝 1) := by
  have h := tendsto_natCast_div_add_atTop s
  exact h.congr' (Eventually.of_forall (fun n => by ring_nf))

-- (s+n)⁻¹ → 0 as n → ∞
private lemma tendsto_inv_add_natCast_zero (s : ℂ) :
    Tendsto (fun n : ℕ => (s + (n : ℂ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv₀_cobounded.comp ((tendsto_const_add_cobounded s).comp tendsto_natCast_atTop_cobounded)

-- log(n/(s+n)) → 0 as n → ∞
private lemma tendsto_log_natCast_div_add_zero (s : ℂ) :
    Tendsto (fun n : ℕ => Complex.log ((n : ℂ) / (s + (n : ℂ)))) atTop (𝓝 0) := by
  rw [← Complex.log_one]
  exact (continuousAt_clog Complex.one_mem_slitPlane).tendsto.comp
    (tendsto_natCast_div_add_swap s)

-- Telescoping sum of log(1+1/(s+j))
private lemma sum_log_one_add_inv (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    ∑ j ∈ Finset.range n, Complex.log (1 + 1 / (s + (j : ℂ))) =
      Complex.log (s + (n : ℂ)) - Complex.log s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hsn : s + (n : ℂ) ≠ 0 := add_natCast_ne_zero s hs n
    have hre_sn : 0 < (s + (n : ℂ)).re := by
      simp only [add_re, natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hre_sn1 : 0 < (s + ((n : ℕ) + 1 : ℂ)).re := by
      have : (s + ((n : ℕ) + 1 : ℂ)).re = s.re + (n : ℝ) + 1 := by
        simp [add_re, natCast_re, one_re]; ring
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have h1 : 1 + 1 / (s + (n : ℂ)) = (s + ((n : ℕ) + 1 : ℂ)) / (s + (n : ℂ)) := by
      field_simp; push_cast; ring
    rw [h1]
    have harg_sn : (s + (n : ℂ)).arg ≠ Real.pi := by
      intro h
      have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre_sn)
      rw [abs_lt] at this; linarith [this.2]
    suffices h : Complex.log ((s + ((n : ℕ) + 1 : ℂ)) / (s + (n : ℂ))) =
        Complex.log (s + ((n : ℕ) + 1 : ℂ)) - Complex.log (s + (n : ℂ)) by
      push_cast at h ⊢; rw [h]; ring
    rw [div_eq_mul_inv]
    have hsn1 : s + ((n : ℕ) + 1 : ℂ) ≠ 0 := by
      have := add_natCast_ne_zero s hs (n + 1); push_cast at this ⊢; exact this
    have harg_inv : (s + (n : ℂ))⁻¹.arg = -(s + (n : ℂ)).arg := by
      rw [Complex.arg_inv]; simp [harg_sn]
    have harg_cond : (s + ((n : ℕ) + 1 : ℂ)).arg + (s + (n : ℂ))⁻¹.arg ∈
        Set.Ioc (-(Real.pi : ℝ)) Real.pi := by
      rw [harg_inv]
      have h1 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre_sn1)
      have h2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre_sn)
      rw [abs_lt] at h1 h2
      constructor <;> linarith
    rw [Complex.log_mul hsn1 (inv_ne_zero hsn) harg_cond,
        Complex.log_inv _ harg_sn, sub_eq_add_neg]

-- ============================================================
-- Section 5: Main identity via uniqueness of limits
-- ============================================================

theorem gauss_series_identity (s : ℂ) (hs_re : 0 < s.re) (hΓ : Gamma s ≠ 0)
    (hsumm : Summable (fun n : ℕ => gaussTerm (s + (n : ℂ)))) :
    deriv Gamma s / Gamma s - Complex.log s =
      ∑' n : ℕ, gaussTerm (s + (n : ℂ)) := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hdiff : ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ
      (fun z => Complex.GammaSeq z n) {s : ℂ | 0 < s.re} := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact GammaSeq_differentiableOn_re_pos (by omega)
  have hlogDeriv := Complex.logDeriv_tendsto hU ⟨s, hs_re⟩
    GammaSeq_tendstoLocallyUniformlyOn_re_pos hdiff hΓ
  have htend_sub : Tendsto
      (fun n : ℕ => logDeriv (fun z => Complex.GammaSeq z n) s - Complex.log s)
      atTop (𝓝 (logDeriv Gamma s - Complex.log s)) :=
    hlogDeriv.sub tendsto_const_nhds
  have htend_gauss : Tendsto
      (fun n : ℕ => logDeriv (fun z => Complex.GammaSeq z n) s - Complex.log s)
      atTop (𝓝 (∑' n : ℕ, gaussTerm (s + (n : ℂ)))) := by
    suffices h : Tendsto
        (fun n : ℕ => Complex.log (n : ℂ) -
          ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹ - Complex.log s)
        atTop (𝓝 (∑' n : ℕ, gaussTerm (s + (n : ℂ)))) by
      apply h.congr'
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      rw [logDeriv_GammaSeq s hs_re (by omega)]
    simp_rw [Finset.sum_range_succ]
    suffices h : Tendsto
        (fun n : ℕ => Complex.log ((n : ℂ) / (s + (n : ℂ))) +
          ∑ j ∈ Finset.range n, gaussTerm (s + (j : ℂ)) -
          (s + (n : ℂ))⁻¹)
        atTop (𝓝 (∑' n : ℕ, gaussTerm (s + (n : ℂ)))) by
      apply h.congr'
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      simp only [gaussTerm]
      rw [Finset.sum_sub_distrib, sum_log_one_add_inv s hs_re n]
      have hsn : s + (n : ℂ) ≠ 0 := add_natCast_ne_zero s hs_re n
      have hre_sn : 0 < (s + (n : ℂ)).re := by
        simp only [add_re, natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have harg_sn : (s + (n : ℂ)).arg ≠ Real.pi := by
        intro h
        have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre_sn)
        rw [abs_lt] at this; linarith [this.2]
      have hlog : Complex.log ((n : ℂ) / (s + (n : ℂ))) =
          Complex.log (n : ℂ) - Complex.log (s + (n : ℂ)) := by
        rw [div_eq_mul_inv]
        have harg_inv : (s + (n : ℂ))⁻¹.arg = -(s + (n : ℂ)).arg := by
          rw [Complex.arg_inv]; simp [harg_sn]
        have harg_n : (n : ℂ).arg = 0 := Complex.natCast_arg
        rw [Complex.log_mul hn' (inv_ne_zero hsn) ?_, Complex.log_inv _ harg_sn]
        · ring
        · rw [harg_n, harg_inv, zero_add]
          have h_abs := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre_sn)
          rw [abs_lt] at h_abs
          exact ⟨by linarith, by linarith⟩
      rw [hlog]; simp only [one_div]; ring
    have h1 := tendsto_log_natCast_div_add_zero s
    have h2 := tendsto_inv_add_natCast_zero s
    have h3 := hsumm.hasSum.tendsto_sum_nat
    convert (h1.add h3).sub h2 using 1
    simp
  have := tendsto_nhds_unique htend_sub htend_gauss
  simp only [logDeriv] at this
  exact this

end GammaSeqLocalUniform
