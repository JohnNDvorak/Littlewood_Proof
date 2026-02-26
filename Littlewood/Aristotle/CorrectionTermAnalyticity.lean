/-
Analyticity of the correction term in the Euler product logarithm.

The Euler product logarithm decomposes as:
  H_zeta_log(s) = ∑_p -log(1 - p^{-s}) = ∑_p p^{-s} + correctionTerm(s)

where correctionTerm(s) = ∑_p (-log(1-p^{-s}) - p^{-s}) converges absolutely
on {Re(s) > 1/2}, hence is analytic there.

## Main Results

* `correctionTermP_analyticOnNhd` : Each per-prime correction term is analytic on {Re > 0}.
* `correctionTerm_analyticOnNhd` : The full correction term is analytic on {Re > α} for α > 1/2.
* `H_zeta_log_eq_add` : H_zeta_log = primeZeta + correctionTerm on {Re > 1}.

## Proof Strategy

For `correctionTermP_analyticOnNhd`: Each term -log(1-p^{-s}) - p^{-s} is a difference
of two analytic functions on {Re > 0}, since 1-p^{-s} ∈ slitPlane there.

For `correctionTerm_analyticOnNhd`: Weierstrass M-test with Mathlib's
`norm_log_one_add_sub_self_le` bound ‖log(1+z)-z‖ ≤ ‖z‖²/(2(1-‖z‖)) combined with
`Nat.Primes.summable_rpow` for ∑_p p^{-2α} < ∞ when α > 1/2.

SORRY COUNT: 0 — All sub-components proved.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.LandauLogZetaObstruction

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Aristotle.CorrectionTermAnalyticity

open Complex Real Filter Topology MeasureTheory Set

/-! ## Definitions -/

/-- Per-prime correction term: -log(1 - p^{-s}) - p^{-s}.
This equals ∑_{k≥2} (1/k)(p^{-s})^k — the higher-order part of the
Taylor expansion of -log(1-z) at z = p^{-s}. -/
def correctionTermP (p : Nat.Primes) (s : ℂ) : ℂ :=
  -Complex.log (1 - (↑(p : ℕ) : ℂ) ^ (-s)) - (↑(p : ℕ) : ℂ) ^ (-s)

/-- Full correction term: ∑_p correctionTermP(p, s). -/
def correctionTerm (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, correctionTermP p s

/-- Prime zeta function: P(s) = ∑_p p^{-s}. -/
def primeZeta (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, (↑(p : ℕ) : ℂ) ^ (-s)

/-! ## Helper lemmas -/

/-- Cast alignment: (p : ℕ) → ℂ factors through ℝ. -/
private lemma prime_natCast_eq_ofReal (p : Nat.Primes) :
    (↑(p : ℕ) : ℂ) = ((↑(p : ℕ) : ℝ) : ℂ) := by
  norm_cast

/-- For prime p ≥ 2 and Re(s) > 0, we have |p^{-s}| < 1. -/
private lemma prime_cpow_norm_lt_one (p : Nat.Primes) (s : ℂ) (hs : 0 < s.re) :
    ‖(↑(p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
  have hp_pos : (0 : ℝ) < (p : ℕ) := Nat.cast_pos.mpr p.prop.pos
  have hp_gt1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.one_lt
  rw [prime_natCast_eq_ofReal p, norm_cpow_eq_rpow_re_of_pos hp_pos, neg_re]
  exact rpow_lt_one_of_one_lt_of_neg hp_gt1 (by linarith)

/-- For prime p ≥ 2 and Re(s) > 0, 1 - p^{-s} is in the slit plane. -/
private lemma one_sub_prime_cpow_mem_slitPlane (p : Nat.Primes) (s : ℂ) (hs : 0 < s.re) :
    1 - (↑(p : ℕ) : ℂ) ^ (-s) ∈ Complex.slitPlane := by
  have h_norm := prime_cpow_norm_lt_one p s hs
  have h_re : 0 < (1 - (↑(p : ℕ) : ℂ) ^ (-s)).re := by
    simp only [sub_re, one_re]
    linarith [Complex.re_le_norm ((↑(p : ℕ) : ℂ) ^ (-s))]
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl h_re

/-- (p : ℂ) is in slitPlane for prime p (since p > 0). -/
private lemma prime_cast_mem_slitPlane (p : Nat.Primes) :
    (↑(p : ℕ) : ℂ) ∈ Complex.slitPlane :=
  Complex.ofReal_mem_slitPlane.mpr (by exact_mod_cast p.prop.pos)

/-! ## Analyticity of correctionTermP -/

/-- The function s ↦ (p:ℂ)^{-s} is differentiable everywhere. -/
private lemma differentiableAt_prime_cpow_neg (p : Nat.Primes) (s : ℂ) :
    DifferentiableAt ℂ (fun s => (↑(p : ℕ) : ℂ) ^ (-s)) s := by
  exact differentiableAt_id.neg.const_cpow (Or.inl (Nat.cast_ne_zero.mpr p.prop.ne_zero))

/-- Each per-prime correction term is analytic on {Re(s) > 0}. -/
theorem correctionTermP_analyticOnNhd (p : Nat.Primes) :
    AnalyticOnNhd ℂ (correctionTermP p) {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | (0 : ℝ) < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ hopen
  intro s hs
  simp only [mem_setOf_eq] at hs
  apply DifferentiableWithinAt.sub
  · apply DifferentiableWithinAt.neg
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.clog
    · exact (differentiableAt_const 1).sub (differentiableAt_prime_cpow_neg p s)
    · exact one_sub_prime_cpow_mem_slitPlane p s hs
  · exact (differentiableAt_prime_cpow_neg p s).differentiableWithinAt

/-! ## Norm bound for correctionTermP

The key estimate uses Mathlib's `norm_log_one_add_sub_self_le`:
  ‖log(1+z) - z‖ ≤ ‖z‖² * (1-‖z‖)⁻¹ / 2
Setting z = -p^{-s}: correctionTermP = -(log(1+z) - z), and ‖z‖ = p^{-σ} < 1.

Proof path: norm_log_one_add_sub_self_le + rpow algebra gives
  ‖correctionTermP p s‖ ≤ p^{-2σ}/(1 - p^{-σ}) -/

/-- Norm bound: ‖correctionTermP(p, s)‖ ≤ p^{-2σ}/(1 - p^{-σ}) where σ = Re(s).
From `norm_log_one_add_sub_self_le` with z = -p^{-s}, dropping the /2 factor. -/
theorem correctionTermP_norm_le (p : Nat.Primes) (s : ℂ) (hs : 0 < s.re) :
    ‖correctionTermP p s‖ ≤
      (↑(p : ℕ) : ℝ) ^ (-2 * s.re) / (1 - (↑(p : ℕ) : ℝ) ^ (-s.re)) := by
  have hp_pos : (0 : ℝ) < (↑(p : ℕ) : ℝ) := Nat.cast_pos.mpr p.prop.pos
  set w := (↑(p : ℕ) : ℂ) ^ (-s) with hw_def
  have hw_norm : ‖w‖ = (↑(p : ℕ) : ℝ) ^ (-s.re) := by
    simp only [hw_def, prime_natCast_eq_ofReal p,
      norm_cpow_eq_rpow_re_of_pos hp_pos, neg_re]
  have hw_lt : ‖w‖ < 1 := prime_cpow_norm_lt_one p s hs
  -- correctionTermP p s = -(log(1 + (-w)) - (-w))
  have h_norm_eq : ‖correctionTermP p s‖ = ‖Complex.log (1 + (-w)) - (-w)‖ := by
    unfold correctionTermP
    have h : -Complex.log (1 - w) - w = -(Complex.log (1 + (-w)) - (-w)) := by
      have : (1 : ℂ) + (-w) = 1 - w := by ring
      rw [this]; ring
    rw [h, norm_neg]
  rw [h_norm_eq]
  -- Apply norm_log_one_add_sub_self_le with z = -w
  have h_neg_lt : ‖(-w : ℂ)‖ < 1 := by rw [norm_neg]; exact hw_lt
  have h_bound := norm_log_one_add_sub_self_le h_neg_lt
  -- ‖-w‖² = p^{-2σ}
  have h_sq : ‖(-w : ℂ)‖ ^ 2 = (↑(p : ℕ) : ℝ) ^ (-2 * s.re) := by
    rw [norm_neg, hw_norm, sq, ← rpow_add hp_pos]; congr 1; ring
  have h_nonneg : 0 ≤ ‖(-w : ℂ)‖ ^ 2 * (1 - ‖(-w : ℂ)‖)⁻¹ :=
    mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (sub_nonneg.mpr h_neg_lt.le))
  calc ‖Complex.log (1 + (-w)) - (-w)‖
      ≤ ‖(-w : ℂ)‖ ^ 2 * (1 - ‖(-w : ℂ)‖)⁻¹ / 2 := h_bound
    _ ≤ ‖(-w : ℂ)‖ ^ 2 * (1 - ‖(-w : ℂ)‖)⁻¹ :=
        div_le_self h_nonneg (by norm_num)
    _ = (↑(p : ℕ) : ℝ) ^ (-2 * s.re) / (1 - (↑(p : ℕ) : ℝ) ^ (-s.re)) := by
        rw [h_sq, norm_neg, hw_norm, div_eq_mul_inv]

/-! ## Summability and uniform convergence -/

/-- The correction term series converges absolutely for Re(s) > α > 1/2.
By correctionTermP_norm_le + rpow monotonicity + Nat.Primes.summable_rpow. -/
theorem correctionTerm_summable (α : ℝ) (hα : 1 / 2 < α) (s : ℂ) (hs : α < s.re) :
    Summable (fun p : Nat.Primes => correctionTermP p s) := by
  have hσ : 0 < s.re := by linarith
  have hα_pos : 0 < α := by linarith
  have h2α_lt : (2 : ℝ) ^ (-α) < 1 :=
    rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1sub_pos : 0 < 1 - (2 : ℝ) ^ (-α) := sub_pos.mpr h2α_lt
  -- Comparison series: (1-2^{-α})⁻¹ * p^{-2α}
  have h_sum : Summable (fun p : Nat.Primes =>
      (1 - (2 : ℝ) ^ (-α))⁻¹ * (p : ℝ) ^ (-2 * α)) :=
    (Nat.Primes.summable_rpow.mpr (by linarith : -2 * α < -1)).mul_left _
  apply Summable.of_norm_bounded h_sum
  intro p
  have hp_pos : (0 : ℝ) < (p : ℕ) := Nat.cast_pos.mpr p.prop.pos
  have hp_ge1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.prop.one_lt.le
  have hp_ge2 : (2 : ℝ) ≤ (↑(p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  -- p^{-s.re} < 1
  have h_psig_lt : (↑(p : ℕ) : ℝ) ^ (-s.re) < 1 := by
    have h := prime_cpow_norm_lt_one p s hσ
    rwa [prime_natCast_eq_ofReal p, norm_cpow_eq_rpow_re_of_pos hp_pos, neg_re] at h
  -- Chain: ‖f p‖ ≤ p^{-2σ}/(1-p^{-σ}) ≤ p^{-2α} * (1-2^{-α})⁻¹
  -- p^{-σ} ≤ 2^{-α} (needed for denominator bound)
  have h_psig_le_2α : (↑(p : ℕ) : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-α) := by
    calc (↑(p : ℕ) : ℝ) ^ (-s.re)
        ≤ (↑(p : ℕ) : ℝ) ^ (-α) := rpow_le_rpow_of_exponent_le hp_ge1 (by linarith)
      _ ≤ (2 : ℝ) ^ (-α) := by
          rw [rpow_neg hp_pos.le, rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
          exact inv_anti₀ (rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) α)
            (rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2) hp_ge2 hα_pos.le)
  calc ‖correctionTermP p s‖
      ≤ (↑(p : ℕ) : ℝ) ^ (-2 * s.re) / (1 - (↑(p : ℕ) : ℝ) ^ (-s.re)) :=
        correctionTermP_norm_le p s hσ
    _ ≤ (↑(p : ℕ) : ℝ) ^ (-2 * α) / (1 - (↑(p : ℕ) : ℝ) ^ (-s.re)) :=
        div_le_div_of_nonneg_right
          (rpow_le_rpow_of_exponent_le hp_ge1 (by linarith))
          (sub_pos.mpr h_psig_lt).le
    _ ≤ (↑(p : ℕ) : ℝ) ^ (-2 * α) / (1 - (2 : ℝ) ^ (-α)) :=
        div_le_div_of_nonneg_left
          (rpow_nonneg hp_pos.le _)
          h1sub_pos
          (sub_le_sub_left h_psig_le_2α 1)
    _ = (1 - (2 : ℝ) ^ (-α))⁻¹ * (↑(p : ℕ) : ℝ) ^ (-2 * α) := by
        rw [div_eq_mul_inv, mul_comm]

/-- The correction term series converges uniformly on {Re(s) > α} for α > 1/2.
Proof: Weierstrass M-test with u_p = p^{-2α}/(1-2^{-α}) via
HasSumUniformlyOn.of_norm_le_summable. -/
theorem correctionTerm_tendstoUniformlyOn (α : ℝ) (hα : 1 / 2 < α) :
    TendstoUniformlyOn
      (fun (N : Finset Nat.Primes) (s : ℂ) => ∑ p ∈ N, correctionTermP p s)
      correctionTerm atTop {s : ℂ | α < s.re} := by
  -- Weierstrass M-test with u_p = (1-2^{-α})⁻¹ * p^{-2α}
  have hα_pos : 0 < α := by linarith
  have h2α_lt : (2 : ℝ) ^ (-α) < 1 :=
    rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1sub_pos : 0 < 1 - (2 : ℝ) ^ (-α) := sub_pos.mpr h2α_lt
  have h_sum : Summable (fun p : Nat.Primes =>
      (1 - (2 : ℝ) ^ (-α))⁻¹ * (↑(p : ℕ) : ℝ) ^ (-2 * α)) :=
    (Nat.Primes.summable_rpow.mpr (by linarith : -2 * α < -1)).mul_left _
  -- correctionTerm unfolds to ∑' p, correctionTermP p s
  show TendstoUniformlyOn
    (fun (N : Finset Nat.Primes) (s : ℂ) => ∑ p ∈ N, correctionTermP p s)
    (fun s => ∑' p, correctionTermP p s) atTop {s : ℂ | α < s.re}
  exact tendstoUniformlyOn_tsum h_sum fun p s hs => by
    simp only [mem_setOf_eq] at hs
    have hσ : 0 < s.re := by linarith
    have hp_pos : (0 : ℝ) < (↑(p : ℕ) : ℝ) := Nat.cast_pos.mpr p.prop.pos
    have hp_ge1 : (1 : ℝ) ≤ (↑(p : ℕ) : ℝ) := by exact_mod_cast p.prop.one_lt.le
    have hp_ge2 : (2 : ℝ) ≤ (↑(p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
    have h_psig_lt : (↑(p : ℕ) : ℝ) ^ (-s.re) < 1 := by
      have h := prime_cpow_norm_lt_one p s hσ
      rwa [prime_natCast_eq_ofReal p, norm_cpow_eq_rpow_re_of_pos hp_pos, neg_re] at h
    have h_psig_le_2α : (↑(p : ℕ) : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-α) :=
      calc (↑(p : ℕ) : ℝ) ^ (-s.re)
          ≤ (↑(p : ℕ) : ℝ) ^ (-α) := rpow_le_rpow_of_exponent_le hp_ge1 (by linarith)
        _ ≤ (2 : ℝ) ^ (-α) := by
            rw [rpow_neg hp_pos.le, rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
            exact inv_anti₀ (rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) α)
              (rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2) hp_ge2 hα_pos.le)
    calc ‖correctionTermP p s‖
        ≤ (↑(p : ℕ) : ℝ) ^ (-2 * s.re) / (1 - (↑(p : ℕ) : ℝ) ^ (-s.re)) :=
          correctionTermP_norm_le p s hσ
      _ ≤ (↑(p : ℕ) : ℝ) ^ (-2 * α) / (1 - (↑(p : ℕ) : ℝ) ^ (-s.re)) :=
          div_le_div_of_nonneg_right
            (rpow_le_rpow_of_exponent_le hp_ge1 (by linarith))
            (sub_pos.mpr h_psig_lt).le
      _ ≤ (↑(p : ℕ) : ℝ) ^ (-2 * α) / (1 - (2 : ℝ) ^ (-α)) :=
          div_le_div_of_nonneg_left
            (rpow_nonneg hp_pos.le _) h1sub_pos (sub_le_sub_left h_psig_le_2α 1)
      _ = (1 - (2 : ℝ) ^ (-α))⁻¹ * (↑(p : ℕ) : ℝ) ^ (-2 * α) := by
          rw [div_eq_mul_inv, mul_comm]

/-! ## Main analyticity result -/

/-- **The full correction term is analytic on {Re(s) > α} for any α > 1/2.**

Proof: Weierstrass M-test gives uniform convergence of the series ∑_p correctionTermP(p, s)
on {Re(s) > α}. Each partial sum is analytic (finite sum of analytic functions).
The uniform limit of analytic functions on an open set is differentiable, hence analytic. -/
theorem correctionTerm_analyticOnNhd (α : ℝ) (hα : 1 / 2 < α) :
    AnalyticOnNhd ℂ correctionTerm {s : ℂ | α < s.re} := by
  have hopen : IsOpen {s : ℂ | α < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  -- Each finite partial sum is analytic
  have h_partial_analytic : ∀ (F : Finset Nat.Primes),
      AnalyticOnNhd ℂ (fun s => ∑ p ∈ F, correctionTermP p s) {s | α < s.re} := by
    intro F
    exact F.analyticOnNhd_fun_sum fun p _ =>
      (correctionTermP_analyticOnNhd p).mono (fun s hs => by simp at hs ⊢; linarith)
  -- Uniform convergence → differentiable → analytic
  apply DifferentiableOn.analyticOnNhd _ hopen
  have h_unif := (correctionTerm_tendstoUniformlyOn α hα).tendstoLocallyUniformlyOn
  exact h_unif.differentiableOn
    (Eventually.of_forall fun F => (h_partial_analytic F).differentiableOn) hopen

/-! ## Decomposition of H_zeta_log -/

/-- The Euler product logarithm decomposes as primeZeta + correctionTerm
on {Re(s) > 1} (where both series converge absolutely).
TODO: close via tsum_add + extensionality. -/
theorem H_zeta_log_eq_add {s : ℂ} (hs : 1 < s.re) :
    LandauLogZetaObstruction.H_zeta_log s = primeZeta s + correctionTerm s := by
  -- Summability of prime zeta for Re(s) > 1
  have h_sum_pz : Summable (fun p : Nat.Primes => (↑(p : ℕ) : ℂ) ^ (-s)) :=
    Summable.of_norm_bounded
      (Nat.Primes.summable_rpow.mpr (by linarith : -s.re < -1))
      (fun p => by
        rw [prime_natCast_eq_ofReal p, norm_cpow_eq_rpow_re_of_pos
          (Nat.cast_pos.mpr p.prop.pos), neg_re])
  -- Summability of correction term for Re(s) > 1 > 1/2
  have h_sum_ct : Summable (fun p : Nat.Primes => correctionTermP p s) :=
    correctionTerm_summable (3/4) (by norm_num) s (by linarith)
  -- Decompose: -log(1-p^{-s}) = p^{-s} + correctionTermP p s
  unfold LandauLogZetaObstruction.H_zeta_log primeZeta correctionTerm
  rw [← h_sum_pz.tsum_add h_sum_ct]
  exact tsum_congr (fun p => by simp only [correctionTermP]; ring)

/-! ## Analyticity of primeZeta and H_zeta_log -/

/-- primeZeta is analytic on {Re(s) > α} for α > 1.
Weierstrass M-test: |p^{-s}| = p^{-σ} ≤ p^{-α}, and ∑_p p^{-α} < ∞ for α > 1. -/
theorem primeZeta_analyticOnNhd (α : ℝ) (hα : 1 < α) :
    AnalyticOnNhd ℂ primeZeta {s : ℂ | α < s.re} := by
  have hopen : IsOpen {s : ℂ | α < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  -- Each partial sum is differentiable
  have h_partial : ∀ (T : Finset Nat.Primes),
      DifferentiableOn ℂ (fun (z : ℂ) => ∑ p ∈ T, (↑(p : ℕ) : ℂ) ^ (-z))
        {s : ℂ | α < s.re} := by
    intro T
    apply DifferentiableOn.fun_sum
    intro p _
    intro z _hz
    exact (differentiableAt_prime_cpow_neg p z).differentiableWithinAt
  -- M-test bound: ‖p^{-s}‖ = p^{-σ} ≤ p^{-α} for σ > α
  have h_bound : ∀ (p : Nat.Primes) (z : ℂ), z ∈ ({s : ℂ | α < s.re} : Set ℂ) →
      ‖(↑(p : ℕ) : ℂ) ^ (-z)‖ ≤ (↑(p : ℕ) : ℝ) ^ (-α) := by
    intro p z hz
    simp only [mem_setOf_eq] at hz
    have hp_pos : (0 : ℝ) < (↑(p : ℕ) : ℝ) := Nat.cast_pos.mpr p.prop.pos
    rw [prime_natCast_eq_ofReal p, norm_cpow_eq_rpow_re_of_pos hp_pos, neg_re]
    exact rpow_le_rpow_of_exponent_le (by exact_mod_cast p.prop.one_lt.le) (by linarith)
  have h_sum : Summable (fun p : Nat.Primes => (↑(p : ℕ) : ℝ) ^ (-α)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  -- Uniform convergence of partial sums via Weierstrass M-test
  have h_unif : TendstoUniformlyOn
      (fun (N : Finset Nat.Primes) (z : ℂ) => ∑ p ∈ N, (↑(p : ℕ) : ℂ) ^ (-z))
      (fun z => ∑' p : Nat.Primes, (↑(p : ℕ) : ℂ) ^ (-z)) atTop
      {s : ℂ | α < s.re} :=
    tendstoUniformlyOn_tsum h_sum h_bound
  -- Uniform limit of holomorphic functions is holomorphic on open sets → analytic
  have h_diff : DifferentiableOn ℂ (fun z => ∑' p : Nat.Primes, (↑(p : ℕ) : ℂ) ^ (-z))
      {s : ℂ | α < s.re} :=
    h_unif.tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall h_partial) hopen
  exact h_diff.analyticOnNhd hopen

/-- **The Euler product logarithm H_zeta_log is analytic on {Re(s) > α} for α ≥ 1.**
Decomposes as primeZeta + correctionTerm; both are analytic. -/
theorem H_zeta_log_analyticOnNhd (α : ℝ) (hα : 1 < α) :
    AnalyticOnNhd ℂ LandauLogZetaObstruction.H_zeta_log {s : ℂ | α < s.re} := by
  -- Show H_zeta_log agrees with primeZeta + correctionTerm on the open set
  have hopen : IsOpen {s : ℂ | α < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h_eq : ∀ s ∈ ({s : ℂ | α < s.re} : Set ℂ),
      LandauLogZetaObstruction.H_zeta_log s = primeZeta s + correctionTerm s := by
    intro s hs
    simp only [mem_setOf_eq] at hs
    exact H_zeta_log_eq_add (by linarith)
  rw [analyticOnNhd_congr hopen h_eq]
  exact (primeZeta_analyticOnNhd α hα).add
    ((correctionTerm_analyticOnNhd (3/4) (by norm_num)).mono fun s hs => by
      simp at hs ⊢; linarith)

end Aristotle.CorrectionTermAnalyticity
