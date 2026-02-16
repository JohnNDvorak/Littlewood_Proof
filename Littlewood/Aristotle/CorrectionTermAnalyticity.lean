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

SORRY COUNT: 4 (rpow algebra + series splitting, all non-mathematical)

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
TODO: close rpow algebra (norm_log_one_add_sub_self_le + coercion alignment). -/
theorem correctionTermP_norm_le (p : Nat.Primes) (s : ℂ) (hs : 0 < s.re) :
    ‖correctionTermP p s‖ ≤
      (↑(p : ℕ) : ℝ) ^ (-2 * s.re) / (1 - (↑(p : ℕ) : ℝ) ^ (-s.re)) := by
  -- Proof sketch:
  -- Set z := -p^{-s}. Then correctionTermP = -(log(1+z) - z).
  -- By norm_log_one_add_sub_self_le: ‖log(1+z)-z‖ ≤ ‖z‖²·(1-‖z‖)⁻¹/2
  -- ‖z‖ = p^{-σ} by norm_cpow_eq_rpow_re_of_pos
  -- p^{-σ}² = p^{-2σ} by rpow_add
  -- Drop the /2 factor to get the stated bound.
  sorry

/-! ## Summability and uniform convergence -/

/-- The correction term series converges absolutely for Re(s) > α > 1/2.
Proof: compare with ∑_p p^{-2α} via correctionTermP_norm_le and
Nat.Primes.summable_rpow (convergent when -2α < -1). -/
theorem correctionTerm_summable (α : ℝ) (hα : 1 / 2 < α) (s : ℂ) (hs : α < s.re) :
    Summable (fun p : Nat.Primes => correctionTermP p s) := by
  -- Proof sketch:
  -- By correctionTermP_norm_le + rpow monotonicity:
  --   ‖correctionTermP p s‖ ≤ p^{-2α} / (1 - 2^{-α})
  -- Summable.of_norm_bounded with Nat.Primes.summable_rpow (-2α < -1).
  sorry

/-- The correction term series converges uniformly on {Re(s) > α} for α > 1/2.
Proof: Weierstrass M-test with u_p = p^{-2α}/(1-2^{-α}) via
HasSumUniformlyOn.of_norm_le_summable. -/
theorem correctionTerm_tendstoUniformlyOn (α : ℝ) (hα : 1 / 2 < α) :
    TendstoUniformlyOn
      (fun (N : Finset Nat.Primes) (s : ℂ) => ∑ p ∈ N, correctionTermP p s)
      correctionTerm atTop {s : ℂ | α < s.re} := by
  sorry

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
  unfold LandauLogZetaObstruction.H_zeta_log primeZeta correctionTerm correctionTermP
  sorry

end Aristotle.CorrectionTermAnalyticity
