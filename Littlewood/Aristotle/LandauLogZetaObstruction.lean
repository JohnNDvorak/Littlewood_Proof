/-
No analytic branch of log ζ exists past Re(s) = 1: obstruction from the pole.

This file proves that the Riemann zeta function has no analytic logarithm
extending to any half-plane {Re(s) > α} with α < 1, and constructs the
Euler product logarithm H_zeta_log on {Re(s) > 1}.

## Main Results

* `zeta_has_no_analytic_log_at_one` : For α < 1, ¬∃ H analytic on {Re > α}
    with exp(H(s)) = ζ(s) on {Re > 1}.
* `H_zeta_log` : The Euler product logarithm ∑' p, -log(1 - p^{-s}).
* `H_zeta_log_exp_eq` : exp(H_zeta_log(s)) = ζ(s) for Re(s) > 1.

SORRY COUNT: 0

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
Co-authored-by: Claude (Anthropic)
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Topology.Order.OrderClosed
import Littlewood.Basic.LogarithmicIntegral

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Aristotle.LandauLogZetaObstruction

open Complex Filter Topology Set

/-! ## Helper: ofReal maps 𝓝[Ioi] 1 into 𝓝[≠] 1

This is the key filter map used to pull the residue back to the real line. -/

/-- The coercion ℝ → ℂ maps nhdsWithin (1 : ℝ) (Ioi 1) into nhdsWithin 1 {1}ᶜ. -/
private lemma ofReal_tendsto_nhdsWithin :
    Tendsto (fun t : ℝ => (↑t : ℂ)) (nhdsWithin (1 : ℝ) (Ioi 1))
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall fun σ hσ => by
      simp only [mem_compl_iff, mem_singleton_iff]
      exact fun h => ne_of_gt hσ (ofReal_injective h)⟩

/-- The residue (s-1)ζ(s) → 1 restricted to real s > 1. -/
private lemma residue_real :
    Tendsto (fun t : ℝ => ((↑t : ℂ) - 1) * riemannZeta (↑t))
      (nhdsWithin (1 : ℝ) (Ioi 1)) (𝓝 1) :=
  riemannZeta_residue_one.comp ofReal_tendsto_nhdsWithin

/-! ## No analytic log ζ past Re = 1 -/

/-- For any α < 1, there is no analytic function H on {s | α < Re(s)}
satisfying exp(H(s)) = ζ(s) for Re(s) > 1. The pole at s = 1 obstructs.

**Proof**: H analytic at s = 1 ⟹ exp ∘ H continuous at 1 ⟹ exp(H(t)) bounded
near t = 1. But exp(H(t)) = ζ(t) for t > 1, and the residue (s-1)ζ(s) → 1
forces ‖ζ(t)‖ ~ 1/(t-1) → ∞ as t → 1⁺. Contradiction. -/
theorem zeta_has_no_analytic_log_at_one (α : ℝ) (hα : α < 1) :
    ¬∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s : ℂ | α < s.re} ∧
      ∀ s : ℂ, 1 < s.re → exp (H s) = riemannZeta s := by
  rintro ⟨H, hH_an, hH_eq⟩
  -- H is analytic (hence continuous) at s = 1
  have h1_mem : (1 : ℂ) ∈ {s : ℂ | α < s.re} := by
    simp only [mem_setOf_eq, one_re]; linarith
  -- exp ∘ H ∘ ofReal is continuous at t = 1
  have h_cont : ContinuousAt (fun t : ℝ => exp (H (↑t))) (1 : ℝ) := by
    have h1 : ContinuousAt (fun s : ℂ => exp (H s)) ((↑(1:ℝ) : ℂ)) :=
      continuous_exp.continuousAt.comp (by rw [ofReal_one]; exact (hH_an 1 h1_mem).continuousAt)
    exact h1.comp continuous_ofReal.continuousAt
  -- B = ‖exp(H(1))‖ + 1, an upper bound for ‖ζ(t)‖ near t = 1
  set B : ℝ := ‖exp (H (1 : ℂ))‖ + 1 with hB_def
  have hB_pos : (0 : ℝ) < B := by rw [hB_def]; positivity
  -- ‖exp(H(↑t))‖ → ‖exp(H(1))‖, so eventually < ‖exp(H(1))‖ + 1 = B
  have h_bdd : ∀ᶠ (t : ℝ) in 𝓝 (1 : ℝ), ‖exp (H (↑t))‖ < B := by
    have h_tends : Tendsto (fun t : ℝ => ‖exp (H (↑t))‖) (𝓝 1) (𝓝 ‖exp (H (1 : ℂ))‖) :=
      continuous_norm.continuousAt.tendsto.comp h_cont
    exact h_tends.eventually (Iio_mem_nhds (by rw [hB_def]; linarith))
  -- Restrict to nhdsWithin (1 : ℝ) (Ioi 1)
  have h_bdd_Ioi : ∀ᶠ (t : ℝ) in nhdsWithin (1 : ℝ) (Ioi 1), ‖exp (H (↑t))‖ < B :=
    nhdsWithin_le_nhds h_bdd
  -- On Ioi 1: exp(H(↑t)) = ζ(↑t)
  have h_eq_ev : ∀ᶠ (t : ℝ) in nhdsWithin (1 : ℝ) (Ioi 1), exp (H (↑t)) = riemannZeta (↑t) :=
    eventually_nhdsWithin_of_forall fun t (ht : 1 < t) =>
      hH_eq (↑t) (by rw [ofReal_re]; linarith)
  -- So eventually ‖ζ(↑t)‖ < B
  have h_zeta_bdd : ∀ᶠ (t : ℝ) in nhdsWithin (1 : ℝ) (Ioi 1), ‖riemannZeta (↑t)‖ < B := by
    filter_upwards [h_bdd_Ioi, h_eq_ev] with t h1 h2
    rwa [← h2]
  -- From the residue: ‖(t-1)·ζ(t)‖ → 1, hence ≥ 1/2 eventually
  have h_res_norm : Tendsto (fun t : ℝ => ‖((↑t : ℂ) - 1) * riemannZeta (↑t)‖)
      (nhdsWithin (1 : ℝ) (Ioi 1)) (𝓝 1) := by
    have := continuous_norm.continuousAt.tendsto.comp residue_real
    simp only [norm_one] at this; exact this
  have h_half : ∀ᶠ (t : ℝ) in nhdsWithin (1 : ℝ) (Ioi 1),
      1 / 2 ≤ ‖((↑t : ℂ) - 1) * riemannZeta (↑t)‖ := by
    filter_upwards [h_res_norm.eventually (Ici_mem_nhds (by norm_num : (1:ℝ)/2 < 1))]
      with t ht; exact ht
  -- Also t - 1 > 0 eventually and t - 1 < 1/(2B) eventually
  have h_small : ∀ᶠ (t : ℝ) in nhdsWithin (1 : ℝ) (Ioi 1), t - 1 < 1 / (2 * B) := by
    have h_lt : (1 : ℝ) < 1 + 1 / (2 * B) := by linarith [div_pos one_pos (mul_pos two_pos hB_pos)]
    filter_upwards [Ioo_mem_nhdsGT h_lt] with t ⟨_, ht2⟩; linarith
  have h_gt1 : ∀ᶠ (t : ℝ) in nhdsWithin (1 : ℝ) (Ioi 1), 1 < t :=
    eventually_nhdsWithin_of_forall fun _ h => h
  -- Combine and derive contradiction
  have h_all := h_half.and (h_small.and (h_gt1.and h_zeta_bdd))
  obtain ⟨t, h_norm, h_close, ht1, h_bound⟩ := h_all.exists
  -- ‖(t-1)·ζ(t)‖ = |t-1| · ‖ζ(t)‖
  rw [norm_mul, show (↑t : ℂ) - 1 = ↑(t - 1) from by push_cast; ring,
    norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < t - 1)] at h_norm
  -- 1/2 ≤ (t-1) · ‖ζ(t)‖ < (1/(2B)) · B = 1/2
  have h_zeta_norm_pos : 0 < ‖riemannZeta (↑t)‖ := by
    rw [norm_pos_iff]; exact riemannZeta_ne_zero_of_one_le_re (by rw [ofReal_re]; linarith)
  have h_prod : (t - 1) * ‖riemannZeta (↑t)‖ < 1 / (2 * B) * B := by
    calc (t - 1) * ‖riemannZeta (↑t)‖
        < 1 / (2 * B) * ‖riemannZeta (↑t)‖ :=
          mul_lt_mul_of_pos_right h_close h_zeta_norm_pos
      _ ≤ 1 / (2 * B) * B :=
          mul_le_mul_of_nonneg_left h_bound.le (div_nonneg one_pos.le (mul_pos two_pos hB_pos).le)
  have h_cancel : 1 / (2 * B) * B = 1 / 2 := by field_simp
  linarith

/-! ## Euler product logarithm -/

/-- The Euler product logarithm: ∑' p prime, -log(1 - p^{-s}). -/
noncomputable def H_zeta_log (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1 - (↑(p : ℕ) : ℂ) ^ (-s))

/-- exp(H_zeta_log(s)) = ζ(s) for Re(s) > 1, from Mathlib's Euler product. -/
theorem H_zeta_log_exp_eq {s : ℂ} (hs : 1 < s.re) :
    exp (H_zeta_log s) = riemannZeta s :=
  riemannZeta_eulerProduct_exp_log hs

end Aristotle.LandauLogZetaObstruction
