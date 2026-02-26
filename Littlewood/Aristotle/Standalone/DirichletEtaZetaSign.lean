/-
The Dirichlet eta function and the sign of ζ on (0, 1).

## Main Results

* `riemannZeta_ofReal_ne_zero_of_mem_Ioo` : ζ(σ) ≠ 0 for real σ ∈ (0, 1).
* `s_sub_one_mul_zetaReal_pos` : (σ - 1) * Re(ζ(σ)) > 0 for real σ ∈ (0, 1).

## Proof Strategy

Define the Dirichlet eta function η(σ) = ∑ (-1)^n / (n+1)^σ for real σ > 0.
By the alternating series test, η converges and η(σ) > 0.
For σ > 1, the algebraic identity η(σ) = (1 - 2^{1-σ}) ζ(σ) holds by
regrouping the absolutely convergent Dirichlet series.
By the identity theorem for analytic functions, this extends to all σ > 0.
Since η(σ) > 0 and 1 - 2^{1-σ} < 0 for σ ∈ (0, 1), we get ζ(σ) < 0.

SORRY COUNT: 0
  PROVED: eta_eq_one_sub_two_rpow_mul_zetaReal — identity η = (1-2^{1-σ})ζ for σ ∈ (0,1)
     via complex identity theorem on paired-sum series
  PROVED: identity_gt_one — algebraic proof for σ > 1 via Dirichlet series regrouping
  PROVED: etaPairedC_eq_gt_one — paired sum = (1-2^{1-s})ζ(s) via even/odd splitting
  PROVED: etaPairedC_differentiableOn — Weierstrass M-test on local balls
  PROVED: riemannZeta_ofReal_im_eq_zero — via riemannZeta_conj from ZeroCountingFunction

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected
import Littlewood.ZetaZeros.ZeroCountingFunction

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Aristotle.Standalone.DirichletEtaZetaSign

open Real Filter Topology Finset

/-! ## Section 1: The real Dirichlet eta function

For real σ > 0, define η(σ) as the limit of the alternating series
  ∑_{n=0}^{N-1} (-1)^n / (n+1)^σ
This converges by the alternating series test and satisfies η(σ) > 0. -/

/-- The terms of the alternating series: f(n) = (n+1)^{-σ}. -/
private def etaTerm (σ : ℝ) (n : ℕ) : ℝ := (↑(n + 1) : ℝ) ^ (-σ)

/-- The partial sums of the alternating eta series. -/
private def etaPartialSum (σ : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, (-1 : ℝ) ^ n * etaTerm σ n

/-- For σ > 0, the eta terms are antitone (decreasing in n).
Proof: (n+1)^{-σ} = 1/(n+1)^σ, and (n+1)^σ is increasing in n. -/
private theorem etaTerm_antitone {σ : ℝ} (hσ : 0 < σ) : Antitone (etaTerm σ) := by
  intro m n hmn
  simp only [etaTerm]
  rw [rpow_neg (by positivity : (0 : ℝ) ≤ ↑(n + 1)),
      rpow_neg (by positivity : (0 : ℝ) ≤ ↑(m + 1))]
  exact inv_anti₀ (rpow_pos_of_pos (by positivity : (0 : ℝ) < ↑(m + 1)) σ)
    (rpow_le_rpow (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn) hσ.le)

/-- For σ > 0, the eta terms tend to 0. -/
private theorem etaTerm_tendsto_zero {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (etaTerm σ) atTop (𝓝 0) := by
  have key : ∀ n : ℕ, etaTerm σ n = ((↑(n + 1) : ℝ) ^ σ)⁻¹ := fun n => by
    unfold etaTerm
    rw [rpow_neg (by positivity : (0 : ℝ) ≤ ↑(n + 1))]
  exact Filter.Tendsto.congr (fun n => (key n).symm)
    (tendsto_inv_atTop_zero.comp
      ((tendsto_rpow_atTop hσ).comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))))

/-- The alternating eta series converges for σ > 0. -/
private theorem eta_series_converges {σ : ℝ} (hσ : 0 < σ) :
    ∃ l, Tendsto (etaPartialSum σ) atTop (𝓝 l) := by
  unfold etaPartialSum
  exact (etaTerm_antitone hσ).tendsto_alternating_series_of_tendsto_zero
    (etaTerm_tendsto_zero hσ)

/-- The Dirichlet eta function for real σ: the limit of the alternating series. -/
private def etaReal (σ : ℝ) : ℝ := limUnder atTop (etaPartialSum σ)

/-- The partial sums converge to etaReal for σ > 0. -/
private theorem etaPartialSum_tendsto {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (etaPartialSum σ) atTop (𝓝 (etaReal σ)) := by
  obtain ⟨l, hl⟩ := eta_series_converges hσ
  have : etaReal σ = l := hl.limUnder_eq
  rw [this]; exact hl

/-! ## Section 2: Positivity of the eta function -/

private theorem etaTerm_zero (σ : ℝ) : etaTerm σ 0 = 1 := by
  simp [etaTerm]

private theorem etaTerm_one (σ : ℝ) : etaTerm σ 1 = (2 : ℝ) ^ (-σ) := by
  simp [etaTerm]

/-- The eta function is positive for σ > 0:
η(σ) ≥ 1 - 2^{-σ} > 0 (from the even partial sum bound). -/
theorem etaReal_pos {σ : ℝ} (hσ : 0 < σ) : 0 < etaReal σ := by
  have h_tendsto := etaPartialSum_tendsto hσ
  unfold etaPartialSum at h_tendsto
  have h_bound := (etaTerm_antitone hσ).alternating_series_le_tendsto h_tendsto 1
  simp only [show 2 * 1 = 2 from by ring] at h_bound
  have h_S2 : ∑ n ∈ range 2, (-1 : ℝ) ^ n * etaTerm σ n = 1 - (2 : ℝ) ^ (-σ) := by
    rw [sum_range_succ, sum_range_succ, sum_range_zero]
    simp [etaTerm_zero, etaTerm_one, sub_eq_add_neg]
  rw [h_S2] at h_bound
  linarith [rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (by linarith : -σ < 0)]

/-! ## Section 3: Sign of 1 - 2^{1-σ} -/

/-- For σ < 1, 1 - 2^{1-σ} < 0, since 2^{1-σ} > 2^0 = 1. -/
theorem one_sub_two_rpow_neg {σ : ℝ} (hσ : σ < 1) : 1 - (2 : ℝ) ^ (1 - σ) < 0 := by
  rw [sub_neg]
  calc (1 : ℝ) = 2 ^ (0 : ℝ) := (rpow_zero 2).symm
    _ < 2 ^ (1 - σ) := rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (by linarith)

/-! ## Section 4: Real-valuedness of ζ on ℝ -/

/-- riemannZeta is real-valued on the real line (away from the pole at s = 1).
Proved via the conjugation symmetry `riemannZeta_conj` from ZeroCountingFunction. -/
theorem riemannZeta_ofReal_im_eq_zero {σ : ℝ} (hσ : σ ≠ 1) :
    (riemannZeta (↑σ : ℂ)).im = 0 := by
  open scoped ComplexConjugate in
  have h1 : (↑σ : ℂ) ≠ 1 := by
    intro h; apply hσ; exact_mod_cast congr_arg Complex.re h
  have h2 := ZetaZeros.riemannZeta_conj h1
  rw [Complex.conj_ofReal] at h2
  have h3 := congr_arg Complex.im h2
  simp only [Complex.conj_im] at h3
  linarith

/-- Extract the real part of riemannZeta at a real argument. -/
private def zetaReal (σ : ℝ) : ℝ := (riemannZeta (↑σ : ℂ)).re

/-! ## Section 5: The key identity η(σ) = (1 - 2^{1-σ}) * ζ(σ)

For σ > 1, proved by Dirichlet series: ζ - η = 2·∑(2k+2)^{-σ} = 2^{1-σ}·ζ.
For σ ∈ (0, 1), by analytic continuation (identity theorem on the connected
punctured half-plane {Re(s) > 0, s ≠ 1} in ℂ).

Note: The identity is false at σ = 1 due to Mathlib's convention riemannZeta 1 = 0. -/

/-! ### Section 5A: Summability for σ > 1 -/

/-- The Dirichlet series ∑ (n+1)^{-σ} is summable for σ > 1. -/
private theorem etaTerm_summable {σ : ℝ} (hσ : 1 < σ) : Summable (etaTerm σ) := by
  refine ((summable_nat_add_iff (f := fun n : ℕ => (↑n : ℝ) ^ (-σ)) 1).mpr
    (Real.summable_nat_rpow.mpr (by linarith : -σ < -1))).congr fun n => ?_
  simp [etaTerm, Nat.cast_succ]

/-- The alternating series ∑ (-1)^n (n+1)^{-σ} is summable for σ > 1. -/
private theorem signed_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n => (-1 : ℝ) ^ n * etaTerm σ n) :=
  (etaTerm_summable hσ).alternating

/-! ### Section 5B: Connection to riemannZeta for σ > 1 -/

/-- Each term of the complex Dirichlet series equals the real-coerced etaTerm.
Note: uses (↑n + 1) to match Mathlib's `zeta_eq_tsum_one_div_nat_add_one_cpow`. -/
private theorem zeta_term_eq_ofReal (σ : ℝ) (n : ℕ) :
    (1 : ℂ) / ((↑n : ℂ) + 1) ^ ((↑σ : ℂ)) = ↑(etaTerm σ n) := by
  have h_nn : (0 : ℝ) ≤ (↑(n + 1) : ℝ) := Nat.cast_nonneg' _
  simp only [etaTerm, one_div]
  rw [show (↑n : ℂ) + 1 = (↑(↑(n + 1) : ℝ) : ℂ) from by push_cast; ring]
  rw [← Complex.ofReal_cpow h_nn σ, rpow_neg h_nn, ← Complex.ofReal_inv]

/-- zetaReal σ equals the tsum of etaTerm for σ > 1. -/
private theorem zetaReal_eq_tsum {σ : ℝ} (hσ : 1 < σ) :
    zetaReal σ = ∑' n, etaTerm σ n := by
  unfold zetaReal
  have hre : 1 < (↑σ : ℂ).re := by simp [hσ]
  -- riemannZeta (↑σ) = ∑' n, ↑(etaTerm σ n)  (complex tsum)
  have h1 : riemannZeta (↑σ : ℂ) = ∑' n, (↑(etaTerm σ n) : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
    exact tsum_congr (zeta_term_eq_ofReal σ)
  rw [h1]
  -- ∑' n, ↑(etaTerm σ n) = ↑(∑' n, etaTerm σ n)  (ofReal preserves tsum)
  have h2 := (Complex.ofRealCLM.map_tsum (etaTerm_summable hσ)).symm
  simp only [Complex.ofRealCLM_apply] at h2
  rw [h2, Complex.ofReal_re]

/-- HasSum for the real Dirichlet series: ∑ (n+1)^{-σ} sums to zetaReal σ for σ > 1. -/
private theorem zetaReal_hasSum {σ : ℝ} (hσ : 1 < σ) :
    HasSum (etaTerm σ) (zetaReal σ) :=
  (zetaReal_eq_tsum hσ) ▸ (etaTerm_summable hσ).hasSum

/-- etaReal σ equals the tsum of the signed series for σ > 1. -/
private theorem etaReal_eq_tsum {σ : ℝ} (hσ : 1 < σ) :
    etaReal σ = ∑' n, (-1 : ℝ) ^ n * etaTerm σ n := by
  -- Both the tsum partial sums and etaPartialSum converge to their limits
  have h_tsum_tendsto := (signed_summable hσ).hasSum.tendsto_sum_nat
  have h_eta_tendsto := etaPartialSum_tendsto (show 0 < σ by linarith)
  -- etaPartialSum σ N = ∑ n in range N, (-1)^n * etaTerm σ n (by definition)
  exact tendsto_nhds_unique h_eta_tendsto h_tsum_tendsto

/-! ### Section 5C: Odd-indexed terms and the algebraic identity -/

/-- The odd-indexed etaTerm factors: (2k+2)^{-σ} = 2^{-σ} · (k+1)^{-σ}. -/
private theorem etaTerm_odd_eq (σ : ℝ) (k : ℕ) :
    etaTerm σ (2 * k + 1) = (2 : ℝ) ^ (-σ) * etaTerm σ k := by
  simp only [etaTerm]
  have h1 : (↑(2 * k + 1 + 1) : ℝ) = 2 * ↑(k + 1) := by push_cast; ring
  rw [h1, mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg' _)]

/-- The algebraic identity η(σ) = (1 - 2^{1-σ}) ζ(σ) for σ > 1.
Proof: ζ - η = ∑(1-(-1)^n)·a_n, only odd terms survive, giving 2^{1-σ}·ζ. -/
private theorem identity_gt_one {σ : ℝ} (hσ : 1 < σ) :
    etaReal σ = (1 - (2 : ℝ) ^ (1 - σ)) * zetaReal σ := by
  have h_sum := etaTerm_summable hσ
  have h_sgn := signed_summable hσ
  -- Suffices to show ζ - η = 2^{1-σ} · ζ
  suffices h : zetaReal σ - etaReal σ = (2 : ℝ) ^ (1 - σ) * zetaReal σ by linarith
  -- HasSum for the signed series
  have h_eta_hs : HasSum (fun n => (-1 : ℝ) ^ n * etaTerm σ n) (etaReal σ) := by
    rw [etaReal_eq_tsum hσ]; exact h_sgn.hasSum
  -- HasSum for the difference g(n) = (1 - (-1)^n) * a_n
  set g := fun n => (1 - (-1 : ℝ) ^ n) * etaTerm σ n with hg_def
  have h_diff : HasSum g (zetaReal σ - etaReal σ) := by
    convert (zetaReal_hasSum hσ).sub h_eta_hs using 1
    ext n; simp [g]; ring
  -- Even terms vanish: g(2k) = 0
  have hg_even : ∀ k, g (2 * k) = 0 := fun k => by simp [g, pow_mul]
  -- Odd terms: g(2k+1) = 2 * a_{2k+1}
  have hg_odd : ∀ k, g (2 * k + 1) = 2 * etaTerm σ (2 * k + 1) := fun k => by
    simp only [g]
    have : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
      rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
    rw [this]; ring
  -- Split: ∑ g = ∑ g(2k) + ∑ g(2k+1) = 0 + ∑ 2 * a_{2k+1}
  have hg_summable := h_diff.summable
  have h_even_sum : Summable (fun k => g (2 * k)) :=
    hg_summable.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  have h_odd_sum : Summable (fun k => g (2 * k + 1)) :=
    hg_summable.comp_injective ((add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ)))
  rw [← h_diff.tsum_eq, ← tsum_even_add_odd h_even_sum h_odd_sum]
  simp only [hg_even, tsum_zero, zero_add, hg_odd]
  -- ∑ 2 * a_{2k+1} = ∑ 2 * 2^{-σ} * a_k = 2^{1-σ} * ζ
  simp only [etaTerm_odd_eq]
  rw [show (fun k => 2 * ((2 : ℝ) ^ (-σ) * etaTerm σ k)) =
    fun k => (2 * (2 : ℝ) ^ (-σ)) * etaTerm σ k from by ext; ring]
  rw [tsum_mul_left, ← zetaReal_eq_tsum hσ]
  congr 1
  rw [show (2 : ℝ) * (2 : ℝ) ^ (-σ) = (2 : ℝ) ^ (1 + (-σ)) from by
    rw [rpow_add (by norm_num : (0 : ℝ) < 2)]; simp]
  ring_nf

/-! ### Section 5D: Complex paired sum and identity theorem

Group the alternating eta series in pairs to get an ABSOLUTELY convergent
series for Re(s) > 0. Use the complex identity theorem to extend the
algebraic identity from Re(s) > 1 to all of {Re(s) > 0} \ {1}. -/

section ComplexPairedSum

open Complex

/-- The paired term: (2k+1)^{-s} - (2k+2)^{-s}. -/
private def pairedTermC (k : ℕ) (s : ℂ) : ℂ :=
  (↑(2 * k + 1 : ℕ) : ℂ) ^ (-s) - (↑(2 * k + 2 : ℕ) : ℂ) ^ (-s)

/-- Bound on paired terms via the mean value theorem:
‖(2k+1)^{-s} - (2k+2)^{-s}‖ ≤ ‖s‖ * (2k+1)^{-Re(s)-1}. -/
private lemma norm_pairedTermC_le (k : ℕ) (s : ℂ) (hσ : 0 < s.re) :
    ‖pairedTermC k s‖ ≤ ‖s‖ * (↑(2 * k + 1) : ℝ) ^ (-s.re - 1) := by
  unfold pairedTermC
  set a : ℝ := ↑(2 * k + 1)
  set b : ℝ := ↑(2 * k + 2)
  have ha_pos : (0 : ℝ) < a := by positivity
  have hab : a ≤ b := by simp_all [a, b]
  have hab1 : b - a = 1 := by simp_all [a, b]; ring
  change ‖(↑a : ℂ) ^ (-s) - (↑b : ℂ) ^ (-s)‖ ≤ _
  rw [norm_sub_rev]
  have hs_ne : s ≠ 0 := fun h => by simp [h] at hσ
  have hns_ne : -s ≠ 0 := neg_ne_zero.mpr hs_ne
  have hf_deriv : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt (fun t : ℝ => (↑t : ℂ) ^ (-s))
        ((-s) * ↑t ^ (-s - 1)) (Set.Icc a b) t := fun t ht =>
    (hasDerivAt_ofReal_cpow_const (ne_of_gt (lt_of_lt_of_le ha_pos ht.1)) hns_ne).hasDerivWithinAt
  have hf_bound : ∀ t ∈ Set.Ico a b,
      ‖(-s) * ↑t ^ (-s - 1)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro t ht
    rw [norm_mul, norm_neg]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
    rw [norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le ha_pos ht.1)]
    simp only [sub_re, neg_re, one_re]
    exact rpow_le_rpow_of_nonpos ha_pos ht.1 (by linarith)
  have := norm_image_sub_le_of_norm_deriv_le_segment' hf_deriv hf_bound
    b (Set.right_mem_Icc.mpr hab)
  rwa [hab1, mul_one] at this

/-- The paired terms are summable for Re(s) > 0. -/
private lemma pairedTermC_summable (s : ℂ) (hσ : 0 < s.re) :
    Summable (fun k => pairedTermC k s) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => norm_pairedTermC_le k s hσ)
  apply Summable.mul_left
  have : Summable (fun k : ℕ => (↑(k + 1) : ℝ) ^ (-(s.re + 1))) := by
    apply (summable_nat_add_iff (f := fun n : ℕ => (↑n : ℝ) ^ (-(s.re + 1))) 1).mpr
    exact Real.summable_nat_rpow.mpr (by linarith : -(s.re + 1) < -1)
  apply this.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
  rw [show -s.re - 1 = -(s.re + 1) from by ring]
  exact rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by linarith)

/-- The complex paired eta sum. -/
private def etaPairedC (s : ℂ) : ℂ := ∑' k, pairedTermC k s

/-- etaPairedC is holomorphic on {Re(s) > 0}.
Proof: Weierstrass M-test (differentiableOn_tsum_of_summable_norm) on local balls. -/
private lemma etaPairedC_differentiableOn :
    DifferentiableOn ℂ etaPairedC {s : ℂ | 0 < s.re} := by
  intro s₀ (hs₀ : 0 < s₀.re)
  apply DifferentiableAt.differentiableWithinAt
  -- Work on B(s₀, r) with r = s₀.re / 2
  set r := s₀.re / 2 with hr_eq
  have hr_pos : 0 < r := half_pos hs₀
  -- Re(s) ≥ r for s in the ball
  have h_ball_re : ∀ s ∈ Metric.ball s₀ r, r ≤ s.re := by
    intro s hs
    have hd : dist s s₀ < r := Metric.mem_ball.mp hs
    have h1 : s₀.re - s.re ≤ dist s s₀ := by
      calc s₀.re - s.re = (s₀ - s).re := (sub_re s₀ s).symm
        _ ≤ ‖s₀ - s‖ := re_le_norm _
        _ = ‖s - s₀‖ := norm_sub_rev s₀ s
        _ = dist s s₀ := (dist_eq_norm s s₀).symm
    have : r = s₀.re / 2 := rfl
    linarith
  -- ‖s‖ ≤ ‖s₀‖ + r for s in the ball
  have h_norm_le : ∀ s ∈ Metric.ball s₀ r, ‖s‖ ≤ ‖s₀‖ + r := by
    intro s hs
    have hd : ‖s - s₀‖ < r := by
      have := Metric.mem_ball.mp hs; rwa [dist_eq_norm] at this
    have h1 : ‖s‖ ≤ ‖s₀‖ + ‖s - s₀‖ := norm_le_insert' s s₀
    linarith
  -- Each pairedTermC k is holomorphic on B(s₀, r)
  have h_diff : ∀ k : ℕ, DifferentiableOn ℂ (pairedTermC k) (Metric.ball s₀ r) := by
    intro k s _; apply DifferentiableAt.differentiableWithinAt
    show DifferentiableAt ℂ (fun s => (↑(2 * k + 1 : ℕ) : ℂ) ^ (-s) -
      (↑(2 * k + 2 : ℕ) : ℂ) ^ (-s)) s
    exact ((differentiableAt_id.neg).const_cpow
        (Or.inl (Nat.cast_ne_zero.mpr (show (2 * k + 1 : ℕ) ≠ 0 by omega)))).sub
      ((differentiableAt_id.neg).const_cpow
        (Or.inl (Nat.cast_ne_zero.mpr (show (2 * k + 2 : ℕ) ≠ 0 by omega))))
  -- Uniform bound: ‖pairedTermC k s‖ ≤ (‖s₀‖ + r) * (2k+1)^{-r-1}
  set u := fun k : ℕ => (‖s₀‖ + r) * (↑(2 * k + 1) : ℝ) ^ (-r - 1)
  have h_bound : ∀ (k : ℕ) (s : ℂ), s ∈ Metric.ball s₀ r → ‖pairedTermC k s‖ ≤ u k := by
    intro k s hs
    calc ‖pairedTermC k s‖
        ≤ ‖s‖ * (↑(2 * k + 1) : ℝ) ^ (-s.re - 1) :=
          norm_pairedTermC_le k s (by linarith [h_ball_re s hs])
      _ ≤ (‖s₀‖ + r) * (↑(2 * k + 1) : ℝ) ^ (-r - 1) :=
          mul_le_mul (h_norm_le s hs)
            (rpow_le_rpow_of_exponent_le
              (by exact_mod_cast (show 1 ≤ 2 * k + 1 by omega))
              (by linarith [h_ball_re s hs]))
            (by positivity) (by linarith [norm_nonneg s₀])
  -- u is summable (since r + 1 > 1)
  have h_sum : Summable u := by
    apply Summable.mul_left
    exact ((summable_nat_add_iff (f := fun n : ℕ => (↑n : ℝ) ^ (-(r + 1))) 1).mpr
        (Real.summable_nat_rpow.mpr (by linarith))).of_nonneg_of_le
      (fun k => by positivity)
      (fun k => by rw [show -r - 1 = -(r + 1) from by ring]
                   exact rpow_le_rpow_of_nonpos (by positivity)
                     (by push_cast; linarith) (by linarith))
  -- Apply Weierstrass M-test
  exact DifferentiableOn.differentiableAt
    (differentiableOn_tsum_of_summable_norm h_sum h_diff Metric.isOpen_ball h_bound)
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos))

/-- For Re(s) > 1, etaPairedC(s) = (1 - 2^{1-s}) * ζ(s). -/
private lemma etaPairedC_eq_gt_one {s : ℂ} (hs : 1 < s.re) :
    etaPairedC s = (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s := by
  -- The zeta series term: g(n) = (n+1)^{-s}
  set g : ℕ → ℂ := fun n => ((n + 1 : ℕ) : ℂ) ^ (-s) with hg_def
  -- g(n) = 1/(n+1)^s in both nat-cast forms
  have hg_cast : ∀ n, g n = 1 / ((↑n : ℂ) + 1) ^ s := fun n => by
    simp [g, one_div, cpow_neg, Nat.cast_succ]
  -- g is summable
  have hg_sum : Summable g := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (↑n : ℂ) ^ s) 1).mpr
      (summable_one_div_nat_cpow.mpr hs)
    exact h.congr fun n => by simp [g, one_div, cpow_neg]
  -- ∑ g = ζ(s)
  have hg_zeta : ∑' n, g n = riemannZeta s := by
    rw [tsum_congr hg_cast]
    exact (zeta_eq_tsum_one_div_nat_add_one_cpow hs).symm
  -- pairedTermC k s = g(2k) - g(2k+1)
  have h_pair : ∀ k, pairedTermC k s = g (2 * k) - g (2 * k + 1) := fun k => by
    simp only [pairedTermC, g]
  -- Even/odd summability
  have hge : Summable (fun k => g (2 * k)) :=
    hg_sum.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  have hgo : Summable (fun k => g (2 * k + 1)) :=
    hg_sum.comp_injective
      ((add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ)))
  -- g(2k+1) = 2^{-s} * g(k)  (via mul_cpow_ofReal_nonneg)
  have h_odd : ∀ k, g (2 * k + 1) = (2 : ℂ) ^ (-s) * g k := fun k => by
    simp only [g]
    show ((2 * k + 1 + 1 : ℕ) : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * ((k + 1 : ℕ) : ℂ) ^ (-s)
    have h1 : ((2 * k + 1 + 1 : ℕ) : ℂ) =
        (↑(2 : ℝ) : ℂ) * (↑(↑(k + 1) : ℝ) : ℂ) := by push_cast; ring
    rw [h1, mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
    norm_cast
  -- ∑' k, g(2k+1) = 2^{-s} * ζ(s)
  have hgo_eq : ∑' k, g (2 * k + 1) = (2 : ℂ) ^ (-s) * riemannZeta s := by
    rw [show (fun k => g (2 * k + 1)) = fun k => (2 : ℂ) ^ (-s) * g k from funext h_odd,
        tsum_mul_left, hg_zeta]
  -- even + odd = ζ(s)
  have h_split : (∑' k, g (2 * k)) + (∑' k, g (2 * k + 1)) = riemannZeta s :=
    (tsum_even_add_odd hge hgo).trans hg_zeta
  -- etaPairedC = even - odd
  have h_eta : etaPairedC s = (∑' k, g (2 * k)) - (∑' k, g (2 * k + 1)) := by
    show ∑' k, pairedTermC k s = _
    rw [show (fun k => pairedTermC k s) = fun k => g (2 * k) - g (2 * k + 1) from
      funext h_pair, (hge.hasSum.sub hgo.hasSum).tsum_eq]
  -- Algebra: A - B where A + B = ζ and B = 2^{-s}·ζ
  rw [h_eta, hgo_eq]
  have h_even : ∑' k, g (2 * k) = riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s := by
    have h := h_split; rw [hgo_eq] at h
    linear_combination h
  rw [h_even]
  -- 2^{1-s} = 2 * 2^{-s}
  have h_pow : (2 : ℂ) ^ ((1 : ℂ) - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = (1 : ℂ) + (-s) from sub_eq_add_neg 1 s]
    rw [cpow_add (1 : ℂ) (-s) (by norm_num : (2 : ℂ) ≠ 0), cpow_one]
  rw [h_pow]; ring

/-- {Re > 0} \ {1} is preconnected (removing a point from a convex open
set in a space of dim ≥ 2 preserves connectedness).
Proof: decompose as union of 4 convex (hence preconnected) sets with overlaps. -/
private lemma halfPlane_sdiff_one_isPreconnected :
    IsPreconnected ({s : ℂ | 0 < s.re} \ {(1 : ℂ)}) := by
  -- Four convex pieces: upper, lower, right of 1, left of 1
  have hUH : IsPreconnected {s : ℂ | 0 < s.re ∧ 0 < s.im} :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hLH : IsPreconnected {s : ℂ | 0 < s.re ∧ s.im < 0} :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hR : IsPreconnected {s : ℂ | 1 < s.re} :=
    (convex_halfSpace_re_gt 1).isPreconnected
  have hL : IsPreconnected {s : ℂ | 0 < s.re ∧ s.re < 1} :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).isPreconnected
  -- A = upper ∪ right (overlap at (2,1))
  have hA : IsPreconnected ({s : ℂ | 0 < s.re ∧ 0 < s.im} ∪ {s | 1 < s.re}) :=
    IsPreconnected.union' ⟨⟨(2 : ℝ), 1⟩, ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩⟩ hUH hR
  -- B = lower ∪ left (overlap at (1/2, -1))
  have hB : IsPreconnected ({s : ℂ | 0 < s.re ∧ s.im < 0} ∪ {s | 0 < s.re ∧ s.re < 1}) :=
    IsPreconnected.union' ⟨⟨(1/2 : ℝ), -1⟩,
      ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩⟩ hLH hL
  -- A ∪ B (overlap at (1/2, 1))
  have hAB : IsPreconnected (({s : ℂ | 0 < s.re ∧ 0 < s.im} ∪ {s | 1 < s.re}) ∪
      ({s | 0 < s.re ∧ s.im < 0} ∪ {s | 0 < s.re ∧ s.re < 1})) :=
    IsPreconnected.union' ⟨⟨(1/2 : ℝ), 1⟩,
      Or.inl ⟨by norm_num, by norm_num⟩, Or.inr ⟨by norm_num, by norm_num⟩⟩ hA hB
  -- Show A ∪ B = {Re > 0} \ {1}
  suffices h : {s : ℂ | 0 < s.re} \ {(1 : ℂ)} =
      ({s | 0 < s.re ∧ 0 < s.im} ∪ {s | 1 < s.re}) ∪
      ({s | 0 < s.re ∧ s.im < 0} ∪ {s | 0 < s.re ∧ s.re < 1}) by rw [h]; exact hAB
  ext s; simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_union]
  constructor
  · rintro ⟨hre, hne⟩
    rcases lt_trichotomy s.im 0 with him | him | him
    · exact Or.inr (Or.inl ⟨hre, him⟩)
    · rcases lt_or_gt_of_ne (fun h : s.re = 1 => hne (ext h him)) with hlt | hgt
      · exact Or.inr (Or.inr ⟨hre, hlt⟩)
      · exact Or.inl (Or.inr hgt)
    · exact Or.inl (Or.inl ⟨hre, him⟩)
  · rintro ((⟨hre, him⟩ | hre) | ⟨hre, him⟩ | ⟨hre, hlt⟩) <;>
    exact ⟨by linarith, fun h => by subst h; simp at *⟩

/-- (1 - 2^{1-s}) * ζ(s) is differentiable on {Re > 0} \ {1}. -/
private lemma rhs_differentiableOn :
    DifferentiableOn ℂ (fun s => (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s)
      ({s : ℂ | 0 < s.re} \ {(1 : ℂ)}) := by
  intro s ⟨_, hs_ne⟩
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.mul
  · exact (differentiableAt_const _).sub
      (((differentiableAt_const _).sub differentiableAt_id).const_cpow
        (Or.inl (by norm_num : (2 : ℂ) ≠ 0)))
  · exact differentiableAt_riemannZeta (by simpa using hs_ne)

/-- Identity theorem: etaPairedC = (1 - 2^{1-s})ζ on all of {Re > 0} \ {1}. -/
private lemma etaPairedC_eq_everywhere {s : ℂ} (hσ : 0 < s.re) (hs1 : s ≠ 1) :
    etaPairedC s = (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s := by
  set U := {s : ℂ | 0 < s.re} \ {(1 : ℂ)} with hU_def
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).sdiff isClosed_singleton
  have hf_anal : AnalyticOnNhd ℂ etaPairedC U :=
    (etaPairedC_differentiableOn.mono Set.diff_subset).analyticOnNhd hU_open
  have hg_anal : AnalyticOnNhd ℂ
      (fun s => (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s) U :=
    rhs_differentiableOn.analyticOnNhd hU_open
  have hs0_mem : (2 : ℂ) ∈ U := by
    refine ⟨by norm_num, ?_⟩
    intro h; have := congr_arg re h; simp at this
  have h_agree : etaPairedC =ᶠ[𝓝 (2 : ℂ)]
      (fun s => (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * riemannZeta s) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨{s : ℂ | 1 < s.re},
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num),
      fun s hs => etaPairedC_eq_gt_one hs⟩
  exact hf_anal.eqOn_of_preconnected_of_eventuallyEq hg_anal
    halfPlane_sdiff_one_isPreconnected hs0_mem h_agree ⟨hσ, hs1⟩

/-- For real σ > 0, etaPairedC(↑σ) = ↑(etaReal σ). -/
private lemma etaPairedC_ofReal_eq_etaReal {σ : ℝ} (hσ : 0 < σ) :
    etaPairedC ↑σ = ↑(etaReal σ) := by
  -- Each paired term at ↑σ is the ofReal of a real paired term
  set rterm := fun k : ℕ => (↑(2 * k + 1) : ℝ) ^ (-σ) - (↑(2 * k + 2) : ℝ) ^ (-σ)
  have h_term : ∀ k : ℕ, pairedTermC k (↑σ) = ↑(rterm k) := by
    intro k
    simp only [pairedTermC, rterm, Complex.ofReal_sub]
    congr 1 <;> {
      rw [show -(↑σ : ℂ) = (↑(-σ) : ℂ) from (Complex.ofReal_neg σ).symm,
          Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ _)]
      push_cast; rfl }
  -- The real paired terms are summable
  have h_real_summable : Summable rterm := by
    have hcs := (pairedTermC_summable (↑σ) (by simp [hσ])).norm
    apply hcs.of_nonneg_of_le
    · intro k; exact sub_nonneg.mpr
        (rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by linarith))
    · intro k
      rw [h_term k, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact sub_nonneg.mpr
        (rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by linarith))
  -- etaPairedC ↑σ = ∑' k, ↑(rterm k) = ↑(∑' k, rterm k)
  have h_tsum : etaPairedC ↑σ = ↑(∑' k, rterm k) := by
    show ∑' k, pairedTermC k (↑σ) = _
    rw [show (fun k => pairedTermC k (↑σ)) = (fun k => (↑(rterm k) : ℂ)) from funext h_term]
    exact (Complex.ofRealCLM.map_tsum h_real_summable).symm
  rw [h_tsum]; congr 1
  -- ∑' k, rterm k = etaReal σ (paired partial sums = even partial sums of etaPartialSum)
  have h_eq_partial : ∀ M : ℕ,
      ∑ k ∈ Finset.range M, rterm k = etaPartialSum σ (2 * M) := by
    intro M; induction M with
    | zero => simp [etaPartialSum]
    | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      have key : etaPartialSum σ (2 * (M + 1)) =
          etaPartialSum σ (2 * M) + etaTerm σ (2 * M) - etaTerm σ (2 * M + 1) := by
        simp only [etaPartialSum]
        rw [show 2 * (M + 1) = (2 * M + 1) + 1 from by omega, Finset.sum_range_succ,
            show 2 * M + 1 = (2 * M) + 1 from by omega, Finset.sum_range_succ]
        have h_even : (-1 : ℝ) ^ (2 * M) = 1 := by rw [pow_mul]; simp
        have h_odd : (-1 : ℝ) ^ (2 * M + 1) = -1 := by rw [pow_succ, pow_mul]; simp
        rw [h_even, h_odd, one_mul, neg_one_mul]; ring
      rw [key]
      suffices h : rterm M = etaTerm σ (2 * M) - etaTerm σ (2 * M + 1) by linarith
      simp only [rterm, etaTerm]
  apply tendsto_nhds_unique (h_real_summable.hasSum.tendsto_sum_nat)
  exact ((etaPartialSum_tendsto hσ).comp (tendsto_atTop_atTop_of_monotone
    (fun a b h => by omega) (fun M => ⟨M, by omega⟩))).congr
    (fun M => (h_eq_partial M).symm)

end ComplexPairedSum

/-! ### Section 5E: Main identity -/

/-- The identity η(σ) = (1 - 2^{1-σ}) * Re(ζ(σ)) for real σ > 0, σ ≠ 1.

For σ > 1: direct Dirichlet series regrouping (identity_gt_one).
For σ ∈ (0, 1): by the identity theorem applied to the connected punctured
half-plane {s ∈ ℂ | Re(s) > 0 ∧ s ≠ 1}. -/
theorem eta_eq_one_sub_two_rpow_mul_zetaReal {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) :
    etaReal σ = (1 - (2 : ℝ) ^ (1 - σ)) * zetaReal σ := by
  rcases lt_or_gt_of_ne hσ1 with h | h
  · -- σ ∈ (0, 1): use complex identity theorem
    have hs1_c : (↑σ : ℂ) ≠ 1 := by
      intro heq; apply hσ1; exact_mod_cast congr_arg Complex.re heq
    have h_complex := etaPairedC_eq_everywhere (by simp [hσ]) hs1_c
    have h_real := etaPairedC_ofReal_eq_etaReal hσ
    -- etaReal σ = Re(etaPairedC ↑σ) = Re((1 - 2^{1-↑σ}) * ζ(↑σ))
    have h4 : etaReal σ = ((1 - (2 : ℂ) ^ ((1 : ℂ) - ↑σ)) * riemannZeta ↑σ).re := by
      conv_lhs => rw [← Complex.ofReal_re (etaReal σ), ← h_real, h_complex]
    rw [h4, zetaReal, Complex.mul_re]
    -- The factor (1 - 2^{1-↑σ}) is real-valued
    have h_factor_im : ((1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - ↑σ)).im = 0 := by
      simp only [Complex.sub_im, Complex.one_im]
      suffices ((2 : ℂ) ^ ((1 : ℂ) - ↑σ)).im = 0 by linarith
      rw [show ((1 : ℂ) - (↑σ : ℂ)) = (↑((1 : ℝ) - σ) : ℂ) from by push_cast; ring,
          show (2 : ℂ) = (↑(2 : ℝ) : ℂ) from by norm_cast,
          ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2), Complex.ofReal_im]
    have h_zeta_im := riemannZeta_ofReal_im_eq_zero hσ1
    rw [h_zeta_im, h_factor_im, mul_zero, sub_zero]
    -- Re part of (1 - 2^{1-↑σ}) = 1 - 2^{1-σ}
    congr 1
    simp only [Complex.sub_re, Complex.one_re]
    rw [show ((1 : ℂ) - (↑σ : ℂ)) = (↑((1 : ℝ) - σ) : ℂ) from by push_cast; ring,
        show (2 : ℂ) = (↑(2 : ℝ) : ℂ) from by norm_cast,
        ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2), Complex.ofReal_re]
  · exact identity_gt_one h

/-! ## Section 6: Main results -/

/-- **Re(ζ(σ)) < 0 for real σ ∈ (0, 1).**
Since η(σ) > 0 and (1 - 2^{1-σ}) < 0, the identity η = (1-2^{1-σ})·ζ gives ζ < 0. -/
theorem zetaReal_neg {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    zetaReal σ < 0 := by
  have h_eta := etaReal_pos hσ0
  have h_factor := one_sub_two_rpow_neg hσ1
  have h_id := eta_eq_one_sub_two_rpow_mul_zetaReal hσ0 (ne_of_lt hσ1)
  -- η > 0 and η = factor * ζ where factor < 0, so ζ < 0
  by_contra h
  push_neg at h
  have : (1 - (2 : ℝ) ^ (1 - σ)) * zetaReal σ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg h_factor.le h
  linarith

/-- **riemannZeta(↑σ) ≠ 0 for σ ∈ (0, 1).** -/
theorem riemannZeta_ofReal_ne_zero_of_mem_Ioo {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    riemannZeta (↑σ : ℂ) ≠ 0 := by
  intro h
  have := zetaReal_neg hσ0 hσ1
  simp only [zetaReal, h, Complex.zero_re] at this
  exact lt_irrefl 0 this

/-- **(σ - 1) * Re(ζ(σ)) > 0 for real σ ∈ (0, 1).**
Product of two negatives. -/
theorem s_sub_one_mul_zetaReal_pos {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    0 < (σ - 1) * zetaReal σ :=
  mul_pos_of_neg_of_neg (by linarith) (zetaReal_neg hσ0 hσ1)

end Aristotle.Standalone.DirichletEtaZetaSign
