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

SORRY COUNT: 1
  1. eta_eq_one_sub_two_rpow_mul_zetaReal — identity η = (1-2^{1-σ})ζ for σ ∈ (0, 1)
     (identity theorem extension from σ > 1 where the identity is fully proved)
  PROVED: identity_gt_one — algebraic proof for σ > 1 via Dirichlet series regrouping
  PROVED: riemannZeta_ofReal_im_eq_zero — via riemannZeta_conj from ZeroCountingFunction

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.PSeries
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

/-! ### Section 5D: Main identity -/

/-- The identity η(σ) = (1 - 2^{1-σ}) * Re(ζ(σ)) for real σ > 0, σ ≠ 1.

For σ > 1: direct Dirichlet series regrouping (identity_gt_one).
For σ ∈ (0, 1): by the identity theorem applied to the connected punctured
half-plane {s ∈ ℂ | Re(s) > 0 ∧ s ≠ 1}, where the complex eta function
η(s) = ∑ (-1)^n/(n+1)^s is holomorphic (conditional Dirichlet series) and
agrees with (1-2^{1-s})ζ(s) for Re(s) > 1. -/
theorem eta_eq_one_sub_two_rpow_mul_zetaReal {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) :
    etaReal σ = (1 - (2 : ℝ) ^ (1 - σ)) * zetaReal σ := by
  rcases lt_or_gt_of_ne hσ1 with h | h
  · -- σ ∈ (0, 1): identity theorem extension (analytic continuation)
    -- The complex eta function η(s) = ∑(-1)^n/(n+1)^s converges for Re(s) > 0
    -- and is holomorphic there. Both sides are holomorphic on {Re > 0}\{1}
    -- (connected), agree for Re > 1, hence agree for all Re > 0, s ≠ 1.
    sorry
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
