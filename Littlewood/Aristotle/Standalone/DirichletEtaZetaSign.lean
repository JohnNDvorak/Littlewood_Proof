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

SORRY COUNT: 2
  1. eta_eq_one_sub_two_rpow_mul_zetaReal — identity η = (1-2^{1-σ})ζ for σ > 0
     (series identity for σ > 1 + identity theorem extension to σ > 0)
  2. riemannZeta_ofReal_im_eq_zero — ζ(↑σ) ∈ ℝ for σ ≠ 1
     (follows from Hurwitz zeta construction being real-valued on ℝ)

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

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
This follows from the construction: completedRiemannZeta₀ is defined via Mellin
transforms of theta functions, which are real-valued for real arguments. -/
theorem riemannZeta_ofReal_im_eq_zero {σ : ℝ} (hσ : σ ≠ 1) :
    (riemannZeta (↑σ : ℂ)).im = 0 := by
  sorry

/-- Extract the real part of riemannZeta at a real argument. -/
private def zetaReal (σ : ℝ) : ℝ := (riemannZeta (↑σ : ℂ)).re

/-! ## Section 5: The key identity η(σ) = (1 - 2^{1-σ}) * ζ(σ)

For σ > 1, proved by Dirichlet series: ζ - η = 2·∑(2k+2)^{-σ} = 2^{1-σ}·ζ.
Extended to σ > 0 by the identity theorem (both sides real-analytic on (0, ∞)). -/

/-- The identity η(σ) = (1 - 2^{1-σ}) * Re(ζ(σ)) for real σ > 0.

For σ > 1: direct Dirichlet series regrouping.
For σ ∈ (0, 1]: by the identity theorem for real-analytic functions.
Both sides are real-analytic on (0, ∞):
- η is the uniformly convergent alternating series
- (1-2^{1-σ})·ζ(σ) is real-analytic because ζ is meromorphic with
  the pole at σ=1 cancelled by the zero of 1-2^{1-σ} at σ=1 -/
theorem eta_eq_one_sub_two_rpow_mul_zetaReal {σ : ℝ} (hσ : 0 < σ) :
    etaReal σ = (1 - (2 : ℝ) ^ (1 - σ)) * zetaReal σ := by
  sorry

/-! ## Section 6: Main results -/

/-- **Re(ζ(σ)) < 0 for real σ ∈ (0, 1).**
Since η(σ) > 0 and (1 - 2^{1-σ}) < 0, the identity η = (1-2^{1-σ})·ζ gives ζ < 0. -/
theorem zetaReal_neg {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    zetaReal σ < 0 := by
  have h_eta := etaReal_pos hσ0
  have h_factor := one_sub_two_rpow_neg hσ1
  have h_id := eta_eq_one_sub_two_rpow_mul_zetaReal hσ0
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
