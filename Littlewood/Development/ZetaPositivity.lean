/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Zeta Function Positivity

For real σ > 1, the Riemann zeta function is positive: ζ(σ) > 0.

## Main Results

* `riemannZeta_im_zero_of_real` : Im(ζ(σ)) = 0 for real σ > 1
* `riemannZeta_pos_of_real_gt_one` : ζ(σ) > 0 for real σ > 1
* `riemannZeta_real_and_pos` : Combined result

## Strategy

ζ(σ) = ∑_{n=1}^∞ 1/n^σ for σ > 1 (absolutely convergent series).
Each term 1/n^σ is a positive real for σ real.
Sum of positive reals is positive.

## References

* Any standard analytic number theory text
-/

open Complex Real

namespace Littlewood.Development.ZetaPositivity

/-! ## Auxiliary lemmas -/

/-- For summable nonneg series with at least one positive term, the sum is positive. -/
lemma tsum_pos_of_nonneg_of_pos {f : ℕ → ℝ} (hf : Summable f)
    (hnonneg : ∀ n, 0 ≤ f n) (k : ℕ) (hk : 0 < f k) :
    0 < ∑' n, f n := by
  obtain ⟨a, ha⟩ := hf
  have hsum_eq : ∑' n, f n = a := ha.tsum_eq
  rw [hsum_eq]
  have hpartial : ∀ s : Finset ℕ, k ∈ s → f k ≤ ∑ i ∈ s, f i := by
    intro s hks
    exact Finset.single_le_sum (fun i _ => hnonneg i) hks
  have h_eventually : ∀ᶠ s in (SummationFilter.unconditional ℕ).filter, k ∈ s := by
    rw [Filter.eventually_iff_exists_mem]
    use {s : Finset ℕ | {k} ⊆ s}
    constructor
    · apply Filter.mem_atTop_sets.mpr
      use {k}
      intro s hs
      simp only [Set.mem_setOf_eq] at hs ⊢
      exact hs
    · intro s hs
      simp only [Set.mem_setOf_eq, Finset.singleton_subset_iff] at hs
      exact hs
  have h_le : f k ≤ a := by
    apply ge_of_tendsto ha
    apply Filter.Eventually.mono h_eventually
    intro s hks
    exact hpartial s hks
  linarith

/-- The imaginary part of 1/n^σ is zero for real σ. -/
lemma one_div_nat_cpow_im_zero (n : ℕ) (σ : ℝ) : (1 / (n : ℂ) ^ (σ : ℂ)).im = 0 := by
  by_cases hn : n = 0
  · subst hn
    by_cases hσ : σ = 0
    · simp [hσ]
    · simp [Complex.zero_cpow (ofReal_ne_zero.mpr hσ)]
  · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [← ofReal_natCast n]
    rw [← ofReal_cpow hn_pos.le σ]
    simp only [one_div]
    rw [← ofReal_inv]
    simp only [ofReal_im]

/-- The real part of 1/n^σ is nonnegative for real σ. -/
lemma one_div_nat_cpow_re_nonneg (n : ℕ) (σ : ℝ) :
    0 ≤ (1 / (n : ℂ) ^ (σ : ℂ)).re := by
  by_cases hn : n = 0
  · subst hn
    by_cases hσ : σ = 0
    · simp [hσ]
    · simp [Complex.zero_cpow (ofReal_ne_zero.mpr hσ)]
  · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [← ofReal_natCast n]
    rw [← ofReal_cpow hn_pos.le σ]
    simp only [one_div]
    rw [← ofReal_inv]
    simp only [ofReal_re]
    exact le_of_lt (inv_pos.mpr (Real.rpow_pos_of_pos hn_pos σ))

/-- Summability of real parts follows from summability of complex. -/
lemma summable_re_of_summable {f : ℕ → ℂ} (hf : Summable f) :
    Summable (fun n => (f n).re) := by
  obtain ⟨a, ha⟩ := hf
  have ha_re : HasSum (fun n => (f n).re) a.re := hasSum_re ha
  exact ha_re.summable

/-! ## Main results -/

/-- For real σ > 1, the imaginary part of ζ(σ) is zero.

This follows because ζ(σ) = ∑ 1/n^σ where each term 1/n^σ is real.
-/
theorem riemannZeta_im_zero_of_real (σ : ℝ) (hσ : 1 < σ) :
    (riemannZeta σ).im = 0 := by
  have hre : 1 < (σ : ℂ).re := by simp [hσ]
  rw [zeta_eq_tsum_one_div_nat_cpow hre]
  have hsumm : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (σ : ℂ)) :=
    summable_one_div_nat_cpow.mpr hre
  rw [im_tsum hsumm]
  simp_rw [one_div_nat_cpow_im_zero]
  simp

/-- For real σ > 1, the Riemann zeta function is positive.

Proof strategy:
- ζ(σ) = ∑ 1/n^σ with all positive terms
- Sum of positives is positive
-/
theorem riemannZeta_pos_of_real_gt_one (σ : ℝ) (hσ : 1 < σ) :
    0 < (riemannZeta σ).re := by
  have hre : 1 < (σ : ℂ).re := by simp [hσ]
  rw [zeta_eq_tsum_one_div_nat_cpow hre]
  have hsumm : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (σ : ℂ)) :=
    summable_one_div_nat_cpow.mpr hre
  rw [re_tsum hsumm]
  have hsumm_re : Summable (fun n : ℕ => (1 / (n : ℂ) ^ (σ : ℂ)).re) :=
    summable_re_of_summable hsumm
  refine tsum_pos_of_nonneg_of_pos hsumm_re ?_ 1 ?_
  · intro n
    exact one_div_nat_cpow_re_nonneg n σ
  · simp only [Nat.cast_one, one_cpow, div_one, one_re]
    exact one_pos

/-- Combining: ζ(σ) is a positive real number for real σ > 1 -/
theorem riemannZeta_real_and_pos (σ : ℝ) (hσ : 1 < σ) :
    (riemannZeta σ).im = 0 ∧ 0 < (riemannZeta σ).re :=
  ⟨riemannZeta_im_zero_of_real σ hσ, riemannZeta_pos_of_real_gt_one σ hσ⟩

/-! ## Zero location from Mathlib non-vanishing -/

/-- If ζ(ρ) = 0, then Re(ρ) < 1.

This follows directly from Mathlib's `riemannZeta_ne_zero_of_one_le_re`.
Note: This applies to ANY zero, not just nontrivial zeros.
-/
theorem zeta_zero_re_lt_one (ρ : ℂ) (hzero : riemannZeta ρ = 0) : ρ.re < 1 := by
  by_contra h
  push_neg at h  -- h : 1 ≤ ρ.re
  have hne := riemannZeta_ne_zero_of_one_le_re h
  exact hne hzero

/-- If ζ(ρ) = 0 and Re(ρ) > 0, then 0 < Re(ρ) < 1 -/
theorem zeta_zero_re_in_strip (ρ : ℂ) (hzero : riemannZeta ρ = 0) (hpos : 0 < ρ.re) :
    0 < ρ.re ∧ ρ.re < 1 :=
  ⟨hpos, zeta_zero_re_lt_one ρ hzero⟩

/-! ## L-series monotonicity for non-negative coefficients -/

/-- For n ≥ 1 and real σ₁ ≤ σ₂, we have n^σ₁ ≤ n^σ₂ -/
lemma nat_rpow_le_of_le {n : ℕ} (hn : 1 ≤ n) {σ₁ σ₂ : ℝ} (hσ : σ₁ ≤ σ₂) :
    (n : ℝ) ^ σ₁ ≤ (n : ℝ) ^ σ₂ := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact Real.rpow_le_rpow_of_exponent_le hn' hσ

/-- For n ≥ 1 and real σ₁ ≤ σ₂, we have n^(-σ₂) ≤ n^(-σ₁) -/
lemma one_div_nat_rpow_antitone {n : ℕ} (hn : 1 ≤ n) {σ₁ σ₂ : ℝ} (hσ : σ₁ ≤ σ₂) :
    (n : ℝ) ^ (-σ₂) ≤ (n : ℝ) ^ (-σ₁) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact Real.rpow_le_rpow_of_exponent_le hn' (neg_le_neg hσ)

/-- Key monotonicity: for non-negative f, the real L-series value decreases as σ increases.

More precisely: for 0 < σ₁ ≤ σ₂ both above the abscissa of convergence,
∑ f(n)/n^σ₂ ≤ ∑ f(n)/n^σ₁

This is the fundamental monotonicity property used in Landau's theorem.
Note: The condition σ₁ > 0 ensures 0^(-σ) = 0 for all terms.
-/
theorem lseries_real_antitone_of_nonneg (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    {σ₁ σ₂ : ℝ} (hσ₁_pos : 0 < σ₁) (hσ : σ₁ ≤ σ₂)
    (h₁ : Summable (fun n => f n * (n : ℝ) ^ (-σ₁)))
    (h₂ : Summable (fun n => f n * (n : ℝ) ^ (-σ₂))) :
    ∑' n, f n * (n : ℝ) ^ (-σ₂) ≤ ∑' n, f n * (n : ℝ) ^ (-σ₁) := by
  refine h₂.tsum_le_tsum ?_ h₁
  intro n
  by_cases hn : n = 0
  · -- n = 0: 0^(-σ) = 0 for σ > 0, so f(0) * 0^(-σ) = 0
    subst hn
    simp only [Nat.cast_zero]
    have hσ₂_pos : 0 < σ₂ := lt_of_lt_of_le hσ₁_pos hσ
    simp [Real.zero_rpow (neg_ne_zero.mpr hσ₁_pos.ne'), Real.zero_rpow (neg_ne_zero.mpr hσ₂_pos.ne')]
  · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    apply mul_le_mul_of_nonneg_left _ (hf n)
    exact one_div_nat_rpow_antitone hn' hσ

end Littlewood.Development.ZetaPositivity
