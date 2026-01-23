/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Littlewood.CoreLemmas.LandauLemma
import Littlewood.Development.ZetaPositivity

/-!
# Logarithmic Derivative of Zeta

For real σ > 1, -ζ'(σ)/ζ(σ) > 0.

## Main Results

* `neg_zeta_logderiv_pos_real` : -ζ'/ζ(σ) > 0 for real σ > 1

## Strategy

-ζ'(σ)/ζ(σ) = ∑_{n=1}^∞ Λ(n) n^{-σ} for σ > 1 (absolutely convergent series).
Λ(n) ≥ 0 (von Mangoldt function is non-negative).
Each term Λ(n) n^{-σ} is non-negative.
The sum includes Λ(2) · 2^{-σ} = log(2) · 2^{-σ} > 0, so sum is positive.

## References

* Any standard analytic number theory text
-/

open Complex Real ArithmeticFunction

namespace Littlewood.Development.ZetaLogDeriv

/-- The von Mangoldt function is non-negative.
Standard fact: Λ(n) = 0 if n is not a prime power, else Λ(p^k) = log(p) ≥ log(2) > 0. -/
lemma vonMangoldt_nonneg' (n : ℕ) : 0 ≤ Λ n := by
  simp only [vonMangoldt_apply]
  split_ifs with h
  · -- When n is a prime power p^k, Λ(n) = log(p) where p ≥ 2
    positivity
  · linarith

/-- Λ(2) = log 2 > 0 since 2 is a prime power -/
lemma vonMangoldt_two_pos : 0 < Λ 2 := by
  simp only [vonMangoldt_apply]
  have h2prime : IsPrimePow 2 := Nat.Prime.isPrimePow Nat.prime_two
  simp only [h2prime, ↓reduceIte]
  exact Real.log_pos (by norm_num : (1 : ℝ) < 2)

/-- For real σ and n ≥ 1, the term Λ(n) / n^σ is a non-negative real. -/
lemma vonMangoldt_term_re_nonneg (n : ℕ) (σ : ℝ) (hn : n ≠ 0) :
    0 ≤ ((Λ n : ℂ) / (n : ℂ) ^ (σ : ℂ)).re := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  -- n^σ = n^σ as a positive real, using Complex.ofReal_cpow
  have hpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [← ofReal_natCast n, ← ofReal_cpow hn_pos.le σ]
  rw [hpow]
  -- Now Λ(n) / (n^σ : ℂ) = (Λ(n) / n^σ : ℝ)
  have hdiv : (Λ n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ) = ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [← ofReal_div]
  rw [hdiv, ofReal_re]
  apply div_nonneg
  · exact vonMangoldt_nonneg' n
  · exact Real.rpow_pos_of_pos hn_pos σ |>.le

/-- For real σ and n ≥ 1, the term Λ(n) / n^σ has imaginary part zero. -/
lemma vonMangoldt_term_im_zero (n : ℕ) (σ : ℝ) (hn : n ≠ 0) :
    ((Λ n : ℂ) / (n : ℂ) ^ (σ : ℂ)).im = 0 := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [← ofReal_natCast n, ← ofReal_cpow hn_pos.le σ]
  rw [hpow, ← ofReal_div, ofReal_im]

/-- For real σ > 1, the logarithmic derivative -ζ'/ζ is positive.

Proof strategy:
- -ζ'/ζ(σ) = ∑ Λ(n) n^{-σ} via vonMangoldt_eq_neg_zeta_logderiv from LandauLemma
- Λ(n) ≥ 0 for all n
- Λ(2) = log(2) > 0, so at least one term is strictly positive
- Sum of non-negatives with at least one positive is positive
-/
theorem neg_zeta_logderiv_pos_real (σ : ℝ) (hσ : 1 < σ) :
    0 < -(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
  -- Use the identity: -ζ'/ζ = L(Λ, s) from LandauLemma
  have hre : 1 < (σ : ℂ).re := by simp [hσ]
  have hid := Landau.vonMangoldt_eq_neg_zeta_logderiv (σ : ℂ) hre
  -- hid : LSeries Λ σ = -ζ'/ζ(σ)
  -- So -(ζ'/ζ).re = (-(-LSeries)).re = (LSeries).re
  have hgoal : -(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re =
      (LSeries (fun n => (Λ n : ℂ)) σ).re := by
    -- hid: LSeries = (-deriv)/ζ = -(deriv/ζ) (by neg_div)
    -- So deriv/ζ = -LSeries
    have h1 : -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) =
              -(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)) := neg_div _ _
    have heq : deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) =
               -(LSeries (fun n => (Λ n : ℂ)) σ) := by
      -- From hid: LSeries = -deriv/ζ
      -- From h1: -deriv/ζ = -(deriv/ζ)
      -- So: LSeries = -(deriv/ζ)
      -- Negating both sides and simplifying: deriv/ζ = -LSeries
      have h2 : LSeries (fun n => (Λ n : ℂ)) σ = -(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)) := by
        rw [h1] at hid; exact hid
      calc deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)
          = - -(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)) := (neg_neg _).symm
        _ = -(LSeries (fun n => (Λ n : ℂ)) σ) := by rw [← h2]
    rw [heq, neg_re, neg_neg]
  rw [hgoal]
  -- Now show LSeries Λ σ has positive real part
  -- The L-series is ∑' n, Λ(n) / n^σ where each term is real and non-negative
  -- and Λ(2) / 2^σ > 0
  have hsumm := ArithmeticFunction.LSeriesSummable_vonMangoldt hre
  rw [LSeries, re_tsum hsumm]
  -- Show the series of real parts is positive
  -- Need: summable, nonneg, at least one positive term
  have hsumm_re : Summable (fun n => (LSeries.term (fun n => (Λ n : ℂ)) σ n).re) := by
    exact ZetaPositivity.summable_re_of_summable hsumm
  have hnonneg : ∀ n, 0 ≤ (LSeries.term (fun n => (Λ n : ℂ)) σ n).re := by
    intro n
    simp only [LSeries.term]
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      exact vonMangoldt_term_re_nonneg n σ hn
  have hpos_term : 0 < (LSeries.term (fun n => (Λ n : ℂ)) σ 2).re := by
    simp only [LSeries.term, show (2 : ℕ) ≠ 0 from by norm_num, ↓reduceIte]
    have h2_pos : (0 : ℝ) < 2 := by norm_num
    -- Show (2 : ℂ) ^ (σ : ℂ) = (2^σ : ℝ) as complex
    have hpow : (2 : ℂ) ^ (σ : ℂ) = ((Real.rpow 2 σ) : ℂ) := by
      have := ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2) σ
      simp only [ofReal_ofNat] at this
      exact this.symm
    simp only [Nat.cast_ofNat, hpow]
    rw [show (Λ 2 : ℂ) = ((Λ 2 : ℝ) : ℂ) from rfl, ← ofReal_div, ofReal_re]
    apply div_pos
    · exact vonMangoldt_two_pos
    · exact Real.rpow_pos_of_pos h2_pos σ
  exact ZetaPositivity.tsum_pos_of_nonneg_of_pos hsumm_re hnonneg 2 hpos_term

/-- The real part of -ζ'/ζ(σ) equals the series for real σ > 1 -/
theorem neg_zeta_logderiv_eq_vonMangoldt_series (σ : ℝ) (hσ : 1 < σ) :
    (-(deriv riemannZeta (σ : ℂ)) / riemannZeta (σ : ℂ)).re = ∑' n : ℕ, Λ n * (n : ℝ) ^ (-σ) := by
  -- Use the identity from LandauLemma
  have hre : 1 < (σ : ℂ).re := by simp [hσ]
  have hid := Landau.vonMangoldt_eq_neg_zeta_logderiv (σ : ℂ) hre
  -- The LSeries for real σ has real part equal to the real series
  -- LSeries Λ σ = ∑' n, Λ(n) / n^σ where the RHS is a real number for real σ
  sorry -- BLOCKED: Need real-part extraction for LSeries at real argument

end Littlewood.Development.ZetaLogDeriv
