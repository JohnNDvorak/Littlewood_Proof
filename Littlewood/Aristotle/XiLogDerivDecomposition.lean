/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Logarithmic derivative decomposition of the Riemann xi function product.

The completed Riemann xi function satisfies (up to a scalar):
  ξ(s) = s·(s-1)·π^{-s/2}·Γ(s/2)·ζ(s)

Taking the logarithmic derivative and using the product rule:
  logDeriv(ξ)(s) = 1/s + 1/(s-1) - (1/2)·log(π) + (1/2)·logDeriv(Γ)(s/2) + logDeriv(ζ)(s)

This identity decomposes logDeriv(ζ) in terms of logDeriv(ξ) (related to zeros
via Hadamard product) and explicitly computable functions (Stirling for digamma,
trivial for the rational terms).

KEY RESULTS:
- logDeriv_xi_product_decomposition: The main decomposition identity, 0 sorry.
- logDeriv_zeta_from_xi: Rearranged form isolating logDeriv(ζ).
-/

import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic

open Complex Filter

noncomputable section

set_option maxHeartbeats 6400000

namespace XiLogDeriv

/-- logDeriv of z·(z-1) = 1/z + 1/(z-1), proved via the polynomial z²-z. -/
private lemma logDeriv_id_mul_sub_one (s : ℂ) (hs0 : s ≠ 0) (hs1 : s - 1 ≠ 0) :
    logDeriv (fun z => z * (z - 1)) s = 1/s + 1/(s - 1) := by
  have hfun : (fun z : ℂ => z * (z - 1)) = (fun z => z ^ 2 - z) := by ext; ring
  rw [hfun]; simp only [logDeriv_apply]
  rw [show s ^ 2 - s = s * (s - 1) from by ring]
  have h := (hasDerivAt_pow 2 s).sub (hasDerivAt_id s)
  have heq : ((fun z : ℂ => z ^ 2) - (fun z : ℂ => z)) =ᶠ[nhds s] (fun z => z ^ 2 - z) := by
    filter_upwards with z; simp [Pi.sub_apply]
  rw [((heq.hasDerivAt_iff).mp h).deriv]; simp [pow_one]; field_simp; ring

/-- logDeriv of π^{-z/2} = -(1/2)·log(π).

Since π^{-z/2} = exp((-log π/2)·z), the logarithmic derivative is just the
coefficient of z in the exponent. -/
private lemma logDeriv_pi_cpow_neg_half (s : ℂ) :
    logDeriv (fun z => (↑Real.pi : ℂ) ^ (-z/2)) s = -(1/2) * Complex.log (↑Real.pi) := by
  have hpi := ofReal_mem_slitPlane.mpr Real.pi_pos
  have : (fun z => (↑Real.pi : ℂ) ^ (-z/2)) =
      (fun z => Complex.exp ((-Complex.log (↑Real.pi) / 2) * z)) := by
    ext z; rw [Complex.cpow_def_of_ne_zero (slitPlane_ne_zero hpi)]; ring_nf
  rw [this]; simp [logDeriv_apply]
  have hd : HasDerivAt (fun z : ℂ => (-Complex.log (↑Real.pi) / 2) * z)
      (-Complex.log (↑Real.pi) / 2) s := by
    simpa using (hasDerivAt_id s).const_mul (-Complex.log (↑Real.pi) / 2)
  rw [hd.cexp.deriv, mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]; ring

/-- logDeriv of Γ(z/2) = (1/2)·logDeriv(Γ)(z/2), by the chain rule. -/
private lemma logDeriv_Gamma_half_eq (s : ℂ) (hs : ∀ n : ℕ, s/2 ≠ -(n : ℂ)) :
    logDeriv (fun z => Complex.Gamma (z/2)) s =
    (1/2) * logDeriv Complex.Gamma (s/2) := by
  simp only [logDeriv_apply]
  have hd := (Complex.differentiableAt_Gamma _ hs).hasDerivAt.comp s
    ((hasDerivAt_id s).div_const 2)
  have heq : (fun z => Complex.Gamma (z/2)) =
      (Complex.Gamma ∘ fun x => id x / 2) := by ext; simp
  rw [heq, hd.deriv]; ring

/-- The logDeriv decomposition of the xi function product.

For s ≠ 0, s ≠ 1, s/2 not a non-positive integer, ζ(s) ≠ 0, and ζ differentiable at s:

  logDeriv(s·(s-1)·π^{-s/2}·Γ(s/2)·ζ(s)) =
    1/s + 1/(s-1) - (1/2)·log(π) + (1/2)·logDeriv(Γ)(s/2) + logDeriv(ζ)(s)

The proof decomposes the five-fold product using `logDeriv_mul` iteratively,
peeling off factors from right to left, then substitutes the computed logDeriv
of each individual factor. -/
theorem logDeriv_xi_product_decomposition (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hsn : ∀ n : ℕ, s/2 ≠ -(n : ℂ)) (hzeta : riemannZeta s ≠ 0)
    (hdz : DifferentiableAt ℂ riemannZeta s) :
    logDeriv (fun z => z * (z - 1) * (↑Real.pi : ℂ) ^ (-z/2) *
      Complex.Gamma (z/2) * riemannZeta z) s =
    1/s + 1/(s - 1) - (1/2) * Complex.log (↑Real.pi) +
      (1/2) * logDeriv Complex.Gamma (s/2) + logDeriv riemannZeta s := by
  have hs1' : s - 1 ≠ 0 := by intro h; exact hs1 (sub_eq_zero.mp h)
  have hpi_ne : (↑Real.pi : ℂ) ^ (-s/2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero)]
    exact Complex.exp_ne_zero _
  have hdpi : DifferentiableAt ℂ (fun z => (↑Real.pi : ℂ) ^ (-z/2)) s := by
    have : (fun z => (↑Real.pi : ℂ) ^ (-z/2)) =
        (fun z => Complex.exp ((-Complex.log (↑Real.pi) / 2) * z)) := by
      ext z; rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero)]; ring_nf
    rw [this]; exact ((differentiableAt_id.const_mul _).cexp)
  have hdG : DifferentiableAt ℂ (fun z => Complex.Gamma (z/2)) s := by
    show DifferentiableAt ℂ (Complex.Gamma ∘ (· / 2)) s
    exact (Complex.differentiableAt_Gamma _ hsn).comp s (differentiableAt_id.div_const 2)
  have hd_sub : DifferentiableAt ℂ (fun z : ℂ => z - (1 : ℂ)) s :=
    differentiableAt_id.sub (differentiableAt_const (1 : ℂ))
  -- Step 1: peel off ζ(s) from the product
  have step1 : logDeriv (fun z => z * (z - 1) * (↑Real.pi : ℂ) ^ (-z/2) *
      Complex.Gamma (z/2) * riemannZeta z) s =
      logDeriv (fun z => z * (z - 1) * (↑Real.pi : ℂ) ^ (-z/2) *
        Complex.Gamma (z/2)) s + logDeriv riemannZeta s := by
    refine logDeriv_mul s ?_ hzeta ?_ hdz
    · exact mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 hs1') hpi_ne)
        (Complex.Gamma_ne_zero hsn)
    · exact (((differentiableAt_id.mul hd_sub).mul hdpi).mul hdG)
  -- Step 2: peel off Γ(s/2)
  have step2 : logDeriv (fun z => z * (z - 1) * (↑Real.pi : ℂ) ^ (-z/2) *
      Complex.Gamma (z/2)) s =
      logDeriv (fun z => z * (z - 1) * (↑Real.pi : ℂ) ^ (-z/2)) s +
        logDeriv (fun z => Complex.Gamma (z/2)) s := by
    refine logDeriv_mul s ?_ (Complex.Gamma_ne_zero hsn) ?_ hdG
    · exact mul_ne_zero (mul_ne_zero hs0 hs1') hpi_ne
    · exact ((differentiableAt_id.mul hd_sub).mul hdpi)
  -- Step 3: peel off π^{-s/2}
  have step3 : logDeriv (fun z => z * (z - 1) * (↑Real.pi : ℂ) ^ (-z/2)) s =
      logDeriv (fun z => z * (z - 1)) s +
        logDeriv (fun z => (↑Real.pi : ℂ) ^ (-z/2)) s := by
    refine logDeriv_mul s ?_ hpi_ne ?_ hdpi
    · exact mul_ne_zero hs0 hs1'
    · exact differentiableAt_id.mul hd_sub
  -- Substitute and simplify
  rw [step1, step2, step3, logDeriv_id_mul_sub_one s hs0 hs1',
      logDeriv_pi_cpow_neg_half, logDeriv_Gamma_half_eq s hsn]
  ring

/-- Rearranged form: logDeriv(ζ) in terms of logDeriv(ξ-product) and known functions.

  logDeriv(ζ)(s) = logDeriv(ξ-product)(s) - 1/s - 1/(s-1) + (1/2)·log(π) - (1/2)·logDeriv(Γ)(s/2)
-/
theorem logDeriv_zeta_from_xi (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hsn : ∀ n : ℕ, s/2 ≠ -(n : ℂ)) (hzeta : riemannZeta s ≠ 0)
    (hdz : DifferentiableAt ℂ riemannZeta s) :
    logDeriv riemannZeta s =
    logDeriv (fun z => z * (z - 1) * (↑Real.pi : ℂ) ^ (-z/2) *
      Complex.Gamma (z/2) * riemannZeta z) s -
    1/s - 1/(s - 1) + (1/2) * Complex.log (↑Real.pi) -
      (1/2) * logDeriv Complex.Gamma (s/2) := by
  have h := logDeriv_xi_product_decomposition s hs0 hs1 hsn hzeta hdz
  linarith

end XiLogDeriv
