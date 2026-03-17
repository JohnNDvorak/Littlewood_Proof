/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Sub-lemmas for the Riemann-von Mangoldt formula: right-edge analysis.

## Overview

For the RvM formula N(T) = (T/2π)log(T/2πe) + O(log T), the argument
principle gives N(T) in terms of the winding integral of logDeriv(Λ) around
a rectangle [1/2, 2] × [0, T]. The RIGHT edge contribution at σ=2 requires
decomposing logDeriv(completedRiemannZeta) into:

  logDeriv(Λ)(s) = logDeriv(Γᵣ)(s) + logDeriv(ζ)(s)

and further decomposing logDeriv(Γᵣ) via Stirling:

  logDeriv(Γᵣ)(s) = -(1/2)·log(π) + (1/2)·ψ(s/2)

where ψ = Γ'/Γ is the digamma function.

## Main Results (all sorry-free)

1. `logDeriv_completedZeta_split`: For Re(s) > 1,
   logDeriv(completedRiemannZeta)(s) = logDeriv(Γᵣ)(s) + logDeriv(ζ)(s)

2. `logDeriv_GammaR_eq`: For Re(s) > 0,
   logDeriv(Γᵣ)(s) = -(1/2)·log(π) + (1/2)·(Γ'/Γ)(s/2)

3. `logDeriv_completedZeta_full`: Combining (1) and (2), for Re(s) > 1,
   logDeriv(Λ)(s) = -(1/2)·log(π) + (1/2)·(Γ'/Γ)(s/2) + (ζ'/ζ)(s)

4. `differentiableAt_GammaR`: Γᵣ is differentiable for Re(s) > 0.

## References

* Montgomery-Vaughan, "Multiplicative Number Theory I", Chapter 14
* Titchmarsh, "The Theory of the Riemann Zeta-Function", §9.3

Co-authored-by: Claude (Anthropic)
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Complex Real Filter Topology MeasureTheory

set_option maxHeartbeats 3200000

noncomputable section

namespace RvMRightEdge

/-! ## Helper: non-pole condition for Gamma at s/2 -/

/-- If Re(s) > 0, then s/2 is not a non-positive integer (pole of Γ). -/
private lemma not_neg_nat_of_half {s : ℂ} (hs : 0 < s.re) :
    ∀ n : ℕ, s / 2 ≠ -(↑n : ℂ) := by
  intro n h
  have : s = -(2 * ↑n : ℂ) := by linear_combination 2 * h
  have hre : s.re = -(2 * (n : ℝ)) := by
    have := congrArg re this; simp at this; exact this
  exact absurd hs (by linarith [Nat.cast_nonneg (α := ℝ) n])

/-! ## Differentiability of Γᵣ -/

/-- The completed Gamma factor Γᵣ(s) = π^{-s/2} · Γ(s/2) is differentiable
    for Re(s) > 0 (away from the poles of Γ). -/
theorem differentiableAt_GammaR (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ Gammaℝ s := by
  unfold Gammaℝ
  apply DifferentiableAt.mul
  · -- π^{-s/2} is differentiable (cpow of positive real constant)
    apply DifferentiableAt.const_cpow
    · exact (differentiableAt_id.neg).div_const 2
    · left; exact_mod_cast Real.pi_pos.ne'
  · -- Γ(s/2) is differentiable for Re(s/2) > 0
    apply DifferentiableAt.comp _ _ (differentiableAt_id.div_const 2)
    exact Complex.differentiableAt_Gamma _ (not_neg_nat_of_half hs)

/-! ## completedRiemannZeta = Gammaℝ * riemannZeta -/

/-- For Re(s) > 0 and s ≠ 0, completedRiemannZeta(s) = Γᵣ(s) · ζ(s). -/
theorem completedZeta_eq_GammaR_mul_zeta (s : ℂ) (hs0 : s ≠ 0) (hG : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  rw [riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀ _ hG]

/-! ## logDeriv of the exponential factor π^{-s/2} -/

/-- logDeriv of the exponential factor π^{-s/2} is the constant -(1/2)·log(π). -/
theorem logDeriv_pi_cpow_neg_half (s : ℂ) :
    logDeriv (fun s => (↑π : ℂ) ^ (-s / 2)) s =
      -(1 / 2 : ℂ) * Complex.log (↑π) := by
  simp only [logDeriv_apply]
  have hpi_ne : (↑π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hf : HasDerivAt (fun s : ℂ => -s / 2) (-(1 / 2 : ℂ)) s := by
    convert (hasDerivAt_id s).neg.div_const (2 : ℂ) using 1; ring
  have hd : HasDerivAt (fun s => (↑π : ℂ) ^ (-s / 2))
      ((↑π : ℂ) ^ (-s / 2) * Complex.log (↑π) * (-(1 / 2 : ℂ))) s :=
    HasDerivAt.const_cpow hf (Or.inl hpi_ne)
  rw [hd.deriv]
  have hne : (↑π : ℂ) ^ (-s / 2) ≠ 0 := by
    simp [cpow_eq_zero_iff, hpi_ne]
  field_simp

/-! ## Chain rule for logDeriv(Γ(s/2)) -/

/-- logDeriv of s ↦ Γ(s/2) equals (1/2) · (Γ'/Γ)(s/2), by the chain rule. -/
theorem logDeriv_Gamma_half (s : ℂ) (hs : 0 < s.re) :
    logDeriv (fun s => Complex.Gamma (s / 2)) s =
      (1 / 2 : ℂ) * logDeriv Complex.Gamma (s / 2) := by
  simp only [logDeriv_apply]
  have hd_inner : HasDerivAt (fun x : ℂ => x / 2) (1 / 2 : ℂ) s := by
    simpa using (hasDerivAt_id s).div_const 2
  have hd_outer : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma _ (not_neg_nat_of_half hs)
  have hchain : deriv (fun s => Complex.Gamma (s / 2)) s =
      deriv Complex.Gamma (s / 2) * (1 / 2 : ℂ) :=
    (hd_outer.hasDerivAt.comp s hd_inner).deriv
  rw [hchain]
  ring

/-! ## Structural decomposition of logDeriv(Γᵣ) -/

/-- **Structural identity**: logDeriv(Γᵣ)(s) = -(1/2)·log(π) + (1/2)·ψ(s/2)
    where ψ = Γ'/Γ is the digamma function.

    Proof: Γᵣ(s) = π^{-s/2} · Γ(s/2), so
    logDeriv(Γᵣ) = logDeriv(π^{-·/2}) + logDeriv(Γ(·/2))
                  = -(1/2)·log(π)      + (1/2)·(Γ'/Γ)(s/2). -/
theorem logDeriv_GammaR_eq (s : ℂ) (hs : 0 < s.re) :
    logDeriv Gammaℝ s =
      -(1 / 2 : ℂ) * Complex.log (↑π) +
        (1 / 2 : ℂ) * logDeriv Complex.Gamma (s / 2) := by
  let f : ℂ → ℂ := fun s => (↑π : ℂ) ^ (-s / 2)
  let g : ℂ → ℂ := fun s => Complex.Gamma (s / 2)
  have hpi_ne : (↑π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hf_ne : f s ≠ 0 := by simp [f, cpow_eq_zero_iff, hpi_ne]
  have hg_ne : g s ≠ 0 := by
    simp only [g]; exact Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hf_diff : DifferentiableAt ℂ f s :=
    DifferentiableAt.const_cpow ((differentiableAt_id.neg).div_const 2) (Or.inl hpi_ne)
  have hg_diff : DifferentiableAt ℂ g s := by
    apply DifferentiableAt.comp _ _ (differentiableAt_id.div_const 2)
    exact Complex.differentiableAt_Gamma _ (not_neg_nat_of_half hs)
  -- Compute derivatives
  have hdf : deriv f s = f s * Complex.log (↑π) * (-(1 / 2 : ℂ)) :=
    (HasDerivAt.const_cpow (by convert (hasDerivAt_id s).neg.div_const (2 : ℂ) using 1; ring)
      (Or.inl hpi_ne)).deriv
  have hdg : deriv g s = deriv Complex.Gamma (s / 2) * (1 / 2 : ℂ) :=
    ((Complex.differentiableAt_Gamma _ (not_neg_nat_of_half hs)).hasDerivAt.comp s
      (by simpa using (hasDerivAt_id s).div_const 2)).deriv
  -- Transfer via Gammaℝ = f * g
  simp only [logDeriv_apply]
  have h_feq : Gammaℝ =ᶠ[𝓝 s] (f * g) :=
    Filter.EventuallyEq.of_eq (funext fun x => Gammaℝ_def x)
  rw [h_feq.deriv_eq, Gammaℝ_def s,
      show deriv (f * g) s = deriv f s * g s + f s * deriv g s from
        deriv_mul hf_diff hg_diff, hdf, hdg]
  simp only [f, g]
  have hG_ne : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  -- s * (1/2) = s / 2 after normalization
  have hs_half : s * (1 / 2 : ℂ) = s / 2 := by ring
  rw [hs_half] at *
  field_simp [hG_ne]

/-! ## Splitting logDeriv(completedRiemannZeta) -/

/-- **Key splitting**: For Re(s) > 1, the logarithmic derivative of
    completedRiemannZeta splits as the sum of the logarithmic derivatives
    of Γᵣ and riemannZeta.

    This uses: completedRiemannZeta = Γᵣ · riemannZeta on {Re(s) > 1},
    and both factors are nonzero and differentiable there. -/
theorem logDeriv_completedZeta_split (s : ℂ) (hs : 1 < s.re) :
    logDeriv completedRiemannZeta s =
      logDeriv Gammaℝ s + logDeriv riemannZeta s := by
  -- Step 1: completedRiemannZeta agrees with Gammaℝ * riemannZeta near s
  have heq : completedRiemannZeta =ᶠ[𝓝 s] (Gammaℝ * riemannZeta) := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    apply Filter.eventuallyEq_iff_exists_mem.mpr
    refine ⟨{s : ℂ | 1 < s.re}, hopen.mem_nhds hs, fun s' (hs' : 1 < s'.re) => ?_⟩
    have hs'0 : s' ≠ 0 := by
      intro h; subst h; simp at hs'; exact absurd hs' (by norm_num)
    have hG : Gammaℝ s' ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
    show completedRiemannZeta s' = (Gammaℝ * riemannZeta) s'
    simp only [Pi.mul_apply]
    rw [riemannZeta_def_of_ne_zero hs'0, mul_div_cancel₀ _ hG]
  -- Step 2: transfer logDeriv via eventuallyEq
  rw [show logDeriv completedRiemannZeta s = logDeriv (Gammaℝ * riemannZeta) s from by
    simp only [logDeriv_apply]; rw [heq.deriv_eq, heq.eq_of_nhds]]
  -- Step 3: logDeriv(f·g) = logDeriv(f) + logDeriv(g)
  have hs1 : s ≠ 1 := by intro h; subst h; simp at hs
  have hre_pos : 0 < s.re := by linarith
  have hG_ne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre_pos
  have hζ_ne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hG_diff : DifferentiableAt ℂ Gammaℝ s := differentiableAt_GammaR s hre_pos
  have hζ_diff : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  simp only [logDeriv_apply, Pi.mul_apply, deriv_mul hG_diff hζ_diff]
  field_simp

/-! ## Combined decomposition -/

/-- **Full decomposition**: For Re(s) > 1, the logarithmic derivative of
    completedRiemannZeta decomposes as:

    logDeriv(Λ)(s) = -(1/2)·log(π) + (1/2)·(Γ'/Γ)(s/2) + (ζ'/ζ)(s)

    This is the key structural identity for the right-edge integral
    in the Riemann-von Mangoldt formula. -/
theorem logDeriv_completedZeta_full (s : ℂ) (hs : 1 < s.re) :
    logDeriv completedRiemannZeta s =
      -(1 / 2 : ℂ) * Complex.log (↑π) +
        (1 / 2 : ℂ) * logDeriv Complex.Gamma (s / 2) +
          logDeriv riemannZeta s := by
  rw [logDeriv_completedZeta_split s hs, logDeriv_GammaR_eq s (by linarith), add_assoc]

/-! ## Right-edge integral: constant term -/

/-- The integral of the constant -(1/2)·log(π) over [1, T] gives the
    constant-term contribution to the right-edge integral:
    ∫₁ᵀ -(1/2)·log(π) dt = -(T-1)/2 · log(π). -/
theorem integral_const_logPi (T : ℝ) :
    ∫ _t in (1 : ℝ)..T, (-(1 / 2 : ℝ) * Real.log π) =
      -(T - 1) / 2 * Real.log π := by
  rw [intervalIntegral.integral_const]
  simp [smul_eq_mul]
  ring

end RvMRightEdge
