/-
Reverse direction: CorrectedPrimeZetaExtensionHyp from PiAtomHardCaseCorrectedCore.

This file proves that the corrected prime zeta extension hypothesis (B6) follows
from the corrected hard-case core (which says ∃ G analytic with exp(G) = (s-1)ζ(s)).

## Key Identity

For Re(s) > 1:
  primeZeta(s) + log(s-1) = H_zeta_log(s) + log(s-1) - correctionTerm(s)
                           = G(s) - correctionTerm(s)  [up to constant 2πik]

where G comes from PiAtomHardCaseCorrectedCore and the constant k is determined
by evaluating at s = 2.

## Proof Strategy

Given G analytic on {Re > α} with exp(G) = (s-1)ζ for Re > 1:

1. Define f(s) = G(s) - H_zeta_log(s) - log(s-1) on {Re > 1}.
2. exp(f(s)) = exp(G)/(exp(H_zeta_log)·exp(log(s-1))) = (s-1)ζ/((s-1)ζ) = 1.
3. f is differentiable on {Re > 1} (connected, open).
4. Since exp∘f = 1 (constant), differentiating: f'(s) = 0.
5. By IsOpen.is_const_of_deriv_eq_zero: f = c constant.
6. Define Q = G - correctionTerm - c.
7. Q is analytic on {Re > α}, and Q = primeZeta + log(s-1) on {Re > 1}.

SORRY COUNT: 0

Co-authored-by: Claude (Anthropic)
-/

import Littlewood.Aristotle.Standalone.PiAtomHardCaseCorrectedCore
import Littlewood.Aristotle.CorrectionTermAnalyticity
import Littlewood.Aristotle.Standalone.PrimeZetaExtensionProof
import Littlewood.Aristotle.HalfPlaneConnected

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace Aristotle.Standalone.CorrectedPrimeZetaFromCore

open Complex Real Filter Topology Set
open Aristotle.CorrectionTermAnalyticity
open Aristotle.LandauLogZetaObstruction
open Aristotle.Standalone.PiAtomHardCaseCorrectedCore
open Aristotle.Standalone.PrimeZetaExtensionProof

/-! ## Auxiliary lemmas -/

/-- The half-plane {Re > α} is open. -/
private lemma halfPlane_isOpen (α : ℝ) : IsOpen {s : ℂ | α < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- The half-plane {Re > 1} is preconnected. -/
private lemma halfPlane_one_isPreconnected : IsPreconnected {s : ℂ | (1 : ℝ) < s.re} := by
  have hconv : Convex ℝ {s : ℂ | (1 : ℝ) < s.re} := by
    have : {s : ℂ | (1 : ℝ) < s.re} = Complex.reCLM ⁻¹' Ioi 1 := by
      ext s; simp [Complex.reCLM_apply]
    rw [this]
    exact (convex_Ioi 1).linear_preimage Complex.reCLM.toLinearMap
  exact hconv.isPreconnected

/-- For s with Re(s) > 1, s - 1 is in the slit plane (needed for Complex.log). -/
private lemma s_sub_one_mem_slitPlane {s : ℂ} (hs : 1 < s.re) :
    s - 1 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left; simp; linarith

/-- For s with Re(s) > 1, s - 1 ≠ 0. -/
private lemma s_sub_one_ne_zero {s : ℂ} (hs : 1 < s.re) : s - 1 ≠ 0 :=
  Complex.slitPlane_ne_zero (s_sub_one_mem_slitPlane hs)

/-- Complex.log(s - 1) is differentiable at s for Re(s) > 1. -/
private lemma differentiableAt_log_sub_one {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (fun z => Complex.log (z - 1)) s :=
  (Complex.differentiableAt_log (s_sub_one_mem_slitPlane hs)).comp s
    ((differentiable_id.differentiableAt).sub (differentiableAt_const 1))

/-- H_zeta_log is differentiable at s for Re(s) > 1. -/
private lemma H_zeta_log_differentiableAt {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ H_zeta_log s := by
  -- Pick α₀ = (1 + s.re)/2, then 1 < α₀ and α₀ < s.re
  have hα₀ : 1 < (1 + s.re) / 2 := by linarith
  have hs_mem : (1 + s.re) / 2 < s.re := by linarith
  exact (H_zeta_log_analyticOnNhd ((1 + s.re) / 2) hα₀ s hs_mem).differentiableAt

/-- exp(H_zeta_log(s) + log(s-1)) = (s-1) * ζ(s) for Re(s) > 1. -/
private lemma exp_H_add_log_eq {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (H_zeta_log s + Complex.log (s - 1)) =
    (s - 1) * riemannZeta s := by
  rw [Complex.exp_add, H_zeta_log_exp_eq hs,
      Complex.exp_log (s_sub_one_ne_zero hs)]
  ring

/-! ## The constancy lemma

If f is differentiable on a connected open set U and exp(f) = 1 on U,
then f is constant on U. Proof: d/ds[exp(f)] = exp(f)·f' = f' = 0. -/

/-- If f is differentiable on {Re > 1} and exp(f(s)) = 1 for all s in {Re > 1},
then f is constant on {Re > 1}. -/
private theorem exp_eq_one_implies_const
    (f : ℂ → ℂ) (hf_diff : DifferentiableOn ℂ f {s : ℂ | (1 : ℝ) < s.re})
    (hf_exp : ∀ s : ℂ, 1 < s.re → exp (f s) = 1)
    {s₁ s₂ : ℂ} (hs₁ : 1 < s₁.re) (hs₂ : 1 < s₂.re) :
    f s₁ = f s₂ := by
  -- Strategy: show deriv f = 0 on {Re > 1}, then use IsOpen.is_const_of_deriv_eq_zero
  have hU_open := halfPlane_isOpen (1 : ℝ)
  have hU_conn := halfPlane_one_isPreconnected
  apply hU_open.is_const_of_deriv_eq_zero hU_conn hf_diff _ hs₁ hs₂
  -- Show deriv f = 0 on {Re > 1}
  intro s hs
  show deriv f s = 0
  -- exp ∘ f = 1 (constant) on {Re > 1}
  -- Differentiate: exp(f(s)) · f'(s) = 0, and exp(f(s)) = 1 ≠ 0, so f'(s) = 0
  have hf_at := hf_diff.differentiableAt (hU_open.mem_nhds hs)
  have h_chain : HasDerivAt (fun z => Complex.exp (f z)) (Complex.exp (f s) * deriv f s) s :=
    (Complex.hasDerivAt_exp (f s)).comp s hf_at.hasDerivAt
  have h_const_near : ∀ᶠ z in 𝓝 s, Complex.exp (f z) = 1 :=
    Filter.Eventually.mono (hU_open.mem_nhds hs) (fun z hz => hf_exp z hz)
  have h_deriv_zero : HasDerivAt (fun z => Complex.exp (f z)) 0 s := by
    rw [hasDerivAt_iff_isLittleO]
    have h1 := h_const_near.self_of_nhds  -- exp (f s) = 1
    simp only [h1]
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [h_const_near] with z hz
    simp [hz, hc]
  have := h_chain.unique h_deriv_zero
  rw [hf_exp s hs, one_mul] at this
  exact this

/-! ## Main theorem: reverse direction -/

/-- **CorrectedPrimeZetaExtensionHyp from PiAtomHardCaseCorrectedCore.**

Given G analytic on {Re > α} with exp(G) = (s-1)ζ for Re > 1 (the corrected core),
construct Q analytic on {Re > α} with Q = primeZeta + log(s-1) for Re > 1
(the corrected prime zeta extension).

The key step: G(s) = H_zeta_log(s) + log(s-1) + c on {Re > 1} for a constant c,
proved by showing exp(G - H_zeta_log - log(·-1)) = 1 and using constancy
on the connected set {Re > 1}. -/
theorem correctedPrimeZetaExtensionHyp_of_correctedCore
    (hCore : PiAtomHardCaseCorrectedCore) :
    CorrectedPrimeZetaExtensionHyp where
  proof := fun α hα hα1 C hC σ_sign hσ hbound => by
    -- Step 1: Get G from the corrected core
    obtain ⟨G, hG_anal, hG_eq⟩ := hCore α hα hα1 C hC σ_sign hσ hbound
    -- Step 2: Define f(s) = G(s) - H_zeta_log(s) - log(s-1) on {Re > 1}
    set f : ℂ → ℂ := fun s => G s - H_zeta_log s - Complex.log (s - 1) with hf_def
    -- Step 3: f is differentiable on {Re > 1}
    have hf_diff : DifferentiableOn ℂ f {s : ℂ | (1 : ℝ) < s.re} := by
      intro s (hs : 1 < s.re)
      apply DifferentiableAt.differentiableWithinAt
      exact (((hG_anal _ (show α < s.re by linarith)).differentiableAt.sub
        (H_zeta_log_differentiableAt hs)).sub
        (differentiableAt_log_sub_one hs))
    -- Step 4: exp(f(s)) = 1 for Re(s) > 1
    have hf_exp : ∀ s : ℂ, 1 < s.re → exp (f s) = 1 := by
      intro s hs
      simp only [hf_def]
      rw [show G s - H_zeta_log s - Complex.log (s - 1) =
        G s - (H_zeta_log s + Complex.log (s - 1)) from by ring]
      rw [Complex.exp_sub, hG_eq s hs, exp_H_add_log_eq hs]
      have h_ne : (s - 1) * riemannZeta s ≠ 0 := by
        apply mul_ne_zero
        · exact sub_ne_zero.mpr (by intro h; have := congr_arg Complex.re h; simp at this; linarith)
        · exact riemannZeta_ne_zero_of_one_lt_re hs
      exact div_self h_ne
    -- Step 5: f is constant on {Re > 1}: f(s) = f(2) for all s with Re > 1
    -- Evaluate the constant c = f(2)
    set c := f 2 with hc_def
    have h_const : ∀ s : ℂ, 1 < s.re → f s = c := by
      intro s hs
      exact exp_eq_one_implies_const f hf_diff hf_exp hs (by simp)
    -- Step 6: Define Q(s) = G(s) - correctionTerm(s) - c
    refine ⟨fun s => G s - correctionTerm s - c, ?_, ?_⟩
    · -- Analyticity: G - correction - c analytic on {Re > α}
      exact ((hG_anal.sub
        ((correctionTerm_analyticOnNhd α hα).mono (fun s hs => by exact hs))).sub
        (analyticOnNhd_const))
    · -- Formula: Q(s) = primeZeta(s) + log(s-1) for Re(s) > 1
      intro s hs
      show G s - correctionTerm s - c = primeZeta s + Complex.log (s - 1)
      -- From constancy: G(s) = H_zeta_log(s) + log(s-1) + c
      have hGs : G s = H_zeta_log s + Complex.log (s - 1) + c := by
        have := h_const s hs; simp only [hf_def] at this; linear_combination this
      -- Substitute and simplify using H_zeta_log = primeZeta + correctionTerm
      rw [hGs, H_zeta_log_eq_add hs]; ring

end Aristotle.Standalone.CorrectedPrimeZetaFromCore
